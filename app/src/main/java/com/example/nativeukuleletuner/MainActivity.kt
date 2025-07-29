package co.uk.doverguitarteacher.voiceukuleletuner

import android.Manifest
import android.content.Context
import android.content.pm.PackageManager
import android.media.AudioAttributes
import android.media.SoundPool
import android.os.Bundle
import android.util.Log
import android.view.LayoutInflater
import android.view.WindowManager
import android.widget.Button
import android.widget.ImageView
import android.widget.TextView
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.slideInVertically
import androidx.compose.foundation.BorderStroke
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.border
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.KeyboardArrowLeft
import androidx.compose.material.icons.filled.KeyboardArrowRight
import androidx.compose.material.icons.filled.VolumeOff
import androidx.compose.material.icons.filled.VolumeUp
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.draw.shadow
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.*
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.res.painterResource
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.text.style.TextOverflow
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.viewinterop.AndroidView
import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat
import androidx.core.content.edit
import androidx.lifecycle.lifecycleScope
import be.tarsos.dsp.AudioDispatcher
import be.tarsos.dsp.AudioEvent
import be.tarsos.dsp.AudioProcessor
import be.tarsos.dsp.filters.HighPass
import be.tarsos.dsp.filters.LowPassFS
import be.tarsos.dsp.io.android.AudioDispatcherFactory
import be.tarsos.dsp.pitch.PitchDetectionHandler
import be.tarsos.dsp.pitch.PitchProcessor
import be.tarsos.dsp.util.fft.FFT
import com.google.android.gms.ads.*
import com.google.android.gms.ads.nativead.NativeAd
import com.google.android.gms.ads.nativead.NativeAdOptions
import com.google.android.gms.ads.nativead.NativeAdView
import kotlinx.coroutines.*
import java.util.Locale
import kotlin.math.abs
import kotlin.math.log2

enum class VisualizerMode { NONE, BARS, WAVEFORM }

class MainActivity : ComponentActivity() {

    companion object {
        private const val TAG = "MainActivity"
        private const val REQUEST_RECORD_AUDIO_PERMISSION = 200
        private const val SAMPLE_RATE = 22050
        private const val AUDIO_BUFFER_SIZE = 2048
        private const val BUFFER_OVERLAP = 0
        private const val CONFIDENCE_THRESHOLD = 0.9f
        private const val PITCH_BUFFER_SIZE = 5
        private const val IN_TUNE_DELAY_MS = 2500L
        private const val IN_TUNE_CENTS_THRESHOLD = 3.0f

        private const val PREFS_NAME = "TunerPrefs"
        private const val PREF_PEDAL_SKIN = "pedal_skin"
        private const val PREF_VDU_SKIN = "vdu_skin"

        private const val SCROLLING_WAVEFORM_MAX_SIZE = 16384
    }

    private var nativeAd by mutableStateOf<NativeAd?>(null)
    private var isAdVisible by mutableStateOf(false)
    private var isRecording by mutableStateOf(false)
    private var detectedNote by mutableStateOf("--")
    private var frequencyText by mutableStateOf("0.00 Hz")
    private var statusText by mutableStateOf("Press Start to Tune")
    private var statusColor by mutableStateOf(Color.White)
    private var rotationAngle by mutableFloatStateOf(0f)
    private var smoothedAngle by mutableFloatStateOf(0f)
    private var voiceModeEnabled by mutableStateOf(false)
    private var cents by mutableFloatStateOf(0f)
    private val activeLedIndex by derivedStateOf { (cents / 10f).coerceIn(-5f, 5f).toInt() }
    private var isMetronomeRunning by mutableStateOf(false)
    private var tempo by mutableIntStateOf(120)
    private var timeSignatureIndex by mutableIntStateOf(0)
    private var metronomeJob: Job? = null
    private var visualizerMode by mutableStateOf(VisualizerMode.WAVEFORM)
    private var magnitudes by mutableStateOf(floatArrayOf())
    private var scrollingWaveformData by mutableStateOf<List<Float>>(emptyList())
    private lateinit var soundPool: SoundPool
    private var soundUp = 0
    private var soundDown = 0
    private var soundIntune = 0
    private var soundTick = 0
    private var soundsLoaded by mutableStateOf(false)
    private var selectedPedal by mutableIntStateOf(R.drawable.u1)
    private var selectedVDU by mutableIntStateOf(R.drawable.dial2)
    private var dispatcher: AudioDispatcher? = null
    private var audioThread: Thread? = null
    private val pitchBuffer = mutableListOf<Float>()
    private var lastFeedbackTime = 0L
    private var inTuneStartTime = 0L
    private var inTuneSoundPlayed = false
    private lateinit var pedalImages: List<Int>
    private lateinit var vduImages: List<Int>
    private lateinit var timeSignatures: List<String>
    private lateinit var noteFrequencies: List<Pair<Float, String>>

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        MobileAds.initialize(this) {}
        loadAd()

        // --- BUG FIX 1: BULLETPROOF SKIN LOADING ---
        // This block fixes crashes caused by invalid data in SharedPreferences.
        // It will safely recover from corrupt/old data instead of crashing the app.
        val prefs = getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
        val defaultPedalId = R.drawable.u1
        val defaultVduId = R.drawable.dial2

        try {
            val pedalSkinName = prefs.getString(PREF_PEDAL_SKIN, "u1") ?: "u1"
            val vduSkinName = prefs.getString(PREF_VDU_SKIN, "dial2") ?: "dial2"

            val pedalId = resources.getIdentifier(pedalSkinName, "drawable", packageName)
            val vduId = resources.getIdentifier(vduSkinName, "drawable", packageName)

            selectedPedal = if (pedalId != 0) pedalId else defaultPedalId
            selectedVDU = if (vduId != 0) vduId else defaultVduId

        } catch (e: ClassCastException) {
            Log.e(TAG, "Old preference file with Integers detected. Wiping prefs and resetting to defaults.", e)
            prefs.edit { clear() }
            selectedPedal = defaultPedalId
            selectedVDU = defaultVduId
        } catch (e: Exception) {
            Log.e(TAG, "Failed to load skins, likely due to invalid preference data. Resetting to default.", e)
            selectedPedal = defaultPedalId
            selectedVDU = defaultVduId
            prefs.edit { clear() }
        }
        // --- END BUG FIX 1 ---

        pedalImages = listOf(
            R.drawable.u1, R.drawable.u2, R.drawable.u3, R.drawable.u4,
            R.drawable.u5, R.drawable.u6, R.drawable.u7, R.drawable.u8,
            R.drawable.u9, R.drawable.u10
        )
        vduImages = listOf(R.drawable.dial2, R.drawable.dial3, R.drawable.dial4)
        timeSignatures = listOf("4/4", "3/4", "6/8", "2/4", "5/4")
        noteFrequencies = listOf(
            392.00f to "G4",
            261.63f to "C4",
            329.63f to "E4",
            440.00f to "A4"
        )

        setupSoundPool()

        setContent {
            val window = this@MainActivity.window
            LaunchedEffect(isRecording, isMetronomeRunning) {
                val keepOn = isRecording || isMetronomeRunning
                if (keepOn) window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
                else window.clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
            }

            // --- BUG FIX 2: STABLE NEEDLE ANIMATION ---
            // This loop is managed by the Compose lifecycle. It automatically and safely
            // handles starting, stopping, and restarting, preventing race condition crashes.
            LaunchedEffect(Unit) {
                while (true) {
                    delay(16)
                    val smoothing = 0.1f
                    if (abs(smoothedAngle - rotationAngle) > 0.01f) {
                        smoothedAngle += (rotationAngle - smoothedAngle) * smoothing
                    } else if (smoothedAngle != rotationAngle) {
                        smoothedAngle = rotationAngle
                    }
                }
            }
            // --- END BUG FIX 2 ---

            MaterialTheme {
                Surface(modifier = Modifier.fillMaxSize()) {
                    Box(modifier = Modifier.fillMaxSize()) {
                        Image(
                            painter = painterResource(id = selectedPedal),
                            contentDescription = null,
                            modifier = Modifier.fillMaxSize(),
                            contentScale = ContentScale.Crop
                        )
                        Column(
                            Modifier.align(Alignment.TopCenter).padding(top = 24.dp),
                            horizontalAlignment = Alignment.CenterHorizontally
                        ) {
                            MetronomeControls(enabled = soundsLoaded)
                            Spacer(Modifier.height(16.dp))
                            Row(
                                horizontalArrangement = Arrangement.spacedBy(8.dp),
                                verticalAlignment = Alignment.CenterVertically
                            ) {
                                Button(
                                    onClick = {
                                        if (isRecording) stopTuner() else requestPermissionAndStartTuner()
                                    },
                                    colors = ButtonDefaults.buttonColors(
                                        containerColor = Color.Black,
                                        contentColor = Color.White
                                    )
                                ) { Text(if (isRecording) "Stop" else "Start") }
                                Button(
                                    onClick = { randomizeSkins() },
                                    colors = ButtonDefaults.buttonColors(
                                        containerColor = Color.Black,
                                        contentColor = Color.White
                                    )
                                ) { Text("Skin") }
                                VisualizerToggleButton()
                            }
                        }
                        Column(
                            horizontalAlignment = Alignment.CenterHorizontally,
                            modifier = Modifier.align(Alignment.Center).offset(y = (-15).dp)
                        ) {
                            LedTuningStrip(activeLedIndex)
                            Image(
                                painter = painterResource(id = selectedVDU),
                                contentDescription = null,
                                modifier = Modifier.size(240.dp)
                            )
                        }
                        Image(
                            painter = painterResource(id = R.drawable.needle),
                            contentDescription = null,
                            modifier = Modifier
                                .size(140.dp)
                                .align(Alignment.Center)
                                .offset(y = (-15).dp)
                                .graphicsLayer {
                                    rotationZ = smoothedAngle
                                    transformOrigin = TransformOrigin(0.5f, 0.84f)
                                }
                        )
                        Icon(
                            imageVector = if (voiceModeEnabled) Icons.Default.VolumeUp else Icons.Default.VolumeOff,
                            contentDescription = "Toggle Voice Feedback",
                            tint = if (voiceModeEnabled) Color.Green else Color.Red,
                            modifier = Modifier
                                .padding(12.dp)
                                .size(28.dp)
                                .align(Alignment.TopStart)
                                .clickable { if (soundsLoaded) voiceModeEnabled = !voiceModeEnabled }
                        )
                        Box(Modifier.align(Alignment.BottomCenter)) {
                            BottomControls()
                        }
                    }
                }
            }
        }
    }

    private fun loadAd() {
        val adUnitId = getString(R.string.native_ad_unit_id)
        val adLoader = AdLoader.Builder(this, adUnitId)
            .forNativeAd { ad ->
                nativeAd = ad
                isAdVisible = true
                Log.d(TAG, "Native ad loaded")
            }
            .withAdListener(object : AdListener() {
                override fun onAdFailedToLoad(error: LoadAdError) {
                    Log.e(TAG, "Ad error: ${error.message}")
                    nativeAd = null
                }
            })
            .withNativeAdOptions(NativeAdOptions.Builder().build())
            .build()
        adLoader.loadAd(AdRequest.Builder().build())
    }

    private fun setupSoundPool() {
        val audioAttr = AudioAttributes.Builder()
            .setUsage(AudioAttributes.USAGE_ASSISTANCE_SONIFICATION)
            .setContentType(AudioAttributes.CONTENT_TYPE_SONIFICATION)
            .build()
        soundPool = SoundPool.Builder().setMaxStreams(4).setAudioAttributes(audioAttr).build()
        var loaded = 0
        val total = 4
        soundPool.setOnLoadCompleteListener { _, _, status ->
            if (status == 0) {
                loaded++
                if (loaded == total) lifecycleScope.launch { soundsLoaded = true }
            }
        }
        soundUp = soundPool.load(this, R.raw.up, 1)
        soundDown = soundPool.load(this, R.raw.down, 1)
        soundIntune = soundPool.load(this, R.raw.intune, 1)
        soundTick = soundPool.load(this, R.raw.metronome_tick, 1)
    }

    override fun onStop()  { super.onStop(); stopMetronome() }

    override fun onDestroy() {
        super.onDestroy()
        nativeAd?.destroy()
        soundPool.release()
        dispatcher?.stop()
    }

    private fun requestPermissionAndStartTuner() {
        when {
            ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) ==
                    PackageManager.PERMISSION_GRANTED -> lifecycleScope.launch { startTuner() }
            else -> ActivityCompat.requestPermissions(this, arrayOf(Manifest.permission.RECORD_AUDIO), REQUEST_RECORD_AUDIO_PERMISSION)
        }
    }

    @Suppress("DEPRECATION")
    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQUEST_RECORD_AUDIO_PERMISSION && grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
            lifecycleScope.launch { startTuner() }
        } else {
            statusText = "Permission Denied"
            statusColor = Color.Red
            Toast.makeText(this, "Microphone permission is required for the tuner.", Toast.LENGTH_LONG).show()
        }
    }

    private suspend fun startTuner() {
        if (isRecording) return
        try {
            dispatcher = withContext(Dispatchers.IO) {
                AudioDispatcherFactory.fromDefaultMicrophone(SAMPLE_RATE, AUDIO_BUFFER_SIZE, BUFFER_OVERLAP)
            }
            val pitchHandler = PitchDetectionHandler { result, _ ->
                if (result.isPitched && result.probability > CONFIDENCE_THRESHOLD) {
                    lifecycleScope.launch { updatePitch(result.pitch) }
                }
            }
            val pitchProcessor = PitchProcessor(PitchProcessor.PitchEstimationAlgorithm.YIN, SAMPLE_RATE.toFloat(), AUDIO_BUFFER_SIZE, pitchHandler)
            val fftProcessor = object : AudioProcessor {
                private val fft = FFT(AUDIO_BUFFER_SIZE)
                override fun process(event: AudioEvent): Boolean {
                    val buf = event.floatBuffer.clone()
                    lifecycleScope.launch {
                        val forFft = buf.clone()
                        val mags = FloatArray(forFft.size / 2)
                        fft.forwardTransform(forFft)
                        fft.modulus(forFft, mags)
                        magnitudes = mags
                        val new = scrollingWaveformData.toMutableList()
                        new.addAll(buf.toList())
                        while (new.size > SCROLLING_WAVEFORM_MAX_SIZE) new.removeAt(0)
                        scrollingWaveformData = new
                    }
                    return true
                }
                override fun processingFinished() {}
            }
            dispatcher?.apply {
                addAudioProcessor(HighPass(60f, SAMPLE_RATE.toFloat()))
                addAudioProcessor(LowPassFS(1500f, SAMPLE_RATE.toFloat()))
                addAudioProcessor(pitchProcessor)
                addAudioProcessor(fftProcessor)
            }
            audioThread = Thread(dispatcher, "AudioDispatcher").apply { isDaemon = true; start() }
            isRecording = true
            statusText = "Listening…"
            statusColor = Color.White
        } catch (e: Exception) {
            Log.e(TAG, "Tuner error", e)
            isRecording = false
            statusText = "Tuner Error"
            statusColor = Color.Red
            if (e is IllegalStateException) Toast.makeText(this, "Microphone might be used by another app.", Toast.LENGTH_LONG).show()
        }
    }

    private fun stopTuner() {
        dispatcher?.stop()
        audioThread?.interrupt()
        isRecording = false
        cents = 0f
        rotationAngle = 0f
        pitchBuffer.clear()
        detectedNote = "--"
        frequencyText = "0.00 Hz"
        statusText = "Press Start to Tune"
        statusColor = Color.White
        magnitudes = floatArrayOf()
        scrollingWaveformData = emptyList()
    }

    private fun updatePitch(pitch: Float) {
        if (!isRecording) return
        pitchBuffer.add(pitch)
        if (pitchBuffer.size < PITCH_BUFFER_SIZE) return

        val stablePitch = pitchBuffer.sorted()[PITCH_BUFFER_SIZE / 2]
        pitchBuffer.removeAt(0)
        val nearest = getNearestNoteFrequency(stablePitch) ?: return
        val (noteFreq, noteName) = nearest
        cents = 1200f * log2(stablePitch / noteFreq)
        rotationAngle = (cents.coerceIn(-50f, 50f) / 50f) * 90f
        detectedNote = noteName
        frequencyText = String.format(Locale.US, "%.2f Hz", stablePitch)

        val inTune = abs(cents) <= IN_TUNE_CENTS_THRESHOLD
        if (inTune) {
            statusText = "$noteName (In Tune)"
            statusColor = Color.Green
            if (inTuneStartTime == 0L) inTuneStartTime = System.currentTimeMillis()
            if (System.currentTimeMillis() - inTuneStartTime >= IN_TUNE_DELAY_MS && !inTuneSoundPlayed) {
                playFeedbackSound(soundIntune)
                inTuneSoundPlayed = true
            }
        } else {
            inTuneStartTime = 0L
            inTuneSoundPlayed = false
            statusText = if (cents < 0) "$noteName (Tune Up)" else "$noteName (Tune Down)"
            statusColor = Color(0xFFFFA000)
            playFeedbackSound(if (cents < 0) soundUp else soundDown)
        }
    }

    private fun playFeedbackSound(soundId: Int) {
        if (!soundsLoaded) return
        val now = System.currentTimeMillis()
        val cooldown = if (soundId == soundIntune) 0 else 1500
        if (voiceModeEnabled && isRecording && now - lastFeedbackTime > cooldown) {
            soundPool.play(soundId, 1f, 1f, 1, 0, 1f)
            lastFeedbackTime = now
        }
    }

    private fun startMetronome() {
        if (isMetronomeRunning || !soundsLoaded) return
        isMetronomeRunning = true
        metronomeJob = lifecycleScope.launch(Dispatchers.Default) {
            while (isActive) {
                withContext(Dispatchers.Main) {
                    soundPool.play(soundTick, 1f, 1f, 0, 0, 1f)
                }
                delay(60_000L / tempo)
            }
        }
    }

    private fun stopMetronome() {
        metronomeJob?.cancel()
        isMetronomeRunning = false
    }

    private fun getNearestNoteFrequency(pitch: Float): Pair<Float, String>? =
        noteFrequencies.minByOrNull { abs(pitch - it.first) }

    // --- BUG FIX: CRASH-PROOF SKIN CHANGE ---
    // This function now safely stops the tuner before changing skins and restarts it after,
    // preventing the race condition crash you identified.
    private fun randomizeSkins() {
        val wasRecording = isRecording
        if (wasRecording) {
            stopTuner()
        }

        val newPedal = pedalImages.random()
        val newVdu = vduImages.random()
        selectedPedal = newPedal
        selectedVDU = newVdu

        val newPedalName = resources.getResourceEntryName(newPedal)
        val newVduName = resources.getResourceEntryName(newVdu)

        getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE).edit {
            putString(PREF_PEDAL_SKIN, newPedalName)
            putString(PREF_VDU_SKIN, newVduName)
        }

        if (wasRecording) {
            lifecycleScope.launch {
                delay(100) // Brief delay to ensure UI has settled before restarting audio.
                startTuner()
            }
        }
    }
    // --- END BUG FIX ---

    @Composable
    fun BottomControls() {
        Column(
            Modifier.fillMaxWidth().padding(16.dp),
            horizontalAlignment = Alignment.CenterHorizontally
        ) {
            VisualizerDisplay()
            Spacer(Modifier.height(16.dp))
            Row(
                Modifier.fillMaxWidth(),
                Arrangement.SpaceEvenly,
                Alignment.CenterVertically
            ) {
                Text(text = "Note: $detectedNote", color = Color.White, fontSize = 18.sp, fontWeight = FontWeight.Bold, style = LocalTextStyle.current.copy(shadow = Shadow(Color.Black, blurRadius = 8f)), maxLines = 1, overflow = TextOverflow.Ellipsis)
                Text(text = frequencyText, fontSize = 14.sp, color = Color.LightGray, style = LocalTextStyle.current.copy(shadow = Shadow(Color.Black, blurRadius = 6f)), maxLines = 1, overflow = TextOverflow.Ellipsis)
                Text(text = statusText, fontSize = 16.sp, color = statusColor, style = LocalTextStyle.current.copy(shadow = Shadow(Color.Black, blurRadius = 8f)), maxLines = 1, overflow = TextOverflow.Ellipsis)
            }
            Spacer(Modifier.height(16.dp))
            nativeAd?.let { ad ->
                AnimatedVisibility(
                    visible = isAdVisible,
                    enter = slideInVertically(initialOffsetY = { it / 2 }, animationSpec = tween(500)) + fadeIn(animationSpec = tween(500))
                ) { NativeAdView(ad) }
            }
        }
    }

    @Composable
    fun MetronomeControls(enabled: Boolean) {
        Surface(
            shape = RoundedCornerShape(12.dp),
            color = Color.Black.copy(alpha = 0.7f),
            border = BorderStroke(1.dp, Color.Gray.copy(alpha = 0.5f))
        ) {
            Row(
                Modifier.height(48.dp).padding(horizontal = 8.dp),
                Arrangement.Center,
                Alignment.CenterVertically
            ) {
                IconButton(onClick = { if (tempo > 40) tempo-- }, enabled = enabled) {
                    Icon(Icons.Default.KeyboardArrowLeft, contentDescription = null, tint = Color.White)
                }
                Text("$tempo BPM", color = Color.White, fontWeight = FontWeight.SemiBold, fontSize = 14.sp, modifier = Modifier.width(80.dp), textAlign = TextAlign.Center)
                IconButton(onClick = { if (tempo < 240) tempo++ }, enabled = enabled) {
                    Icon(Icons.Default.KeyboardArrowRight, contentDescription = null, tint = Color.White)
                }
                Spacer(Modifier.width(4.dp)); Divider(Modifier.height(24.dp).width(1.dp), color = Color.Gray); Spacer(Modifier.width(4.dp))
                IconButton(
                    onClick = { timeSignatureIndex = (timeSignatureIndex - 1 + timeSignatures.size) % timeSignatures.size },
                    enabled = enabled
                ) {
                    Icon(Icons.Default.KeyboardArrowLeft, null, tint = Color.White)
                }
                Text(timeSignatures[timeSignatureIndex], color = Color.White, fontWeight = FontWeight.SemiBold, fontSize = 14.sp, modifier = Modifier.width(40.dp), textAlign = TextAlign.Center)
                IconButton(
                    onClick = { timeSignatureIndex = (timeSignatureIndex + 1) % timeSignatures.size },
                    enabled = enabled
                ) {
                    Icon(Icons.Default.KeyboardArrowRight, null, tint = Color.White)
                }
                Spacer(Modifier.width(8.dp))
                Button(
                    onClick = { if (isMetronomeRunning) stopMetronome() else startMetronome() },
                    enabled = enabled,
                    modifier = Modifier.fillMaxHeight(0.75f),
                    contentPadding = PaddingValues(horizontal = 10.dp),
                    colors = ButtonDefaults.buttonColors(containerColor = if (isMetronomeRunning) Color(0xFFE53935) else Color(0xFF43A047))
                ) { /* empty */ }
            }
        }
    }

    @Composable
    fun VisualizerToggleButton() {
        Button(
            onClick = {
                val all = VisualizerMode.values()
                visualizerMode = all[(all.indexOf(visualizerMode) + 1) % all.size]
            },
            colors = ButtonDefaults.buttonColors(containerColor = Color.Black, contentColor = Color.White)
        ) {
            val name = when (visualizerMode) {
                VisualizerMode.WAVEFORM -> "Wave"
                VisualizerMode.BARS     -> "Bars"
                VisualizerMode.NONE     -> "Off"
            }
            Text("Visualizer: $name")
        }
    }

    @Composable
    fun VisualizerDisplay() {
        Box(
            Modifier.fillMaxWidth(0.9f).height(80.dp).background(Color.Black.copy(alpha = 0.6f), RoundedCornerShape(8.dp)).clip(RoundedCornerShape(8.dp)).padding(8.dp),
            contentAlignment = Alignment.Center
        ) {
            when (visualizerMode) {
                VisualizerMode.BARS     -> BarsVisualizer(Modifier.fillMaxSize(), magnitudes)
                VisualizerMode.WAVEFORM -> WaveformVisualizer(Modifier.fillMaxSize(), scrollingWaveformData)
                VisualizerMode.NONE     -> Text("No Visualizer", color = Color.Gray, fontSize = 12.sp)
            }
        }
    }

    @Composable
    fun BarsVisualizer(modifier: Modifier, magnitudes: FloatArray) {
        Canvas(modifier) {
            if (magnitudes.isEmpty()) return@Canvas
            val bars = 64
            val barWidth = size.width / bars
            val space = 1.dp.toPx()
            val maxMag = magnitudes.take(bars).maxOrNull()?.coerceAtLeast(1f) ?: 1f
            magnitudes.take(bars).forEachIndexed { i, m ->
                val h = (m / maxMag).coerceIn(0f, 1f) * size.height
                val color = lerp(Color.Green, Color.Red, m / maxMag)
                drawRect(color, topLeft = Offset(i * barWidth, size.height - h), size = Size((barWidth - space).coerceAtLeast(0f), h))
            }
        }
    }

    @Composable
    fun WaveformVisualizer(modifier: Modifier, data: List<Float>) {
        Canvas(modifier) {
            val samples = 4096
            if (data.isEmpty()) return@Canvas
            val slice = data.takeLast(samples)
            val display = if (slice.size < samples) List(samples - slice.size) { 0f } + slice else slice
            val step = size.width / display.size
            val midY = size.height / 2f
            val wave = Color(0xFF4CAF50)
            val center = Color.Black.copy(alpha = 0.3f)
            val top = Path().apply {
                moveTo(0f, midY)
                display.forEachIndexed { i, v -> lineTo(i * step, midY - (v.coerceAtLeast(0f) * midY)) }
                lineTo(size.width, midY); close()
            }
            val bottom = Path().apply {
                moveTo(0f, midY)
                display.forEachIndexed { i, v -> lineTo(i * step, midY - (v.coerceAtMost(0f) * midY)) }
                lineTo(size.width, midY); close()
            }
            drawPath(top, wave); drawPath(bottom, wave)
            drawLine(center, Offset(0f, midY), Offset(size.width, midY), 1.dp.toPx())
        }
    }

    @Composable
    fun LedTuningStrip(index: Int) {
        Row(
            Modifier.shadow(8.dp, RoundedCornerShape(6.dp), spotColor = Color.Green),
            Arrangement.Center,
            Alignment.CenterVertically
        ) {
            (-5..5).forEach {
                val isActive = when {
                    index < 0 -> it in index until 0
                    index > 0 -> it in 1..index
                    else      -> it == 0
                }
                val color = when {
                    it == 0        -> Color(0xFF00C853)
                    abs(it) <= 2   -> Color(0xFFFFFF00)
                    else           -> Color(0xFFD50000)
                }
                LedIndicator(isActive, color)
                if (it < 5) Spacer(Modifier.width(2.dp))
            }
        }
    }

    @Composable
    fun LedIndicator(active: Boolean, activeColor: Color) {
        val c = if (active) activeColor else Color.DarkGray.copy(alpha = 0.5f)
        Box(
            Modifier.size(20.dp, 24.dp).background(c, RoundedCornerShape(4.dp)).border(1.dp, Color.Black.copy(alpha = 0.3f), RoundedCornerShape(4.dp))
        )
    }
}

@Composable
fun NativeAdView(ad: NativeAd) {
    AndroidView(
        modifier = Modifier.fillMaxWidth().padding(vertical = 8.dp),
        factory = { ctx -> LayoutInflater.from(ctx).inflate(R.layout.ad_unified, null) as NativeAdView },
        update = { adView ->
            adView.headlineView = adView.findViewById(R.id.ad_headline)
            adView.bodyView = adView.findViewById(R.id.ad_body)
            adView.callToActionView = adView.findViewById(R.id.ad_call_to_action)
            adView.iconView = adView.findViewById(R.id.ad_app_icon)
            (adView.headlineView as? TextView)?.text = ad.headline
            (adView.bodyView as? TextView)?.text = ad.body
            (adView.callToActionView as? Button)?.text = ad.callToAction
            (adView.iconView as? ImageView)?.setImageDrawable(ad.icon?.drawable)
            adView.setNativeAd(ad)
        }
    )
}
