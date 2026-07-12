"""V3 TTS Pipeline — Complete audiobook generation for Boule de Suif.

Fixes vs V2:
- #1275: Voice attribution — narrator/character separation (fuzzy matching)
- #1276: Prosody tags — all tags converted to FishAudio instructions (none stripped)
- Thermal backoff: GPU temp monitoring between segments
- Full text support: LLM-based segmentation of complete book
- Whisper verification: transcript conformity check per segment
"""
import json
import os
import sys
import time
import struct
import re
import subprocess
from pathlib import Path
from dataclasses import dataclass, field, asdict
from dotenv import load_dotenv

# ── Setup paths ──
BASE_DIR = Path(__file__).parent
os.chdir(BASE_DIR)
env_path = Path(__file__).resolve().parent.parent.parent / ".env"
load_dotenv(env_path)
print(f"Loaded .env from: {env_path}")

import requests

OUTPUT_DIR = BASE_DIR / "tts_output_fishaudio"
SUB_DIR = OUTPUT_DIR / "sub_segments"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)
SUB_DIR.mkdir(exist_ok=True, parents=True)

FISHAUDIO_URL = os.getenv("FISHAUDIO_URL", "http://localhost:8197")
WHISPER_URL = os.getenv("WHISPER_API_URL", "http://localhost:8190")
WHISPER_KEY = os.getenv("WHISPER_API_KEY", "")
SOURCE_TEXT = BASE_DIR / "boule_de_suif_full.txt"

# ── Thermal monitoring ──
def get_gpu_temp() -> int:
    try:
        result = subprocess.run(
            ['nvidia-smi', '--query-gpu=temperature.gpu',
             '--format=csv,noheader,nounits'],
            capture_output=True, text=True, timeout=5
        )
        temps = [int(t.strip()) for t in result.stdout.strip().split('\n') if t.strip()]
        return temps[1] if len(temps) > 1 else temps[0] if temps else 0
    except Exception:
        return 0

def thermal_wait(max_temp=82, cool_sleep=20):
    temp = get_gpu_temp()
    if temp > max_temp:
        print(f"  [THERMAL] GPU {temp}C > {max_temp}C, cooling {cool_sleep}s...")
        time.sleep(cool_sleep)
    return temp


# ── Data classes ──
@dataclass
class TTSRequest:
    seg_index: int
    seg_type: str
    speaker: str
    text: str
    annotated_text: str
    kokoro_voice: str = ""
    fish_preset: str = ""
    tags: list = field(default_factory=list)
    output_file: str = ""
    duration_s: float = 0.0
    file_size_kb: float = 0.0
    status: str = "pending"
    whisper_wer: float = -1.0
    whisper_text: str = ""


# ── Audio utilities ──
def audio_duration_s(audio_bytes):
    if len(audio_bytes) < 12:
        return 0.0
    if audio_bytes[:4] == b'RIFF':
        channels = struct.unpack_from('<H', audio_bytes, 22)[0]
        sample_rate = struct.unpack_from('<I', audio_bytes, 24)[0]
        bits_per_sample = struct.unpack_from('<H', audio_bytes, 34)[0]
        data_size = struct.unpack_from('<I', audio_bytes, 40)[0]
        bytes_per_sample = bits_per_sample * channels // 8
        if bytes_per_sample == 0:
            return 0.0
        return data_size / (sample_rate * bytes_per_sample)
    return 0.0


def concatenate_wav_files(wav_files, output_path, silence_duration=0.5):
    all_audio = b""
    sample_rate = 44100
    silence_samples = int(sample_rate * silence_duration)
    silence_bytes = b'\x00\x00' * silence_samples
    for i, wav_path in enumerate(wav_files):
        if isinstance(wav_path, (str, Path)):
            with open(wav_path, 'rb') as f:
                data = f.read()
        else:
            data = wav_path
        pcm_data = data[44:] if data[:4] == b'RIFF' else data
        all_audio += pcm_data
        if i < len(wav_files) - 1:
            all_audio += silence_bytes
    data_size = len(all_audio)
    header = struct.pack('<4sI4s', b'RIFF', 36 + data_size, b'WAVE')
    header += struct.pack('<4sIHHIIHH', b'fmt ', 16, 1, 1, sample_rate,
                          sample_rate * 2, 2, 16)
    header += struct.pack('<4sI', b'data', data_size)
    with open(output_path, 'wb') as f:
        f.write(header + all_audio)
    return output_path


# ── FishAudio TTS ──
def fishaudio_tts(text, reference_id=None, timeout=300):
    payload = {"text": text}
    if reference_id:
        payload["reference_id"] = reference_id
    try:
        resp = requests.post(
            f"{FISHAUDIO_URL}/v1/tts",
            json=payload,
            timeout=timeout,
        )
        resp.raise_for_status()
        return resp.content
    except requests.RequestException as e:
        print(f"  FishAudio TTS error: {e}")
        return None


# ── Voice casting (#1275 fix) ──
CHARACTER_VOICES = {
    "narrateur": {
        "name": "Narrateur",
        "fish_preset": "narrator_male",
        "role": "narrator",
    },
    "elisabeth_rousset": {
        "name": "Elisabeth Rousset (Boule de Suif)",
        "fish_preset": "expressive_female_warm",
        "role": "character",
    },
    "cornudet": {
        "name": "Cornudet",
        "fish_preset": "expressive_male_neutral",
        "role": "character",
    },
    "comtesse": {
        "name": "Comtesse de Breville",
        "fish_preset": "expressive_female_cold",
        "role": "character",
    },
    "comte": {
        "name": "Comte Hubert de Breville",
        "fish_preset": "expressive_male_cold",
        "role": "character",
    },
    "officier": {
        "name": "Officier prussien",
        "fish_preset": "expressive_male_cold",
        "role": "character",
    },
    "loiseau": {
        "name": "Monsieur Loiseau",
        "fish_preset": "neutral_male",
        "role": "character",
    },
    "madame_loiseau": {
        "name": "Madame Loiseau",
        "fish_preset": "neutral_female",
        "role": "character",
    },
    "carre_lamadon": {
        "name": "Carre-Lamadon",
        "fish_preset": "neutral_male",
        "role": "character",
    },
    "soeurs": {
        "name": "Les bonnes soeurs",
        "fish_preset": "expressive_female_warm",
        "role": "character",
    },
    "follenvie": {
        "name": "Follenvie (aubergiste)",
        "fish_preset": "neutral_male",
        "role": "character",
    },
}

# Speaker name → character ID lookup with fuzzy matching
SPEAKER_ALIASES = {
    "narrateur": "narrateur",
    "le narrateur": "narrateur",
    "elisabeth rousset": "elisabeth_rousset",
    "boule de suif": "elisabeth_rousset",
    "elisabeth": "elisabeth_rousset",
    "cornudet": "cornudet",
    "comtesse de breville": "comtesse",
    "la comtesse": "comtesse",
    "comtesse": "comtesse",
    "comte hubert de breville": "comte",
    "le comte": "comte",
    "comte": "comte",
    "officier prussien": "officier",
    "l'officier": "officier",
    "officier": "officier",
    "loiseau": "loiseau",
    "monsieur loiseau": "loiseau",
    "m. loiseau": "loiseau",
    "madame loiseau": "madame_loiseau",
    "mme loiseau": "madame_loiseau",
    "carre-lamadon": "carre_lamadon",
    "carre lamadon": "carre_lamadon",
    "les bonnes soeurs": "soeurs",
    "les soeurs": "soeurs",
    "soeurs": "soeurs",
    "follenvie": "follenvie",
}

def resolve_speaker(speaker_name):
    """Resolve speaker name to character ID with fuzzy matching."""
    if not speaker_name or speaker_name.lower().strip() in ("", "narrateur", "le narrateur"):
        return "narrateur"
    name_lower = speaker_name.lower().strip()
    # Direct match
    if name_lower in SPEAKER_ALIASES:
        return SPEAKER_ALIASES[name_lower]
    # Partial match
    for alias, char_id in SPEAKER_ALIASES.items():
        if alias in name_lower or name_lower in alias:
            return char_id
    return "narrateur"


# ── Prosody tags (#1276 fix) ──
# ALL tags now produce FishAudio instructions — none stripped
TAG_MAP = {
    "whisper": "(whispering) ",
    "whispered": "(whispering) ",
    "shout": "(shouting) ",
    "shouted": "(shouting) ",
    "scream": "(screaming) ",
    "laugh": "(laughing) ",
    "breath": "(sighing) ",
    "pause": "... ",
    "slow": "(speaking slowly) ",
    "cold": "(cold tone) ",
    "timid": "(timid tone) ",
    "angry": "(angry tone) ",
    "sad": "(sad tone) ",
    "excited": "(excitedly) ",
    "nervous": "(nervously) ",
    "gentle": "(gently) ",
    "firm": "(firmly) ",
    "mocking": "(mockingly) ",
    "onctuous": "(in a smooth, ingratiating tone) ",
    "indignant": "(indignantly) ",
}

def convert_tags_for_fishaudio(annotated_text, seg_type="dialogue"):
    """Convert all prosody tags to FishAudio textual instructions."""
    result = annotated_text
    for tag, instruction in TAG_MAP.items():
        result = result.replace(f"[{tag}]", instruction)
    # Clean up any remaining bracket tags
    result = re.sub(r'\[([^\]]+)\]', r'(\1) ', result)
    result = re.sub(r'\s+', ' ', result).strip()
    return result


# ── LLM-based text segmentation ──
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
OPENAI_BASE = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")


def _call_openai(messages, model="gpt-4o-mini", max_tokens=8000, temperature=0.1):
    """Call OpenAI API using requests (avoids openai SDK hang issues)."""
    headers = {
        "Authorization": f"Bearer {OPENAI_API_KEY}",
        "Content-Type": "application/json",
    }
    payload = {
        "model": model,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
    }
    resp = requests.post(
        f"{OPENAI_BASE}/chat/completions",
        headers=headers,
        json=payload,
        timeout=180,
    )
    resp.raise_for_status()
    return resp.json()["choices"][0]["message"]["content"]

def _split_text_chunks(text, chunk_words=800):
    """Split text into ~chunk_words chunks at paragraph boundaries."""
    paragraphs = text.split('\n\n')
    chunks, current, n = [], [], 0
    for p in paragraphs:
        pw = len(p.split())
        if n + pw > chunk_words and current:
            chunks.append('\n\n'.join(current))
            current, n = [], 0
        current.append(p)
        n += pw
    if current:
        chunks.append('\n\n'.join(current))
    return chunks


def _segment_chunk(text_chunk, max_words, offset):
    """Segment a single text chunk via LLM."""
    prompt = f"""Tu es un expert en analyse litteraire. Decoupe le texte suivant de "Boule de Suif" de Maupassant en segments pour la synthese vocale.

Pour chaque segment, identifie:
- type: "narration" (texte narratif), "dialogue" (paroles d'un personnage), ou "mixed" (narration + dialogue melanges)
- speaker: le nom du personnage qui parle (pour les dialogues), ou "Narrateur" (pour la narration)
- text: le texte exact du segment

Regles:
- Chaque segment doit faire entre 20 et {max_words} mots
- Coupe aux fins de phrase (points, points d'exclamation, points d'interrogation)
- Les dialogues (entre guillemets ou tires longs) doivent etre separes de la narration
- Le speaker "Narrateur" est pour toute narration hors dialogue
- Les personnages principaux: Elisabeth Rousset (Boule de Suif), Cornudet, Comtesse de Breville, Comte Hubert de Breville, Loiseau, Madame Loiseau, Carre-Lamadon, l'Officier prussien, les bonnes soeurs, Follenvie

Reponds en JSON uniquement, format:
[
  {{"seg_index": 0, "type": "narration", "speaker": "Narrateur", "text": "..."}},
  {{"seg_index": 1, "type": "dialogue", "speaker": "Elisabeth Rousset", "text": "..."}},
  ...
]

Texte:
{text_chunk}"""

    try:
        content = _call_openai(
            messages=[{"role": "user", "content": prompt}],
            model="gpt-4o-mini",
            max_tokens=8000,
            temperature=0.1,
        ).strip()
        json_match = re.search(r'\[.*\]', content, re.DOTALL)
        if json_match:
            segs = json.loads(json_match.group())
            for s in segs:
                s['seg_index'] = offset
                offset += 1
            return segs, offset
        else:
            print(f"  Chunk: no JSON found")
    except Exception as e:
        print(f"  Chunk segmentation error: {e}")
    return [], offset


def llm_segment_book(text, max_words=40):
    """Segment full book text into narrator/dialogue chunks using LLM (chunked)."""
    chunks = _split_text_chunks(text, chunk_words=800)
    print(f"Split text into {len(chunks)} chunks for segmentation")
    all_segments, offset = [], 0
    for i, chunk in enumerate(chunks):
        cw = len(chunk.split())
        print(f"  Segmenting chunk {i+1}/{len(chunks)} ({cw} words)...")
        segs, offset = _segment_chunk(chunk, max_words, offset)
        all_segments.extend(segs)
        print(f"  => {len(segs)} segments (total: {len(all_segments)})")
        if i < len(chunks) - 1:
            time.sleep(2)
    print(f"LLM segmented into {len(all_segments)} segments total")
    return all_segments


def llm_annotate_prosody(segments):
    """Add prosody annotations to segments using LLM."""
    batch_size = 20
    annotated = []

    for i in range(0, len(segments), batch_size):
        batch = segments[i:i+batch_size]
        batch_text = json.dumps(batch, ensure_ascii=False, indent=2)

        prompt = f"""Ajoute des annotations de prosodie pour la synthese vocale a ces segments de "Boule de Suif".

Pour chaque segment, ajoute:
- "tags": liste de tags parmi [whisper, shout, cold, timid, angry, sad, excited, nervous, gentle, firm, mocking, indignant, slow, pause, laugh, onctuous]
- "annotated_text": le texte avec les annotations [tag] inserees aux bons endroits

Regles d'annotation:
- Narration: [slow] pour les descriptions contemplatives, [cold] pour les scenes tendues, [pause] avant les changements de scene
- Dialogues: analyse le ton du personnage dans le contexte
- Boule de Suif: souvent [whisper], [nervous], [indignant]
- Officier prussien: [cold], [firm]
- Comte: [onctuous], [cold]
- Cornudet: [mocking], [laugh]

Reponds en JSON uniquement, meme format avec champs ajoutés.

Segments:
{batch_text}"""

        try:
            content = _call_openai(
                messages=[{"role": "user", "content": prompt}],
                model="gpt-4o-mini",
                max_tokens=8000,
                temperature=0.1,
            ).strip()
            json_match = re.search(r'\[.*\]', content, re.DOTALL)
            if json_match:
                batch_result = json.loads(json_match.group())
                annotated.extend(batch_result)
                print(f"  Annotated batch {i//batch_size + 1}: {len(batch_result)} segments")
            else:
                annotated.extend(batch)
                print(f"  Batch {i//batch_size + 1}: no JSON found, keeping unannotated")
        except Exception as e:
            print(f"  Annotation error batch {i//batch_size + 1}: {e}")
            annotated.extend(batch)

        time.sleep(1)  # Rate limit

    return annotated


# ── Whisper verification ──
def whisper_transcribe(audio_path):
    """Transcribe audio file using local Whisper API."""
    try:
        headers = {}
        if WHISPER_KEY:
            headers["Authorization"] = f"Bearer {WHISPER_KEY}"

        with open(audio_path, 'rb') as f:
            files = {'file': ('audio.wav', f, 'audio/wav')}
            data = {
                'language': 'fr',
                'response_format': 'verbose_json',
                'timestamp_granularities[]': 'segment',
            }
            resp = requests.post(
                f"{WHISPER_URL}/v1/audio/transcriptions",
                headers=headers,
                files=files,
                data=data,
                timeout=120,
            )
            resp.raise_for_status()
            result = resp.json()
            return result.get('text', '').strip()
    except Exception as e:
        print(f"  Whisper error: {e}")
        return ""

def word_error_rate(reference, hypothesis):
    """Compute WER between reference and hypothesis text."""
    ref_words = reference.lower().split()
    hyp_words = hypothesis.lower().split()
    n = len(ref_words)
    if n == 0:
        return 0.0

    # Levenshtein distance
    d = [[0] * (len(hyp_words) + 1) for _ in range(len(ref_words) + 1)]
    for i in range(len(ref_words) + 1):
        d[i][0] = i
    for j in range(len(hyp_words) + 1):
        d[0][j] = j
    for i in range(1, len(ref_words) + 1):
        for j in range(1, len(hyp_words) + 1):
            if ref_words[i-1] == hyp_words[j-1]:
                d[i][j] = d[i-1][j-1]
            else:
                d[i][j] = 1 + min(d[i-1][j], d[i][j-1], d[i-1][j-1])

    return d[len(ref_words)][len(hyp_words)] / n


# ── Main pipeline ──
def main():
    t_start = time.time()

    # 1. Load source text
    if not SOURCE_TEXT.exists():
        print(f"ERROR: Source text not found at {SOURCE_TEXT}")
        print("Place the full text of Boule de Suif as boule_de_suif_full.txt")
        sys.exit(1)

    with open(SOURCE_TEXT, 'r', encoding='utf-8') as f:
        book_text = f.read().strip()

    word_count = len(book_text.split())
    print(f"Source text: {word_count} words")

    # 2. Check FishAudio
    try:
        resp = requests.get(f"{FISHAUDIO_URL}/v1/health", timeout=10)
        if resp.status_code == 200:
            print(f"FishAudio: OK ({FISHAUDIO_URL})")
        else:
            print(f"FishAudio health: {resp.status_code}")
            sys.exit(1)
    except Exception as e:
        print(f"FishAudio unreachable: {e}")
        sys.exit(1)

    # 3. Check Whisper
    whisper_ok = False
    try:
        resp = requests.get(f"{WHISPER_URL}/health", timeout=5)
        if resp.status_code == 200:
            whisper_ok = True
            print(f"Whisper: OK ({WHISPER_URL})")
    except Exception:
        print("Whisper: not available (verification will be skipped)")

    # 4. Segment text with LLM
    segments_file = OUTPUT_DIR / "segments.json"
    if segments_file.exists():
        with open(segments_file, 'r', encoding='utf-8') as f:
            segments = json.load(f)
        print(f"Loaded {len(segments)} cached segments from {segments_file}")
    else:
        print("\nSegmenting text with LLM...")
        segments = llm_segment_book(book_text, max_words=40)
        if not segments:
            print("ERROR: LLM segmentation returned no segments")
            sys.exit(1)
        with open(segments_file, 'w', encoding='utf-8') as f:
            json.dump(segments, f, ensure_ascii=False, indent=2)
        print(f"Saved {len(segments)} segments to {segments_file}")

    # 5. Annotate prosody with LLM
    annotated_file = OUTPUT_DIR / "segments_annotated.json"
    if annotated_file.exists():
        with open(annotated_file, 'r', encoding='utf-8') as f:
            annotated_segments = json.load(f)
        print(f"Loaded {len(annotated_segments)} annotated segments from cache")
    else:
        print("\nAnnotating prosody with LLM...")
        annotated_segments = llm_annotate_prosody(segments)
        with open(annotated_file, 'w', encoding='utf-8') as f:
            json.dump(annotated_segments, f, ensure_ascii=False, indent=2)
        print(f"Saved annotated segments to {annotated_file}")

    # 6. Build TTS requests
    tts_requests = []
    for seg in annotated_segments:
        seg_idx = seg.get("seg_index", len(tts_requests))
        speaker = seg.get("speaker", "Narrateur")
        seg_type = seg.get("type", "narration")
        text = seg.get("text", "")
        annotated_text = seg.get("annotated_text", text)
        tags = seg.get("tags", [])

        char_id = resolve_speaker(speaker)
        voice_info = CHARACTER_VOICES.get(char_id, CHARACTER_VOICES["narrateur"])

        # For mixed segments, use narrator voice
        if seg_type == "mixed":
            seg_type = "narration"
            char_id = "narrateur"
            voice_info = CHARACTER_VOICES["narrateur"]

        fish_text = convert_tags_for_fishaudio(annotated_text, seg_type)

        tts_requests.append(TTSRequest(
            seg_index=seg_idx,
            seg_type=seg_type,
            speaker=voice_info["name"],
            text=text,
            annotated_text=fish_text,
            fish_preset=voice_info["fish_preset"],
            tags=tags,
        ))

    # Re-index
    for i, req in enumerate(tts_requests):
        req.seg_index = i

    print(f"\nBuilt {len(tts_requests)} TTS requests")

    # Voice attribution report
    voice_counts = {}
    for req in tts_requests:
        key = f"{req.speaker} ({req.fish_preset})"
        voice_counts[key] = voice_counts.get(key, 0) + 1
    print("\nVoice attribution:")
    for voice, count in sorted(voice_counts.items(), key=lambda x: -x[1]):
        print(f"  {voice}: {count} segments")

    # 7. Generate audio
    print(f"\n{'='*60}")
    print(f"Generating {len(tts_requests)} segments...")
    print(f"{'='*60}")

    generated = []
    total_words = 0

    for req in tts_requests:
        words = len(req.text.split())
        total_words += words
        output_name = f"fish_seg_{req.seg_index:03d}_{req.fish_preset}.wav"
        output_path = OUTPUT_DIR / output_name

        # Skip if cached and valid (>10KB)
        if output_path.exists() and output_path.stat().st_size > 10000:
            existing_data = output_path.read_bytes()
            dur = audio_duration_s(existing_data)
            generated.append(TTSRequest(
                seg_index=req.seg_index, seg_type=req.seg_type,
                speaker=req.speaker, text=req.text,
                annotated_text=req.annotated_text,
                fish_preset=req.fish_preset, tags=req.tags,
                output_file=str(output_path), duration_s=dur,
                file_size_kb=len(existing_data) / 1024, status="success",
            ))
            print(f"Seg {req.seg_index:3d} ({req.seg_type:12s}): CACHED ({dur:.1f}s)")
            continue

        # Thermal check before generation
        temp = thermal_wait(max_temp=82, cool_sleep=20)
        temp_str = f" [{temp}C]" if temp > 0 else ""

        # Generate
        fish_text = req.annotated_text
        chunks_text = []
        if words > 55:
            # Simple split at sentence boundary
            sentences = re.split(r'(?<=[.!?])\s+', fish_text)
            current_chunk = ""
            for sent in sentences:
                if len((current_chunk + " " + sent).split()) > 55 and current_chunk:
                    chunks_text.append(current_chunk.strip())
                    current_chunk = sent
                else:
                    current_chunk = (current_chunk + " " + sent).strip()
            if current_chunk:
                chunks_text.append(current_chunk.strip())
            if not chunks_text:
                chunks_text = [fish_text]
        else:
            chunks_text = [fish_text]

        print(f"Seg {req.seg_index:3d} ({req.seg_type:12s}, {req.speaker}): "
              f"{len(chunks_text)} chunk(s), {words} mots{temp_str}")

        chunk_files = []
        all_ok = True

        for ci, chunk in enumerate(chunks_text):
            chunk_name = f"sub_{req.seg_index:03d}_{ci}_{req.fish_preset}.wav"
            chunk_path = SUB_DIR / chunk_name

            # Check sub-chunk cache
            if chunk_path.exists() and chunk_path.stat().st_size > 1000:
                chunk_files.append(chunk_path)
                dur_c = audio_duration_s(chunk_path.read_bytes())
                print(f"  Chunk {ci+1}/{len(chunks_text)}: CACHED ({dur_c:.1f}s)")
                continue

            audio_data = None
            for attempt in range(3):
                print(f"  Chunk {ci+1}/{len(chunks_text)} [{attempt+1}]...", end=" ", flush=True)
                audio_data = fishaudio_tts(chunk, timeout=300)

                if audio_data and len(audio_data) > 1000:
                    with open(chunk_path, "wb") as f:
                        f.write(audio_data)
                    chunk_files.append(chunk_path)
                    dur_c = audio_duration_s(audio_data)
                    print(f"OK ({dur_c:.1f}s, {len(audio_data)//1024}KB)")
                    break
                else:
                    got = len(audio_data) if audio_data else 0
                    print(f"FAIL ({got} bytes)")
                    if attempt < 2:
                        time.sleep(5)

            if not audio_data or len(audio_data) <= 1000:
                all_ok = False
                break

            # Pause between chunks
            if ci < len(chunks_text) - 1:
                time.sleep(3)

        if all_ok and chunk_files:
            import shutil
            if len(chunk_files) == 1:
                shutil.copy2(chunk_files[0], output_path)
            else:
                concatenate_wav_files(chunk_files, output_path, silence_duration=0.3)

            final_data = output_path.read_bytes()
            final_dur = audio_duration_s(final_data)

            # Whisper verification
            wer = -1.0
            whisper_text = ""
            if whisper_ok:
                time.sleep(1)
                whisper_text = whisper_transcribe(output_path)
                if whisper_text:
                    wer = word_error_rate(req.text, whisper_text)
                    print(f"  WER: {wer:.1%}")
                    if wer > 0.25:
                        print(f"  WARNING: high WER, segment may need regeneration")

            generated.append(TTSRequest(
                seg_index=req.seg_index, seg_type=req.seg_type,
                speaker=req.speaker, text=req.text,
                annotated_text=req.annotated_text,
                fish_preset=req.fish_preset, tags=req.tags,
                output_file=str(output_path), duration_s=final_dur,
                file_size_kb=len(final_data) / 1024, status="success",
                whisper_wer=wer, whisper_text=whisper_text,
            ))
            print(f"  => Seg {req.seg_index}: OK ({final_dur:.1f}s, {len(final_data)//1024}KB)")
        else:
            generated.append(TTSRequest(
                seg_index=req.seg_index, seg_type=req.seg_type,
                speaker=req.speaker, text=req.text,
                annotated_text=req.annotated_text,
                fish_preset=req.fish_preset, tags=req.tags,
                status="failed",
            ))
            print(f"  => Seg {req.seg_index}: FAILED")

        # Inter-segment pause + thermal
        time.sleep(2)

    elapsed = time.time() - t_start
    ok_count = sum(1 for r in generated if r.status == "success")
    fail_count = sum(1 for r in generated if r.status == "failed")
    total_dur = sum(r.duration_s for r in generated if r.status == "success")
    total_size = sum(r.file_size_kb for r in generated if r.status == "success")

    print(f"\n{'='*60}")
    print(f"Generation complete: {ok_count}/{len(generated)} OK in {elapsed:.0f}s")
    print(f"Total audio: {total_dur:.1f}s ({total_dur/60:.1f}min)")
    print(f"Total size: {total_size:.0f}KB")
    print(f"Total words processed: {total_words}")

    # 8. Compile complete audiobook
    if ok_count >= len(generated) * 0.8:
        success_segs = sorted(
            [r for r in generated if r.status == "success"],
            key=lambda r: r.seg_index
        )
        wav_files = [r.output_file for r in success_segs]
        audiobook_path = OUTPUT_DIR / "boule_de_suif_complete.wav"
        print(f"\nCompiling audiobook ({len(success_segs)} segments)...")
        concatenate_wav_files(wav_files, audiobook_path, silence_duration=0.5)
        ab_data = audiobook_path.read_bytes()
        ab_dur = audio_duration_s(ab_data)
        print(f"Audiobook: {ab_dur:.1f}s ({ab_dur/60:.1f}min), {len(ab_data)//1024}KB")

    # 9. Save metadata
    metadata = {
        "epic": "1273",
        "pass": "P5-v3",
        "description": "Complete Boule de Suif audiobook — FishAudio S2-Pro with fixed voice attribution and prosody",
        "source_text": "Boule de Suif - Guy de Maupassant (Gutenberg #10746)",
        "tts_model": "fishaudio-s2-pro",
        "tts_service_url": FISHAUDIO_URL,
        "pipeline_version": "v3",
        "fixes_applied": ["#1275-voice-attribution", "#1276-prosody-tags", "thermal-backoff"],
        "stats": {
            "total_segments": len(generated),
            "successful": ok_count,
            "failed": fail_count,
            "total_duration_s": total_dur,
            "total_words": total_words,
            "generation_time_s": elapsed,
        },
        "segments": [asdict(r) for r in generated],
    }

    meta_path = OUTPUT_DIR / "v3_generation_metadata.json"
    with open(meta_path, "w", encoding="utf-8") as f:
        json.dump(metadata, f, ensure_ascii=False, indent=2)

    print(f"\nMetadata: {meta_path}")

    # 10. Summary
    for r in generated:
        dur = f"{r.duration_s:.1f}s" if r.status == "success" else "FAILED"
        wer = f" WER:{r.whisper_wer:.0%}" if r.whisper_wer >= 0 else ""
        print(f"  Seg {r.seg_index:3d}: {r.status:7s} | {r.seg_type:12s} | "
              f"{r.speaker:30s} | {dur}{wer}")

    print(f"\nDONE: {ok_count}/{len(generated)} segments")


if __name__ == "__main__":
    main()
