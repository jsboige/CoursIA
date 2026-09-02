"""P6 -- MP3/M4B Compilation for the v4 audiobook pipeline.


Concatenates individual segment MP3s into a single audiobook file
using pydub with crossfade and act-boundary silence.
"""
from __future__ import annotations

import json
import shutil

import subprocess

import tempfile

from pathlib import Path

from dotenv import load_dotenv

from .schemas import AnnotatedBatch, DramaticContextBatch

BASE_DIR = Path(__file__).parent

SEGMENT_GAP_MS = 400
ACT_GAP_MS = 1500
CROSSFADE_MS = 20
BITRATE = "192k"


def _detect_act_boundaries(dramatic_path: Path) -> dict[int, str]:
    """Build seg_index -> act label mapping for act boundary detection."""
    if not dramatic_path.exists():
        return {}

    batch = DramaticContextBatch.model_validate_json(
        dramatic_path.read_text(encoding="utf-8")
    )
    return {ctx.seg_index: ctx.act for ctx in batch.contexts}


# Mapping human-readable pour les titres de chapitres (ActLabel -> titre court).

# Source : ACT_DESCRIPTIONS dans p3_dramatic_context.py (cles canoniques).

_CHAPTER_TITLES: dict[str, str] = {

    "act1_diligence_aller":     "Acte I -- La diligence de l'aller",

    "act2_auberge_jours":       "Acte II -- L'auberge, les jours",

    "act3_pressing_collectif":  "Acte III -- Le pressing collectif",

    "act4_diligence_retour":    "Acte IV -- La diligence du retour",

}





def _build_chapters(act_start_ms: dict[str, int], total_duration_ms: int) -> list[dict]:

    """Construit la liste des chapitres FFMetadata depuis les timestamps d'acte.



    Tri par start_ms croissant. Le dernier chapitre utilise total_duration_ms comme END.

    Retourne [] si act_start_ms est vide.

    """

    if not act_start_ms:

        return []

    sorted_acts = sorted(act_start_ms.items(), key=lambda kv: kv[1])

    chapters = []

    for i, (act_key, start_ms) in enumerate(sorted_acts):

        if i + 1 < len(sorted_acts):

            end_ms = sorted_acts[i + 1][1]

        else:

            end_ms = total_duration_ms

        chapters.append({

            "title": _CHAPTER_TITLES.get(act_key, act_key),

            "start_ms": int(start_ms),

            "end_ms": int(end_ms),

        })

    return chapters





def _write_ffmetadata(chapters, tags, path):

    """Ecrit un fichier FFMETADATA (format ffmetadata) a `path`.



    Format : https://ffmpeg.org/ffmpeg-formats.html#Metadata-1

    """

    parts = [";FFMETADATA1\n"]

    for k, v in tags.items():

        # Escape \ ; = et nouvelle-ligne dans les valeurs, spec FFMETADATA.

        v_esc = str(v).replace("\\", "\\\\").replace(";", "\\;").replace("=", "\\=").replace("\n", " \\n")

        parts.append(f"{k}={v_esc}\n")

    if chapters:

        for ch in chapters:

            parts.append("[CHAPTER]\n")

            parts.append("TIMEBASE=1/1000\n")

            parts.append("START={0}\n".format(ch["start_ms"]))

            parts.append("END={0}\n".format(ch["end_ms"]))

            title_esc = ch["title"].replace("\\", "\\\\").replace(";", "\\;").replace("=", "\\=").replace("\n", " ")

            parts.append(f"title={title_esc}\n")

    path.write_text("".join(parts), encoding="utf-8")





def _run_ffmpeg_m4b(ffmpeg_exe, mp3_path, m4b_path, chapters, tags):

    """Remuxe le mp3 vers m4b (AAC) avec chapitres FFMetadata.



    Le mp3 source n'est pas reencode au meme bitrate ; ffmpeg transcode l'audio

    vers AAC pour le container m4b (codec audiobook standard).

    """

    with tempfile.TemporaryDirectory() as td:

        meta_path = Path(td) / "ffmeta.txt"

        _write_ffmetadata(chapters, tags, meta_path)

        cmd = [

            ffmpeg_exe, "-y", "-loglevel", "error",

            "-i", str(mp3_path),

            "-i", str(meta_path),

            "-map_metadata", "1",

            "-map", "0:a",

            "-c:a", "aac", "-b:a", "192k",

            "-map_chapters", "1",

            str(m4b_path),

        ]

        result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")

        if result.returncode != 0:

            print(f"  [P6] WARN: ffmpeg a echoue (rc={result.returncode}). .m4b non produit.")

            if result.stderr:

                print(f"    stderr: {result.stderr.strip()[:200]}")

            return

        size_mb = m4b_path.stat().st_size / (1024 * 1024)

        ch_n = len(chapters) if chapters else 0

        print(f"  [P6] m4b: {m4b_path} ({size_mb:.1f} MB, {ch_n} chapitres)")







def run(force: bool = False) -> Path:
    """Run P6 — MP3 compilation. Returns path to audiobook MP3."""
    output_path = BASE_DIR / "outputs" / "boule_de_suif_v4.mp3"
    tts_path = BASE_DIR / "outputs" / "tts_results.json"
    annotated_path = BASE_DIR / "outputs" / "annotated_v4.json"
    dramatic_path = BASE_DIR / "outputs" / "dramatic_context.json"

    if not tts_path.exists():
        raise FileNotFoundError(
            f"tts_results.json not found: {tts_path}\n"
            "Run P5 (TTS generation) first."
        )

    if output_path.exists() and not force:
        print(f"[P6] Cached: {output_path}")
        return output_path

    print("[P6] Compiling audiobook...")

    try:
        from pydub import AudioSegment
    except ImportError:
        raise ImportError("pydub is required for MP3 compilation. Install with: pip install pydub")

    tts_data = json.loads(tts_path.read_text(encoding="utf-8"))
    tts_by_idx = {r["seg_index"]: r for r in tts_data}

    act_map = _detect_act_boundaries(dramatic_path)

    # Build ordered list of MP3 segments
    segments_ordered = sorted(tts_data, key=lambda r: r["seg_index"])
    total = len(segments_ordered)

    print(f"  Segments to compile: {total}")

    audiobook = AudioSegment.silent(duration=500)  # Opening silence
    # Chapitrage : timestamp ms du premier segment de chaque acte.

    act_start_ms: dict[str, int] = {}

    # NB: audiobook_open_ms = 500 (silence d'ouverture). On l'utilise pour

    # positionner le 1er acte correctement si son premier segment est le tout

    # premier segment de l'audiobook.



    prev_act: str | None = None
    compiled = 0
    skipped = 0

    for entry in segments_ordered:
        seg_idx = entry["seg_index"]
        mp3_path = entry.get("mp3_path", "")

        if not mp3_path or not Path(mp3_path).exists():
            skipped += 1
            continue

        try:
            seg_audio = AudioSegment.from_mp3(mp3_path)
        except Exception as e:
            print(f"  [P6] Error loading seg {seg_idx}: {e}")
            skipped += 1
            continue

        # Act boundary detection

        current_act = act_map.get(seg_idx)

        if current_act is not None and current_act not in act_start_ms:

            # Chapitrage : on note le timestamp (ms) AVANT d'ajouter le gap+seg

            # du segment courant. act_start_ms[act] = position du premier sample

            # du gap qui suit ce segment (i.e. debut "audible" de l'acte).

            act_start_ms[current_act] = len(audiobook)

        if prev_act is not None and current_act != prev_act:

            audiobook += AudioSegment.silent(duration=ACT_GAP_MS)

            print(f"  Act boundary: {prev_act} -> {current_act} at seg {seg_idx}")

        prev_act = current_act



        # Add segment with gap and crossfade
        gap = AudioSegment.silent(duration=SEGMENT_GAP_MS)
        audiobook += gap.append(seg_audio, crossfade=CROSSFADE_MS)
        compiled += 1

        if compiled % 100 == 0:
            print(f"  Progress: {compiled}/{total}")

    # Export
    audiobook.export(
        str(output_path),
        format="mp3",
        bitrate=BITRATE,
        tags={
            "title": "Boule de Suif",
            "artist": "Guy de Maupassant",
            "comment": "v4 FishAudio S2-Pro audiobook pipeline",
        },
    )
    # Chapitrage .m4b (issue #14188) : on remuxe le mp3 vers m4b avec metadata chapitres.

    # Source : act_start_ms captee pendant la boucle ci-dessus. On appelle ffmpeg

    # avec un fichier FFMETADATA (chapitres au format ffmetadata). Fallback gracieux

    # : si ffmpeg est absent, le mp3 reste valide (warning, pas d'erreur fatale).

    m4b_path = output_path.with_suffix('.m4b')

    ffmpeg_exe = shutil.which('ffmpeg')

    if ffmpeg_exe is None:

        print(f"  [P6] WARN: ffmpeg absent du PATH -- .m4b non produit (mp3 ok).")

        print(f"    Install ffmpeg puis re-executer p6_compile pour produire le .m4b.")

    elif not act_start_ms:

        print(f"  [P6] WARN: aucun acte detecte dans dramatic_context.json -- .m4b produit SANS chapitres.")

        _run_ffmpeg_m4b(ffmpeg_exe, output_path, m4b_path, chapters=None,

                         tags={"title": "Boule de Suif", "artist": "Guy de Maupassant"})

    else:

        chapters = _build_chapters(act_start_ms, len(audiobook))

        _run_ffmpeg_m4b(ffmpeg_exe, output_path, m4b_path, chapters=chapters,

                         tags={"title": "Boule de Suif", "artist": "Guy de Maupassant"})




    duration_s = len(audiobook) / 1000.0
    size_mb = output_path.stat().st_size / (1024 * 1024)

    print(f"[P6] Done: {output_path}")
    print(f"  Compiled: {compiled}, Skipped: {skipped}")
    print(f"  Duration: {duration_s:.1f}s ({duration_s/60:.1f}min)")
    print(f"  Size: {size_mb:.1f} MB")

    return output_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
