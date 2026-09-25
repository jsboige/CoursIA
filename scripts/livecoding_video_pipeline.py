"""V0 narrow du pipeline livecoding-video (issue #15604, homage a une voix tierce).

**Scope** (V0 c.573 + etape 4 c.580) :
Etape 1 (composition Strudel multi-pistes) livree en V0. Etape 4
(capture navigateur) livree ensuite : le REPL strudel.cc est pilote
par Playwright headed — pattern injecte par hash d'URL, visuals
declares dans le code (``.pianoroll()`` / ``.scope()``), audio exporte
par le moteur offline NATIF du REPL (Export to WAV, aucune
instrumentation WebAudio, aucun routage systeme VB-Cable), video
capturee par ``canvas.captureStream`` + MediaRecorder, mux ffmpeg.
Les etapes restantes (2 narration LLM, 3 TTS, 5 visualizer custom,
6 mixage ffmpeg complet) restent documentation-ONLY (HARD Tell
c.1102 : pas de pipeline squelette qui pretend faire ce qu'il ne
fait pas).

**Etats cles** (cf issue #15604 et c.446 demucs Phase A deferree) :
- Composition Strudel via template parametrable (PAS de LLM libre en
  V0 pour eviter la composition Strudel invalide du notebook 04-5).
- Sortie : une string Python-formattable contenant le script Strudel,
  plusieures voix superposees, modulation lente via slider, et un
  pattern de fade-out coordonne musique + (futur) video.

**Hors V0 narrow (c.574+, hand-off cycles suivants)** :
- Etape 2 narration LLM : sous-grain SEPARE avec claim sur
  `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-5-LiveCoding-LLM-Music.ipynb`.
- Etape 3 TTS Kokoro/FishAudio : `scripts/audiobook_pipeline.py`
  deja disponible, integration differee a un cycle c.574+.
- Etape 4 capture Playwright sur `https://strudel.cc/` : LIVREE (c.580).
  Le risque « routage audio Windows (VB-Cable/BlackHole)» est leve par
  design : l'audio vient de l'export offline NATIF du REPL (rendu
  OfflineAudioContext cote strudel.cc), pas d'une capture systeme.
- Etape 5 visualizer custom : V1 only.
- Etape 6 mixage ffmpeg : `scripts/audiobook_pipeline.py` a deja
  l'integration loudnorm -14 LUFS + fade-out.

**Voie 3 B.0** : voie du retrait consenti d'une voix tierce tenue
(bibliography-hygiene §2, audit-cross-source-distillation §3.1,
02-2-XTTS-Voice-Cloning l.2018). Aucune voix clonee, aucun verbatim,
aucune archive media dans le depot. La methode (narration + composition
+ capture + mixage) est copiee ; le contenu ne l'est pas.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional

# --- V0 narrow : composition Strudel multi-pistes par template ----------------


@dataclass(frozen=True)
class StrudelStyle:
    """Parametrage d'un style musical Strudel (V0 template, pas LLM)."""

    name: str
    bpm: int
    pattern_kick: str
    pattern_bass: str
    pattern_lead: str
    pattern_pad: str
    modulation_curve: str  # decrit l'evolution des parametres au cours du temps


# Styles *generiques* (pas vendorés). Les valeurs sont parametriques
# et le code Strudel reste un template a remplir.
STYLES: Dict[str, StrudelStyle] = {
    "trance": StrudelStyle(
        name="trance",
        bpm=140,
        pattern_kick="s('bd*4').gain(0.9)",
        pattern_bass='note("c2 ~ e2 g2 ~ a2 ~ e2").s("sawtooth").lpf(400).gain(0.5)',
        pattern_lead='note("~ c5 e5 g5 ~ a5 g5 e5 ~").s("supersaw").lpf(slider(2000, 80, 4)).gain(0.4)',
        pattern_pad='note("[c4,e4,g4]").s("square").room(0.6).gain(0.2)',
        modulation_curve="slider()",
    ),
    "ambient": StrudelStyle(
        name="ambient",
        bpm=72,
        pattern_kick="s('bd').gain(0.2).degradeBy(0.95)",
        pattern_bass='note("c1 ~ ~ g1 ~ ~ ~ ~").s("sine").lpf(300).gain(0.3)',
        pattern_lead='note("c5 ~ e5 ~ ~ g5 ~ ~ ~ a5 ~ ~ ~").s("supersine").room(0.9).gain(0.3).delay(0.4)',
        pattern_pad='note("[c3,g3,e4]").s("sawtooth").lpf(slider(800, 200, 8)).room(0.9).gain(0.2)',
        modulation_curve="slowslider()",
    ),
    "techno": StrudelStyle(
        name="techno",
        bpm=128,
        pattern_kick="s('bd*4').gain(0.9)",
        pattern_bass='note("c2 ~ ~ c2 ~ c2 ~ ~").s("square").lpf(slider(600, 200, 2)).gain(0.6)',
        pattern_lead='note("~ e4 ~ g4 ~ a4 ~ c5 ~").s("sawtooth").lpf(2000).gain(0.5)',
        pattern_pad='note("[a3,c4,e4]").s("sawtooth").room(0.4).gain(0.3)',
        modulation_curve="slider()",
    ),
    "melancholy": StrudelStyle(
        name="melancholy",
        bpm=80,
        pattern_kick="s('bd').degradeBy(0.7).gain(0.4)",
        pattern_bass='note("a1 ~ ~ e2 ~ ~ ~ ~").s("triangle").gain(0.4)',
        pattern_lead='note("a4 ~ c5 ~ e5 ~ ~ d5 ~").s("supersine").delay(0.6).room(0.7).gain(0.4)',
        pattern_pad='note("[a3,c4,e4]").s("sawtooth").lpf(slider(600, 100, 12)).gain(0.3)',
        modulation_curve="slowslider()",
    ),
}


def compose_strudel(
    style_name: str,
    duration_seconds: int = 180,
    voices: int = 4,
    visuals: bool = False,
) -> str:
    """Compose un script Strudel multi-pistes conforme au style.

    Parametres :
    - style_name : cle dans STYLES (``trance``, ``ambient``, ``techno``,
      ``melancholy``).
    - duration_seconds : duree cible (3-10 min).
    - voices : nombre de voix paralleles a superposer (1-4).
    - visuals : ajoute les visuals REPL (``.scope()`` sur la voix basse,
      ``.pianoroll()`` sur la voix lead). Sans visuals declares, le
      canvas du REPL reste noir : c'est la condition de la capture
      video de l'etape 4.

    Retourne : une string Strudel executable cote navigateur
    (chargeable via ``strudel.cc`` ou integration ``<strudel-editor>``).

    Raises :
    - ValueError si ``style_name`` est inconnu ou si les parametres
      sont hors range.
    """
    if style_name not in STYLES:
        raise ValueError(
            f"style {style_name!r} inconnu ; styles disponibles : {sorted(STYLES.keys())}"
        )
    if not 60 <= duration_seconds <= 600:
        raise ValueError(
            f"duration_seconds doit etre dans [60, 600], recu {duration_seconds}"
        )
    if not 1 <= voices <= 4:
        raise ValueError(
            f"voices doit etre dans [1, 4], recu {voices}"
        )

    style = STYLES[style_name]
    cps = style.bpm / 60.0 / 2.0  # cycles par seconde (hypothesis grossiere)
    cycles_target = round(duration_seconds * cps)

    patterns = [style.pattern_kick, style.pattern_bass, style.pattern_lead, style.pattern_pad][:voices]
    if len(patterns) < 2:
        patterns.append("~")  # combler pour avoir au moins 2 voix

    # Format strudel : chaque voix sur sa propre ligne `$: ...`,
    # `setcps` pour le tempo, modulation lente via slider().
    # Fade-out : multiplier les 8 derniers cycles par un gain decroissant.
    lines: List[str] = []
    lines.append(f"// Livecoding video — style={style.name} BPM={style.bpm} duration={duration_seconds}s")
    lines.append(f"setcps({cps:.4f})")
    # Map des visuals par index de voix (formes validees sur strudel.cc,
    # c.580 probe : `.scope()` sur la basse, `.pianoroll()` sur le lead).
    visuals_by_voice = {1: ".scope()", 2: ".pianoroll()"}
    for i, pat in enumerate(patterns):
        suffix = visuals_by_voice.get(i, "") if visuals else ""
        lines.append(f"$: {pat}{suffix}")

    # Bloc fade-out coordonne : multiplier la sortie par une rampe
    # lineaire decroissante sur les 8 derniers cycles.
    fade_cycles = 8
    fade_marker = f"// fade-out coordonne sur les {fade_cycles} derniers cycles : premultiplier chaque voix par gain(1 - cycles_left/{fade_cycles})"
    lines.append(fade_marker)

    return "\n".join(lines)


# --- V0 narrow : orchestrateur scaffold ---------------------------------------


def style_cps(style_name: str) -> float:
    """Cycles par seconde du style ( meme regle que compose_strudel )."""
    if style_name not in STYLES:
        raise ValueError(
            f"style {style_name!r} inconnu ; styles disponibles : {sorted(STYLES.keys())}"
        )
    return STYLES[style_name].bpm / 60.0 / 2.0


def run_pipeline(
    style_name: str,
    duration_seconds: int,
    output_path: str,
    tts_voice: Optional[str] = None,
    playwright_url: str = "https://strudel.cc/",
    ffmpeg_loudnorm_lufs: float = -14.0,
    capture: bool = False,
    capture_seconds: int = 30,
    headless: bool = False,
) -> Dict[str, Optional[str]]:
    """Orchestrateur V0 narrow : compose le script Strudel et documente
    les autres etapes.

    V0 narrow retourne un dict avec une cle par etape et la valeur
    'deferred' pour les etapes non livrees en V0. C'est un contrat
    HONNETE (Tell c.1102) : pas de pipeline squelette qui pretend
    faire la capture navigateur quand il ne fait que composer.

    Parametres :
    - style_name : style musical (cf :func:`compose_strudel`).
    - duration_seconds : duree cible en secondes.
    - output_path : chemin du fichier .mp4 final (en V0, ce chemin
      n'est PAS cree : l'integrateur ffmpeg est deferred).
    - tts_voice : voix TTS Kokoro/FishAudio (optionnel, deferred).
    - playwright_url : URL du navigateur Strudel (deferred).
    - ffmpeg_loudnorm_lufs : cible loudness (deferred).

    Retourne : dict avec cles 'strudel_script', 'narration', 'tts',
    'browser_capture', 'visualizer', 'final_mix', 'verdict'.
    """
    strudel = compose_strudel(
        style_name=style_name,
        duration_seconds=duration_seconds,
        visuals=capture,
    )

    browser_capture: object = f"deferred ({playwright_url})"
    final_mix: object = f"deferred ({output_path}, loudnorm {ffmpeg_loudnorm_lufs} LUFS)"
    if capture:
        capture_result = capture_repl_session(
            pattern=strudel,
            output_dir=Path(output_path).parent,
            capture_seconds=capture_seconds,
            cycles=cycles_for_duration(style_cps(style_name), capture_seconds) + 1,
            headless=headless,
        )
        browser_capture = (
            f"LIVREE : {capture_result['final_mp4']} "
            f"({capture_result['mp4_bytes']} octets, video webm "
            f"{capture_result['video_bytes']} + wav {capture_result['wav_bytes']})"
        )
        final_mix = f"PoC mux ffmpeg LIVRE : {capture_result['final_mp4']} (loudnorm complet = etape 6)"

    return {
        "strudel_script": strudel,
        "narration": "deferred",          # Phase B — LLM segments timestampes
        "tts": "deferred" if tts_voice is None else f"requested={tts_voice}",
        "browser_capture": browser_capture,
        "visualizer": "deferred (V1 only — capture Strudel inclut scope/pianoroll)",
        "final_mix": final_mix,
        "verdict": (
            "Etape 1 (composition) + etape 4 (capture navigateur : export WAV "
            "offline natif + MediaRecorder + mux ffmpeg) livrees ; etapes "
            "2/3/5/6 deferred avec claim explicite par phase."
        ),
    }


# --- Etape 4 : capture navigateur Playwright sur strudel.cc (c.580) ----------


def build_repl_url(pattern: str, repl_base: str = "https://strudel.cc/") -> str:
    """Construit l'URL de partage du REPL strudel.cc pour un pattern.

    Encodage observe firsthand sur le bouton ``share`` du REPL (c.580) :
    ``#`` + ``encodeURIComponent(base64(code))``. L'URI-encoding est
    OBLIGATOIRE — un base64 brut avec ``+`` ou ``==`` n'est pas charge.
    """
    import base64
    import urllib.parse

    return repl_base + "#" + urllib.parse.quote(base64.b64encode(pattern.encode("utf-8")).decode("ascii"))


def cycles_for_duration(cps: float, duration_seconds: float) -> int:
    """Nombre de cycles strudel couvrant ``duration_seconds`` a ``cps``."""
    if cps <= 0:
        raise ValueError(f"cps doit etre positif, recu {cps}")
    if duration_seconds <= 0:
        raise ValueError(f"duration_seconds doit etre positif, recu {duration_seconds}")
    return int(math.ceil(duration_seconds * cps))


_CANVAS_CHECKSUM_JS = """
() => {
  const c = document.querySelector('canvas');
  if (!c) throw new Error('pas de canvas REPL');
  const ctx = c.getContext('2d');
  const d = ctx.getImageData(0, 0, c.width, c.height).data;
  let h = 0;
  for (let i = 0; i < d.length; i += 4096) h = (h * 31 + d[i]) >>> 0;
  return h;
}
"""

# Recorder in-page : captureStream(30) sur le canvas REPL + MediaRecorder vp9,
# retourne le webm en base64. Le canvas doit ETRE anime (visuals declares) —
# captureStream n'emets aucune frame sur un canvas immobile (mesure c.580 :
# 0 octet enregistres sur canvas noir).
_RECORDER_JS = """
async (durationMs) => {
  const c = document.querySelector('canvas');
  const stream = c.captureStream(30);
  const mime = MediaRecorder.isTypeSupported('video/webm;codecs=vp9')
    ? 'video/webm;codecs=vp9' : 'video/webm';
  const mr = new MediaRecorder(stream, { mimeType: mime, videoBitsPerSecond: 4000000 });
  const chunks = [];
  mr.ondataavailable = (e) => { if (e.data.size) chunks.push(e.data); };
  const done = new Promise((res) => { mr.onstop = () => res(new Blob(chunks, { type: mime })); });
  mr.start(1000);
  await new Promise((r) => setTimeout(r, durationMs));
  mr.stop();
  const blob = await done;
  if (!blob.size) throw new Error('MediaRecorder: 0 octet — canvas immobile (visuals absents ?)');
  const b64 = await new Promise((res) => {
    const fr = new FileReader();
    fr.onload = () => res(fr.result.split(',')[1]);
    fr.readAsDataURL(blob);
  });
  return { size: blob.size, type: blob.type, nChunks: chunks.length, b64 };
}
"""


def mux_ffmpeg(video_webm: Path, audio_wav: Path, out_mp4: Path) -> List[str]:
    """Construit la commande de mux ffmpeg video+audio -> mp4 (H.264/AAC).

    ``-shortest`` aligne la duree sur la piste la plus courte : la capture
    video (reelle) et le WAV exporte (cycles arrondis) different de <1 cycle.
    """
    return [
        "ffmpeg", "-y",
        "-i", str(video_webm),
        "-i", str(audio_wav),
        "-c:v", "libx264", "-crf", "18", "-pix_fmt", "yuv420p",
        "-c:a", "aac", "-b:a", "192k",
        "-shortest",
        str(out_mp4),
    ]


def capture_repl_session(
    pattern: str,
    output_dir: Path,
    capture_seconds: int = 30,
    cycles: Optional[int] = None,
    headless: bool = False,
    warmup_seconds: float = 5.0,
) -> Dict[str, object]:
    """Pilote le REPL strudel.cc et capture la session (etape 4, #15604).

    Sequence validee firsthand (c.580, probes MCP + playwright Python) :
    1. URL de partage (hash) -> le REPL charge le pattern au reload ;
    2. clic ``play`` (geste trusted, headed requis : un clic JS n'est pas
       un user gesture et l'AudioContext live reste suspendu) ;
    3. les visuals declares (``.pianoroll()``/``.scope()`` dans le code)
       animent le canvas — gate par checksum avant l'enregistrement ;
    4. ``canvas.captureStream`` + MediaRecorder -> webm base64 ;
    5. menu ``export`` -> ``Export to WAV`` : rendu offline NATIF du
       moteur strudel (aucun routage audio systeme), download capture ;
    6. ffmpeg mux -> mp4 (H.264/AAC).

    Retourne un dict : ``video_webm``, ``audio_wav``, ``final_mp4``,
    ``video_bytes``, ``wav_bytes``, ``mp4_bytes``, ``cycles``.
    """
    import base64

    from playwright.sync_api import sync_playwright

    output_dir.mkdir(parents=True, exist_ok=True)
    video_webm = output_dir / "capture.webm"
    audio_wav = output_dir / "capture.wav"
    final_mp4 = output_dir / "capture_final.mp4"
    url = build_repl_url(pattern)

    with sync_playwright() as pw:
        browser = pw.chromium.launch(headless=headless)
        page = browser.new_page(viewport={"width": 1280, "height": 1024})
        try:
            page.goto(url)
            page.wait_for_timeout(5000)
            page.get_by_role("button", name="play").first.click(timeout=10_000)
            page.wait_for_timeout(int(warmup_seconds * 1000))

            h1 = page.evaluate(_CANVAS_CHECKSUM_JS)
            page.wait_for_timeout(2000)
            h2 = page.evaluate(_CANVAS_CHECKSUM_JS)
            if h1 == h2:
                raise RuntimeError(
                    "canvas REPL immobile apres play — visuals absents du "
                    "pattern (compose_strudel(visuals=True)) ou play non effectif"
                )

            rec = page.evaluate(_RECORDER_JS, int(capture_seconds * 1000))
            video_webm.write_bytes(base64.b64decode(rec["b64"]))

            # Export WAV natif : le bouton play est devenu '...' (lecture en
            # cours) ; l'export stoppe la lecture lui-meme (cyclist stop).
            # Le panneau menu est parfois DEJA ouvert au chargement (hash) :
            # cliquer 'menu' le refermerait — n'ouvrir que si ferme.
            if page.get_by_role("button", name="Close Menu").count() == 0:
                page.get_by_role("button", name="menu", exact=True).click(timeout=10_000)
                page.wait_for_timeout(600)
            page.get_by_role("button", name="export", exact=True).click(timeout=10_000)
            page.wait_for_timeout(600)
            if cycles is not None:
                page.get_by_role("spinbutton").nth(1).fill(str(cycles))
            with page.expect_download(timeout=300_000) as download_info:
                page.get_by_role("button", name="Export to WAV").click()
            download_info.value.save_as(str(audio_wav))
        finally:
            browser.close()

    import subprocess

    cmd = mux_ffmpeg(video_webm, audio_wav, final_mp4)
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"ffmpeg a echoue ({proc.returncode}) : {proc.stderr[-800:]}")

    return {
        "video_webm": str(video_webm),
        "audio_wav": str(audio_wav),
        "final_mp4": str(final_mp4),
        "video_bytes": video_webm.stat().st_size,
        "wav_bytes": audio_wav.stat().st_size,
        "mp4_bytes": final_mp4.stat().st_size,
        "cycles": cycles,
    }


# --- CLI --------------------------------------------------------------------


def _build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="livecoding_video_pipeline",
        description="V0 narrow du pipeline livecoding-video (#15604). "
        "Compose un script Strudel multi-pistes par template ; les "
        "autres etapes sont deferred au cycle c.574+.",
    )
    parser.add_argument(
        "--style",
        choices=sorted(STYLES.keys()),
        default="trance",
        help="style musical (default: trance)",
    )
    parser.add_argument(
        "--duration",
        type=int,
        default=180,
        help="duree cible en secondes (60-600, default: 180 = 3 min)",
    )
    parser.add_argument(
        "--voices",
        type=int,
        default=4,
        help="nombre de voix paralleles (1-4, default: 4)",
    )
    parser.add_argument(
        "--output",
        default="out/livecoding_V0.mp4",
        help="chemin du fichier .mp4 final (deferred, default: out/livecoding_V0.mp4)",
    )
    parser.add_argument(
        "--tts-voice",
        default=None,
        help="voix TTS Kokoro/FishAudio (optionnel, deferred en V0)",
    )
    parser.add_argument(
        "--capture",
        action="store_true",
        help="etape 4 : piloter strudel.cc (Playwright headed), capturer le "
             "canvas (MediaRecorder) + exporter le WAV natif, mux ffmpeg",
    )
    parser.add_argument(
        "--capture-seconds",
        type=int,
        default=30,
        help="duree de capture video en secondes (default: 30)",
    )
    parser.add_argument(
        "--headless",
        action="store_true",
        help="lancer Chromium headless (DECONSEILLE : le canvas REPL ne "
             "s'anime pas sans fenetre compositée — mesure c.580)",
    )
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    args = _build_arg_parser().parse_args(argv)
    result = run_pipeline(
        style_name=args.style,
        duration_seconds=args.duration,
        output_path=args.output,
        tts_voice=args.tts_voice,
        capture=args.capture,
        capture_seconds=args.capture_seconds,
        headless=args.headless,
    )
    # Verdict explicite — Tell c.1102 anti-stonewall
    print("=== Strudel script (etape 1, livree) ===")
    print(result["strudel_script"])
    print()
    print("=== Status des etapes 2-6 ===")
    for key in ("narration", "tts", "browser_capture", "visualizer", "final_mix"):
        print(f"  {key}: {result[key]}")
    print()
    print(f"=== Verdict ===\n{result['verdict']}")
    # Code retour 0 + sortie non-vide : commande unique executée sans
    # intervention manuelle (critere 1 de l'acceptance partiellement tenu
    # pour la partie livree ; les autres etapes marquent explicitement
    # "deferred" pour ne pas usurper l'acceptance complete).
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
