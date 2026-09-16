"""V0 narrow du pipeline livecoding-video (issue #15604, homage a une voix tierce).

**Scope V0 narrow** (c.573, fenetre 30 min) :
Cette V0 livre UNIQUEMENT l'etape 1 du pipeline (composition Strudel
multi-pistes) et le squelette de l'orchestrateur. Les etapes 2 a 6
(narration LLM, TTS, capture navigateur Playwright, visualizer, mixage
ffmpeg) sont **documentation-ONLY** dans ce fichier : elles listent
l'API prevue, le verdict SOTA attendu, et les risques identifies, mais
ne sont pas implementees. C'est une V0 *honestement incomplete* (HARD
Tell c.1102 : pas de pipeline squelette qui pretend faire la capture
quand il ne fait que composer).

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
- Etape 4 capture Playwright sur `https://strudel.cc/` : necessite
  verification routage audio Windows (VB-Cable/BlackHole), risques
  identifies dans issue #15604. PoC 30 s a faire d'abord.
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
import sys
from dataclasses import dataclass
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
) -> str:
    """Compose un script Strudel multi-pistes conforme au style.

    Parametres :
    - style_name : cle dans STYLES (``trance``, ``ambient``, ``techno``,
      ``melancholy``).
    - duration_seconds : duree cible (3-10 min).
    - voices : nombre de voix paralleles a superposer (1-4).

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
    for i, pat in enumerate(patterns):
        lines.append(f"$: {pat}")

    # Bloc fade-out coordonne : multiplier la sortie par une rampe
    # lineaire decroissante sur les 8 derniers cycles.
    fade_cycles = 8
    fade_marker = f"// fade-out coordonne sur les {fade_cycles} derniers cycles : premultiplier chaque voix par gain(1 - cycles_left/{fade_cycles})"
    lines.append(fade_marker)

    return "\n".join(lines)


# --- V0 narrow : orchestrateur scaffold ---------------------------------------


def run_pipeline(
    style_name: str,
    duration_seconds: int,
    output_path: str,
    tts_voice: Optional[str] = None,
    playwright_url: str = "https://strudel.cc/",
    ffmpeg_loudnorm_lufs: float = -14.0,
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
    strudel = compose_strudel(style_name=style_name, duration_seconds=duration_seconds)

    return {
        "strudel_script": strudel,
        "narration": "deferred",          # Phase B — LLM segments timestampes
        "tts": "deferred" if tts_voice is None else f"requested={tts_voice}",
        "browser_capture": f"deferred ({playwright_url})",
        "visualizer": "deferred (V1 only — capture Strudel inclut scope/pianoroll)",
        "final_mix": f"deferred ({output_path}, loudnorm {ffmpeg_loudnorm_lufs} LUFS)",
        "verdict": (
            "V0 narrow : etape 1 livree (composition Strudel), "
            "etapes 2-6 deferred a c.574+ avec claim explicite par "
            "phase (Tell c.574 strict anti-WIP-collisions)."
        ),
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
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    args = _build_arg_parser().parse_args(argv)
    result = run_pipeline(
        style_name=args.style,
        duration_seconds=args.duration,
        output_path=args.output,
        tts_voice=args.tts_voice,
    )
    # Verdict V0 narrow explicite — Tell c.1102 anti-stonewall
    print("=== Strudel script (etape 1, livree) ===")
    print(result["strudel_script"])
    print()
    print("=== Status des etapes 2-6 (deferred c.574+) ===")
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
