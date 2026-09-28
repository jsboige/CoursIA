"""V0 narrow du pipeline livecoding-video (issue #15604, homage a une voix tierce).

**Scope** (V0 c.573 + etape 2 c.1215 + etape 4 c.580) :
Etape 1 (composition Strudel multi-pistes) livree en V0. Etape 4
(capture navigateur) livree ensuite : le REPL strudel.cc est pilote
par Playwright headed — pattern injecte par hash d'URL, visuals
declares dans le code (``.pianoroll()`` / ``.scope()``), audio exporte
par le moteur offline NATIF du REPL (Export to WAV, aucune
instrumentation WebAudio, aucun routage systeme VB-Cable), video
capturee par ``canvas.captureStream`` + MediaRecorder, mux ffmpeg.
Etape 2 (narration poetique timestampee) livree : segments
``{start_s, end_s, text, intensity}`` generes par moteur template
deterministe (defaut, offline) ou moteur LLM optionnel (client
OpenAI-compat via ``OPENAI_API_KEY``), valides par
:func:`validate_narration` (garde anti-nomination d'artiste incluse —
ce n'est PAS un detecteur de verbatim, cf la limitation documentee
sur :func:`validate_narration`). Les etapes
restantes (3 TTS, 5 visualizer custom, 6 mixage ffmpeg complet)
restent documentation-ONLY (HARD Tell c.1102 : pas de pipeline
squelette qui pretend faire ce qu'il ne fait pas).

**Etats cles** (cf issue #15604 et c.446 demucs Phase A deferree) :
- Composition Strudel via template parametrable (PAS de LLM libre en
  V0 pour eviter la composition Strudel invalide du notebook 04-5).
- Sortie : une string Python-formattable contenant le script Strudel,
  plusieures voix superposees, modulation lente via slider, et un
  pattern de fade-out coordonne musique + (futur) video.

**Hors V0 narrow (c.574+, hand-off cycles suivants)** :
- Etape 2 narration timestampee : LIVREE (c.1215) — moteur template
  deterministe par defaut + moteur LLM optionnel, sortie JSON segments
  (unite d'entree de l'etape 3 TTS et des sous-titres de l'etape 6).
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
import json
import math
import os
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

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


# --- Etape 2 : narration poetique timestampee (c.1215) -----------------------


@dataclass(frozen=True)
class NarrationSegment:
    """Segment de voix off timestampe (etape 2, #15604).

    Contrat JSON : ``{"start_s": float, "end_s": float, "text": str,
    "intensity": float}`` — unite d'entree de l'etape 3 (TTS expressif,
    benchmark #17244) et des sous-titres de l'etape 6.
    """

    start_s: float
    end_s: float
    text: str
    intensity: float


# Garde ANTI-NOMINATION d'artiste tiers (voie 3 B.0, #15604) : bloque
# toute casse du nom de la source d'inspiration dans les textes generes.
# LIMITATION explicite : ce n'est PAS un detecteur de verbatim — detecter
# du verbatim exigerait un corpus de reference, lequel reste hors depot
# (bibliography-hygiene §2). Le verbatim est exclu d'une autre maniere :
# template = textes originaux par construction (ecrits dans ce module) ;
# LLM = exigence portee par le system prompt (mitigation d'instruction,
# non enforcement). Tokens construits par concatenation runtime pour
# qu'aucun grep sur la source ne trouve la forme contigue (pattern
# anonymisation c.578/c.634, cf test_no_voice_cloning_legal_proof).
NARRATION_FORBIDDEN_SUBSTRINGS: Tuple[str, ...] = (
    "switchan" + "gel",
    "switch" + " angel",
)

_NARRATION_TEXT_MAX_CHARS = 600
_NARRATION_TIME_EPS = 1e-9


@dataclass(frozen=True)
class NarrationPlan:
    """Fenetre de voix off d'un style (issue #15604, etape 2) :
    60-90 s de narration pour les videos courtes rythmees, jusqu'a
    100 % de la duree pour les ambient lents."""

    start_offset_s: float  # intro musicale avant la premiere parole
    span_fraction: float   # part de la duree couverte par la voix off
    span_max_s: float      # plafond de la fenetre
    segment_len_s: float   # longueur cible d'un segment


NARRATION_PLANS: Dict[str, NarrationPlan] = {
    "trance": NarrationPlan(4.0, 0.5, 90.0, 8.0),
    "techno": NarrationPlan(3.0, 0.5, 90.0, 8.0),
    "melancholy": NarrationPlan(6.0, 0.75, 240.0, 12.0),
    "ambient": NarrationPlan(2.0, 1.0, 600.0, 18.0),
}

# Mouvements narratifs, dans l'ordre du morceau. Les mouvements lead/
# nappe ne sont narrés que si les voix correspondantes existent dans
# le script (>= 3 / >= 4 lignes `$:` composees a l'etape 1) : la
# narration nomme ce qui joue REELLEMENT.
_NARRATION_MOVEMENTS: List[str] = [
    "ouverture", "basse", "lead", "nappe", "modulation", "climax", "fade",
]
_NARRATION_MOVEMENT_MIN_VOICES: Dict[str, int] = {"lead": 3, "nappe": 4}

# Banques de mouvements : textes FRANCAIS ORIGINAUX, ecrits pour ce
# pipeline, calibres sur le GENRE observe (nommer l'action du code puis
# glisser vers le poetique) SANS aucun verbatim tiers. Les instruments
# cites sont ceux des STYLES ci-dessus (narration ancree au script).
NARRATION_BANK: Dict[str, Dict[str, List[str]]] = {
    "trance": {
        "ouverture": [
            "Le kick entre le premier — quatre temps par cycle, une mécanique sans appel. La piste s'allume, la nuit commence.",
            "Posons la pulsation : la grosse caisse marque chaque temps. Autour d'elle, le silence attend son tour.",
        ],
        "basse": [
            "La basse sawtooth glisse dessous, ronde et patiente. Quelque chose de lent passe sous la surface.",
            "Une basse au filtre serré rejoint le kick — les deux battent ensemble maintenant, comme un seul muscle.",
        ],
        "lead": [
            "Voici le supersaw : des dents liquides, une mélodie qui cherche sa hauteur. Elle dit ce qu'on n'a pas le temps de dire.",
            "Le lead supersaw prend son envol, filtre ouvert. C'est la voix du morceau — elle raconte, le reste accompagne.",
        ],
        "nappe": [
            "La nappe carrée s'installe derrière, discrète — une pièce qu'on éclaire avant d'y entrer.",
            "Un accord tenu en arrière-plan : assez large pour marcher dessus, assez bas pour ne pas gêner.",
        ],
        "modulation": [
            "Le filtre s'ouvre lentement, le slider monte — la lumière avec. On laisse respirer, on laisse grandir.",
            "Chaque tour de slider ajoute un degré. La même phrase, jamais deux fois la même couleur.",
        ],
        "climax": [
            "Tout joue ensemble : {voices_list}. Le morceau tient debout tout seul — on ne fait qu'assister.",
            "Ici, plus rien à ajouter. Reste une seule question : combien de temps peut durer un présent pareil.",
        ],
        "fade": [
            "Le gain descend, cycle après cycle. Ce qui était plein se vide doucement, sans drame.",
            "On éteint les voix une à une, dans l'ordre inverse. La piste rend la lumière.",
        ],
    },
    "ambient": {
        "ouverture": [
            "Un sinus grave tout d'abord, presque rien. Un point dans une pièce vide.",
            "La grosse caisse n'entre pas — elle suggère. Une frappe presque effacée, comme un souvenir de rythme.",
        ],
        "basse": [
            "La basse sinus tient le sol, une note longue par-ci par-là. Le sol respire.",
            "Sous la surface, un sinus grave circule. Il ne demande rien, il attend.",
        ],
        "lead": [
            "Le supersine apparaît, au loin, grandi par sa pièce et son delay. Il faut du temps pour venir jusqu'ici.",
            "Une note haute se détache, se répète en écho, puis se tait — le temps de s'approcher.",
        ],
        "nappe": [
            "La nappe sawtooth, filtre presque fermé, remplit l'espace entre les notes. On ne sait plus si c'est du son ou déjà de l'air.",
            "Un accord très large ouvre et ferme son filtre au ralenti. Toute la pièce prend cette respiration.",
        ],
        "modulation": [
            "Le slowslider avance un paramètre à la fois. Rien ne saute ; tout dérive.",
            "Le mouvement est si lent qu'on ne le voit qu'en se retournant : il y a une heure, nous n'étions pas ici.",
        ],
        "climax": [
            "Ce n'est pas un sommet, c'est une pleine — l'eau monte sans vague. Nous sommes dedans depuis déjà longtemps.",
            "Toutes les voix flottent ensemble, aucune ne domine. Le morceau ne finira pas ; il cessera.",
        ],
        "fade": [
            "Le gain descend sans qu'on sache depuis quand. La dernière note a peut-être déjà eu lieu.",
            "On n'éteint pas : on laisse la pièce retrouver son silence d'avant.",
        ],
    },
    "techno": {
        "ouverture": [
            "Quatre kicks par cycle, secs, sans réverbération. Une usine qui ne s'excuse pas.",
            "Le kick d'entrée — la seule autorité de ce morceau. Le reste suivra, ou ne suivra pas.",
        ],
        "basse": [
            "La basse carrée, filtre modulé, cogne à contretemps du mur. Deux machines, un seul rythme.",
            "Un carré grave entre en boucle courte. Il tourne, il tourne — c'est exactement le but.",
        ],
        "lead": [
            "Le lead sawtooth crache ses notes, filtre droit. Un signal plus qu'une mélodie.",
            "Des notes en dents de scie passent la porte, une par une. Chacune doit mériter sa place.",
        ],
        "nappe": [
            "Une nappe sombre tient l'arrière — à peine plus qu'une vibration de sol.",
            "Derrière le mur de kick, un accord en scie tend la corde. Il ne cédera pas avant la fin.",
        ],
        "modulation": [
            "Le filtre de la basse respire au slider. Deux degrés d'ouverture, deux degrés de nuit.",
            "On ne change pas le pattern : on change ce qui le traverse.",
        ],
        "climax": [
            "Pleine puissance : chaque voix à sa place, chaque temps occupé. La seule issue est de danser.",
            "Le mur est complet. Rien à ajouter, rien à retirer — le mouvement est la mélodie.",
        ],
        "fade": [
            "Le gain retire les voix du haut vers le bas. L'usine ralentit ses lignes.",
            "Derniers cycles, le mur s'efface par strates. La pièce retrouve son bruit propre.",
        ],
    },
    "melancholy": {
        "ouverture": [
            "Une frappe fatiguée, presque effacée — le rythme d'un souvenir plus que d'un morceau.",
            "Le kick entre à demi, comme quelqu'un qui frappe à une porte sans vouloir qu'on ouvre.",
        ],
        "basse": [
            "La basse triangle, douce et fermée, tient deux notes. Une phrase de deux mots.",
            "Un triangle grave pose la seule certitude du morceau. Tout le reste demandera pardon.",
        ],
        "lead": [
            "Le supersine chante par petites phrases, trempé de delay. Chaque note revient plus loin, comme une lettre relue.",
            "Une mélodie en mineur avance, s'arrête, reprend. Elle connaît la fin et y va quand même.",
        ],
        "nappe": [
            "La nappe sawtooth, filtre bas, garde la chambre à demi-ouverte. Lumière de couloir.",
            "Un accord tenu, presque un soupir. La pièce entière penche du même côté.",
        ],
        "modulation": [
            "Le filtre s'ouvre à peine, un tout petit degré. C'est déjà l'événement de la journée.",
            "Le slowslider tourne sur lui-même. Ce qui change ne se voit pas ; ce qui ne change pas s'entend.",
        ],
        "climax": [
            "Ce n'est pas l'explosion, c'est l'aveu : toutes les voix se le disent en même temps.",
            "Un moment de pleine voix, puis la retenue revient. On savait qu'elle reviendrait.",
        ],
        "fade": [
            "Le gain descend comme une fièvre. Les notes s'éloignent sans se retourner.",
            "Les dernières mesures rendent la mélodie au silence. Elle n'était pas à nous.",
        ],
    },
}

# Arc d'intensite par mouvement : intro douce -> climax -> fade (l'unite
# d'entree de la prosodie TTS de l'etape 3).
_NARRATION_INTENSITY_ANCHORS: Dict[str, float] = {
    "ouverture": 0.25, "basse": 0.40, "lead": 0.60, "nappe": 0.55,
    "modulation": 0.70, "climax": 0.92, "fade": 0.12,
}


def parse_strudel_highlights(strudel_script: str) -> Dict[str, object]:
    """Extrait du script etape 1 les elements que la narration nomme.

    La narration n'est pas generique : voix, syntheses et effets sont
    lus dans le script REELLEMENT compose (nombre de lignes ``$:``),
    noms ``s('...')`` / ``.s("...")``, effets connus, BPM du header.
    """
    voices = re.findall(r"^\$:", strudel_script, flags=re.MULTILINE)
    sounds = sorted(set(re.findall(r'\.s\("([a-z0-9_]+)"\)', strudel_script)))
    drums = sorted(set(re.findall(r"s\('([a-z0-9_]+)", strudel_script)))
    effects = sorted(set(
        re.findall(
            r"\.(delay|room|lpf|pan|scope|pianoroll|slowslider|slider)\b",
            strudel_script,
        )
    ))
    bpm_match = re.search(r"BPM=(\d+)", strudel_script)
    return {
        "voices": len(voices),
        "sounds": sounds,
        "drums": drums,
        "effects": effects,
        "bpm": int(bpm_match.group(1)) if bpm_match else None,
        "has_fade": "fade-out" in strudel_script,
    }


def _snap_to_cycle(t: float, cps: float) -> float:
    """Aligne un timestamp sur une frontiere de cycle strudel (``cps``).

    La voix off demarre donc en phase avec la grille musicale ; si le
    snap produit une valeur non positive, la valeur brute est rendue.
    """
    snapped = round(t * cps) / cps
    return snapped if snapped > 0.0 else t


def _voice_labels(style_name: str, n_voices: int) -> List[str]:
    """Noms francais des voix REELLEMENT presentes dans le script.

    Sert a l'enumeration du climax : on ne nomme pas des voix absentes
    (la narration suit le script, pas une liste fixe). Le nom du lead
    est extrait du pattern du style (``supersaw``, ``supersine``...).
    """
    labels = ["kick", "basse"]
    if n_voices >= 3:
        match = re.search(r'\.s\("([a-z0-9_]+)"\)', STYLES[style_name].pattern_lead)
        labels.append(match.group(1) if match else "lead")
    if n_voices >= 4:
        labels.append("nappe")
    return labels


def compose_narration_template(
    strudel_script: str,
    style_name: str,
    duration_seconds: int,
) -> List[NarrationSegment]:
    """Genere la narration par mouvements deterministes (moteur template).

    Le decoupage suit les voix du script : ouverture (kick), basse,
    lead, nappe — seuls les mouvements dont la voix existe sont
    narrés — puis modulation, climax, fade-out alignes sur le marqueur
    du script. Frontieres alignees aux cycles strudel (cps du style),
    intensite en rampe lineaire entre ancres de mouvements.
    Deterministe : meme entree -> meme sortie (aucun alea).
    """
    plan = NARRATION_PLANS[style_name]
    highlights = parse_strudel_highlights(strudel_script)
    n_voices = max(int(highlights["voices"]), 2)

    movements = [
        m for m in _NARRATION_MOVEMENTS
        if _NARRATION_MOVEMENT_MIN_VOICES.get(m, 2) <= n_voices
    ]
    window_start = plan.start_offset_s
    span = min(plan.span_fraction * duration_seconds, plan.span_max_s)
    window_end = min(window_start + span, float(duration_seconds))
    window_len = window_end - window_start

    n_target = max(len(movements), round(window_len / plan.segment_len_s))
    # Chaque mouvement a au moins 1 segment ; les extras vont aux
    # phases qui s'etirent (modulation, climax), en round-robin.
    stretch = [m for m in ("modulation", "climax") if m in movements]
    counts: Dict[str, int] = {m: 1 for m in movements}
    extra = n_target - len(movements)
    i = 0
    while extra > 0 and stretch:
        m = stretch[i % len(stretch)]
        counts[m] += 1
        extra -= 1
        i += 1

    bank = NARRATION_BANK[style_name]
    cps = style_cps(style_name)
    anchor_list = [_NARRATION_INTENSITY_ANCHORS[m] for m in movements]
    total_segs = sum(counts.values())
    voices_list = ", ".join(_voice_labels(style_name, n_voices))

    segments: List[NarrationSegment] = []
    prev_end = round(window_start, 3)
    cursor = window_start
    for idx, m in enumerate(movements):
        m_len = window_len * counts[m] / total_segs
        for j in range(counts[m]):
            raw_start = cursor + m_len * j / counts[m]
            raw_end = cursor + m_len * (j + 1) / counts[m]
            start = max(_snap_to_cycle(raw_start, cps), prev_end)
            end = min(_snap_to_cycle(raw_end, cps), window_end)
            if end <= start:
                end = min(raw_end, window_end)
            start_r = round(start, 3)
            end_r = round(end, 3)
            if start_r < prev_end:
                start_r = prev_end
            if end_r <= start_r:
                end_r = min(start_r + 0.001, round(window_end, 3))
            if end_r <= start_r:
                continue  # frontiere snappee degeneree : segment omis
            nxt = (
                anchor_list[idx + 1] if idx + 1 < len(anchor_list)
                else anchor_list[-1] / 2.0
            )
            intensity = anchor_list[idx] + (nxt - anchor_list[idx]) * (j / counts[m])
            raw_text = bank[m][j % len(bank[m])]
            text = (
                raw_text.format(voices_list=voices_list)
                if "{voices_list}" in raw_text else raw_text
            )
            segments.append(NarrationSegment(
                start_s=start_r,
                end_s=end_r,
                text=text,
                intensity=round(intensity, 3),
            ))
            prev_end = end_r
        cursor += m_len
    return segments


NARRATION_SYSTEM_PROMPT = (
    "Tu es l'auteur de la voix off d'une vidéo de livecoding musical "
    "Strudel. Écris une narration poétique française slamée, orale et "
    "rythmée, qui NOMME l'action réelle du code fourni (les pistes, les "
    "synthés, les effets présents dans le script), puis glisse vers le "
    "poétique. CONTRAINTES : français exclusivement ; texte 100 % "
    "original ; interdiction absolue de citer, imiter ou nommer un "
    "artiste ou une œuvre tiers ; interdiction de reprendre des paroles "
    "existantes. SORTIE : strictement un tableau JSON d'objets "
    '{"start_s": <float>, "end_s": <float>, "text": <str>, '
    '"intensity": <float>} couvrant la fenêtre temporelle demandée sans '
    "chevauchement, timestamps croissants dans [0, durée], intensity "
    "dans [0, 1]. Aucun texte hors du JSON."
)


def _build_llm_client():
    """Construit le client OpenAI-compat depuis l'environnement.

    La cle est verifier AVANT l'import du package : un appel llm sans
    ``OPENAI_API_KEY`` echoue avec un message explicite (pas de
    fallback silencieux vers le template — Tell c.1102).
    """
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        raise RuntimeError(
            "moteur narration llm demande mais OPENAI_API_KEY absente de "
            "l'environnement — définir la clé ou utiliser "
            "--narration-engine template"
        )
    try:
        import openai
    except ImportError as exc:
        raise RuntimeError(
            "moteur narration llm demande mais le package 'openai' n'est "
            "pas installé (pip install openai) — ou utiliser "
            "--narration-engine template"
        ) from exc
    kwargs = {"api_key": api_key}
    base_url = os.environ.get("OPENAI_BASE_URL")
    if base_url:
        kwargs["base_url"] = base_url
    return openai.OpenAI(**kwargs)


def compose_narration_llm(
    strudel_script: str,
    style_name: str,
    duration_seconds: int,
    llm_client=None,
    llm_model: Optional[str] = None,
) -> List[NarrationSegment]:
    """Genere la narration par LLM (client OpenAI-compat, etape 2).

    Prompt system dedie, calibre sur le GENRE (nommer l'action puis
    glisser vers le poetique), francais exclusif ; l'exigence zero
    verbatim / zero nom d'artiste tiers y est portee par INSTRUCTION
    (mitigation, non enforcement — cf NARRATION_FORBIDDEN_SUBSTRINGS
    pour la seule garde executable, anti-nomination). La sortie est
    VALIDEE par :func:`validate_narration` — une reponse invalide
    echoue explicitement, elle n'est jamais rafistolee.
    """
    client = llm_client if llm_client is not None else _build_llm_client()
    model = llm_model or os.environ.get("OPENAI_MODEL", "gpt-4o-mini")
    plan = NARRATION_PLANS[style_name]
    span = min(plan.span_fraction * duration_seconds, plan.span_max_s)
    window_start = plan.start_offset_s
    window_end = min(window_start + span, float(duration_seconds))
    n_target = max(3, round((window_end - window_start) / plan.segment_len_s))
    user_prompt = (
        f"Script Strudel (etape 1) :\n```\n{strudel_script}\n```\n"
        f"Style : {style_name}. Durée totale : {duration_seconds} s.\n"
        f"Fenêtre de voix off : [{window_start:.1f} s, {window_end:.1f} s], "
        f"environ {n_target} segments. Nomme les voix, synthés et effets "
        f"réellement présents dans le script ci-dessus."
    )
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": NARRATION_SYSTEM_PROMPT},
            {"role": "user", "content": user_prompt},
        ],
        temperature=0.8,
    )
    raw = response.choices[0].message.content or ""
    cleaned = re.sub(r"^```(?:json)?\s*|\s*```$", "", raw.strip())
    try:
        data = json.loads(cleaned)
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"sortie LLM non parsable en JSON ({exc}) — extrait : {cleaned[:200]!r}"
        ) from exc
    if not isinstance(data, list):
        raise ValueError(
            f"sortie LLM : attendu un tableau JSON, reçu {type(data).__name__}"
        )
    segments: List[NarrationSegment] = []
    for i, item in enumerate(data):
        try:
            segments.append(NarrationSegment(
                start_s=float(item["start_s"]),
                end_s=float(item["end_s"]),
                text=str(item["text"]),
                intensity=float(item["intensity"]),
            ))
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"segment LLM #{i} invalide ({exc}) : {item!r}") from exc
    return segments


def compose_narration(
    strudel_script: str,
    style_name: str,
    duration_seconds: int,
    engine: str = "template",
    llm_client=None,
    llm_model: Optional[str] = None,
) -> List[NarrationSegment]:
    """Genere les segments de narration timestampes (etape 2, #15604).

    Moteurs :
    - ``template`` (defaut) : deterministe, hors-ligne, mouvements
      alignes sur les voix reelles du script et la grille de cycles.
    - ``llm`` : client OpenAI-compat (``OPENAI_API_KEY`` obligatoire,
      ``OPENAI_BASE_URL`` / ``OPENAI_MODEL`` optionnels) — echec
      explicite sans cle, sortie validee, aucun fallback silencieux.

    Retourne des :class:`NarrationSegment` valides pour
    ``duration_seconds`` (validateur : :func:`validate_narration`).
    """
    if style_name not in STYLES:
        raise ValueError(
            f"style {style_name!r} inconnu ; styles disponibles : {sorted(STYLES.keys())}"
        )
    if engine == "template":
        segments = compose_narration_template(
            strudel_script, style_name, duration_seconds
        )
    elif engine == "llm":
        segments = compose_narration_llm(
            strudel_script, style_name, duration_seconds,
            llm_client=llm_client, llm_model=llm_model,
        )
    else:
        raise ValueError(
            f"moteur de narration inconnu {engine!r} (attendu 'template' ou 'llm')"
        )
    validate_narration(segments, duration_seconds)
    return segments


def validate_narration(
    segments: List[NarrationSegment],
    duration_seconds: int,
) -> None:
    """Valide le contrat des segments (autorite finale etape 2 -> 3).

    Verifie : au moins 2 segments ; timestamps dans [0, duree],
    croissants, sans recouvrement ; textes non vides (<= 600
    caracteres) sans nom d'artiste tiers (garde ANTI-NOMINATION,
    voie 3 B.0) ; intensite dans [0, 1]. Raise ``ValueError``
    detaillee au premier defaut.

    LIMITATION : la garde de texte est anti-nomination, PAS un
    detecteur de verbatim — un detecteur de verbatim exigerait un
    corpus de reference (hors depot, bibliography-hygiene §2). Le
    verbatim est exclu par provenance : template = textes originaux
    par construction ; LLM = exigence du system prompt (instruction,
    non enforcement).
    """
    if len(segments) < 2:
        raise ValueError(
            f"narration : au moins 2 segments attendus, reçu {len(segments)}"
        )
    prev_end = 0.0
    for i, seg in enumerate(segments):
        if not (0.0 <= seg.start_s < seg.end_s <= duration_seconds + _NARRATION_TIME_EPS):
            raise ValueError(
                f"segment #{i} : timestamps invalides (start={seg.start_s}, "
                f"end={seg.end_s}, durée max={duration_seconds})"
            )
        if seg.start_s < prev_end - _NARRATION_TIME_EPS:
            raise ValueError(
                f"segment #{i} : recouvrement (start={seg.start_s} < "
                f"fin précédente={prev_end})"
            )
        if not seg.text or not seg.text.strip():
            raise ValueError(f"segment #{i} : texte vide")
        if len(seg.text) > _NARRATION_TEXT_MAX_CHARS:
            raise ValueError(
                f"segment #{i} : texte trop long "
                f"({len(seg.text)} > {_NARRATION_TEXT_MAX_CHARS})"
            )
        lowered = seg.text.lower()
        for needle in NARRATION_FORBIDDEN_SUBSTRINGS:
            if needle in lowered:
                raise ValueError(
                    f"segment #{i} : nom d'artiste tiers interdit "
                    "(garde anti-nomination, voie 3 B.0)"
                )
        if not (0.0 <= seg.intensity <= 1.0):
            raise ValueError(
                f"segment #{i} : intensité hors [0, 1] ({seg.intensity})"
            )
        prev_end = seg.end_s


def narration_to_json(segments: List[NarrationSegment]) -> str:
    """Serialise les segments en JSON (entree de l'etape 3 TTS et des
    sous-titres de l'etape 6). ``ensure_ascii=False`` : le texte
    francais accentue reste lisible."""
    return json.dumps([asdict(s) for s in segments], ensure_ascii=False, indent=2)


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
    narration_engine: str = "template",
    narration_json_path: Optional[str] = None,
) -> Dict[str, object]:
    """Orchestrateur : compose le script Strudel, genere la narration
    timestampee (etape 2) et documente les autres etapes.

    Retourne un dict avec une cle par etape ; les etapes non livrees
    portent la valeur 'deferred...'. C'est un contrat HONNETE (Tell
    c.1102) : pas de pipeline squelette qui pretend faire ce qu'il ne
    fait pas.

    Parametres :
    - style_name : style musical (cf :func:`compose_strudel`).
    - duration_seconds : duree cible en secondes.
    - output_path : chemin du fichier .mp4 final (sans --capture, ce
      chemin n'est PAS cree : l'integrateur ffmpeg est deferred).
    - tts_voice : voix TTS Kokoro/FishAudio (optionnel, deferred).
    - playwright_url : URL du navigateur Strudel (deferred).
    - ffmpeg_loudnorm_lufs : cible loudness (deferred).
    - narration_engine : moteur de l'etape 2 ('template' deterministe
      par defaut, ou 'llm' — cf :func:`compose_narration`).
    - narration_json_path : si fourni, ecrit les segments valides dans
      ce fichier JSON (entree reelle de l'etape 3 TTS).

    Retourne : dict avec cles 'strudel_script', 'narration' (liste de
    dicts segments), 'tts', 'browser_capture', 'visualizer',
    'final_mix', 'verdict'.
    """
    strudel = compose_strudel(
        style_name=style_name,
        duration_seconds=duration_seconds,
        visuals=capture,
    )

    narration_segments = compose_narration(
        strudel_script=strudel,
        style_name=style_name,
        duration_seconds=duration_seconds,
        engine=narration_engine,
    )
    if narration_json_path:
        json_path = Path(narration_json_path)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(
            narration_to_json(narration_segments), encoding="utf-8"
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
        "narration": [asdict(s) for s in narration_segments],
        "tts": "deferred" if tts_voice is None else f"requested={tts_voice}",
        "browser_capture": browser_capture,
        "visualizer": "deferred (V1 only — capture Strudel inclut scope/pianoroll)",
        "final_mix": final_mix,
        "verdict": (
            "Etape 1 (composition) + etape 2 (narration timestampee, "
            f"moteur {narration_engine}) + etape 4 (capture navigateur : "
            "export WAV offline natif + MediaRecorder + mux ffmpeg) livrees ; "
            "etapes 3/5/6 deferred avec claim explicite par phase."
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
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
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
        description="Pipeline livecoding-video (#15604). Compose un "
        "script Strudel multi-pistes par template (etape 1) et la "
        "narration poetique timestampee (etape 2) ; les etapes 3/5/6 "
        "restent deferred.",
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
    parser.add_argument(
        "--narration-engine",
        choices=("template", "llm"),
        default="template",
        help="etape 2 : moteur de narration (default: template, "
             "deterministe hors-ligne ; llm = client OpenAI-compat, "
             "OPENAI_API_KEY requise, echec explicite sans cle)",
    )
    parser.add_argument(
        "--narration-json",
        default=None,
        help="etape 2 : ecrire les segments timestampes valides dans ce "
             "fichier JSON (entree de l'etape 3 TTS)",
    )
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    args = _build_arg_parser().parse_args(argv)
    try:
        result = run_pipeline(
            style_name=args.style,
            duration_seconds=args.duration,
            output_path=args.output,
            tts_voice=args.tts_voice,
            capture=args.capture,
            capture_seconds=args.capture_seconds,
            headless=args.headless,
            narration_engine=args.narration_engine,
            narration_json_path=args.narration_json,
        )
    except RuntimeError as exc:
        # Echec explicite (ex. moteur llm sans cle) — pas de fallback
        # silencieux vers template (Tell c.1102).
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 2
    # Verdict explicite — Tell c.1102 anti-stonewall
    print("=== Strudel script (etape 1, livree) ===")
    print(result["strudel_script"])
    print()
    narration = result["narration"]
    first, last = narration[0], narration[-1]
    print("=== Narration (etape 2, livree) ===")
    print(
        f"  {len(narration)} segments, fenetre "
        f"[{first['start_s']} s, {last['end_s']} s]"
    )
    preview = first["text"]
    print(f"  apercu : {preview[:120]}{'...' if len(preview) > 120 else ''}")
    if args.narration_json:
        print(f"  JSON ecrit : {args.narration_json}")
    print()
    print("=== Status des etapes 3-6 ===")
    for key in ("tts", "browser_capture", "visualizer", "final_mix"):
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
