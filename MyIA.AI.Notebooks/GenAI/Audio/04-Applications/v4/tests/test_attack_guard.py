"""Garde d'attaque par chunk (#19739) — tests hors reseau et hors GPU.

Couvre le detecteur (`detect_missing_attack`), la convention de re-roll
(`spaced_seed`, `plan_reroll`), l'agregat (`evaluate_chunks`) et la CLI
(manifeste + transcriptions deja mesurees).

Les deux controls sont explicites et c'est l'essentiel du fichier :
- **controle negatif** : un chunk rendu fidelement n'est jamais signale ;
- **controle positif** : un chunk dont l'attaque a disparu est signale, et
  la raison indiquee permet de distinguer « span de tete » de « mots de tete
  absents ».

Run from the v4 directory:
    python -m pytest tests/test_attack_guard.py -v
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def _detect(source: str, transcript: str, **kw) -> dict:
    from v4.attack_guard import detect_missing_attack

    return detect_missing_attack(source, transcript, **kw)


def test_healthy_chunk_is_not_flagged():
    """Controle negatif : un rendu fidele ne declenche aucune alerte."""
    source = (
        "Les voyageurs se regardaient avec une certaine honte, comme des "
        "enfants punis qui n'osent pas lever les yeux."
    )
    verdict = _detect(source, source)
    assert verdict["attack_dropped"] is False
    assert verdict["reason"] == "none"
    assert verdict["n_missing_leading"] == 0


def test_healthy_chunk_tolerates_punctuation_and_case():
    """La normalisation de p7 absorbe casse et ponctuation."""
    source = "Le vent souffle sur la plaine, et les blés se couchent."
    verdict = _detect(source, "le vent souffle sur la plaine et les bles se couchent")
    assert verdict["attack_dropped"] is False


def test_dropped_attack_is_flagged_by_leading_span():
    """Controle positif : le rendu commence au milieu du texte source.

    Cas mesure de #19699 : l'ASR montre la parole demarrant au milieu du
    texte fourni — la premiere proposition n'est jamais prononcee.
    """
    source = (
        "Pendant plusieurs jours de suite des lambeaux d'armee en deroute "
        "avaient traverse la ville. Ce n'etait point de la troupe."
    )
    transcript = "Ce n'etait point de la troupe."
    verdict = _detect(source, transcript)
    assert verdict["attack_dropped"] is True
    assert verdict["reason"] == "leading_span"
    assert verdict["n_missing_leading"] > 0
    assert verdict["first_missing_word"] == "pendant"
    assert verdict["span"]["start"] == 0


def test_head_loss_is_positional_not_presence():
    """Le critere est positionnel : un mot source absent *ailleurs* ne suffit pas.

    C'est le point corrige par la mesure sur rendus reels : la presence des
    mots de tete dans la transcription n'est pas la preuve que l'attaque a
    ete dite. Ici la source commence par « un deux trois » et la
    transcription aussi — le mot « trois » est absent de part et d'autre,
    mais le rendu n'a pas saute son debut : ce n'est pas une attaque.
    """
    source = "un deux trois quatre cinq"
    verdict = _detect(source, "un deux X quatre cinq", min_attack_words=2)
    assert verdict["attack_dropped"] is False
    assert verdict["reason"] == "none"

    # En revanche, si la transcription commence plus loin dans la source,
    # la perte de tete est mesuree : « un deux trois » ont disparu.
    verdict_2 = _detect(source, "quatre cinq", min_attack_words=2)
    assert verdict_2["attack_dropped"] is True
    assert verdict_2["reason"] == "leading_span"
    assert verdict_2["n_missing_leading"] == 3


def test_single_mispronounced_word_is_not_an_attack():
    """Une faute de prononciation sur un mot n'est pas une attaque perdue.

    Le seuil est le meme que celui de p7 : sans cela, la garde crierait au
    loup sur chaque render imparfait.
    """
    source = "Les voyageurs se regardaient avec une certaine honte."
    verdict = _detect(source, "Les voyageurs se regardaient avec une certaine hontt.")
    assert verdict["attack_dropped"] is False


def test_empty_transcript_is_an_attack():
    """Un chunk muet est le pire cas d'attaque : tout le texte est perdu."""
    source = "Les voyageurs se regardaient avec une certaine honte."
    verdict = _detect(source, "")
    assert verdict["attack_dropped"] is True
    assert verdict["reason"] == "empty_transcript"
    assert verdict["n_missing_leading"] == len(source.split())


def test_empty_source_is_not_measured():
    """Pas de source, pas de verdict : la garde ne doit pas crier au loup."""
    verdict = _detect("", "quelque chose")
    assert verdict["attack_dropped"] is False
    assert verdict["reason"] == "source_too_short"


# --- Donnees mesurees (2026-10-19, GPU 2) ----------------------------------
#
# Chunk 0 du corpus `boule_de_suif_full.txt`, rendu par Chatterbox
# (graine 42), transcrit par `openai/whisper-large-v3-turbo`. Le controle
# positif est le meme rendu ampute de ses 1,5 premieres secondes.
#
# Ces deux tests sont les **temoins de la mesure** : ils encodent le
# comportement que la mesure a etabli, pas un comportement invente.

_SRC_0 = (
    "BOULE DE SUIF Pendant plusieurs jours de suite des lambeaux d'armee en "
    "deroute avaient traverse la ville. Ce n'etait point de la troupe, mais "
    "des hordes debandees."
)

# Rendu naturel : la transcription est bruitee (l'ASR se trompe sur le
# debut) mais elle COMMENCE par le texte source.
_NAT_0 = (
    " Bordes suives pendants plus cieuses jouent au sud de l'embol d'armee "
    "et une deroute avaient traverse la ville. Ce n'etait point de la "
    "troupe, mais des hordees des bandaises."
)

# Controle positif : meme rendu, attaque amputee.
_TRO_0 = (
    " Les policieuses jouent de suite de l'embol d'armee et une deroute "
    "avaient traverse la ville. Ce n'etait point de la troupe, mais des "
    "hordees des bandaises."
)


def test_measured_render_with_asr_noise_is_not_an_attack():
    """Temoin de mesure : un rendu reel bruite n'est PAS une attaque perdue.

    Cet audio a ete rendu puis transcrit : l'ASR se trompe sur plusieurs
    mots de tete (« boule de suif » -> « bordes suives »). Un critere de
    presence des mots de tete le signalait a tort ; le critere positionnel
    (perte de tete contigue) ne le signale pas.
    """
    verdict = _detect(_SRC_0, _NAT_0)
    assert verdict["attack_dropped"] is False
    assert verdict["reason"] == "none"
    assert verdict["n_missing_leading"] == 0


def test_measured_truncated_render_is_an_attack():
    """Temoin de mesure : le controle positif (attaque amputee) EST signale."""
    verdict = _detect(_SRC_0, _TRO_0)
    assert verdict["attack_dropped"] is True
    assert verdict["reason"] == "leading_span"
    assert verdict["n_missing_leading"] >= 3
    assert verdict["span"]["start"] == 0


def test_spaced_seed_matches_the_p5_formula():
    """La graine de re-roll est celle de p5 : `seed + i + attempt * 104_729`."""
    from v4.attack_guard import RETRY_SEED_STRIDE, spaced_seed

    assert RETRY_SEED_STRIDE == 104_729
    # attempt 0 reproduit la graine d'origine : un chunk sain ne bouge pas.
    assert spaced_seed(42, 3, 0) == 45
    assert spaced_seed(42, 3, 1) == 42 + 3 + 104_729
    assert spaced_seed(42, 3, 2) == 42 + 3 + 2 * 104_729


def test_evaluate_chunks_lists_only_the_faulty_chunks():
    """L'agregat ne re-roule que les chunks fautifs, avec leur graine."""
    from v4.attack_guard import evaluate_chunks

    chunks = [
        {"chunk_index": 0, "text": "Les voyageurs se regardaient avec honte.", "seed": 42},
        {
            "chunk_index": 1,
            "text": "Pendant plusieurs jours des lambeaux ont traverse la ville.",
            "seed": 43,
        },
        {"chunk_index": 2, "text": "Le soir venu, on alluma les lanternes.", "seed": 44},
    ]
    transcripts = {
        0: "Les voyageurs se regardaient avec honte.",
        1: "ont traverse la ville.",
        2: "Le soir venu, on alluma les lanternes.",
    }

    report = evaluate_chunks(chunks, lambda c: transcripts[int(c["chunk_index"])])
    assert report["n_chunks"] == 3
    assert report["n_attack_dropped"] == 1
    assert [p["chunk_index"] for p in report["reroll_plan"]] == [1]
    assert report["reroll_plan"][0]["next_seed"] == 42 + 1 + 104_729
    assert report["verdicts"][0]["attack_dropped"] is False
    assert report["verdicts"][2]["attack_dropped"] is False


def test_cli_reads_manifest_and_transcripts(tmp_path):
    """La CLI consomme un manifeste et des transcriptions deja mesurees."""
    from v4.attack_guard import main

    manifest = {
        "engine": "chatterbox",
        "base_seed": 42,
        "chunks": [
            {"chunk_index": 0, "text": "Les voyageurs se regardaient avec honte.", "seed": 42},
            {
                "chunk_index": 1,
                "text": "Pendant plusieurs jours des lambeaux ont traverse la ville.",
                "seed": 43,
            },
        ],
    }
    transcripts = {"0": "Les voyageurs se regardaient avec honte.", "1": "traverse la ville."}
    manifest_path = tmp_path / "chunks.json"
    transcripts_path = tmp_path / "transcripts.json"
    out_path = tmp_path / "attack_report.json"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    transcripts_path.write_text(json.dumps(transcripts), encoding="utf-8")

    rc = main(
        [
            "--manifest",
            str(manifest_path),
            "--transcripts",
            str(transcripts_path),
            "--out",
            str(out_path),
        ]
    )
    assert rc == 0
    report = json.loads(out_path.read_text(encoding="utf-8"))
    assert report["n_chunks"] == 2
    assert report["n_attack_dropped"] == 1
    assert report["engine"] == "chatterbox"
    assert report["reroll_plan"][0]["chunk_index"] == 1
