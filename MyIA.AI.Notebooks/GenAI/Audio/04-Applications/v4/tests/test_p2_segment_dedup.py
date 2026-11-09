"""P2 -- la deduplication des segments ne doit pas perdre de contenu.

Un paragraphe produit legitimement PLUSIEURS segments : le SYSTEM_PROMPT de
p2_segmentation l'impose (regle 2 -- un paragraphe mixte est decoupe en
segments distincts ; regle 4 -- 15 a 60 mots par segment ; regle 6 -- chaque
segment porte le paragraph_id de son paragraphe source). La deduplication
doit donc resoudre le chevauchement entre chunks SANS sacrifier les segments
d'un meme paragraphe.

Ces tests sont hermetiques : aucun reseau, aucune cle d'API, aucun appel LLM.
`segment_chunk` et `load_source_text` sont remplaces par des doublures.

Lancer depuis le repertoire v4 :
    python -m pytest tests/test_p2_segment_dedup.py -v
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


def _seg(idx: int, pid: int, text: str):
    from v4.schemas import Segment

    return Segment(
        seg_index=idx,
        type="narration",
        speaker_raw="narrateur",
        speaker="narrateur",
        text=text,
        paragraph_id=pid,
    )


# ── deduplicate_overlaps ────────────────────────────────────────────────


def test_un_paragraphe_multi_segments_est_entierement_conserve():
    """Un paragraphe decoupe en 4 segments, dans UN SEUL chunk.

    Sans chevauchement, il n'y a rien a dedupliquer : les 4 segments sont
    le contenu du paragraphe. Le code d'avant n'en gardait qu'un.
    """
    from v4 import p2_segmentation as p2

    chunk = [
        _seg(0, 7, "Le vent s'elevait contre les vitres et la neige tournoyait."),
        _seg(1, 7, "Madame Rousset, plus pale que le linge, ecoutait le silence."),
        _seg(2, 7, "Elle monta l'echelle et ouvrit la fenetre du corridor."),
        _seg(3, 7, "Le vent s'engouffra dans la chambre et fit tinter les glasses."),
    ]

    out = p2.deduplicate_overlaps(chunk, chunk_sizes=[4])

    assert len(out) == 4, (
        f"les 4 segments du paragraphe 7 doivent etre conserves, "
        f"{len(out)} conserves"
    )
    assert [s.paragraph_id for s in out] == [7, 7, 7, 7]
    assert [s.text for s in out] == [s.text for s in chunk]
    # Re-indexation sequentielle de 0
    assert [s.seg_index for s in out] == [0, 1, 2, 3]


def test_le_chunk_le_plus_recent_gagne_sans_ecraser_les_autres_segments():
    """Chevauchement : le dernier chunk gagne, mais TOUS ses segments restent.

    Le paragraphe 6 est dans les deux chunks. Le code d'avant n'en conservait
    qu'un seul segment (le dernier de la liste), quel que soit le chunk.
    """
    from v4 import p2_segmentation as p2

    chunk0 = [
        _seg(0, 5, "chunk zero, paragraphe precedent."),
        _seg(1, 6, "chunk zero, premier fragment du paragraphe."),
        _seg(2, 6, "chunk zero, second fragment du paragraphe."),
    ]
    chunk1 = [
        _seg(3, 6, "chunk un, premier fragment du paragraphe."),
        _seg(4, 6, "chunk un, second fragment du paragraphe."),
        _seg(5, 7, "chunk un, paragraphe suivant."),
    ]

    out = p2.deduplicate_overlaps(chunk0 + chunk1, chunk_sizes=[3, 3])

    # p5 : un seul chunk -> 1 segment ; p6 : deux chunks -> les 2 segments du
    # dernier ; p7 : un seul chunk -> 1 segment.
    assert len(out) == 4, f"4 segments attendus (1 p5, 2 p6, 1 p7), {len(out)}"
    texts = [s.text for s in out]
    assert "chunk un, premier fragment du paragraphe." in texts
    assert "chunk un, second fragment du paragraphe." in texts
    assert "chunk un, paragraphe suivant." in texts
    # Le paragraphe 5 n'est couvert par qu'un chunk : son segment est conserve.
    assert "chunk zero, paragraphe precedent." in texts
    # Aucun segment du chunk zero ne subsiste pour le paragraphe 6
    assert not any(
        s.paragraph_id == 6 and s.text.startswith("chunk zero") for s in out
    )


def test_repli_sans_frontieres_de_chunk_ne_perd_pas_un_segment_unique():
    """Sans information de chunk, deux segments ne sont doublons que si leur
    (paragraph_id, text) coincide : un segment au texte unique est conserve."""
    from v4 import p2_segmentation as p2

    segs = [
        _seg(0, 3, "un texte propre a ce paragraphe."),
        _seg(1, 3, "un autre texte propre a ce paragraphe."),
        _seg(2, 3, "un texte propre a ce paragraphe."),
    ]

    out = p2.deduplicate_overlaps(segs)

    assert len(out) == 2
    assert [s.text for s in out] == [
        "un autre texte propre a ce paragraphe.",
        "un texte propre a ce paragraphe.",
    ]


def test_des_frontieres_de_chunk_incoherentes_sont_refusees():
    """Un chunk_sizes qui ne decrit pas les segments est une erreur franche,
    pas une deduplication silencieuse."""
    from v4 import p2_segmentation as p2

    try:
        p2.deduplicate_overlaps([_seg(0, 1, "un segment sans doute.")], chunk_sizes=[2])
    except ValueError as exc:
        assert "chunk_sizes" in str(exc)
    else:
        raise AssertionError("un chunk_sizes incoherent doit lever ValueError")


# ── run() : le contrôle de couverture doit bloquer ──────────────────────


_PARAGRAPHS = [
    "Le vent s'elevait contre les vitres et la neige tournoyait dans la cour "
    "de l'auberge, tandis que les voyageurs attendaient sans rien dire.",
    "Madame Rousset, plus pale que le linge, ecoutait le silence de la salle "
    "et comptait les tasses posees sur la table de bois.",
    "Elle monta l'echelle, ouvrit la fenetre du corridor, et la nuit entra "
    "d'un coup, bringing l'odeur de la neige et du fumier de cheval.",
    "Personne ne parla dans la chambre ; le train, quelque part, repartit "
    "dans la nuit bleue et laissa derriere lui un silence plus grand.",
]


def _install_stubs(monkeypatch, tmp_path, split_in_two: bool):
    """Remplace la source et le segmentateur LLM par des doublures.

    `split_in_two=True` : chaque paragraphe est coupe en deux segments
    (un paragraphe mixte, comme le demande le SYSTEM_PROMPT).
    `split_in_two=False` : chaque paragraphe ne rend que sa premiere moitie,
    le texte source est donc partiellement perdu.
    """
    from v4 import p2_segmentation as p2

    source = "\n\n".join(_PARAGRAPHS)
    monkeypatch.setattr(p2, "OUTPUTS", tmp_path)
    monkeypatch.setattr(p2, "load_source_text", lambda *a, **k: source)

    def fake_segment_chunk(chunk, start_seg_index, previous_segments):
        out = []
        index = start_seg_index
        for paragraph in chunk:
            words = paragraph["text"].split()
            if split_in_two:
                half = len(words) // 2
                parts = [" ".join(words[:half]), " ".join(words[half:])]
            else:
                parts = [" ".join(words[: len(words) // 2])]
            for part in parts:
                out.append(_seg(index, paragraph["paragraph_id"], part))
                index += 1
        return out

    monkeypatch.setattr(p2, "segment_chunk", fake_segment_chunk)
    return source


def test_run_conserve_tous_les_segments_d_un_paragraphe_multi(monkeypatch, tmp_path):
    """Le run complet garde les 8 segments (4 paragraphes x 2) et ne leve rien."""
    from v4 import p2_segmentation as p2

    _install_stubs(monkeypatch, tmp_path, split_in_two=True)

    output_path = p2.run(force=True)

    batch = json.loads(output_path.read_text(encoding="utf-8"))
    assert len(batch["segments"]) == 8, (
        f"les 8 segments du texte source doivent etre conserves, "
        f"{len(batch['segments'])} ecrits"
    )

    report = json.loads(
        (tmp_path / "segmentation_report.json").read_text(encoding="utf-8")
    )
    assert report["coverage_ratio"] == 1.0
    assert report["complete"] is True
    assert report["missing_paragraphs"] == []


def test_run_leve_quand_la_segmentation_ne_couvre_pas_le_source(monkeypatch, tmp_path):
    """Un texte source a moitie perdu fait echouer la phase.

    Les artefacts restent ecrits : la phase ne declare pas une reussite qu'elle
    n'a pas mesuree, mais elle ne jette pas le travail fait.
    """
    from v4 import p2_segmentation as p2

    _install_stubs(monkeypatch, tmp_path, split_in_two=False)

    try:
        p2.run(force=True)
    except p2.IncompleteSegmentationError as exc:
        assert "couverture" in str(exc)
    else:
        raise AssertionError(
            "une segmentation qui perd la moitie du texte doit lever "
            "IncompleteSegmentationError"
        )

    assert (tmp_path / "segments_v4.json").exists(), "les artefacts sont conserves"
    report = json.loads(
        (tmp_path / "segmentation_report.json").read_text(encoding="utf-8")
    )
    assert report["complete"] is False
    assert report["coverage_ratio"] < 0.85


def test_allow_incomplete_ne_leve_pas(monkeypatch, tmp_path):
    """Le desistement explicite : un run de diagnostic ne bloque pas."""
    from v4 import p2_segmentation as p2

    _install_stubs(monkeypatch, tmp_path, split_in_two=False)

    output_path = p2.run(force=True, allow_incomplete=True)

    assert output_path.exists()
    report = json.loads(
        (tmp_path / "segmentation_report.json").read_text(encoding="utf-8")
    )
    assert report["complete"] is False


def test_un_cache_incomplet_est_refuse(monkeypatch, tmp_path):
    """Une segmentation incomplete ecrit puis levee ne doit pas etre resservie
    par un run sans --force : la phase suivante la recevrait telle quelle."""
    from v4 import p2_segmentation as p2

    _install_stubs(monkeypatch, tmp_path, split_in_two=False)

    try:
        p2.run(force=True)
    except p2.IncompleteSegmentationError:
        pass
    else:
        raise AssertionError("le premier run doit lever")

    try:
        p2.run()
    except p2.IncompleteSegmentationError as exc:
        assert "cache" in str(exc)
    else:
        raise AssertionError("un cache incomplet doit etre refuse")
