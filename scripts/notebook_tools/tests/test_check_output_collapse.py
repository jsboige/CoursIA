"""Tests for check_output_collapse.py — output-volume collapse axis (#15327).

Pins the discriminating design (ai-01 measurement on the issue: aggregate
contraction alone is ~100 % FP): the SIGNATURE signal fires on a
graceful-degradation motif over a substantial base, the MAGNITUDE signal on
a per-cell order-of-magnitude loss, and the two mechanically detectable
legitimate causes (content moved to a notebook created by the same diff,
diagnostic-text purge) exempt the magnitude signal only. Benign variance,
sub-floor bases, growth, deleted cells and added notebooks are silent.
The logic under test is the pure ``analyze`` / ``_apply_moved_content`` —
no git, no kernel.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_output_collapse import (
    BASE_FLOOR,
    DIAGNOSTIC_LINE_FRACTION,
    MAGNITUDE_FACTOR,
    MOVED_GAIN_FRACTION,
    SIGNATURE_FACTOR,
    _apply_moved_content,
    _diagnostic_fraction,
    _normalize,
    analyze,
)


def code_cell(cid, text):
    return {"cell_type": "code", "id": cid,
            "outputs": [{"output_type": "stream", "text": text}]}


def nb(code_cells):
    return {"cells": [code_cell(k, t) for k, t in code_cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def base(code_cells, added=False):
    """None when the notebook is ADDED by the branch (no baseline)."""
    return None if added else nb(code_cells)


LONG = "x" * 1000
SKIP_NOTICE = ("[INFO] API non configuree - execution sautee\n"
               "Configurez OPENAI_API_KEY pour executer les exemples\n")
WARNINGS = "".join(
    "warning CS8632: Une reference nullable est requise %d\n" % i
    for i in range(30))


def test_signature_fires_on_skip_notice():
    got = analyze(base([("a", LONG)]), nb([("a", SKIP_NOTICE)]))
    assert got["regressed"]
    assert got["cells"][0]["kind"] == "signature"
    assert got["cells"][0]["factor"] >= SIGNATURE_FACTOR


def test_signature_is_accent_blind():
    # "sautée" / "configurée" with accents must match the accent-stripped
    # motifs (both spellings exist in the wild).
    got = analyze(base([("a", LONG)]),
                  nb([("a", "Execution sautée (API non configurée)\n")]))
    assert got["cells"] and got["cells"][0]["kind"] == "signature"


def test_signature_fires_on_motif_even_when_grown():
    # Issue #21424 T2-corrige : la signature attrape le motif "nouveau"
    # independamment de la contraction. Un "skipped" apparu dans une
    # sortie reelle est un signal de degradation (meme si la cellule
    # a grossi en meme temps, le motif a ete ajoute). C'est le cas
    # fondateur Kokoro f82ed24e (566 -> 15602 chars).
    got = analyze(base([("a", LONG)]),
                  nb([("a", "skipped 0 tests\n" + "x" * 1500)]))
    assert any(f["kind"] == "signature" for f in got["cells"]), got["cells"]


def test_magnitude_fires_on_order_of_magnitude_loss():
    got = analyze(base([("a", LONG)]), nb([("a", "y" * 40)]))
    assert got["regressed"]
    assert got["cells"][0]["kind"] == "magnitude"
    assert got["cells"][0]["factor"] >= MAGNITUDE_FACTOR


def test_benign_variance_silent():
    got = analyze(base([("a", LONG)]), nb([("a", "x" * 700)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_subfloor_base_silent():
    # Below the noise floor a base is jitter, even at x400 contraction.
    assert len("x" * 400) < BASE_FLOOR
    got = analyze(base([("a", "x" * 400)]), nb([("a", "y")]))
    assert got["cells"] == []


def test_growth_silent():
    got = analyze(base([("a", LONG)]), nb([("a", "x" * 5000)]))
    assert got["cells"] == []


def test_diagnostic_purge_exempt():
    got = analyze(base([("a", WARNINGS)]), nb([("a", "Build succeeded.\n")]))
    assert got["cells"][0]["kind"] == "exempt-diagnostic"
    assert got["cells"][0]["diagnostic_fraction"] >= DIAGNOSTIC_LINE_FRACTION
    assert not got["regressed"]


def test_purge_swallowing_real_output_still_fires():
    # Char-weighted classification: a purge that also swallows a large real
    # output line must not ride along the short warning lines.
    got = analyze(base([("a", WARNINGS + "real: " + "z" * 900 + "\n")]),
                  nb([("a", "real: " + "z" * 50 + "\n")]))
    assert got["cells"][0]["kind"] == "magnitude"
    assert got["regressed"]


def test_deleted_cell_silent():
    # A PR that deletes code cells loses volume legitimately: the deleted
    # cell has no head counterpart, so no finding is produced.
    got = analyze(base([("a", LONG), ("b", LONG)]), nb([("a", LONG)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_added_notebook_never_regressed():
    got = analyze(base([], added=True), nb([("a", SKIP_NOTICE)]))
    assert not got["regressed"]
    assert got["added"]


def test_index_shift_not_misattributed():
    got = analyze(base([("a", LONG)]), nb([("zz", "y"), ("a", LONG)]))
    assert got["cells"] == []


def test_moved_content_exempts_at_diff_scale():
    # Split pattern (#14795): notebook A collapses a cell, notebook B is
    # CREATED by the same diff with comparable volume.
    rows = [analyze(base([("a", LONG * 3)]), nb([("a", "y" * 30)])),
            analyze(base([], added=True), nb([("b", "z" * 1500)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "exempt-moved"
    assert not rows[0]["regressed"]


def test_insufficient_moved_gain_does_not_exempt():
    rows = [analyze(base([("a", LONG * 3)]), nb([("a", "y" * 30)])),
            analyze(base([], added=True), nb([("b", "z" * 300)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "magnitude"
    assert rows[0]["regressed"]


def test_moved_content_never_exempts_signature():
    rows = [analyze(base([("a", LONG)]), nb([("a", SKIP_NOTICE)])),
            analyze(base([], added=True), nb([("b", "z" * 5000)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "signature"
    assert rows[0]["regressed"]


def test_normalize_strips_accents_and_lowercases():
    assert _normalize("Exécution Sautée (non configuré)") == \
        "execution sautee (non configure)"


def test_diagnostic_fraction_char_weighted():
    removed_real = "z" * 900
    got = _diagnostic_fraction(WARNINGS + removed_real + "\n",
                               removed_real + "\n")
    # All removed chars are warnings here: fraction 1.0.
    assert got == 1.0
    got = _diagnostic_fraction(WARNINGS + removed_real + "\n", "\n")
    # The real 900-char line dominates the removed volume: fraction < 0.8.
    assert got < DIAGNOSTIC_LINE_FRACTION


def test_constants_pinned():
    # Calibration provenance: reference case factors 14.9/67.6/49.4 (all
    # above 10), noise floor 500 chars, moved-gain fraction from ai-01's
    # "un volume comparable" on #14795's split.
    assert BASE_FLOOR == 500
    assert MAGNITUDE_FACTOR == 10
    assert SIGNATURE_FACTOR == 2
    assert MOVED_GAIN_FRACTION == 0.5
    assert DIAGNOSTIC_LINE_FRACTION == 0.8


# ---------------------------------------------------------------------------
# Issue #21424 T1 + T2: --history mode and the body-justification bypass.
# ---------------------------------------------------------------------------

def test_parse_collapse_justification_absent():
    """No section header -> no justification, regardless of body content."""
    from check_output_collapse import parse_collapse_justification
    assert parse_collapse_justification("") == {}
    assert parse_collapse_justification("## unrelated section") == {}
    assert parse_collapse_justification(
        "## output-collapse justification\nno cells here"
    ) == {}


def test_parse_collapse_justification_form_dash_cell():
    """`- notebook.ipynb cell abcd: reason` is recognized."""
    from check_output_collapse import parse_collapse_justification
    body = ("## Output-collapse justification\n"
            "- Lean-7b-Examples.ipynb cell eb711ddb: API key absent\n"
            "## Next section")
    j = parse_collapse_justification(body)
    assert ("Lean-7b-Examples.ipynb", "eb711ddb") in j
    assert "API key absent" in j[("Lean-7b-Examples.ipynb", "eb711ddb")]


def test_parse_collapse_justification_form_hash():
    """`notebook.ipynb#abcd reason` is recognized (alternate spelling)."""
    from check_output_collapse import parse_collapse_justification
    body = ("## Output-collapse justification\n"
            "- Lean-7b-Examples.ipynb#4d4322dd: re-execution skipped\n")
    j = parse_collapse_justification(body)
    assert ("Lean-7b-Examples.ipynb", "4d4322dd") in j


def test_parse_collapse_justification_hyphenated_cell_id():
    """A cell id with a hyphen is captured whole (`cell-melody`).

    The nbformat ids of this repo are `cell-<nom>`; a capture that stopped
    at the hyphen named a cell that does not exist, and the finding stayed
    unaddressed on exactly the notebooks the bypass targets (measured on
    `02-3-MusicGen-Generation.ipynb`, cell `cell-melody`).
    """
    from check_output_collapse import (
        parse_collapse_justification, _unaddressed,
    )
    nb = "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-3-MusicGen-Generation.ipynb"
    body = ("## Output-collapse justification\n"
            f"- {nb} cell cell-melody: allegement declare (sorties de progression)\n")
    j = parse_collapse_justification(body)
    assert (nb, "cell-melody") in j, j
    # The alternate spelling carries the hyphen too.
    body_hash = ("## Output-collapse justification\n"
                 f"- {nb}#cell-text-to-music: faux positif\n")
    j_hash = parse_collapse_justification(body_hash)
    assert (nb, "cell-text-to-music") in j_hash, j_hash
    # And the cell drops out of the unaddressed list.
    bad = [{"notebook": nb, "cells": [
        {"cell": "cell-melody", "kind": "magnitude", "factor": 14.3,
         "base": 27566, "head": 1923},
    ]}]
    assert _unaddressed(bad, j) == []


def test_unaddressed_keeps_only_unjustified_cells():
    """The unaddressed list is the gate signal -- justified cells drop out
    only when the reason is one of the 3 accepted motifs (faux positif,
    allegement, contenu deplace)."""
    from check_output_collapse import (
        parse_collapse_justification, _unaddressed,
    )
    body = ("## Output-collapse justification\n"
            "- Lean-7b-Examples.ipynb cell eb711ddb: faux positif (avertissement transformers)\n")
    j = parse_collapse_justification(body)
    bad = [
        {"notebook": "Lean-7b-Examples.ipynb",
         "cells": [
             {"cell": "eb711ddb", "kind": "signature",
              "factor": 14.9, "base": 1000, "head": 67},
             {"cell": "32aa3fbb", "kind": "magnitude",
              "factor": 49.4, "base": 1000, "head": 20},
         ]},
    ]
    un = _unaddressed(bad, j)
    assert len(un) == 1
    assert un[0]["cell"] == "32aa3fbb"


def test_unaddressed_drops_exempt_entries():
    """Exempt (moved, diagnostic) findings are never unaddressed."""
    from check_output_collapse import _unaddressed
    bad = [
        {"notebook": "Foo.ipynb", "cells": [
            {"cell": "a", "kind": "exempt-moved", "factor": 5,
             "base": 100, "head": 20},
        ]},
    ]
    assert _unaddressed(bad, {}) == []


# ---------------------------------------------------------------------------
# Issue #21424 T2-corrige : 4 controles positifs + soupape 3 motifs.
# ---------------------------------------------------------------------------

def test_calibration_bonsai_under_floor():
    """Bonsai `recipe-cell` (274 chars base) is caught by motif nouveau
    even though it sits under the legacy BASE_FLOOR=500."""
    from check_output_collapse import analyze
    base = ("ComfyUI connecte : http://127.0.0.1:8188\n"
            "GPU : cuda:0\nGeneration terminee en 2.0s\n"
            "Image : bonsai_demo_00001_.png\n")
    head = ("ComfyUI non disponible : COMFYUI_API_URL manquant dans .env\n"
            "Generation skipped (ComfyUI non disponible).\n")
    b = {"cells": [{"cell_type": "code", "id": "recipe-cell",
                    "outputs": [{"output_type": "stream", "text": base}]}]}
    h = {"cells": [{"cell_type": "code", "id": "recipe-cell",
                    "outputs": [{"output_type": "stream", "text": head}]}]}
    r = analyze(b, h)
    assert r["regressed"]
    assert any(f["kind"] == "signature" and f["cell"] == "recipe-cell"
               for f in r["cells"])


def test_calibration_planners0_equal_length():
    """Planners-0 `cell-17` (538->593 chars) is caught despite no
    contraction, because the motif is newly present in head."""
    from check_output_collapse import analyze
    base = "Plateforme: Windows\nPython: 3.13.12\nFast Downward: OK (Docker)\n"
    head = "Plateforme: Windows\nPython: 3.13.7\nFast Downward: Non disponible\n"
    b = {"cells": [{"cell_type": "code", "id": "cell-17",
                    "outputs": [{"output_type": "stream", "text": base}]}]}
    h = {"cells": [{"cell_type": "code", "id": "cell-17",
                    "outputs": [{"output_type": "stream", "text": head}]}]}
    r = analyze(b, h)
    assert r["regressed"]
    assert any(f["kind"] == "signature" and f["cell"] == "cell-17"
               for f in r["cells"])


def test_calibration_kokoro_grows():
    """Kokoro `f82ed24e` (566->15602 chars) is caught despite growing,
    because the motif is newly present in head."""
    from check_output_collapse import analyze
    base = "INFLECT-NANO-V1\nRecuperation du modele...\nGeneration reussie\n"
    head = ("INFLECT-NANO-V1\n" + "x" * 15000 +
            "\nInflect-Nano n'est pas installe - demonstration sautee.\n")
    b = {"cells": [{"cell_type": "code", "id": "f82ed24e",
                    "outputs": [{"output_type": "stream", "text": base}]}]}
    h = {"cells": [{"cell_type": "code", "id": "f82ed24e",
                    "outputs": [{"output_type": "stream", "text": head}]}]}
    r = analyze(b, h)
    assert r["regressed"]
    assert any(f["kind"] == "signature" and f["cell"] == "f82ed24e"
               for f in r["cells"])


def test_calibration_sd35_classic():
    """SD-3.5 `cell-1` (598->346 chars) is caught by motif nouveau
    even though the motif sits after a `WARNING:` prefix."""
    from check_output_collapse import analyze
    base = "Toutes les dependances sont disponibles\nHuggingFace: OK\n"
    head = ("WARNING: diffusers non installe - pip install diffusers\n"
            "Dependances manquantes: ['diffusers']\nHuggingFace: OK\n")
    b = {"cells": [{"cell_type": "code", "id": "cell-1",
                    "outputs": [{"output_type": "stream", "text": base}]}]}
    h = {"cells": [{"cell_type": "code", "id": "cell-1",
                    "outputs": [{"output_type": "stream", "text": head}]}]}
    r = analyze(b, h)
    assert r["regressed"]
    assert any(f["kind"] == "signature" and f["cell"] == "cell-1"
               for f in r["cells"])


def test_soupape_refuses_api_key_absence():
    """A justification naming an absent API key is refused -- the
    Epic #21424 / #21427 (CLAUDE.md C.2) close this door."""
    from check_output_collapse import classify_justification_reason
    for r in ["API key not configured", "cle api absente", "mode degrade",
              "GPU absent", "skipped", "demonstration sautee",
              "non disponible", "non installe", "out of scope"]:
        assert classify_justification_reason(r) == "refused", r


def test_soupape_accepts_three_motifs():
    """Only faux positif, allegement declare, contenu deplace are
    accepted by the body-justification bypass."""
    from check_output_collapse import classify_justification_reason
    for r in ["faux positif (transformers warning)",
              "allègement déclaré (probe de diagnostic)",
              "contenu déplacé vers cellule 6",
              "moved content",
              "allege"]:
        assert classify_justification_reason(r) == "accepted", r


def test_soupape_prose_without_keyword_refused():
    """A justification line that names no accepted motif is refused."""
    from check_output_collapse import classify_justification_reason
    assert classify_justification_reason("") == "empty"
    assert classify_justification_reason("just prose") == "refused"


def test_unaddressed_keeps_refused_justification():
    """A refused reason keeps the cell unaddressed -- the soupape
    restriction from the #21426 CHANGES_REQUESTED review."""
    from check_output_collapse import parse_collapse_justification, _unaddressed
    body = ("## Output-collapse justification\n"
            "- Foo.ipynb cell a: faux positif\n"
            "- Foo.ipynb cell b: API key not configured\n"
            "- Foo.ipynb cell c: allégement déclaré\n")
    j = parse_collapse_justification(body)
    bad = [{"notebook": "Foo.ipynb", "cells": [
        {"cell": "a", "kind": "signature", "factor": 5, "base": 100, "head": 20},
        {"cell": "b", "kind": "signature", "factor": 5, "base": 100, "head": 20},
        {"cell": "c", "kind": "signature", "factor": 5, "base": 100, "head": 20},
    ]}]
    un = _unaddressed(bad, j)
    cells_unaddressed = sorted(u["cell"] for u in un)
    assert cells_unaddressed == ["b"], cells_unaddressed


def test_history_yields_no_findings_on_clean_diff():
    """A diff that adds a notebook yields no finding (added == exempt)."""
    from check_output_collapse import history
    # The 'added-notebook' case: pass an empty list of paths through the
    # helper. We assert only that the iterator returns a list (we don't
    # drive a real git walk in this unit test).
    assert list(history("2026-10-10", "2026-10-19",
                         notebook="does-not-exist.ipynb",
                         limit=1)) == []


# --- #21426 R2 / R3 : exemption line-scoped, marqueurs restants testes ---

# Base de 600 chars : au-dessus du plancher de magnitude (500), assez
# court pour que le ratio base/tete reste sous MAGNITUDE_FACTOR. Ces
# tests mesurent l'EXEMPTION, pas la regle de contraction.
EXEMPT_BASE = "x" * 600

EXEMPT_HEADS = {
    "transformers": ("[transformers] the fast path is not available because"
                     " one of the required library is not installed.\n"
                     "Falling back to torch implementation.\n"
                     "loading weights: 0%|          | 0/320\n"),
    "sdpa fallback": ("Loading checkpoint: sdpa fallback engaged due to flash"
                      " attention absence.\n"
                      "model output: tensor([0.1, 0.2, 0.3])\n"),
    "allow_fallback": ("torch.backends.cuda.allow_fallback = True\n"
                       "model output: tensor([0.1, 0.2, 0.3])\n"),
    "flash-attn": ("flash-attn fallback engaged, torch native attention used\n"
                   "model output: tensor([0.1, 0.2, 0.3])\n"),
    ".env non trouve": ("warning: .env non trouve, utilisation variables"
                        " environnement\n"
                        "verification gpu...\n"
                        "model output: tensor([0.1, 0.2, 0.3])\n"),
}


def test_each_exempt_marker_silences_its_own_line():
    """R2 : les cinq marqueurs de EXEMPT_FP_PATTERNS sont testes un par un.

    Hors ligne exemptee, le contenu est neutre : ce qui tait la cellule,
    c'est l'exemption de la ligne.
    """
    for label, head in EXEMPT_HEADS.items():
        got = analyze(base([("x", EXEMPT_BASE)]), nb([("x", head)]))
        assert got["cells"] == [], (label, got["cells"])


def test_cooccurrence_exempt_line_plus_real_degradation_fires():
    """R3 (controle positif) : la co-occurrence doit rester signalee.

    L'exemption porte sur la LIGNE, pas sur la cellule. Une cellule qui
    melange un avertissement de bibliotheque et une degradation reelle
    (ici ComfyUI non disponible / generation skippee) doit etre signalee
    comme signature.
    """
    head = ("Loading checkpoint: sdpa fallback engaged due to flash"
            " attention absence.\n"
            "ComfyUI non disponible : generation skippee.\n"
            "model output: tensor([0.1, 0.2, 0.3])\n")
    got = analyze(base([("x", EXEMPT_BASE)]), nb([("x", head)]))
    assert len(got["cells"]) == 1, got["cells"]
    assert got["cells"][0]["kind"] == "signature", got["cells"][0]
    assert "non disponible" in got["cells"][0]["motif"], got["cells"][0]


def test_exempt_line_removal_keeps_transformers_line_silent():
    """R3 : la ligne ``[transformers] ... not available`` porte un motif.

    Si l'exemption ne retirait que le MOTIF au lieu de la LIGNE, le
    "not available" de l'avertissement resterait et la cellule serait
    a nouveau signalee -- d'ou le retrait de la ligne entiere.
    """
    head = EXEMPT_HEADS["transformers"]
    assert "not available" in head
    got = analyze(base([("x", EXEMPT_BASE)]), nb([("x", head)]))
    assert got["cells"] == [], got["cells"]


def test_magnitude_keeps_its_own_floor():
    """R1 : le plancher porte sur la BASE (b_chars >= BASE_FLOOR).

    Une cellule dont la base est sous 500 chars n'est jugee par aucune
    des deux regles -- point mort documente (QC @17, 428 -> 0).
    """
    small_base = "x" * (BASE_FLOOR - 1)
    head = "y" * 10
    got = analyze(base([("a", small_base)]), nb([("a", head)]))
    assert got["cells"] == [], got["cells"]
    # ... et la meme cellule, avec une base au-dessus du plancher, est
    # bien jugee : le plancher est la seule difference.
    got2 = analyze(base([("a", "x" * BASE_FLOOR)]), nb([("a", head)]))
    assert [c["kind"] for c in got2["cells"]] == ["magnitude"], got2["cells"]
