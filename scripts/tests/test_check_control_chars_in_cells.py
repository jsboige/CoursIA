"""Tests du garde caracteres de controle dans les sources de cellules (#18048).

Les deux temoins du body de l'issue sont reproduits en fixture decodee :

- POSITIF (tete f19ca6ff91 de la PR #17919, MGS-01-Introduction cellule 10) :
  un outil d'ecriture a interprete l'echappement Python ``\\a`` de
  ``\\approx`` en BEL ; la source decodee porte ``$\\sigma <BEL>pprox 12$``.
- NEGATIF (main post-fix, auditer-la-conformite-visuelle cellule 18) : la
  source porte le texte LITERAL ``\\b`` (frontiere de regex, backslash + b
  en clair) -- un backslash suivi d'une lettre ne doit JAMAIS rougir, seul
  le caractere de controle decode compte.

Le garde ne rougit que sur le DELTA : une source presente a l'identique
dans la base (stock herite, deplacement inclus) est exemee.
"""

from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

from check_control_chars_in_cells import (  # noqa: E402
    cell_sources,
    compare_cells,
    scan_raw_control_bytes,
)
from fast_lane_registry import TRANCHE16  # noqa: E402


def nb(cells: list[tuple[str, str]]) -> dict:
    """Notebook minimal : liste de (cell_type, source en une chaine)."""
    return {"cells": [
        {"cell_type": t, "source": s.splitlines(keepends=True)}
        for t, s in cells
    ]}


# Témoin positif : BEL x3, intention \approx (regex Python mangee).
WITNESS_BEL = (
    "1. **L'ordre des moyennes n'est pas significatif** : avec 5 runs et "
    "$\\sigma \x07pprox 12$, l'erreur standard $\\sigma/\\sqrt{5} \x07pprox 5$"
    " reste du meme ordre\x07."
)
# Témoin négatif : backslash + b LITERAL (frontiere de regex), pas de controle.
WITNESS_LITERAL_B = (
    "Les deux mondes differents. Le `_HEX` porte\n"
    "un `\\b` apres les six chiffres : sans lui, un identifiant plus long"
)


def test_positive_witness_bel_approx():
    head = cell_sources(nb([("markdown", WITNESS_BEL)]))
    base = cell_sources(nb([("markdown", "1. texte sans controle.")]))
    findings = compare_cells(head, base)
    assert len(findings) == 1
    assert findings[0]["chars"] == [0x07]
    assert findings[0]["cell_index"] == 0
    assert findings[0]["cell_type"] == "markdown"
    assert "pprox" in findings[0]["excerpt"]


def test_negative_witness_literal_backslash_b():
    head = cell_sources(nb([("markdown", WITNESS_LITERAL_B)]))
    base = cell_sources(nb([("markdown", "texte avant correction")]))
    assert compare_cells(head, base) == []


def test_stock_herite_identique_exempte():
    # Une cellule portant un controle, PRESENTE A L'IDENTIQUE dans la base,
    # est du stock : le garde ne rougit pas sur la dette heritee.
    head = cell_sources(nb([("markdown", WITNESS_BEL)]))
    base = cell_sources(nb([("markdown", WITNESS_BEL)]))
    assert compare_cells(head, base) == []


def test_cellule_deplacee_identique_exempte():
    head = cell_sources(nb([
        ("markdown", "nouvelle intro"),
        ("markdown", WITNESS_LITERAL_B.replace("\\b", "\x08")),
    ]))
    base = cell_sources(nb([
        ("markdown", WITNESS_LITERAL_B.replace("\\b", "\x08")),
        ("markdown", "nouvelle intro"),
    ]))
    assert compare_cells(head, base) == []


def test_cellule_modifiee_avec_controle_constat():
    head = cell_sources(nb([("markdown", "un `\x08` apres les six chiffres")]))
    base = cell_sources(nb([("markdown", "un frontiere apres les six chiffres")]))
    findings = compare_cells(head, base)
    assert len(findings) == 1
    assert findings[0]["chars"] == [0x08]


def test_notebook_ajoute_base_vide_constat():
    head = cell_sources(nb([
        ("markdown", "propre"),
        ("code", "x = '\x0by'\n"),
    ]))
    findings = compare_cells(head, [])
    assert len(findings) == 1
    assert findings[0]["cell_index"] == 1
    assert findings[0]["chars"] == [0x0B]


def test_vt_et_ff_detectes_avec_echappements_probables():
    head = cell_sources(nb([
        ("code", "a\x0bb"),
        ("code", "c\x0cd"),
    ]))
    base = cell_sources(nb([("code", "a"), ("code", "c")]))
    findings = compare_cells(head, base)
    assert [f["chars"] for f in findings] == [[0x0B], [0x0C]]


def test_scan_raw_control_bytes():
    assert scan_raw_control_bytes(b'{"a": "x\x07y"}') == [0x07]
    assert scan_raw_control_bytes(b'{"a": "\\u0007"}') == []
    assert scan_raw_control_bytes(b'{"a": "propre"}') == []


def test_tranche16_enregistree_avec_contrat():
    assert len(TRANCHE16) == 1
    guard = TRANCHE16[0]
    assert guard.name == "control-chars-in-cells-guard"
    assert guard.blocking is True
    assert guard.needs_base is True
    assert guard.warn_rc == (2,)
    assert "--diff" in guard.argv and "{base_ref}...HEAD" in guard.argv
    assert "scripts/ci/check_control_chars_in_cells.py" in guard.paths
    assert "scripts/tests/test_check_control_chars_in_cells.py" in guard.paths


def test_tranche16_cablee_dans_le_moteur():
    # Un garde enregistre mais pas somme par le moteur ne tourne jamais :
    # parite textuelle import + somme (le defaut que ce test ferme est
    # exactement l'oubli de cablage, silencieux par construction).
    src = (CI_DIR / "fast_lane.py").read_text(encoding="utf-8")
    assert "TRANCHE16, Guard," in src
    assert "+ TRANCHE15 + TRANCHE16" in src
