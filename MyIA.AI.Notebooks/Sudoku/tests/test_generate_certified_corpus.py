"""
Tests pour Sudoku/scripts/generate_certified_corpus.py.

Couvre les criteres d'acceptation de l'issue #26426 (volet 1 de l'EPIC
Sudoku #26242) :

  1. Determinisme : meme graine, memes grilles (facile et moyen -- les deux
     strategies rapides).
  2. Cas degeneres tranches par le verdict de denombrement certifie :
     grille pleine = unique, grille sans indice = sous-determinee, grille
     contradictoire = sans solution.
  3. Certification : toute grille emise porte ``unique`` (1 solution,
     arret exhausted), le palier facile est entierement resoluble par
     propagation seule, et les paliers se separant par la difficulte
     MESUREE (facile < moyen).
  4. Bandes calibrees : le tirage-rejet n'accepte que dans la bande du
     palier (controles directes sur ``tier_accepts``).

Le palier ``difficile`` (creusage adversarial, ~1 s par tentative) n'est
pas genere ici : son determinisme et sa certification sont couverts par la
generation du corpus commite, rejouable par le script. Les tests restent
bornes en temps.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

# Le module vit dans scripts/ de la serie ; les tests dans tests/.
_SERIES = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_SERIES / "scripts"))
sys.path.insert(0, str(_SERIES))

import generate_certified_corpus as gen  # noqa: E402


def test_determinisme_facile():
    """Meme graine -> memes grilles, sortie stable en chaine 0-pour-vide."""
    first = gen.generate_tier("facile", per_tier=2, seed=7, medium_clues=28)
    second = gen.generate_tier("facile", per_tier=2, seed=7, medium_clues=28)
    assert [r["puzzle"] for r in first] == [r["puzzle"] for r in second]
    assert all(len(r["puzzle"]) == 81 for r in first)
    assert all(ch in "0123456789" for r in first for ch in r["puzzle"])


def test_determinisme_moyen():
    first = gen.generate_tier("moyen", per_tier=2, seed=7, medium_clues=28)
    second = gen.generate_tier("moyen", per_tier=2, seed=7, medium_clues=28)
    assert [r["puzzle"] for r in first] == [r["puzzle"] for r in second]


def test_grille_pleine_unique():
    """Cas degenere : une grille complete a exactement une solution, epuisee."""
    rng_full = np.random.RandomState(1)
    full = [int(v) for v in gen.generate_complete_grid(rng_full).flatten()]
    status, found = gen.uniqueness_verdict(gen.puzzle_to_string(full))
    assert (status, found) == ("exhausted", 1)


def test_grille_vide_sous_determinee():
    """Cas degenere : sans aucun indice, le denombrement sature au plafond."""
    status, found = gen.uniqueness_verdict("0" * 81)
    assert found >= 2
    assert status == "limit_reached"


def test_grille_contradictoire_sans_solution():
    """Cas degenere : deux 5 dans une meme ligne -> aucune solution, epuisee."""
    cells = ["0"] * 81
    cells[0], cells[8] = "5", "5"  # ligne 0, colonnes 0 et 8
    status, found = gen.uniqueness_verdict("".join(cells))
    assert (status, found) == ("exhausted", 0)


def test_palier_facile_propagation_seule_et_certifie():
    records = gen.generate_tier("facile", per_tier=3, seed=11, medium_clues=28)
    assert len(records) == 3
    for r in records:
        assert r["unique"], "facile doit etre unique (exhausted, 1 solution)"
        assert r["propagation_only"], "facile doit se resoudre par propagation seule"
        assert r["decisions"] == 0


def test_separation_facile_moyen_par_la_mesure():
    """La difficulte mesuree separe les paliers : facile strictement sous moyen."""
    facile = gen.generate_tier("facile", per_tier=3, seed=11, medium_clues=28)
    moyen = gen.generate_tier("moyen", per_tier=3, seed=11, medium_clues=28)
    max_facile = max(r["decisions"] for r in facile)
    min_moyen = min(r["decisions"] for r in moyen)
    assert max_facile == 0
    assert min_moyen >= 1


def test_bandes_calibrees_refusent_hors_bande():
    """Le tirage-rejet n'accepte que dans la bande mesuree de son palier."""
    ok_facile = {"unique": True, "decisions": 0}
    ok_moyen = {"unique": True, "decisions": 5}
    ok_difficile = {"unique": True, "decisions": 25}
    assert gen.tier_accepts("facile", ok_facile)
    assert gen.tier_accepts("moyen", ok_moyen)
    assert gen.tier_accepts("difficile", ok_difficile)
    # Hors bande : refuse, meme certifie unique.
    assert not gen.tier_accepts("facile", {"unique": True, "decisions": 4})
    assert not gen.tier_accepts("moyen", {"unique": True, "decisions": 0})
    assert not gen.tier_accepts("moyen", {"unique": True, "decisions": 40})
    assert not gen.tier_accepts("difficile", {"unique": True, "decisions": 3})
    # Non unique : refuse partout (le verdict DLX tranche, pas la bande).
    for tier in gen.TIERS:
        assert not gen.tier_accepts(tier, {"unique": False, "decisions": 0})


def test_corpus_commite_certifie():
    """Le corpus livre porte des grilles uniques, par fichier de palier."""
    puzzles_dir = _SERIES / "Puzzles"
    emitted = 0
    for tier in gen.TIERS:
        path = puzzles_dir / f"Sudoku_gen_{tier}.txt"
        if not path.exists():
            pytest.skip(f"corpus non encore genere : {path.name}")
        lines = [l for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]
        assert lines, f"{path.name} vide"
        for line in lines:
            status, found = gen.uniqueness_verdict(line)
            assert (status, found) == ("exhausted", 1), (
                f"{path.name} : grille non certifiee unique ({status}, {found})"
            )
            emitted += 1
    assert emitted >= 30, "corpus equilibre attendu : au moins 10 grilles par palier"


def test_audit_irreductibilite_documente_le_cardinal(capsys):
    """Le cardinal d'irreductibilite est documente par grille (critere livrable 2).

    ``minimal_clue_set`` etant glouton (a l'ordre de suppression pres), les
    invariants testes sont structurels : conserves + redondants = indices,
    et au moins 17 indices conserves (minimum connu pour l'unicite Sudoku).
    """
    puzzles_dir = _SERIES / "Puzzles"
    if not (puzzles_dir / "Sudoku_gen_facile.txt").exists():
        pytest.skip("corpus non encore genere")
    rows = gen.audit_irredundancy(puzzles_dir, per_tier=2)
    out = capsys.readouterr().out
    assert len(rows) == 2 * len(gen.TIERS)
    for row in rows:
        assert row["kept"] + row["retired"] == row["clues"]
        assert row["kept"] >= 17
        assert row["retired"] >= 0
    assert "irreductibilite : mediane" in out
    assert "redondants" in out
