"""Tests du schema de motifs/reactions de Game of Life (tranche 1+2 de #15635).

Le contrat teste ici est celui du critere 2 de #15635 : « aucune metadonnee
declaree n'est acceptee sur confiance ». Chaque test de rejet falsifie UNE
metadonnee du fixture et exige que la validation la refuse -- c'est la seule
facon de montrer que le validateur mesure au lieu de recopier.
"""

from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

LEAN_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT = LEAN_DIR.parent.parent
FIXTURE = LEAN_DIR / "life_components_fixture.json"

sys.path.insert(0, str(LEAN_DIR))

from life_components import (  # noqa: E402
    FULL_DIHEDRAL,
    SCHEMA_VERSION,
    SchemaError,
    admissible_symmetries,
    canonical_form,
    load_catalog,
    same_object,
    validate_catalog,
)


def fixture_doc() -> dict:
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def motif_entry(doc: dict, motif_id: str) -> dict:
    for entry in doc["motifs"]:
        if entry["id"] == motif_id:
            return entry
    raise AssertionError(f"motif {motif_id!r} absent du fixture")


def reaction_entry(doc: dict, reaction_id: str) -> dict:
    for entry in doc["reactions"]:
        if entry["id"] == reaction_id:
            return entry
    raise AssertionError(f"reaction {reaction_id!r} absente du fixture")


def validate_doc(doc: dict, tmp_path: Path) -> list[dict]:
    path = tmp_path / "catalogue.json"
    path.write_text(json.dumps(doc, ensure_ascii=False), encoding="utf-8")
    return validate_catalog(load_catalog(path))


# --------------------------------------------------------------------------
# Le fixture lui-meme
# --------------------------------------------------------------------------


def test_fixture_valide_sans_erreur(tmp_path: Path) -> None:
    report = validate_doc(fixture_doc(), tmp_path)
    assert len(report) == len(fixture_doc()["motifs"]) + len(fixture_doc()["reactions"])


def test_rapport_separe_motifs_et_reactions(tmp_path: Path) -> None:
    report = validate_doc(fixture_doc(), tmp_path)
    kinds = {row["kind"] for row in report}
    assert kinds == {"motif", "reaction"}


def test_fixture_couvre_les_quatre_categories_de_la_tranche(tmp_path: Path) -> None:
    """§1 de #15635 : still lifes, oscillateurs, spaceships et reactions."""
    report = validate_doc(fixture_doc(), tmp_path)
    cats = {row["categorie"] for row in report if row["kind"] == "motif"}
    assert {"still_life", "oscillator", "spaceship"} <= cats
    assert any(row["kind"] == "reaction" for row in report)


# --------------------------------------------------------------------------
# Motifs : chaque metadonnee declaree est comparee a la mesure
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("champ", "valeur", "attendu"),
    [
        ("period", 3, "periode"),
        ("translation", [0, 0], "translation"),
        ("population", 6, "population"),
        ("box", [4, 4], "boite"),
        ("envelope", [5, 5], "enveloppe"),
        ("kind", "oscillator", "nature"),
    ],
)
def test_metadonnee_fausse_refusee(
    champ: str, valeur: object, attendu: str, tmp_path: Path
) -> None:
    doc = fixture_doc()
    motif_entry(doc, "glider")[champ] = valeur
    with pytest.raises(SchemaError, match=attendu):
        validate_doc(doc, tmp_path)


def test_cellules_non_canoniques_refusees(tmp_path: Path) -> None:
    doc = fixture_doc()
    entry = motif_entry(doc, "block")
    entry["cells"] = [[x + 3, y + 2] for x, y in entry["cells"]]
    with pytest.raises(SchemaError, match="non canoniques"):
        validate_doc(doc, tmp_path)


def test_regle_inconnue_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    motif_entry(doc, "block")["rule"] = "B36/S23"
    with pytest.raises(SchemaError, match="regle"):
        validate_doc(doc, tmp_path)


def test_symetrie_inadmissible_refusee(tmp_path: Path) -> None:
    """Une symetrie qui change la translation echangerait deux objets distincts."""
    doc = fixture_doc()
    motif_entry(doc, "glider")["symmetries"] = ["T", "R90"]
    with pytest.raises(SchemaError, match="inadmissible"):
        validate_doc(doc, tmp_path)


def test_symetrie_translation_obligatoire(tmp_path: Path) -> None:
    doc = fixture_doc()
    motif_entry(doc, "block")["symmetries"] = ["R90"]
    with pytest.raises(SchemaError, match="obligatoire"):
        validate_doc(doc, tmp_path)


def test_phases_fausses_refusees(tmp_path: Path) -> None:
    doc = fixture_doc()
    entry = motif_entry(doc, "blinker")
    entry["phases"] = {k: v for k, v in entry["phases"].items() if k != "1"}
    with pytest.raises(SchemaError, match="phases"):
        validate_doc(doc, tmp_path)


def test_vitesse_fausse_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    motif_entry(doc, "glider")["speed"] = 99.0
    with pytest.raises(SchemaError, match="vitesse"):
        validate_doc(doc, tmp_path)


def test_motif_duplique_refuse(tmp_path: Path) -> None:
    doc = fixture_doc()
    doc["motifs"].append(copy.deepcopy(motif_entry(doc, "block")))
    with pytest.raises(SchemaError, match="duplique"):
        validate_doc(doc, tmp_path)


def test_champ_manquant_refuse(tmp_path: Path) -> None:
    doc = fixture_doc()
    del motif_entry(doc, "block")["population"]
    with pytest.raises(SchemaError, match="manquant"):
        validate_doc(doc, tmp_path)


def test_schema_version_inconnue_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    doc["schema_version"] = "9.9.9"
    with pytest.raises(SchemaError, match="schema_version"):
        validate_doc(doc, tmp_path)


def test_provenance_incomplete_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    motif_entry(doc, "block")["provenance"] = {"source": "moi", "license": "?", "retrieved": ""}
    with pytest.raises(SchemaError, match="provenance"):
        validate_doc(doc, tmp_path)


# --------------------------------------------------------------------------
# Reactions : produit, clearance et nature mesures, pas declares
# --------------------------------------------------------------------------


def test_reaction_motif_inconnu_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "glider_pair_annihilation")["reactants"][0]["motif_id"] = "licorne"
    with pytest.raises(SchemaError, match="inconnu"):
        validate_doc(doc, tmp_path)


def test_reaction_produit_declare_faux_refuse(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "glider_pair_annihilation")["product_cells"] = [[0, 0], [1, 0], [0, 1]]
    with pytest.raises(SchemaError, match="produit mesure"):
        validate_doc(doc, tmp_path)


def test_reaction_stabilisation_trop_precoce_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "glider_pair_two_blocks")["stabilization_time"] = 2
    with pytest.raises(SchemaError, match="produit mesure"):
        validate_doc(doc, tmp_path)


def test_reaction_clearance_traversee_refusee(tmp_path: Path) -> None:
    """Controle negatif : une clearance posee sur la zone occupee doit rougir."""
    doc = fixture_doc()
    entry = reaction_entry(doc, "glider_pair_annihilation")
    x0, y0, w, h = entry["occupied_region"]
    entry["clearance"] = [[x0, y0, w, h]]
    with pytest.raises(SchemaError, match="clearance"):
        validate_doc(doc, tmp_path)


def test_reaction_consommable_avec_survivant_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "block_catalyses_glider")["nature"] = "consumable"
    with pytest.raises(SchemaError, match="consumable"):
        validate_doc(doc, tmp_path)


def test_reaction_catalytique_sans_survivant_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "glider_pair_annihilation")["nature"] = "catalytic"
    with pytest.raises(SchemaError, match="aucun reactif"):
        validate_doc(doc, tmp_path)


def test_reaction_phase_hors_bornes_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "glider_pair_two_blocks")["reactants"][0]["phase"] = 7
    with pytest.raises(SchemaError, match="phase"):
        validate_doc(doc, tmp_path)


def test_produits_et_cellules_brutes_exclusifs(tmp_path: Path) -> None:
    doc = fixture_doc()
    entry = reaction_entry(doc, "glider_pair_two_blocks")
    entry["product_cells"] = [[0, 0], [1, 0], [0, 1], [1, 1]]
    with pytest.raises(SchemaError, match="exclusifs"):
        validate_doc(doc, tmp_path)


def test_reaction_nature_inconnue_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "glider_pair_annihilation")["nature"] = "magique"
    with pytest.raises(SchemaError, match="nature"):
        validate_doc(doc, tmp_path)


def test_region_occupee_fausse_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    reaction_entry(doc, "glider_pair_annihilation")["occupied_region"] = [0, 0, 1, 1]
    with pytest.raises(SchemaError, match="region occupee"):
        validate_doc(doc, tmp_path)


def test_port_hors_region_refuse(tmp_path: Path) -> None:
    doc = fixture_doc()
    entry = reaction_entry(doc, "glider_pair_two_blocks")
    entry["ports"] = [{"name": "in0", "offset": [99, 99], "direction": [0, 1], "phase": 0}]
    with pytest.raises(SchemaError, match="hors de la region"):
        validate_doc(doc, tmp_path)


def test_port_direction_nulle_refusee(tmp_path: Path) -> None:
    doc = fixture_doc()
    entry = reaction_entry(doc, "glider_pair_two_blocks")
    entry["ports"] = [
        {"name": "in0", "offset": entry["reactants"][0]["offset"], "direction": [0, 0], "phase": 0}
    ]
    with pytest.raises(SchemaError, match="direction nulle"):
        validate_doc(doc, tmp_path)


# --------------------------------------------------------------------------
# Canonicalisation : normaliser sans fusionner des objets non equivalents
# --------------------------------------------------------------------------


def test_canonical_form_merge_les_symetries_dun_still_life() -> None:
    block = [(0, 0), (1, 0), (0, 1), (1, 1)]
    rotated = [(y, -x) for (x, y) in block]
    assert canonical_form(block, FULL_DIHEDRAL) == canonical_form(rotated, FULL_DIHEDRAL)


def test_symetries_admissibles_suivent_la_translation() -> None:
    assert admissible_symmetries((0, 0)) == FULL_DIHEDRAL
    assert admissible_symmetries((1, -1)) == ("T", "D2")
    assert admissible_symmetries((-1, -1)) == ("T", "D1")
    assert admissible_symmetries((-2, 0)) == ("T", "My")


def test_same_object_ne_fusionne_pas_deux_gliders_de_directions_opposees(tmp_path: Path) -> None:
    """Le coeur du critere 2 : deux formes en miroir ne sont pas le meme objet."""
    catalog = load_catalog(FIXTURE)
    gauche = catalog.motif("glider")
    droite = catalog.motif("glider_mirror")
    assert gauche.translation_step != droite.translation_step
    assert not same_object(gauche.cells, droite.cells)
    assert same_object(gauche.cells, gauche.cells)


def test_symetrie_inconnue_refusee() -> None:
    with pytest.raises(SchemaError, match="inconnue"):
        canonical_form([(0, 0)], ("Z9",))


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def test_cli_valide_le_fixture() -> None:
    proc = subprocess.run(
        [sys.executable, str(LEAN_DIR / "life_components.py"), "--fixture", str(FIXTURE)],
        capture_output=True, text=True, timeout=600,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "OK" in proc.stdout


def test_cli_rougit_sur_fixture_falsifie(tmp_path: Path) -> None:
    doc = fixture_doc()
    motif_entry(doc, "glider")["period"] = 3
    bad = tmp_path / "faux.json"
    bad.write_text(json.dumps(doc, ensure_ascii=False), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(LEAN_DIR / "life_components.py"), "--fixture", str(bad)],
        capture_output=True, text=True, timeout=600,
    )
    assert proc.returncode == 1
    assert "ECHEC" in proc.stdout


def test_schema_version_exportee() -> None:
    assert SCHEMA_VERSION == fixture_doc()["schema_version"]
