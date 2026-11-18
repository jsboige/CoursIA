#!/usr/bin/env python3
"""Tests du pilote de mesure des baselines sur le corpus tranche B.

Le pilote **rejoue** l'organe canonique `baseline_branch_detection.py`. Ces
tests gardent deux proprietes :

* le filtre de round-trip ne garde que les paires reussies, et il est
  **comptable** (conservees / lues) ;
* un niveau refuse par l'organe (support par etiquette sous le plancher) est
  rendu **verbatim** dans l'agregat, jamais masque par un `None` silencieux.
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import measure_baselines_tranche_b as mesure  # noqa: E402


def write_corpus(path: Path, rows: list[dict]) -> Path:
    path.write_text(
        "\n".join(json.dumps(row, ensure_ascii=False) for row in rows) + "\n",
        encoding="utf-8",
    )
    return path


def ligne(scenario: str, famille: str, noeud: str, roundtrip: bool = True) -> dict:
    return {
        "text": f"texte {scenario} {noeud}",
        "family": famille,
        "node_key": noeud,
        "node_pk": noeud[-1],
        "scenario_path": scenario,
        "roundtrip": roundtrip,
    }


def write_taxonomie(tmp_path: Path, rows: list[dict]) -> Path:
    """Taxonomie synthetique au schema sophismes (colonnes attendues par l'organe)."""
    path = tmp_path / "taxo.csv"
    fields = ["PK", "Famille", "nom_vulgarisé", "desc_fr", "example_fr"]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({f: row.get(f, "") for f in fields})
    return path


# --- Le filtre -----------------------------------------------------------------------


def test_filtre_ne_garde_que_les_round_trip_reussis(tmp_path: Path):
    source = write_corpus(tmp_path / "train_fr.jsonl", [
        ligne("s1", "A", "n1"),
        ligne("s2", "A", "n2", roundtrip=False),
        ligne("s3", "B", "n3"),
    ])
    destination = tmp_path / "filtre.jsonl"
    conservees, lues = mesure.filtrer_corpus(source, destination)
    assert (lues, conservees) == (3, 2)
    gardes = [json.loads(ligne) for ligne in destination.read_text(encoding="utf-8").splitlines()]
    assert [r["node_key"] for r in gardes] == ["n1", "n3"]


def test_filtre_est_deterministe(tmp_path: Path):
    """Deux passes donnent le meme fichier : l'agregat reste falsifiable."""
    source = write_corpus(tmp_path / "train_fr.jsonl", [
        ligne("s1", "A", "n1"), ligne("s2", "A", "n2", roundtrip=False),
    ])
    premier = tmp_path / "a.jsonl"
    second = tmp_path / "b.jsonl"
    mesure.filtrer_corpus(source, premier)
    mesure.filtrer_corpus(source, second)
    assert premier.read_bytes() == second.read_bytes()


# --- Le refus d'un niveau non mesurable ----------------------------------------------


def test_niveau_refuse_est_rendu_verbatim(tmp_path: Path):
    """Un noeud par paire : sous le plancher de 2, l'organe refuse par son nom."""
    source = write_corpus(tmp_path / "val_fr.jsonl", [
        ligne("s1", "A", "n1"), ligne("s2", "A", "n2"), ligne("s3", "B", "n3"),
    ])
    resultat = mesure.mesurer(source, "node", folds=2, draws=1, seed=42)
    assert resultat["refuse"] is True
    assert "non mesurable" in resultat["message"]
    assert resultat["message"] == resultat["message"].strip()


def test_niveau_mesurable_passe(tmp_path: Path):
    """Deux paires par noeud : le niveau passe, et l'agregat porte les baselines."""
    source = write_corpus(tmp_path / "train_fr.jsonl", [
        ligne("s1", "A", "n1"), ligne("s2", "A", "n1"),
        ligne("s3", "B", "n2"), ligne("s4", "B", "n2"),
    ])
    taxo = write_taxonomie(tmp_path, [
        {"PK": "1", "Famille": "A", "nom_vulgarisé": "Titre A", "desc_fr": "alpha beta"},
        {"PK": "2", "Famille": "B", "nom_vulgarisé": "Titre B", "desc_fr": "gamma delta"},
    ])
    resultat = mesure.mesurer(source, "node", folds=2, draws=1, seed=42, taxonomies=[taxo])
    assert resultat["refuse"] is False
    resume = mesure.resumer(resultat)
    assert resume["node_level"]["measurable"] is True
    assert set(resume["baselines"]) == {
        "majority_grouped", "random_grouped", "rules_full",
        "lexical_centroid_grouped", "lexical_centroid_naive",
    }


# --- L'assainissement des chemins ------------------------------------------------------


def test_chemin_publie_ne_garde_pas_le_chemin_de_poste():
    """Un chemin de poste ne doit jamais atteindre l'agregat commite."""
    # Un gisement partage reste tel quel : il est lisible par tous.
    assert mesure.chemin_publie("G:/Mon Drive/IA/x.csv") == "G:/Mon Drive/IA/x.csv"
    # Un chemin deja relatif est inchange.
    assert mesure.chemin_publie("a/b.csv") == "a/b.csv"
    # Un chemin absolu du depot devient relatif au depot.
    dans_le_depot = mesure.RACINE / "scripts" / "fallacy_detection" / "x.csv"
    assert mesure.chemin_publie(dans_le_depot) == "scripts/fallacy_detection/x.csv"


def test_chemin_publie_nomme_logiquement_un_derive_hors_depot():
    """Le corpus filtre vit sous le repertoire personnel : il ne doit pas etre nomme."""
    derive = Path.home() / "AppData" / "Local" / "Temp" / "fallacy-tranche-b-xyz" \
        / "corpus" / "train_fr_roundtrip.jsonl"
    publie = mesure.chemin_publie(derive)
    assert publie == "corpus-filtre/train_fr_roundtrip.jsonl"
    assert str(Path.home()) not in publie


def test_assainir_agregat_retire_les_chemins_de_poste():
    """Un chemin absolu du depot devient relatif ; le gisement partage reste tel quel."""
    dans_le_depot = str(mesure.RACINE / "MyIA.AI.Notebooks" / "x.csv")
    agregat = {
        "variantes": [{
            "source": {"path": dans_le_depot, "sha256": "abc"},
            "niveaux": {"branch": {"rapport": {
                "corpus": {"path": dans_le_depot, "sha256": "abc"},
                "lexicon": {"taxonomies": [dans_le_depot, "G:/Mon Drive/IA/t.csv"]},
            }}},
        }],
    }
    assaini = mesure.assainir_agregat(agregat)
    rapport = assaini["variantes"][0]["niveaux"]["branch"]["rapport"]
    assert rapport["corpus"]["path"] == "MyIA.AI.Notebooks/x.csv"
    assert rapport["lexicon"]["taxonomies"] == [
        "MyIA.AI.Notebooks/x.csv", "G:/Mon Drive/IA/t.csv"]
    assert str(mesure.RACINE) not in json.dumps(assaini)


# --- Le rapport ----------------------------------------------------------------------


def test_rapport_une_ligne_par_variante_et_niveau():
    agregat = {
        "instrument": "scripts/fallacy_detection/baseline_branch_detection.py",
        "graine": 42, "plis": 5, "tirages_aleatoires": 200,
        "variantes": [{
            "variante": "val_complet",
            "niveaux": {
                "branch": {"level": "branch", "refuse": False, "rapport": {
                    "structure": {"rows": 10, "labels": 2, "support_min": 4,
                                  "support_max": 6, "groups": 4, "group_max_reuse": 3},
                    "node_level": {"measurable": False, "labels": 10, "support_max": 1, "floor": 2},
                    "folds_identical": 0,
                    "baselines": {
                        "majority_grouped": {"macro_f1_mean": 0.1},
                        "random_grouped": {"macro_f1_mean": 0.2},
                        "rules_full": {"macro_f1": 0.05},
                        "lexical_centroid_grouped": {"macro_f1_mean": 0.3},
                        "lexical_centroid_naive": {"macro_f1_mean": 0.4},
                    },
                    "leakage": {"grouped_mean": 0.3, "naive_mean": 0.4, "gap": 0.1},
                }},
                "node": {"level": "node", "refuse": True, "message": "Niveau 'node' non mesurable"},
            },
        }],
    }
    rapport = mesure.rendre_rapport(agregat)
    lignes = [l for l in rapport.splitlines() if l.startswith("| val_complet")]
    assert len(lignes) == 2
    assert "0.3" in lignes[0] and "0.1" in lignes[0]
    assert "non mesurable" in lignes[1]
