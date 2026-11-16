"""Tests de l'organe de qualification du cursus (#24996).

Le principe : l'organe doit **roucir** sur un manifeste fautif. Chaque
controle negatif est donc verifie par un test qui construit un manifeste
faux et exige un ``error`` -- un organe qui ne detecte pas sa propre faute
ne prouve rien quand il dit vert.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
TOOLS_DIR = REPO_ROOT / "scripts" / "notebook_tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import curriculum_qualification as cq  # noqa: E402


def _manifest(notebooks: list[dict]) -> dict:
    return {
        "version": 1,
        "series": [
            {
                "id": "TEST",
                "path": "notebooks",
                "notebooks": notebooks,
            }
        ],
    }


def _entry(path: str, **overrides) -> dict:
    entry = {
        "path": path,
        "difficulte": "D2",
        "recherche": "R1",
        "criteres": {"prerequis": 1, "outillage": 1, "autonomie": 2},
        "justification": "Une justification suffisamment longue pour passer le seuil minimal de l'organe.",
        "mesures": {},
    }
    entry.update(overrides)
    return entry


# ---------------------------------------------------------------------------
# Regle de derivation
# ---------------------------------------------------------------------------


def test_derive_difficulty_uses_prerequis_and_autonomie_only():
    assert cq.derive_difficulty({"prerequis": 1, "outillage": 4, "autonomie": 2}) == "D2"
    assert cq.derive_difficulty({"prerequis": 3, "outillage": 1, "autonomie": 2}) == "D3"
    assert cq.derive_difficulty({"prerequis": 1, "outillage": 1, "autonomie": 4}) == "D4"


def test_outillage_ne_produit_pas_le_niveau():
    """L'outillage est un cout d'acces, il ne monte pas le rang."""
    with_tools = cq.derive_difficulty({"prerequis": 1, "outillage": 3, "autonomie": 2})
    without_tools = cq.derive_difficulty({"prerequis": 1, "outillage": 1, "autonomie": 2})
    assert with_tools == without_tools == "D2"


# ---------------------------------------------------------------------------
# Le manifeste livre : il doit etre vert
# ---------------------------------------------------------------------------


def test_manifeste_livre_est_valide():
    manifest = cq.load_manifest()
    findings = cq.check_manifest(manifest)
    errors = [f for f in findings if f.severity == "error"]
    assert errors == [], "\n".join(f"{f.kind} {f.path}: {f.message}" for f in errors)


# Les onze sources du pilote restent obligatoires. Les compagnons C# sont
# admis individuellement ; leur qualification et la couverture de l'arbre
# restent controlees par check_manifest, sans compteur global fige.
_NLP_PILOT_SOURCES = frozenset({
    'MyIA.AI.Notebooks/NLP/01_TAL_Du_Mot_Aux_Dependances.ipynb',
    'MyIA.AI.Notebooks/NLP/02_NGrammes_Modeles_De_Langue.ipynb',
    'MyIA.AI.Notebooks/NLP/03_CRF_Etiquetage_Sequentiel.ipynb',
    'MyIA.AI.Notebooks/NLP/04_PCFG_CYK_Parsing.ipynb',
    'MyIA.AI.Notebooks/NLP/05-HMM-Viterbi.ipynb',
    'MyIA.AI.Notebooks/NLP/06-Recherche-Information-TFIDF-BM25.ipynb',
    'MyIA.AI.Notebooks/NLP/07-Vecteurs-de-Mots-Coocc-PPMI-SVD.ipynb',
    'MyIA.AI.Notebooks/NLP/08-Word2Vec-CBOW-SkipGram.ipynb',
    'MyIA.AI.Notebooks/NLP/09-FastText-Subword-Vectors.ipynb',
    'MyIA.AI.Notebooks/NLP/10-Classement-Texte-NaiveBayes-FromScratch.ipynb',
    'MyIA.AI.Notebooks/NLP/11-Classement-Texte-RegressionLogistique-FromScratch.ipynb',
})
_NLP_PILOT_COMPANIONS = frozenset(
    path.removesuffix(".ipynb") + "-CSharp.ipynb" for path in _NLP_PILOT_SOURCES
)


def _assert_nlp_pilot_inventory(notebooks):
    paths = [entry["path"] for entry in notebooks]
    assert len(paths) == len(set(paths)), "entree NLP dupliquee"
    assert _NLP_PILOT_SOURCES <= set(paths), "source du pilote NLP absente"
    assert set(paths) <= _NLP_PILOT_SOURCES | _NLP_PILOT_COMPANIONS, (
        "carnet hors du pilote NLP ou compagnon sans source reconnue"
    )


def test_manifeste_livre_couvre_la_serie_pilote():
    manifest = cq.load_manifest()
    series = {s["id"]: s for s in manifest["series"]}
    assert "NLP" in series
    notebooks = series["NLP"]["notebooks"]
    # La couverture carnet par carnet est portee par check_manifest (deux sens) :
    # un compte fige casserait a chaque jumeau ajoute a la serie. Le controle
    # ci-dessous verifie donc l'inventaire (sources du pilote + compagnons
    # admis individuellement) sans figer un total.
    _assert_nlp_pilot_inventory(notebooks)
    for entry in notebooks:
        assert entry["difficulte"] in cq.DIFFICULTY_LEVELS
        assert entry["recherche"] in cq.RESEARCH_LEVELS
        assert len(entry["justification"].strip()) >= cq.MIN_JUSTIFICATION_CHARS


@pytest.mark.parametrize("companions", [0, 1, 3, 11])
def test_pilote_accepte_des_compagnons_sans_figer_le_total(companions):
    sources = [_entry(path) for path in sorted(_NLP_PILOT_SOURCES)]
    twins = [_entry(path) for path in sorted(_NLP_PILOT_COMPANIONS)[:companions]]
    _assert_nlp_pilot_inventory(sources + twins)


def test_pilote_refuse_source_omise_meme_si_le_total_reste_onze():
    sources = [_entry(path) for path in sorted(_NLP_PILOT_SOURCES)[1:]]
    sources.append(_entry(sorted(_NLP_PILOT_COMPANIONS)[0]))
    with pytest.raises(AssertionError, match="source du pilote NLP absente"):
        _assert_nlp_pilot_inventory(sources)


@pytest.mark.parametrize("extra_path", [
    "MyIA.AI.Notebooks/NLP/99-Sans-Source-CSharp.ipynb",
    sorted(_NLP_PILOT_SOURCES)[0],
])
def test_pilote_refuse_orphelin_et_doublon(extra_path):
    sources = [_entry(path) for path in sorted(_NLP_PILOT_SOURCES)]
    with pytest.raises(AssertionError):
        _assert_nlp_pilot_inventory(sources + [_entry(extra_path)])


def test_champ_difficulte_expose_pour_le_generateur():
    manifest = cq.load_manifest()
    path = "MyIA.AI.Notebooks/NLP/03_CRF_Etiquetage_Sequentiel.ipynb"
    found = cq.qualification_for(manifest, path)
    assert found is not None
    assert found["difficulte"] == "D3"
    assert found["recherche"] == "R2"
    assert cq.qualification_for(manifest, "MyIA.AI.Notebooks/NLP/99_absent.ipynb") is None


# ---------------------------------------------------------------------------
# Controles negatifs : l'organe doit rougir
# ---------------------------------------------------------------------------


def _fake_repo(tmp_path: Path, notebooks: list[str]) -> Path:
    root = tmp_path / "repo"
    (root / "notebooks").mkdir(parents=True)
    for name in notebooks:
        (root / "notebooks" / name).write_text(
            json.dumps({"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}),
            encoding="utf-8",
        )
    return root


def test_carnet_absent_du_manifeste_est_une_erreur(tmp_path):
    root = _fake_repo(tmp_path, ["a.ipynb", "b.ipynb"])
    manifest = _manifest([_entry("notebooks/a.ipynb")])
    findings = cq.check_manifest(manifest, root=root)
    couverture = [f for f in findings if f.kind == "couverture"]
    assert any(f.path == "notebooks/b.ipynb" for f in couverture)
    assert any(f.severity == "error" for f in couverture)


def test_entree_sans_carnet_est_une_erreur(tmp_path):
    root = _fake_repo(tmp_path, ["a.ipynb"])
    manifest = _manifest([_entry("notebooks/a.ipynb"), _entry("notebooks/disparu.ipynb")])
    findings = cq.check_manifest(manifest, root=root)
    assert any(f.kind == "couverture" and f.path == "notebooks/disparu.ipynb" for f in findings)


def test_valeur_hors_enumeration_est_une_erreur(tmp_path):
    root = _fake_repo(tmp_path, ["a.ipynb"])
    manifest = _manifest([_entry("notebooks/a.ipynb", difficulte="D9", recherche="R7")])
    findings = cq.check_manifest(manifest, root=root)
    messages = " ".join(f.message for f in findings)
    assert "difficulte invalide" in messages
    assert "recherche invalide" in messages


def test_justification_absente_est_une_erreur(tmp_path):
    root = _fake_repo(tmp_path, ["a.ipynb"])
    manifest = _manifest([_entry("notebooks/a.ipynb", justification="court")])
    findings = cq.check_manifest(manifest, root=root)
    assert any("justification" in f.message for f in findings)


def test_niveau_incompatible_avec_la_regle_est_une_erreur(tmp_path):
    root = _fake_repo(tmp_path, ["a.ipynb"])
    manifest = _manifest(
        [
            _entry(
                "notebooks/a.ipynb",
                difficulte="D4",
                criteres={"prerequis": 1, "outillage": 1, "autonomie": 2},
            )
        ]
    )
    findings = cq.check_manifest(manifest, root=root)
    assert any(f.kind == "niveau" for f in findings)


def test_derive_des_mesures_est_une_erreur(tmp_path):
    """Un carnet modifie depuis sa qualification doit etre signale."""
    root = _fake_repo(tmp_path, ["a.ipynb"])
    manifest = _manifest(
        [
            _entry(
                "notebooks/a.ipynb",
                mesures={
                    "exercices": 3,
                    "cellules_code": 14,
                    "cellules_md": 33,
                    "prose_chars": 20662,
                    "densite": 1475,
                },
            )
        ]
    )
    findings = cq.check_manifest(manifest, root=root)
    derive = [f for f in findings if f.kind == "derive"]
    assert derive, "une mesure obsolete doit etre signalee"
    assert derive[0].severity == "error"


def test_densite_sous_plancher_est_un_avertissement_pas_une_erreur(tmp_path):
    """#13410 : une densite basse est un defaut d'enrichissement, pas un classement faux.

    Controle negatif **synthetique** : un carnet present sur l'arbre, dont la
    densite (prose par cellule code) est sous le plancher de 1200, doit etre
    signale en ``warning`` -- jamais en ``error``. Le temoin est synthetique et
    ne depend pas de l'etat du manifeste livre : un carnet reele enrichi (le 09
    via #24930) sort du plancher et cesserait d'etre un temoin fiable.
    """
    # Carnet sous le plancher : 1 cellule code, prose minuscule -> densite < 1200.
    root = tmp_path / "repo"
    (root / "notebooks").mkdir(parents=True)
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["Introduction au module."]},
            {"cell_type": "code", "source": ["x = 1"]},
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    (root / "notebooks" / "densite-basse.ipynb").write_text(
        json.dumps(nb), encoding="utf-8"
    )
    manifest = _manifest([_entry("notebooks/densite-basse.ipynb")])
    findings = cq.check_manifest(manifest, root=root)
    densite = [f for f in findings if f.kind == "densite"]
    assert densite, "le carnet sous le plancher doit etre signale"
    assert all(f.severity == "warning" for f in densite)
    assert any("densite-basse" in f.path for f in densite)


def test_organe_indisponible_est_signale_pas_avale(tmp_path, monkeypatch):
    """Un organe qui perd un signal doit le dire (CLAUDE.md section F)."""
    monkeypatch.setitem(sys.modules, "pedagogy_density", None)
    root = _fake_repo(tmp_path, ["a.ipynb"])
    manifest = _manifest([_entry("notebooks/a.ipynb")])
    findings = cq.check_manifest(manifest, root=root)
    degrade = [f for f in findings if f.kind == "degrade"]
    assert degrade, "la perte de pedagogogy_density doit etre signalee"
    assert all(f.severity == "warning" for f in degrade)
    assert any("pedagogy_density" in f.message for f in degrade)


@pytest.mark.parametrize(
    "champ,valeur",
    [
        ("difficulte", "D2"),
        ("recherche", "R1"),
        ("criteres", {"prerequis": 1, "outillage": 1, "autonomie": 2}),
    ],
)
def test_refresh_ne_touche_pas_les_valeurs_declarees(tmp_path, champ, valeur):
    """`--refresh` re-mesure ; il ne regenere jamais un jugement."""
    root = _fake_repo(tmp_path, ["a.ipynb"])
    entry = _entry("notebooks/a.ipynb")
    manifest = _manifest([entry])
    cq.refresh_manifest(manifest, root=root)
    assert entry[champ] == valeur
    assert "mesures" in entry
