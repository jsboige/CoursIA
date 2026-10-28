#!/usr/bin/env python3
"""Tests de la porte du budget de creation dans le tapis (#23174).

La porte est branchee sur `scripts/pick_idle_grain.py` : quand le compteur
de carnets neufs demarres par la flotte depasse le budget, le tapis cesse de
servir un grain de creation — avec la cause nommee `BUDGET CRÉATION`.

Ce que ces tests verrouillent, par ordre d'importance :

  1. **un grain de REPARATION n'est jamais ecarte** — c'est la borne de
     securite du regime ;
  2. **la porte est INERTE sans etat** : une variable d'environnement non
     posee ne doit pas vider le tapis ;
  3. **la porte est fail-OPEN** : un etat mal forme, un catalogue inconnu
     n'ecartent personne ;
  4. **la porte ne s'active QUE sur un depassement** : sous le budget, le
     tapis sert tout le monde.

Le regime RALENTIT la creation, il ne l'ARRETE pas : le plancher de 1 du
budget et le veto de reparation portent cette promesse, et ces tests la
verrouillent.
"""

import importlib.util
import pathlib
import sys

import pytest

SCRIPTS = pathlib.Path(__file__).resolve().parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

_spec = importlib.util.spec_from_file_location(
    "pick_idle_grain_local", SCRIPTS / "pick_idle_grain.py")
pig = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pig)

import creation_budget as cb  # noqa: E402

CATALOG_PATHS = [
    "MyIA.AI.Notebooks/NLP/01-Introduction-Python.ipynb",
    "MyIA.AI.Notebooks/NLP/02-Ngrammes-Python.ipynb",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/28-mobius-inversion.ipynb",
]


def issue(number=1, title="", body="", labels=None, parent=None):
    return {"number": number, "title": title, "body": body,
            "labels": labels or [], "parent": parent}


@pytest.fixture
def catalog(monkeypatch):
    cat = cb.NotebookCatalog(CATALOG_PATHS)
    monkeypatch.setattr(cb.NotebookCatalog, "from_repo",
                        classmethod(lambda cls, *a, **k: cat))
    return cat


def test_sans_etat_la_porte_est_inerte(monkeypatch, catalog):
    """La variable d'environnement n'est pas posee par defaut : aucune lane
    n'ecarte rien tant que le coordinateur n'a pas pose l'etat."""
    monkeypatch.delenv(cb.ENV_STATE, raising=False)
    pool = [issue(number=1, title="NLP — carnet 07 : classification")]
    assert pig.creation_budget_gate(pool) == {}


def test_un_depassement_ecarte_le_grain_de_creation(monkeypatch, catalog, tmp_path):
    etat = tmp_path / "etat.json"
    etat.write_text('{"carnets_neufs_demarres": 90, "budget": 50}',
                     encoding="utf-8")
    monkeypatch.setenv(cb.ENV_STATE, str(etat))
    pool = [issue(number=1, title="NLP — carnet 07 : classification")]
    gate = pig.creation_budget_gate(pool)
    assert 1 in gate
    assert "BUDGET CRÉATION" in gate[1]
    assert "ralentie, pas arretee" in gate[1]


def test_un_grain_de_reparation_nest_jamais_ecarte(monkeypatch, catalog, tmp_path):
    """Le regime ne doit pas perdre le travail de consolidation : un grain
    de reparation passe toujours."""
    etat = tmp_path / "etat.json"
    etat.write_text('{"carnets_neufs_demarres": 90, "budget": 50}',
                     encoding="utf-8")
    monkeypatch.setenv(cb.ENV_STATE, str(etat))
    pool = [issue(number=2, title="Fix(lean,#18408): aligner la prose de ANALYSE-04")]
    assert pig.creation_budget_gate(pool) == {}


def test_sous_le_budget_la_porte_ne_declenche_pas(monkeypatch, catalog, tmp_path):
    etat = tmp_path / "etat.json"
    etat.write_text('{"carnets_neufs_demarres": 10, "budget": 50}',
                     encoding="utf-8")
    monkeypatch.setenv(cb.ENV_STATE, str(etat))
    pool = [issue(number=1, title="NLP — carnet 07 : classification")]
    assert pig.creation_budget_gate(pool) == {}


def test_un_etat_mal_forme_n_ecarte_personne(monkeypatch, catalog, tmp_path):
    etat = tmp_path / "etat.json"
    etat.write_text('{"carnets_neufs_demarres": "beaucoup"}', encoding="utf-8")
    monkeypatch.setenv(cb.ENV_STATE, str(etat))
    pool = [issue(number=1, title="NLP — carnet 07 : classification")]
    assert pig.creation_budget_gate(pool) == {}


def test_un_catalogue_inconnu_n_ecarte_personne(monkeypatch, tmp_path):
    """Un `git` muet ne doit pas vider le tapis : le catalogue inconnu
    rend le classement indeterminate partout."""
    monkeypatch.setattr(cb.NotebookCatalog, "from_repo",
                        classmethod(lambda cls, *a, **k: cb.NotebookCatalog([])))
    etat = tmp_path / "etat.json"
    etat.write_text('{"carnets_neufs_demarres": 90, "budget": 50}',
                     encoding="utf-8")
    monkeypatch.setenv(cb.ENV_STATE, str(etat))
    pool = [issue(number=1, title="NLP — carnet 07 : classification")]
    assert pig.creation_budget_gate(pool) == {}
