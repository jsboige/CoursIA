"""Temoins de la VOIE D'ECRITURE du balayage de suspicion (#28454).

Le balayage (`scripts/coordination/tapis_livraison.py`) pose un marqueur dans
le fil et un label candidat sur l'issue. La voie `--apply` ecrit -- c'est la
seule voie qui mute, et elle est donc la seule qui doit appliquer le VETO
HUMAIN : si une personne a retire le label candidat, le balayage ne peut pas
le reposer (il poserait sous le login partage, et sa pose deviendrait le
dernier evenement humain, effacant le veto du classificateur).

Ces temoins regardent les **ecritures** (marqueur + label), pas la
detection : la detection a ses propres temoins
(`test_candidate_delivered_chemins.py`).

Aucun test ne touche le reseau : `gh` est un faux.
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_livraison as tl

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

REPO = "jsboige/CoursIA"

ISSUE = {"number": 42, "title": "Grain 42", "body": "Un grain ordinaire",
         "labels": [], "createdAt": "2026-11-01T00:00:00Z"}

SUSPECT = {"chemin": "docs/reference/exemple.md", "statut": "modified",
           "date": "2026-11-20T10:00:00Z", "sujet": "Fix: cite #42"}


def _balayage(monkeypatch, fil_=None, evenements_=None) -> list[str]:
    """Prepare un balayage a faux et rend la liste des ECRITURES vues."""
    ecritures: list[str] = []

    monkeypatch.setattr(tl.chemins, "touches_main",
                        lambda depot: {"docs/reference/exemple.md": {}})
    monkeypatch.setattr(tl, "pool", lambda repo, limit: [ISSUE])
    monkeypatch.setattr(tl, "prs_ouverts", lambda repo, limit=300: set())
    monkeypatch.setattr(tl, "suspecter",
                        lambda issue, touches, commentaires: [SUSPECT])
    monkeypatch.setattr(tl, "fil", lambda repo, number: fil_)
    monkeypatch.setattr(tl, "evenements", lambda repo, number: evenements_)
    monkeypatch.setattr(tl, "poster",
                        lambda repo, number, corps: ecritures.append(f"marqueur:{number}"))
    monkeypatch.setattr(tl, "poser_label",
                        lambda repo, number: ecritures.append(f"label:{number}"))
    return ecritures


def test_le_balayage_pose_le_marqueur_et_le_label_quand_nothing_ne_l_interdit(monkeypatch):
    """TEMOIN DE CONTROLE POSITIF : sans veto ni lecture incomplete, le
    balayage ecrit bien les deux choses.

    Sans ce temoin, les temoins « zero ecriture » ne prouveraient rien : ils
    passeraient aussi sur un balayage qui n'ecrit jamais.
    """
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=[])
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == ["marqueur:42", "label:42"], ecritures


def test_une_lecture_incomplete_du_fil_empêche_toute_ecriture(monkeypatch, capsys):
    """Le fil illisible -> ZERO ecriture (ni marqueur, ni label)."""
    ecritures = _balayage(monkeypatch, fil_=None, evenements_=[])
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "LECTURE INCOMPLETE" in capsys.readouterr().out


def test_une_lecture_incomplete_des_evenements_empêche_toute_ecriture(monkeypatch, capsys):
    """La timeline illisible -> ZERO ecriture."""
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=None)
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "LECTURE INCOMPLETE" in capsys.readouterr().out


def test_un_retrait_humain_du_label_empêche_toute_ecriture(monkeypatch, capsys):
    """Une personne a retire le label -> ZERO ecriture (le veto prime)."""
    evenements = [{"event": "unlabeled", "actor": "jsboige",
                   "created_at": "2026-11-22T10:00:00Z"}]
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=evenements)
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == [], f"ecritures inattendues : {ecritures}"
    assert "VETO" in capsys.readouterr().out.upper()


def test_un_evenement_de_pose_humain_ne_bloque_pas_le_balayage(monkeypatch):
    """CONTROLE NEGATIF du veto : une pose humaine (et non un retrait) ne
    veto pas -- seule la pose sous le login partage est un risque, et c'est
    le RETRAIT qui fait veto."""
    evenements = [{"event": "labeled", "actor": "jsboige",
                   "created_at": "2026-11-22T10:00:00Z"}]
    ecritures = _balayage(monkeypatch, fil_=[], evenements_=evenements)
    rc = tl.main(["--apply", "--repo", REPO])
    assert rc == 0
    assert ecritures == ["marqueur:42", "label:42"], ecritures
