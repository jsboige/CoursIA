#!/usr/bin/env python3
"""Le signal « chemin cible sur main » : ce qu'il prouve, et ce qu'il ne prouve pas.

Le dispatch `c0035b` du coordinateur (24/11) : « le chemin cible est sur
main » ne doit que **soupconner** une livraison, jamais la conclure ; le
grain passe a l'urne avec un label candidat.

Ce fichier verifie les trois briques :

- `nommes` -- les chemins qu'une issue nomme ;
- `touches_main` / `suspects` -- ce que `main` en dit, et la regle ;
- `suspicion_dans_le_fil` -- la DONNEE que le poseur de label (CI, sans
  historique) et le tapis lisent.

Et le point qui compte : la suspicion **route** le grain vers l'urne, elle
ne clot rien -- une attestation de livraison et une suspicion n'ont pas le
meme sens.
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import candidate_delivered_chemins as chemins  # noqa: E402
from candidate_delivered import classify  # noqa: E402


# --- les chemins nommes ------------------------------------------------------

def test_une_issue_qui_nomme_un_carnet_le_nomme():
    assert chemins.nommes(
        "Ajouter le carnet MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-20-Demo.ipynb"
    ) == ["MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-20-Demo.ipynb"]


def test_un_repertoire_sans_extension_n_est_pas_un_chemin():
    assert chemins.nommes("voir scripts/coordination pour le detail") == []


def test_les_doublons_tombent_et_l_ordre_du_texte_est_tenu():
    texte = ("`scripts/a.py` puis `scripts/b.py` puis encore `scripts/a.py`")
    assert chemins.nommes(texte) == ["scripts/a.py", "scripts/b.py"]


def test_le_nombre_de_chemins_est_borne():
    texte = " ".join(f"scripts/f{i}.py" for i in range(50))
    assert len(chemins.nommes(texte)) == chemins.MAX_CHEMINS


def test_un_texte_vide_ne_leve_ni_erreur():
    assert chemins.nommes("") == []


# --- ce que main en dit ------------------------------------------------------

def test_touches_main_echoue_ou_paie_sur_un_depot_absent():
    # Un depot qui n'existe pas : aucun chemin, aucune exception.
    assert chemins.touches_main("/d/nexiste-pas-du-tout") == {}


def test_touches_main_lit_ce_que_main_a_touche(tmp_path: Path):
    """Un vrai depot, un vrai commit : le chemin, sa date et son sujet."""
    depot = tmp_path / "depot"
    depot.mkdir()
    def git(*args: str) -> None:
        subprocess.run(["git", "-C", str(depot), *args], check=True,
                       capture_output=True)
    git("init", "-q")
    git("config", "user.email", "test@example.invalid")
    git("config", "user.name", "test")
    (depot / "scripts").mkdir()
    (depot / "scripts" / "a.py").write_text("x = 1\n", encoding="utf-8")
    git("add", "-A")
    git("commit", "-qm", "Ajoute scripts/a.py")
    git("branch", "-M", "main")
    git("update-ref", "refs/remotes/origin/main", "HEAD")

    touches = chemins.touches_main(str(depot))
    assert "scripts/a.py" in touches
    date, statut, sujet = touches["scripts/a.py"]
    assert statut == "A"
    assert date[:4].isdigit()
    assert "scripts/a.py" in sujet


# --- la regle : un mouvement posterieur au silence de l'issue ----------------

def _touches(path: str = "scripts/a.py", date: str = "2026-11-20T10:00:00+00:00",
             sujet: str = "Fix(notebook,#7): ajoute scripts/a.py"):
    return {path: (date, "M", sujet)}


def test_un_chemin_touche_apres_la_creation_est_un_soupcon():
    out = chemins.suspects(["scripts/a.py"], _touches(),
                           cree_le="2026-11-01T00:00:00Z", numero=7)
    assert [s["chemin"] for s in out] == ["scripts/a.py"]


def test_un_commit_qui_ne_cite_pas_l_issue_n_est_pas_un_soupcon():
    """Un commit de masse touche beaucoup de chemins : il ne prouve rien."""
    out = chemins.suspects(["scripts/a.py"],
                           _touches(sujet="Refactor(depot): touche beaucoup de fichiers"),
                           cree_le="2026-11-01T00:00:00Z", numero=7)
    assert out == []


def test_un_chemin_touche_avant_la_creation_ne_l_est_pas():
    out = chemins.suspects(["scripts/a.py"], _touches(),
                           cree_le="2026-11-25T00:00:00Z")
    assert out == []


def test_un_commentaire_posterieur_au_mouvement_annule_le_soupcon():
    """Quelqu'un parle apres le mouvement du depot : le travail n'est pas muet."""
    out = chemins.suspects(["scripts/a.py"], _touches(),
                           cree_le="2026-11-01T00:00:00Z",
                           dernier_commentaire="2026-11-21T00:00:00Z")
    assert out == []


def test_sans_date_de_creation_le_signal_ne_devine_pas():
    assert chemins.suspects(["scripts/a.py"], _touches(), cree_le=None) == []


def test_un_chemin_absent_de_main_n_est_pas_un_soupcon():
    assert chemins.suspects(["scripts/inexistant.py"], _touches(),
                            cree_le="2026-11-01T00:00:00Z") == []


# --- la donnee : le marqueur dans le fil --------------------------------------

def test_le_marqueur_de_suspicion_est_reconnu():
    corps = "[INFO] suspicion-livraison -- `scripts/a.py` (M, 2026-11-20)"
    assert chemins.suspicion_dans_le_fil([corps]) is not None


def test_une_attestation_de_livraison_n_est_pas_une_suspicion():
    corps = "[INFO] candidate-delivered -- les criteres sont couverts"
    assert chemins.suspicion_dans_le_fil([corps]) is None


def test_un_marqueur_qui_ressemble_mais_ne_porte_pas_le_forme():
    corps = "on a parle de suspicion-livraison sans le poser"
    assert chemins.suspicion_dans_le_fil([corps]) is None


def test_un_fil_vide_ne_porte_pas_de_suspicion():
    assert chemins.suspicion_dans_le_fil([]) is None


# --- le poseur de label : la suspicion route, elle ne clot pas ---------------

def _issue(comments=None, title="Ajouter le carnet X"):
    return {
        "title": title,
        "number": 4242,
        "labels": [],
        "created_at": "2026-11-01T00:00:00Z",
        "body": "",
        "comments": comments or [],
    }


def test_le_fil_qui_porte_la_suspicion_donne_le_verdict_candidate():
    issue = _issue(comments=[{
        "created_at": "2026-11-21T00:00:00Z",
        "body": "[INFO] suspicion-livraison -- `scripts/a.py` (M, 2026-11-20)",
    }])
    verdict, why = classify(issue, [])
    assert verdict == "candidate"
    assert "SUSPICION" in why


def test_sans_suspicion_et_sans_preuve_le_verdict_reste_no_delivery():
    verdict, _ = classify(_issue(), [])
    assert verdict == "no_delivery"


def test_une_pr_ouverte_prime_sur_la_suspicion():
    """Le travail en cours garde le grain servi : la suspicion attend."""
    issue = _issue(comments=[{
        "created_at": "2026-11-21T00:00:00Z",
        "body": "[INFO] suspicion-livraison -- `scripts/a.py`",
    }])
    refs = [{"pr_number": 7, "is_pr": True, "state": "open",
             "merged_at": None, "title": "voir #4242", "body": "See #4242"}]
    verdict, _ = classify(issue, refs)
    assert verdict == "in_flight"


def test_un_verdict_humain_prime_sur_la_suspicion():
    """La retraction d'un humain l'emporte : le marqueur ne la renverse pas."""
    issue = _issue(comments=[{
        "created_at": "2026-11-21T00:00:00Z",
        "body": "[INFO] suspicion-livraison -- `scripts/a.py`",
    }])
    events = [{"event": "unlabeled", "actor": "un-humain",
               "created_at": "2026-11-22T00:00:00Z"}]
    verdict, _ = classify(issue, [], events)
    assert verdict == "retracted"
