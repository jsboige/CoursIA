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


def test_touches_main_garde_le_commit_le_plus_recent_quand_un_fichier_est_touche_deux_fois(tmp_path: Path):
    """Un fichier touche deux fois : c'est le commit LE PLUS RECENT qui parle.

    `git log` parcourt du plus recent au plus ancien ; ecraser a chaque
    occurrence gardait donc l'**ancien** commit (defaut mesure le 25/11, revue
    du coordinateur sur #28454). Ici, seul le commit le plus recent cite
    l'issue 7 : c'est lui qui doit commander la suspicion.
    """
    depot = tmp_path / "depot"
    depot.mkdir()

    def git(*args: str, date: str | None = None) -> None:
        env = None
        if date:
            env = {**os.environ, "GIT_AUTHOR_DATE": date,
                   "GIT_COMMITTER_DATE": date}
        subprocess.run(["git", "-C", str(depot), *args], check=True,
                       capture_output=True, env=env)

    git("init", "-q")
    git("config", "user.email", "test@example.invalid")
    git("config", "user.name", "test")
    (depot / "scripts").mkdir()
    chemin = depot / "scripts" / "a.py"
    chemin.write_text("x = 1\n", encoding="utf-8")
    git("add", "-A")
    git("commit", "-qm", "Refactor(depot): touche scripts/a.py (#70)",
        date="2026-11-20T10:00:00+00:00")
    chemin.write_text("x = 2\n", encoding="utf-8")
    git("add", "-A")
    git("commit", "-qm", "Fix(notebook,#7): corrige scripts/a.py",
        date="2026-11-21T10:00:00+00:00")
    git("branch", "-M", "main")
    git("update-ref", "refs/remotes/origin/main", "HEAD")

    touches = chemins.touches_main(str(depot))
    date, statut, sujet = touches["scripts/a.py"]
    assert "#7" in sujet, f"le commit le plus recent doit commander : {sujet!r}"
    assert "#70" not in sujet
    assert date.startswith("2026-11-21")

    # Et la suspicion suit : le commit le plus recent cite l'issue 7.
    out = chemins.suspects(["scripts/a.py"], touches,
                           cree_le="2026-11-01T00:00:00Z", numero=7)
    assert [s["chemin"] for s in out] == ["scripts/a.py"]


# --- la regle : un mouvement posterieur au silence de l'issue ----------------

def _touches(path: str = "scripts/a.py", date: str = "2026-11-20T10:00:00+00:00",
             sujet: str = "Fix(notebook,#7): ajoute scripts/a.py"):
    return {path: (date, "M", sujet)}


def test_une_reference_entiere_est_requise_pour_soupconner():
    """`#70` ne cite pas l'issue 7 : la reference doit etre ENTIERE.

    Le test par sous-chaine faisait soupconner l'issue 7 sur un commit qui ne
    citait que `#70` (defaut mesure le 25/11, revue du coordinateur sur
    #28454).
    """
    out = chemins.suspects(["scripts/a.py"],
                           _touches(sujet="Fix(notebook,#70): corrige scripts/a.py"),
                           cree_le="2026-11-01T00:00:00Z", numero=7)
    assert out == [], "un commit qui cite #70 ne cite pas l'issue 7"

    # Témoin négatif symétrique : `#7` ne cite pas l'issue 70.
    out70 = chemins.suspects(["scripts/a.py"],
                             _touches(sujet="Fix(notebook,#7): corrige scripts/a.py"),
                             cree_le="2026-11-01T00:00:00Z", numero=70)
    assert out70 == [], "un commit qui cite #7 ne cite pas l'issue 70"

    # Témoin positif : la reference exacte, elle, soupconne.
    out7 = chemins.suspects(["scripts/a.py"],
                            _touches(sujet="Fix(notebook,#7): corrige scripts/a.py"),
                            cree_le="2026-11-01T00:00:00Z", numero=7)
    assert [s["chemin"] for s in out7] == ["scripts/a.py"]


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
