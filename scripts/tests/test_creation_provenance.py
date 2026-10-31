#!/usr/bin/env python3
"""Tests de la garde de provenance des carnets neufs (#23174).

Le contrat de la garde, en une phrase : **un carnet neuf doit avoir attendu
son tour** — l'issue servie a ete servie par un tirage du tapis
(`draw_id`), ou elle a plus de 48 h quand la PR s'est ouverte.

Ce que ces tests verrouillent :

  1. la detection du **carnet neuf** — un `added` est un carnet neuf, un
     deménagement (`added` + `removed` de meme nom) n'en est pas un, un
     jumeau `_en` non plus ;
  2. les **deux conformites** (l'age, le tirage) et la sanction quand
     aucune n'est remplie ;
  3. le **fail-OPEN du journal** : un journal absent rend le critere du
     tirage NON EVALUABLE, et le motif le dit ;
  4. la **sortie advisory** : la garde signale, elle ne bloque pas.

Les cas sont des MESURES : ils reprennent des PRs et des issues REELS du
2026-10-21 (semaine de la simulation), pour qu'une regression se relise
contre la realite.
"""

import importlib.util
import pathlib
import sys

import pytest

SCRIPTS_CI = pathlib.Path(__file__).resolve().parent.parent / "ci"
if str(SCRIPTS_CI) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_CI))

_spec = importlib.util.spec_from_file_location(
    "check_creation_provenance", SCRIPTS_CI / "check_creation_provenance.py")
cp = importlib.util.module_from_spec(_spec)
sys.modules["check_creation_provenance"] = cp
_spec.loader.exec_module(cp)


def fichier(nom, statut):
    return {"filename": nom, "status": statut}


# --- la detection du carnet neuf --------------------------------------------

def test_un_carnet_ajoute_est_un_carnet_neuf():
    neufs, demenages = cp.new_notebooks([
        fichier("MyIA.AI.Notebooks/NLP/07-NaiveBayes.ipynb", "added")])
    assert neufs == ["MyIA.AI.Notebooks/NLP/07-NaiveBayes.ipynb"]
    assert demenages == []


def test_un_jumeau_en_nest_pas_un_carnet_neuf():
    """#23038 — une PR `Add` livre la paire FR + EN : le carnet neuf c'est
    le FR, le jumeau `_en` en est la traduction."""
    neufs, _ = cp.new_notebooks([
        fichier("MyIA.AI.Notebooks/GenAI/Texte/07-Embedding.ipynb", "added"),
        fichier("MyIA.AI.Notebooks/GenAI/Texte/07-Embedding_en.ipynb", "added")])
    assert neufs == ["MyIA.AI.Notebooks/GenAI/Texte/07-Embedding.ipynb"]


def test_un_demenagement_nest_pas_un_carnet_neuf():
    """#21733 — neuf carnets deplaces de `Applications/` vers
    `Part3-Cas-pratiques/`. GitHub les rapporte `added` + `removed` (la
    similarite est sous son seuil) : un carnet deplace n'est pas un carnet
    neuf."""
    noms = ["App-1-NQueens", "App-10-Portfolio", "App-11-Picross",
            "App-2-GraphColoring", "App-3-NurseScheduling",
            "App-5-Timetabling", "App-6-Minesweeper", "App-9-EdgeDetection",
            "App-9b-EdgeDetection-CSharp"]
    files = [fichier(f"MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/{n}.ipynb",
                     "added") for n in noms]
    files += [fichier(f"MyIA.AI.Notebooks/Search/Applications/{n}.ipynb",
                      "removed") for n in noms]
    neufs, demenages = cp.new_notebooks(files)
    assert neufs == []
    assert len(demenages) == 9


def test_un_fichier_non_carnet_ne_compte_pas():
    neufs, _ = cp.new_notebooks([
        fichier("scripts/lean/knot_anymoves_search.py", "added")])
    assert neufs == []


# --- le verdict --------------------------------------------------------------

def test_une_issue_vieille_est_conforme():
    """#21733 — issue #19253 creee 378 h avant la PR : elle a attendu."""
    verdict, motif = cp.decide(19253, 378.2, {"disponible": False,
                                              "raison": "journal vide"})
    assert verdict == "CONFORME (age)"
    assert "attendu son tour" in motif


def test_une_issue_fraiche_sans_tirage_est_signalee():
    """#21738 — issue #21736 creee 0,3 h avant la PR, aucun tirage : le
    carnet neuf n'a pas attendu son tour."""
    verdict, motif = cp.decide(21736, 0.3, {"disponible": False,
                                             "raison": "journal vide"})
    assert verdict == "SIGNALE"
    assert "n'a pas attendu son tour" in motif


def test_un_tirage_nomme_valide_meme_issue_fraiche():
    """Le tirage du tapis vaut attente : c'est lui qui a proposé le grain."""
    verdict, motif = cp.decide(21736, 0.3, {
        "disponible": True, "vues": 3,
        "retenue": {"draw_id": "ab12cd34", "lane": "myia-po-2025:CoursIA-2",
                    "ts": "2026-10-21T02:00:00Z", "mode": "belt"}})
    assert verdict == "CONFORME (tirage)"
    assert "ab12cd34" in motif


def test_un_journal_absent_dit_quil_ne_sait_pas():
    """L'absence de journal n'est pas une absence de tirage : le motif le
    dit, pour que le verdict ne soit pas lu comme une mesure."""
    verdict, motif = cp.decide(21736, 0.3, {"disponible": False,
                                             "raison": "journal vide"})
    assert verdict == "SIGNALE"
    assert "non evaluable" in motif


def test_un_age_non_mesure_ne_conforme_pas():
    verdict, motif = cp.decide(1234, None, {"disponible": True, "vues": 0,
                                             "retenue": None})
    assert verdict == "SIGNALE"
    assert "age non mesure" in motif


# --- le perimetre ------------------------------------------------------------

def test_une_pr_externe_est_hors_perimetre():
    assert cp.is_fleet({"author": {"login": "jsboige"},
                         "headRepositoryOwner": {"login": "jsboige"}}) is True
    assert cp.is_fleet({"author": {"login": "myia-po-2025"},
                         "headRepositoryOwner": {"login": "MyIntelligenceAgency"}}) is True
    assert cp.is_fleet({"author": {"login": "etudiant-epita"},
                         "headRepositoryOwner": {"login": "etudiant-epita"}}) is False


def test_la_reference_de_l_issue_servie_est_lue():
    assert cp._SERVED_RE.search("Closes #23174").group(1) == "23174"
    assert cp._SERVED_RE.search("See #19253 (livraison partielle)").group(1) == "19253"
    assert cp._SERVED_RE.search("Part of #18390").group(1) == "18390"
    assert cp._SERVED_RE.search("rien ici") is None


def test_le_seuil_est_48_heures():
    """Le seuil vient de l'issue : 48 h. Il n'est pas une constante posee
    a l'oeil — le test le verrouille pour qu'un changement passe par une
    PR explicite."""
    assert cp.AGE_MIN_H == 48.0


@pytest.mark.parametrize("age,attendu", [
    (0.1, "SIGNALE"),
    (47.9, "SIGNALE"),
    (48.0, "CONFORME (age)"),
    (378.2, "CONFORME (age)"),
])
def test_la_frontiere_du_seuil_est_exacte(age, attendu):
    verdict, _ = cp.decide(1, age, {"disponible": True, "vues": 0,
                                    "retenue": None})
    assert verdict == attendu


# --- la mesure indisponible n'est pas un constat -----------------------------

def test_un_gh_en_echec_leve_une_mesure_indisponible(monkeypatch):
    """Mesure du 2026-10-30 : le quota d'installation GitHub etait epuise
    dans le job, `gh api` est sorti non-zero, et l'organe a rendu un rouge
    sur #22977 et #22576 -- deux PRs sans rapport avec la panne."""
    class Faux:
        returncode = 1
        stderr = ("API rate limit exceeded for installation.")
        stdout = ""

    monkeypatch.setattr(cp.subprocess, "run", lambda *a, **k: Faux())
    with pytest.raises(cp.MesureIndisponible):
        cp.pr_files(22977)


def test_une_mesure_indisponible_sort_0_et_ne_produit_aucun_constat(
        monkeypatch, capsys):
    def panne(_pr):
        raise cp.MesureIndisponible("gh api a echoue : quota epuise")

    monkeypatch.setattr(cp, "pr_meta", panne)
    monkeypatch.setattr(cp, "pr_files", panne)
    rc = cp.main(["--pr", "22977"])
    sortie = capsys.readouterr().out
    assert rc == 0
    assert "NON MESURE (UNKNOWN)" in sortie
    assert "constat" not in sortie


def test_une_mesure_indisponible_nest_pas_un_constat_meme_en_strict(
        monkeypatch, capsys):
    """--strict rougit sur un CONSTAT. Une panne de mesure n'en est pas un :
    la faire rougir ferait d'un incident d'infrastructure un defaut de PR."""
    monkeypatch.setattr(cp, "pr_meta",
                        lambda _pr: (_ for _ in ()).throw(
                            cp.MesureIndisponible("reseau absent")))
    monkeypatch.setattr(cp, "pr_files",
                        lambda _pr: (_ for _ in ()).throw(
                            cp.MesureIndisponible("reseau absent")))
    assert cp.main(["--pr", "22977", "--strict"]) == 0
    assert "NON MESURE (UNKNOWN)" in capsys.readouterr().out
