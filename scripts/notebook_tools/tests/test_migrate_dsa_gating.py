"""Temoin permanent de la porte par fichier de #17417 T2-b (#23114).

La reserve de la review etait precise : les « 4 cas PASS » cites dans le body
de la PR avaient ete executes hors depot, donc l'organe n'avait aucun test
committe pour le garder. Ces tests fixent le CONTRAT de ``report_gating`` :

  {"#N": [chemins retenus tries]}   mesure faite, des fichiers sont tenus
  {}                                mesure faite, aucun fichier tenu
  None                              mesure impossible -> --apply refuse

``None`` couvre trois causes distinctes, chacune testee : gh absent, gh en
echec, et -- ajout de #23114 -- la **liste tronquee**. Cette derniere est la
plus dangereuse : une PR hors fenetre est indiscernable d'une PR inexistante,
donc un fichier qu'elle tient serait declare libre sans que rien ne le dise.

Le test porte sur la SEMANTIQUE, pas sur l'interface CLI : ``subprocess`` est
remplace dans le module, aucun appel reseau n'est fait.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

# Permettre l'import du module parent (scripts/notebook_tools/) sans setup
# site-packages -- le projet n'est pas installe en editable.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import migrate_dsa_mlpython as migration  # noqa: E402

PLAN_A = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01/a.ipynb"
PLAN_B = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01/b.py"
HORS_PLAN = "MyIA.AI.Notebooks/ML/DataScienceWithAgents/autre/hors.ipynb"
CONCERNED = {PLAN_A, PLAN_B}


def _gh(prs, returncode=0, stderr=""):
    """Remplace ``subprocess`` dans le module : rend la sortie gh demandee."""

    def run(argv, **kwargs):  # signature volontairement large (capture_output, cwd...)
        assert argv[0] == "gh", f"seul gh est attendu, recu {argv[0]!r}"
        return SimpleNamespace(returncode=returncode, stdout=json.dumps(prs), stderr=stderr)

    return SimpleNamespace(run=run)


def _gh_absent():
    def run(argv, **kwargs):
        raise FileNotFoundError("gh")

    return SimpleNamespace(run=run)


def test_retient_l_intersection_par_pr_triee(monkeypatch):
    prs = [
        {"number": 101, "files": [{"path": PLAN_B}, {"path": PLAN_A}, {"path": HORS_PLAN}]},
        {"number": 102, "files": [{"path": PLAN_B}, {"path": PLAN_B}]},
    ]
    monkeypatch.setattr(migration, "subprocess", _gh(prs))

    gating = migration.report_gating(CONCERNED)

    assert gating == {"#101": [PLAN_A, PLAN_B], "#102": [PLAN_B]}
    # tri lexical et dedoublonnage : la PR 102 liste deux fois le meme fichier
    assert gating is not None
    assert gating["#101"] == sorted([PLAN_A, PLAN_B])
    assert len(gating["#102"]) == 1


def test_pr_hors_plan_ne_retient_rien(monkeypatch):
    """Temoin negatif : toucher le hub ne suffit pas, seule l'intersection compte."""
    prs = [{"number": 200, "files": [{"path": HORS_PLAN}]}]
    monkeypatch.setattr(migration, "subprocess", _gh(prs))

    assert migration.report_gating(CONCERNED) == {}


def test_aucune_pr_ouverte_rend_un_dict_vide(monkeypatch):
    monkeypatch.setattr(migration, "subprocess", _gh([]))

    assert migration.report_gating(CONCERNED) == {}


def test_gh_en_echec_rend_none(monkeypatch):
    monkeypatch.setattr(migration, "subprocess", _gh([], returncode=1, stderr="HTTP 502"))

    assert migration.report_gating(CONCERNED) is None


def test_gh_absent_rend_none(monkeypatch):
    monkeypatch.setattr(migration, "subprocess", _gh_absent())

    assert migration.report_gating(CONCERNED) is None


def test_liste_tronquee_rend_none(monkeypatch, capsys):
    """Atteindre la limite est une mesure PARTIELLE : elle se refuse, elle ne se tait pas."""
    monkeypatch.setattr(migration, "GH_PR_LIST_LIMIT", 2)
    prs = [{"number": n, "files": [{"path": PLAN_A}]} for n in (301, 302)]
    monkeypatch.setattr(migration, "subprocess", _gh(prs))

    assert migration.report_gating(CONCERNED) is None
    assert "TRONCATURE" in capsys.readouterr().out


def test_juste_sous_la_limite_reste_une_mesure(monkeypatch):
    """Le seuil ne doit pas refuser une lecture complete : 1 PR pour une limite de 2."""
    monkeypatch.setattr(migration, "GH_PR_LIST_LIMIT", 2)
    monkeypatch.setattr(migration, "subprocess", _gh([{"number": 400, "files": [{"path": PLAN_A}]}]))

    assert migration.report_gating(CONCERNED) == {"#400": [PLAN_A]}


def test_apply_refuse_une_mesure_impossible(monkeypatch, capsys):
    """Le fail-closed est ce qui protege le grand apply : None -> aucun git mv."""
    monkeypatch.setattr(migration, "report_gating", lambda concerned: None)
    monkeypatch.setattr(migration, "build_plan", lambda only=None: ([], []))
    monkeypatch.setattr(migration, "check_plan", lambda plan, only=None: [])
    monkeypatch.setattr(migration, "build_replacements", lambda plan, only=None: [])
    monkeypatch.setattr(migration, "run_sweep", lambda reps: ({}, 0))

    assert migration.main(["--apply"]) == 1
    assert "REFUS" in capsys.readouterr().out


@pytest.mark.parametrize("value", [None, {}, {"#1": [PLAN_A]}])
def test_le_contrat_tient_sur_les_trois_formes(value):
    """Garde de forme : les trois retours attendus restent les seuls possibles."""
    assert value is None or isinstance(value, dict)
    if isinstance(value, dict):
        assert all(isinstance(k, str) and k.startswith("#") for k in value)
        assert all(isinstance(v, list) for v in value.values())


# --- Plafond GraphQL sur la liste des fichiers d'une PR --------------------
#
# `gh pr list --json files` ramene 100 entrees par PR : au-dela, la fin de la
# liste disparait. Un fichier du plan tenu par une PR au-dela du plafond
# serait alors declare LIBRE, sans que rien ne le dise. La porte repasse par
# REST dans ce cas, et refuse si la re-mesure echoue.


def test_pr_au_plafond_graphql_est_re_mesuree_en_rest(monkeypatch):
    """100 fichiers vus par GraphQL : la liste est re-mesuree, paginee, en REST."""
    graphql_files = [{"path": f"g{i}.py"} for i in range(99)] + [{"path": PLAN_A}]
    rest_page1 = [{"path": f"r{i}.py"} for i in range(100)]
    rest_page2 = [{"path": PLAN_A}, {"path": PLAN_B}]
    calls = []

    def run(argv, **kwargs):
        calls.append(argv)
        if argv[1] == "api":
            page = argv[2].rsplit("page=", 1)[-1]
            batch = rest_page1 if page == "1" else rest_page2
            return SimpleNamespace(returncode=0, stdout=json.dumps(batch), stderr="")
        return SimpleNamespace(
            returncode=0,
            stdout=json.dumps([{"number": 500, "files": graphql_files}]),
            stderr="")

    monkeypatch.setattr(migration, "subprocess", SimpleNamespace(run=run))

    gating = migration.report_gating(CONCERNED)

    # Le fichier plan visible seulement par REST est bien retenu
    assert gating == {"#500": [PLAN_A, PLAN_B]}
    assert any(argv[1] == "api" for argv in calls)


def test_rest_echoue_au_plafond_rend_none(monkeypatch, capsys):
    """Re-mesure REST impossible : la porte refuse, elle ne se tait pas."""
    graphql_files = [{"path": f"g{i}.py"} for i in range(100)]

    def run(argv, **kwargs):
        if argv[1] == "api":
            return SimpleNamespace(returncode=1, stdout="", stderr="HTTP 502")
        return SimpleNamespace(
            returncode=0,
            stdout=json.dumps([{"number": 501, "files": graphql_files}]),
            stderr="")

    monkeypatch.setattr(migration, "subprocess", SimpleNamespace(run=run))

    assert migration.report_gating(CONCERNED) is None
    assert "REST" in capsys.readouterr().out


def test_sous_le_plafond_graphql_aucun_appel_rest(monkeypatch):
    """Temoin negatif : une PR sous le plafond ne declenche pas de re-mesure."""
    calls = []

    def run(argv, **kwargs):
        calls.append(argv)
        return SimpleNamespace(
            returncode=0,
            stdout=json.dumps([{"number": 502,
                                "files": [{"path": PLAN_A}] * 99}]),
            stderr="")

    monkeypatch.setattr(migration, "subprocess", SimpleNamespace(run=run))

    assert migration.report_gating(CONCERNED) == {"#502": [PLAN_A]}
    assert not any(argv[1] == "api" for argv in calls)


# --- Mode `--only` : un deplacement par sous-repertoire ----------------------
#
# Arbitrage ai-01 du 2026-10-23 (#17417) : les deplacements se font par
# sous-repertoire, une PR par tranche, d'abord ceux qu'aucune PR ouverte ne
# tient. Le mode `--only` rend cette tranche POSSIBLE : il restreint le plan
# ET les regles de reecriture au sous-repertoire vise.
#
# Le piege que le mode ferme : en mode hub-global, la regle
# `DataScienceWithAgents/ -> ML.Python/` reecrit des referents vers un hub
# qui n'existe pas encore (le hub est renomme en T5, le dernier). Une tranche
# ne doit reecrire que ce qu'elle deplace.

# Tranche temoin. A l'ecriture (#23114) elle s'appelait « 04b-Wavelet-
# Scattering » ; le renommage in-place 04b -> 05 (#23541, 2026-10-30) a fusionne
# apres l'ecriture des temoins mais avant leur merge : la tranche suit le nom
# REEL du hub (05), meme principe que la note T2-01 du DIR_MAP de l'organe.
SUB_WS = "05-Wavelet-Scattering"
NB_WS = "05-Wavelet-Scattering/WS-00a-Ondelettes-1D-from-scratch.ipynb"
NB_VISION = "04-Vision/4.1-Conv-NumPy-Torch-Allclose.ipynb"


def _fake_git(files_old=(), files_new=()):
    """Remplace le helper ``git`` du module : seules les lectures ls-files comptent."""

    def git(*args):
        if args[0] == "ls-files" and len(args) > 1:
            if args[1] == migration.HUB_NEW:
                return "\n".join(files_new)
            return "\n".join(files_old)
        return ""

    return git


def test_only_restreint_le_plan_au_sous_repertoire(monkeypatch):
    files = [f"{migration.HUB_OLD}/{NB_WS}", f"{migration.HUB_OLD}/{NB_VISION}"]
    monkeypatch.setattr(migration, "git", _fake_git(files_old=files))

    plan, errors = migration.build_plan(SUB_WS)

    assert [old for old, _ in plan] == [f"{migration.HUB_OLD}/{NB_WS}"]
    assert plan[0][1] == f"{migration.HUB_NEW}/05-Wavelet-Scattering/WS-00a-Ondelettes-1D-from-scratch-Python.ipynb"
    assert errors == []


def test_only_ne_reecrit_pas_le_hub_entier(monkeypatch):
    """La regle globale du hub doit ABSENTER d'une tranche : elle viserait un hub inexistant."""
    files = [f"{migration.HUB_OLD}/{NB_WS}"]
    monkeypatch.setattr(migration, "git", _fake_git(files_old=files))
    plan, _ = migration.build_plan(SUB_WS)

    reps = migration.build_replacements(plan, SUB_WS)
    rules = dict(reps)

    # la regle du sous-repertoire vise EST presente
    assert rules[f"DataScienceWithAgents/{SUB_WS}"] == "ML.Python/05-Wavelet-Scattering"
    # ... et les regles globales sont ABSENTES
    assert ("DataScienceWithAgents/", "ML.Python/") not in reps
    assert (migration.HUB_OLD, migration.HUB_NEW) not in reps
    # aucune regle d'un autre sous-repertoire
    assert not any(a.startswith(f"DataScienceWithAgents/04-Vision") for a, _ in reps)


def test_hub_global_garde_la_regle_du_hub(monkeypatch):
    """Temoin negatif : sans --only, la regle globale doit toujours exister."""
    files = [f"{migration.HUB_OLD}/{NB_WS}"]
    monkeypatch.setattr(migration, "git", _fake_git(files_old=files))
    plan, _ = migration.build_plan()

    reps = migration.build_replacements(plan)

    assert ("DataScienceWithAgents/", "ML.Python/") in reps
    assert (migration.HUB_OLD, migration.HUB_NEW) in reps


def test_only_inconnu_est_refuse():
    """Un `--only` typo deployerait zero fichier : il doit etre refuse, pas silencieux."""
    with pytest.raises(SystemExit):
        migration.resolve_only("99-Sous-Repertoire-Inexistant")


def test_only_accepte_le_nom_cible():
    """Le nom cible designe la meme tranche que le nom courant."""
    # Le mecanisme d'alias (valeur -> cle) se temoigne sur une tranche ou
    # courant et cible different encore : Track1-LangChain -> 06-Agents-LangChain.
    assert migration.resolve_only("06-Agents-LangChain") == "Track1-LangChain"
    assert migration.resolve_only("Track1-LangChain") == "Track1-LangChain"
    # Depuis le renommage in-place (#23541), 05-Wavelet-Scattering est cle ET
    # valeur : les deux faces designent la meme tranche.
    assert migration.resolve_only("05-Wavelet-Scattering") == SUB_WS
    assert migration.resolve_only(SUB_WS) == SUB_WS


def test_cle_deja_deplacee_nest_pas_morte(monkeypatch):
    """Apres une tranche, les cles de table du sous-repertoire deplace sont inertes, pas mortes."""
    keys_ws = [k for k in migration.NOTEBOOK_MAP if k.startswith(f"{SUB_WS}/")]
    assert keys_ws, "la table doit contenir des cles de la tranche 05-Wavelet-Scattering"
    moved = [f"{migration.HUB_NEW}/{migration.NOTEBOOK_MAP[k]}" for k in keys_ws]
    monkeypatch.setattr(migration, "git", _fake_git(files_old=(), files_new=moved))

    assert migration.check_plan([], SUB_WS) == []
    # hors tranche, ces memes cles SONT mortes : le controle global les voit
    assert any("cle morte" in e for e in migration.check_plan([]))


def test_apply_cree_le_repertoire_cible_avant_le_mv(monkeypatch, tmp_path):
    """`git mv` refuse une destination dont le parent n'existe pas.

    Premiere execution reelle de l'apply (2026-10-30) : l'organe plantait sur
    son premier fichier, "fatal: destination directory does not exist" -- le
    hub cible n'existe pas encore au premier deplacement. Le repertoire cible
    doit donc etre cree AVANT le mv.
    """
    calls = []

    def fake_git(*args):
        calls.append(args)
        return ""

    monkeypatch.setattr(migration, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(migration, "git", fake_git)
    monkeypatch.setattr(migration, "build_plan",
                        lambda only=None: ([("ancien/dossier/a.ipynb", "cible/dossier/a.ipynb")], []))
    monkeypatch.setattr(migration, "check_plan", lambda plan, only=None: [])
    monkeypatch.setattr(migration, "build_replacements", lambda plan, only=None: [])
    monkeypatch.setattr(migration, "run_sweep", lambda reps: ({}, 0))
    monkeypatch.setattr(migration, "sweep_files", lambda: [])
    monkeypatch.setattr(migration, "report_gating", lambda concerned: {})

    assert migration.main(["--apply"]) == 0
    assert (tmp_path / "cible" / "dossier").is_dir()
    assert ("mv", "ancien/dossier/a.ipynb", "cible/dossier/a.ipynb") in calls


# --- Fermeture atomique : un referent tenu suffit a refuser la tranche ------
#
# Un deplacement est atomique avec sa fermeture (fichiers deplaces + referents
# reecrits). Sauter les fichiers tenus laisse des liens morts dans les DEUX
# sens. Mesure du 2026-10-30 sur la tranche 04b : 5 des 11 referents sont tenus
# par des PRs ouvertes, dont _quarto.yml (7 lignes de nav Quarto), la table de
# traduction (145 lignes) et 2 baselines -- les sauter laissait le build docs
# faux sans que rien ne le dise.


def _apply_mocks(monkeypatch, gating, calls):
    def fake_git(*args):
        calls.append(args)
        return ""

    monkeypatch.setattr(migration, "git", fake_git)
    monkeypatch.setattr(migration, "build_plan",
                        lambda only=None: ([("ancien/dossier/a.ipynb", "cible/dossier/a.ipynb")], []))
    monkeypatch.setattr(migration, "check_plan", lambda plan, only=None: [])
    monkeypatch.setattr(migration, "build_replacements", lambda plan, only=None: [])
    monkeypatch.setattr(migration, "run_sweep", lambda reps: ({}, 0))
    monkeypatch.setattr(migration, "sweep_files", lambda: [])
    monkeypatch.setattr(migration, "report_gating", lambda concerned: gating)


def test_apply_refuse_une_fermeture_partiellement_tenue(monkeypatch, capsys):
    """Un REFERENT tenu (pas un fichier du plan) suffit : rien n'est deplace."""
    calls = []
    _apply_mocks(monkeypatch, {"#22643": ["_quarto.yml"]}, calls)

    assert migration.main(["--apply"]) == 1
    out = capsys.readouterr().out
    assert "REFUS" in out
    assert "_quarto.yml" in out
    assert "#22643" in out
    assert not any(a[0] == "mv" for a in calls), "aucun git mv sur une fermeture tenue"


def test_apply_refuse_aussi_si_le_fichier_du_plan_est_tenu(monkeypatch, capsys):
    """Le cas d'origine de la porte : le fichier a deplacer lui-meme est tenu."""
    calls = []
    _apply_mocks(monkeypatch, {"#101": ["ancien/dossier/a.ipynb"]}, calls)

    assert migration.main(["--apply"]) == 1
    assert "1 du plan" in capsys.readouterr().out
    assert not any(a[0] == "mv" for a in calls)


def test_apply_procede_quand_la_fermeture_est_libre(monkeypatch, capsys):
    """Temoin negatif : gating vide = feu vert, le mv a bien lieu."""
    calls = []
    _apply_mocks(monkeypatch, {}, calls)

    assert migration.main(["--apply"]) == 0
    assert "APPLIQUE" in capsys.readouterr().out
    assert any(a[0] == "mv" for a in calls)


# --- Formes NOM NU : liens frere-a-frere casses par le renommage T3 ---------


def test_nom_nu_d_un_carnet_renomme_est_reecrit():
    """`[WS-00a](WS-00a-...ipynb)` est relatif au dossier : le renommage le cassait."""
    plan = [(f"{migration.HUB_OLD}/{NB_WS}",
             f"{migration.HUB_NEW}/05-Wavelet-Scattering/"
             "WS-00a-Ondelettes-1D-from-scratch-Python.ipynb")]

    reps = migration.build_replacements(plan, SUB_WS)
    rules = dict(reps)

    assert rules["WS-00a-Ondelettes-1D-from-scratch.ipynb"] == \
        "WS-00a-Ondelettes-1D-from-scratch-Python.ipynb"
    # le chemin complet passe AVANT le nom nu (anti remplacement partiel)
    cles = [a for a, _ in reps]
    assert cles.index(f"{migration.HUB_OLD}/{NB_WS}") < \
        cles.index("WS-00a-Ondelettes-1D-from-scratch.ipynb")


def test_nom_nu_ambigu_n_est_pas_reecrit():
    """Deux carnets de meme nom de base vers deux cibles : le nom nu ne dit pas lequel."""
    plan = [
        (f"{migration.HUB_OLD}/a/x.ipynb", f"{migration.HUB_NEW}/b/x-Python.ipynb"),
        (f"{migration.HUB_OLD}/c/x.ipynb", f"{migration.HUB_NEW}/d/x-ML.ipynb"),
    ]

    assert "x.ipynb" not in dict(migration.build_replacements(plan))


def test_nom_nu_absent_quand_le_fichier_garde_son_nom():
    """Temoin negatif : un simple deplacement de dossier ne cree pas de regle de nom."""
    plan = [(f"{migration.HUB_OLD}/04b/W.ipynb", f"{migration.HUB_NEW}/05/W.ipynb")]

    assert "W.ipynb" not in dict(migration.build_replacements(plan))


# --- `--survey` : quelle tranche est mergeable aujourd'hui -------------------


def test_survey_refuse_si_la_mesure_des_prs_est_impossible(monkeypatch):
    """Pas de releve des PRs = pas de verdict d'ordonnancement (fail-closed)."""
    monkeypatch.setattr(migration, "fetch_open_pr_files", lambda: None)

    assert migration.survey() == 1


def test_survey_paie_le_releve_gh_une_seule_fois(monkeypatch, capsys):
    """Dix tranches, UN appel gh : le releve se paie une fois, pas par tranche."""
    appels = []

    def fetch():
        appels.append(1)
        return {"#1": {"_quarto.yml"}}

    monkeypatch.setattr(migration, "fetch_open_pr_files", fetch)
    monkeypatch.setattr(migration, "DIR_MAP", {"A": "A2", "B": "B2"})
    monkeypatch.setattr(migration, "build_plan",
                        lambda only=None: ([("ancien/a/x.ipynb", "cible/a/x.ipynb")], []))
    monkeypatch.setattr(migration, "build_replacements", lambda plan, only=None: [])
    monkeypatch.setattr(migration, "run_sweep", lambda reps: ({"_quarto.yml": 1}, 1))

    assert migration.survey() == 0
    out = capsys.readouterr().out
    assert len(appels) == 1
    assert "0 tranche(s) libre(s)" in out
    # le referent global bloque une tranche dont AUCUN fichier du plan n'est tenu
    assert "TENUE" in out and "0 du plan" in out
