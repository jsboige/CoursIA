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


# --- la panne d'instrument n'est pas un rouge --------------------------------

def _gh_rate_limited(args, timeout=120):
    raise RuntimeError(
        "gh api repos/jsboige/CoursIA/pulls/1/files a echoue : gh: API rate "
        "limit exceeded for installation.")


def test_un_instrument_injoignable_rend_unknown_et_sort_0(monkeypatch, capsys):
    """Mesure du 2026-10-29 (PR #23282, run 40868243719).

    `gh api .../files` a rendu `API rate limit exceeded for installation` :
    le script levait une RuntimeError, le step sortait 1, et la PR portait
    un rouge de TRANSPORT alors que son contenu etait conforme (verdict
    local : « aucun carnet neuf dans la PR »). Un organe injoignable rend
    UNKNOWN, jamais un rouge (#14849).
    """
    monkeypatch.setattr(cp, "_gh", _gh_rate_limited)

    rc = cp.main(["--pr", "1"])

    assert rc == 0, "une panne d'instrument ne doit jamais faire rougir le job"
    sortie = capsys.readouterr().out
    assert "UNKNOWN" in sortie
    assert "NON EVALUEE" in sortie


def test_strict_ne_convertit_pas_une_panne_d_instrument_en_constat(
        monkeypatch, capsys):
    """`--strict` sanctionne un VERDICT. Une panne n'en produit aucun : elle
    ne doit pas devenir un constat sous le seul effet du drapeau."""
    monkeypatch.setattr(cp, "_gh", _gh_rate_limited)

    assert cp.main(["--pr", "1", "--strict"]) == 0
    assert "UNKNOWN" in capsys.readouterr().out


def test_un_bug_de_code_n_est_pas_avale_par_la_garde(monkeypatch):
    """Le try n'attrape que la panne d'instrument : un defaut de code doit
    remonter, sinon la garde masquerait ses propres regressions."""
    def gh_buggue(args, timeout=120):
        raise ValueError("defaut de code, pas une panne de transport")

    monkeypatch.setattr(cp, "_gh", gh_buggue)

    with pytest.raises(ValueError):
        cp.main(["--pr", "1"])


# --- la panne d'instrument ne doit pas devenir un constat (revue 2026-10-29) --

def test_issue_created_remonte_une_panne_d_instrument(monkeypatch):
    """Le correctif precedent s'arretait a l'entree.

    `issue_created` ecrasait TOUTE exception en `None` : pendant la famine
    d'API decrite dans le corps, une PR parfaitement conforme recevait
    « issue #N d'age non mesure » puis un `::warning::`. Le grief que cette
    garde existe pour supprimer etait toujours produit, une requete plus
    loin. Un `None` n'a pas deux significations selon la fonction qui le
    rend.
    """
    def gh_famine(args, timeout=120):
        raise cp.InstrumentError(
            "gh issue view a echoue : gh: API rate limit exceeded")

    monkeypatch.setattr(cp, "_gh", gh_famine)

    with pytest.raises(cp.InstrumentError):
        cp.issue_created(4242)


def test_issue_created_rend_none_quand_gh_rend_un_verdict(monkeypatch):
    """Un 404 EST un constat sur l'entree : l'issue n'existe pas, donc
    « age non mesure » est vrai. Seule la panne de transport remonte."""
    def gh_introuvable(args, timeout=120):
        raise cp.GhError(
            "gh issue view a echoue : GraphQL: Could not resolve to an Issue")

    monkeypatch.setattr(cp, "_gh", gh_introuvable)

    assert cp.issue_created(4242) is None


def test_gh_discrimine_le_transport_du_verdict_d_entree(monkeypatch):
    """Tout `returncode != 0` devenait « instrument injoignable ».

    Un 404, un argument refuse, un depot non autorise sont des VERDICTS sur
    l'entree, pas des pannes de transport : les confondre rend l'organe
    aveugle a ses propres erreurs d'invocation.
    """
    class _Fini:
        def __init__(self, err):
            self.returncode, self.stderr, self.stdout = 1, err, ""

    monkeypatch.setattr(
        cp.subprocess, "run",
        lambda *a, **k: _Fini("gh: API rate limit exceeded for installation."))
    with pytest.raises(cp.InstrumentError):
        cp._gh(["api", "x"])

    monkeypatch.setattr(
        cp.subprocess, "run",
        lambda *a, **k: _Fini("GraphQL: Could not resolve to a PullRequest"))
    with pytest.raises(cp.GhError):
        cp._gh(["pr", "view", "999999999"])


def test_un_json_illisible_est_une_panne_d_instrument(monkeypatch):
    """Un stdout tronque pendant une famine vient de `gh`, pas du code.

    `JSONDecodeError` est une `ValueError` : il echappait donc au `try` de
    `main()` et produisait le rouge de transport que ce correctif supprime.
    Le discriminant n'est pas la classe d'exception, c'est la provenance.
    """
    monkeypatch.setattr(cp, "_gh", lambda args, timeout=120: '{"truncated": ')

    with pytest.raises(cp.InstrumentError):
        cp._gh_json(["api", "x"])


def test_un_age_non_mesure_avec_tirage_nomme_est_conforme():
    """Le cas `(None, tirage disponible)` n'etait couvert par aucun test.

    Une issue dont l'age est illisible mais qui a ete servie par un tirage
    nomme EST conforme : le tirage vaut attente.
    """
    verdict, _ = cp.decide(1234, None, {
        "disponible": True, "vues": 1,
        "retenue": {"draw_id": "d-1", "lane": "l", "ts": "t"}})

    assert verdict == "CONFORME (tirage)"


def _pr_conforme(monkeypatch):
    monkeypatch.setattr(cp, "pr_meta", lambda pr: {
        "title": "t", "author": {"login": "jsboige"},
        "createdAt": "2026-10-29T10:00:00Z", "body": "Closes #4242"})
    monkeypatch.setattr(cp, "pr_files", lambda pr: [
        {"filename": "a/b/carnet.ipynb", "status": "added"}])


def test_une_panne_sur_issue_created_rend_unknown_et_sort_0(
        monkeypatch, capsys):
    """La famine epargne `pr_files` et frappe la requete suivante : le job
    doit rendre UNKNOWN, pas accuser la PR."""
    _pr_conforme(monkeypatch)

    def gh_famine(args, timeout=120):
        raise cp.InstrumentError(
            "gh issue view a echoue : gh: API rate limit exceeded")

    monkeypatch.setattr(cp, "_gh", gh_famine)

    assert cp.main(["--pr", "1"]) == 0
    sortie = capsys.readouterr().out
    assert "UNKNOWN" in sortie
    assert "NON EVALUEE" in sortie


def test_le_statut_est_pose_en_marche_normale(monkeypatch, tmp_path):
    """`statut` n'existait que dans la branche de panne : un consommateur de
    `--json` ne pouvait pas distinguer CONFORME de « pas de statut »."""
    _pr_conforme(monkeypatch)
    monkeypatch.setattr(cp, "issue_created",
                        lambda n: "2026-10-01T00:00:00Z")
    monkeypatch.setattr(cp, "draws_for",
                        lambda i, j: {"disponible": True, "vues": 0,
                                      "retenue": None})

    sortie = tmp_path / "rapport.json"
    assert cp.main(["--pr", "1", "--json", str(sortie)]) == 0
    assert '"statut": "CONFORME"' in sortie.read_text(encoding="utf-8")
def test_gh_classe_la_panne_de_transport_et_le_verdict_d_entree(monkeypatch):
    """Le discriminant est le stderr de `gh`, pas le code de sortie : les deux
    rendent non-zero. Un quota epuise ou un DNS muet est une panne de
    TRANSPORT (UNKNOWN) ; un `Could not resolve to a PullRequest` est un
    verdict sur l'ENTREE, et le motif ne doit pas annoncer un instrument
    injoignable (test repris de main, PR #23283)."""
    class Faux:
        returncode = 1

        def __init__(self, err):
            self.stderr = err
            self.stdout = ""

    monkeypatch.setattr(
        cp.subprocess, "run",
        lambda *a, **k: Faux("API rate limit exceeded for installation."))
    with pytest.raises(cp.InstrumentError):
        cp.pr_files(22977)

    monkeypatch.setattr(
        cp.subprocess, "run",
        lambda *a, **k: Faux("GraphQL: Could not resolve to a PullRequest "
                             "with the number of 99999."))
    with pytest.raises(cp.GhError):
        cp.pr_files(99999)

