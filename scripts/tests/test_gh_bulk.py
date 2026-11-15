"""Tests de `coordination/gh_bulk.py`, les lectures groupees du tapis rapide (#22983).

Aucun test ne touche le reseau ni le vrai depot : chaque lecture recoit un faux
`run(argv, timeout)`, et la sentinelle `forbid_shell_escape` refuse tout processus.
"""
import json
import subprocess
import sys
import time
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")


def _noeud(n: int, commentaires: int = 1) -> dict:
    return {"number": n, "title": f"Issue {n}", "body": "corps", "createdAt": "2026-10-01T00:00:00Z",
            "updatedAt": "2026-11-01T00:00:00Z", "labels": {"nodes": [{"name": "EPIC"}]},
            "comments": {"totalCount": commentaires + 3,
                         "nodes": [{"createdAt": "2026-11-02T00:00:00Z", "author": {"login": "x"},
                                    "body": "[CLAIMED] lane a:b"}] * commentaires}}


def _page(nums: list[int], suite: str | None) -> str:
    return json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": suite is not None, "endCursor": suite},
        "nodes": [_noeud(n) for n in nums]}}}})


def _taille(argv: list[str]) -> int:
    return int(next(a for a in argv if a.startswith("n="))[2:])


def _erreur(argv: list[str], stderr: str) -> subprocess.CalledProcessError:
    return subprocess.CalledProcessError(1, argv, output="", stderr=stderr)


def test_issues_paginees_et_a_plat():
    appels: list[list[str]] = []

    def run(argv, timeout):
        appels.append(argv)
        return _page([1, 2], "c1") if not any(a.startswith("after=") for a in argv) \
            else _page([3], None)

    issues = gh_bulk.lire_issues_ouvertes(run)
    assert [it["number"] for it in issues] == [1, 2, 3]
    assert "after=c1" in appels[1]
    assert issues[0]["labels"] == ["EPIC"] and issues[0]["comments_total"] == 4
    assert issues[0]["comments"][0] == {"created_at": "2026-11-02T00:00:00Z", "author": "x",
                                        "body": "[CLAIMED] lane a:b"}


def test_un_504_relit_la_meme_page_en_plus_petit():
    tailles: list[int] = []

    def run(argv, timeout):
        tailles.append(_taille(argv))
        if tailles[-1] == 50:
            raise _erreur(argv, "gh: HTTP 504: Gateway Timeout")
        return _page([7], None)

    assert [it["number"] for it in gh_bulk.lire_issues_ouvertes(run)] == [7]
    assert tailles == [50, 25]


def test_troisieme_echec_leve_lecture_incomplete():
    tailles: list[int] = []

    def run(argv, timeout):
        tailles.append(_taille(argv))
        if tailles[-1] == 25:
            raise subprocess.TimeoutExpired(argv, timeout)
        raise _erreur(argv, "HTTP 502 Bad Gateway")

    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_bulk.lire_issues_ouvertes(run)
    assert tailles == [50, 25, 12]
    assert exc.value.lecture == "issues" and exc.value.page == 1


def test_une_erreur_non_transitoire_ne_se_rejoue_pas():
    tailles: list[int] = []

    def run(argv, timeout):
        tailles.append(_taille(argv))
        raise _erreur(argv, "HTTP 401: Bad credentials")

    with pytest.raises(gh_bulk.LectureIncomplete, match="401"):
        gh_bulk.lire_issues_ouvertes(run)
    assert tailles == [50]


def test_prs_paginees_par_cent():
    def pr(n: int) -> dict:
        return {"number": n, "title": f"PR {n}", "body": "lane a:b", "draft": False,
                "created_at": "2026-11-01T00:00:00Z", "updated_at": "", "merged_at": None,
                "head": {"ref": f"fix/{n}"}, "user": {"login": "jsboige"}}

    def run(argv, timeout):
        page = int(argv[-1].rsplit("page=", 1)[1])
        return json.dumps([pr(n) for n in range(1, 101)] if page == 1 else [pr(101)])

    prs = gh_bulk.lire_prs_ouvertes(run)
    assert len(prs) == 101
    assert prs[-1] == {"number": 101, "title": "PR 101", "body": "lane a:b", "draft": False,
                       "created_at": "2026-11-01T00:00:00Z", "updated_at": "",
                       "merged_at": None, "head": "fix/101", "author": "jsboige"}


def test_prs_reponse_illisible():
    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_bulk.lire_prs_ouvertes(lambda argv, timeout: "<html>")
    assert exc.value.lecture == "prs_ouvertes"


GIT_LOG = (
    "\x1eaaaaaaaaaaaa\x1f1762992000\x1fFix(x,#123): sujet (#2001)\x1fCloses #1234\nSee #123\n\n"
    "\x1ebbbbbbbbbbbb\x1f1762905600\x1fAdd(y): autre (#2002)\x1fPart of #77\n"
)


def test_citations_mergees_sur_git_log_simule():
    vus: list[list[str]] = []

    def run(argv, timeout):
        vus.append(argv)
        return GIT_LOG

    cit = gh_bulk.lire_citations_mergees("d:/depot", 14, run)
    assert vus[0][:4] == ["git", "-C", "d:/depot", "log"] and "--since=14.days" in vus[0]
    assert [c["sha"] for c in cit[123]] == ["aaaaaaaaaaaa"]  # une fois, pas deux
    assert [c["sha"] for c in cit[1234]] == ["aaaaaaaaaaaa"]
    assert set(cit) == {123, 1234, 2001, 2002, 77}
    assert cit[77][0] == {"sha": "bbbbbbbbbbbb", "date": "2025-11-12T00:00:00Z",
                          "sujet": "Add(y): autre (#2002)", "ferme": False}
    # ferme : mot de fermeture (#1234) ou portee du sujet (#123) ; ni `See`, ni `Part of`,
    # ni le numero de la PR du squash
    assert {n: cit[n][0]["ferme"] for n in cit} == {
        123: True, 1234: True, 2001: False, 2002: False, 77: False}
    lecture = gh_bulk.Lecture(issues=[], prs=[], citations=cit)
    assert lecture.origin_main_le == "2025-11-13T00:00:00Z"


def test_citations_git_en_panne():
    def run(argv, timeout):
        raise _erreur(argv, "fatal: bad revision 'origin/main'")

    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_bulk.lire_citations_mergees(".", 14, run)
    assert exc.value.lecture == "citations_mergees"


def _run_complet(compteur: list[int]):
    def run(argv, timeout):
        compteur[0] += 1
        if argv[0] == "git" and "--format=%ct" in argv:
            return str(int(time.time()))  # pointe locale fraiche : pas de fetch
        if argv[0] == "git":
            return GIT_LOG
        if "graphql" in argv:
            return _page([1, 2], None)
        return "[]"
    return run


# --- fetch d'origin/main avant les citations -----------------------------------

def _run_fetch(compteur: list[list[str]], age_pointe: int | str, fetch_ecart=None):
    """Faux `run` : pointe locale d'origin/main d'age donne (s ou illisible),
    fetch qui reussit ou qui echoue avec `fetch_ecart`, reste complet."""
    def run(argv, timeout):
        compteur.append(list(argv))
        if "--format=%ct" in argv:
            return str(int(time.time()) - age_pointe) if isinstance(age_pointe, int) \
                else age_pointe
        if "fetch" in argv:
            if fetch_ecart is not None:
                raise fetch_ecart(argv, stderr="fatal: réseau injoignable")
            return ""
        if argv[0] == "git":
            return GIT_LOG
        if "graphql" in argv:
            return _page([1], None)
        return "[]"
    return run


def test_pointe_fraiche_ne_fetch_pas(tmp_path):
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(".", 0, _run_fetch(appels, 3600), dossier_cache=tmp_path)
    assert not any("fetch" in a for a in appels)
    assert lecture.fetch_note is None and 1234 in lecture.citations


def test_pointe_perimee_fetch_puis_lit(tmp_path):
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(".", 0, _run_fetch(appels, 7 * 86400),
                                dossier_cache=tmp_path)
    assert ["git", "-C", ".", "fetch", "-q", "origin", "main"] in appels
    # le fetch precede la lecture des citations
    assert appels.index(["git", "-C", ".", "fetch", "-q", "origin", "main"]) < next(
        i for i, a in enumerate(appels) if "--since" in " ".join(a))
    assert lecture.fetch_note is None and 1234 in lecture.citations


def test_pointe_illisible_tente_le_fetch(tmp_path):
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(".", 0, _run_fetch(appels, "pas un entier"),
                                dossier_cache=tmp_path)
    assert ["git", "-C", ".", "fetch", "-q", "origin", "main"] in appels
    assert lecture.fetch_note is None


def test_fetch_en_echec_ne_leve_pas_et_se_nomme(tmp_path):
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(".", 0, _run_fetch(appels, 7 * 86400, _erreur),
                                dossier_cache=tmp_path)
    assert "fetch origin/main impossible" in (lecture.fetch_note or "")
    assert 1234 in lecture.citations  # la lecture continue sur la pointe locale


def test_cache_relu_puis_cache_corrompu_ignore(tmp_path):
    compteur = [0]
    premiere = gh_bulk.lire_tout(".", 300, _run_complet(compteur), dossier_cache=tmp_path)
    assert compteur[0] == 4 and premiere.appels == 4 and not premiere.depuis_cache

    def interdit(argv, timeout):
        raise AssertionError("le cache frais devait servir")

    relue = gh_bulk.lire_tout(".", 300, interdit, dossier_cache=tmp_path)
    assert relue.depuis_cache and relue.issues == premiere.issues
    assert relue.citations == premiere.citations and 123 in relue.citations

    for fichier in tmp_path.glob("*.json"):
        fichier.write_text("{ pas du json", encoding="utf-8")
    compteur[0] = 0
    rejouee = gh_bulk.lire_tout(".", 300, _run_complet(compteur), dossier_cache=tmp_path)
    assert compteur[0] == 4 and not rejouee.depuis_cache


def test_cache_desactive(tmp_path):
    compteur = [0]
    gh_bulk.lire_tout(".", 0, _run_complet(compteur), dossier_cache=tmp_path)
    gh_bulk.lire_tout(".", 0, _run_complet(compteur), dossier_cache=tmp_path)
    assert compteur[0] == 8 and not list(tmp_path.iterdir())


def test_charger_depuis_un_dossier(tmp_path):
    (tmp_path / "issues.json").write_text(json.dumps([{"number": 5}]), encoding="utf-8")
    (tmp_path / "prs_ouvertes.json").write_text("[]", encoding="utf-8")
    (tmp_path / "meta.json").write_text('{"fetched_at": "2026-11-13T12:57:46Z"}',
                                        encoding="utf-8")
    lecture = gh_bulk.charger_depuis(tmp_path)
    assert lecture.issues == [{"number": 5}] and lecture.lu_a == "2026-11-13T12:57:46Z"
    vus: list[list[str]] = []

    def run(argv, timeout):
        vus.append(list(argv))
        return GIT_LOG

    avec_git = gh_bulk.charger_depuis(tmp_path, ".", 14, run)
    assert 1234 in avec_git.citations and avec_git.appels == 1
    # un rejeu de dossier ne fetch jamais, meme pointe perimee
    assert not any("fetch" in a for a in vus)
    (tmp_path / "prs_ouvertes.json").unlink()
    with pytest.raises(gh_bulk.LectureIncomplete):
        gh_bulk.charger_depuis(tmp_path)
