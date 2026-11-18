"""Tests de l'ECRITURE de claim : constater le succes, ou refuser (#22758).

Contexte mesure le 2026-10-26 (issue #22758, `Part of #17437`) : quand le
quota GraphQL du compte partage est epuise, `check_lane_claim.py --claim`
pouvait rendre un verdict rassurant alors qu'aucun commentaire `[CLAIMED]`
n'existait sur l'issue. La LECTURE basculait deja en REST sous panne GraphQL
(#17038, `test_lane_claim_transport_fallback.py`) ; l'ECRITURE, non.

Acceptance visee :
1. une ecriture constatee (compte +1) rend succes, sans banniere ;
2. un `gh issue comment` mort bascule l'ECRITURE en REST (quota distinct) et
   la banniere NOMME le transport -- puis la verification passe ;
3. un transport qui rend succes sans que le compte bouge est REFUSE : c'est
   la classe de defaut la plus couteuse, un organe qui ment sur un succes ;
4. les deux transports d'ecriture morts nomment les DEUX et refusent ;
5. un comptage impossible avant ecriture refuse d'ecrire : un succes non
   constatable n'est pas un succes ;
6. la verification ne lit JAMAIS l'instantane (#22630) -- sinon elle compare
   l'etat d'avant a lui-meme.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402

SLUG = "jsboige/CoursIA"
ISSUE = "22758"


class _Proc:
    """Stand-in de subprocess.CompletedProcess."""

    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


class _Gh:
    """Faux `gh` : etat mutable du nombre de commentaires et des transports.

    Un transport qui « reussit » n'incremente le compte que si
    ``post_lands`` est vrai : c'est exactement la distinction entre une
    ecriture reelle et un succes rapporte sans effet (#22758 point 3).
    """

    def __init__(self, n=5):
        self.n = n
        self.calls = []
        self.gh_comment = "ok"      # ok | fail
        self.rest_post = "ok"       # ok | fail
        self.rest_count = "ok"      # ok | fail
        self.gql_count = "ok"       # ok | fail
        self.post_lands = True

    def run(self, cmd, *a, **kw):
        argv = list(cmd)
        self.calls.append(argv)
        if argv[:3] == ["gh", "issue", "comment"]:
            if self.gh_comment == "fail":
                return _Proc(
                    returncode=1, stderr="GraphQL: API rate limit exceeded")
            if self.post_lands:
                self.n += 1
            return _Proc(stdout="posted", stderr="")
        if argv[:3] == ["gh", "issue", "view"]:
            if self.gql_count == "fail":
                return _Proc(returncode=1, stderr="graphql: boom")
            return _Proc(stdout=json.dumps(
                {"comments": [{"body": "x"}] * self.n}), stderr="")
        if argv[:2] == ["gh", "api"]:
            path = argv[2]
            if path.endswith("/comments"):
                if self.rest_post == "fail":
                    return _Proc(returncode=1, stderr="gh api: secondary limit")
                if self.post_lands:
                    self.n += 1
                return _Proc(stdout="{}", stderr="")
            if self.rest_count == "fail":
                return _Proc(returncode=1, stderr="gh api: rate limited")
            return _Proc(stdout=str(self.n), stderr="")
        return _Proc(returncode=1, stderr=f"unexpected call {argv}")

    def kinds(self):
        """Verdicts lisibles : quels transports ont ete frappes."""
        out = []
        for argv in self.calls:
            if argv[:3] == ["gh", "issue", "comment"]:
                out.append("gql_post")
            elif argv[:3] == ["gh", "issue", "view"]:
                out.append("gql_count")
            elif argv[:2] == ["gh", "api"]:
                out.append("rest_post" if argv[2].endswith("/comments")
                           else "rest_count")
        return out


@pytest.fixture(autouse=True)
def _pin_slug(monkeypatch):
    monkeypatch.setattr(clc, "_repo_slug", lambda: SLUG)


def test_ecriture_constatee_rend_succes(monkeypatch, capsys):
    """Compte +1 -> succes silencieux, une seule ecriture."""
    gh = _Gh(n=5)
    monkeypatch.setattr(clc.subprocess, "run", gh.run)
    clc._post_comment(ISSUE, "[CLAIMED] lane x -- y")
    assert gh.n == 6
    assert gh.kinds() == ["rest_count", "gql_post", "rest_count"]
    assert "bascule" not in capsys.readouterr().err


def test_ecriture_graphql_morte_bascule_rest_de_l_ecriture(monkeypatch, capsys):
    """`gh issue comment` mort -> POST REST, banniere nommant le transport."""
    gh = _Gh(n=3)
    gh.gh_comment = "fail"
    monkeypatch.setattr(clc.subprocess, "run", gh.run)
    clc._post_comment(ISSUE, "[CLAIMED] lane x -- y")
    assert gh.n == 4
    assert "rest_post" in gh.kinds()
    err = capsys.readouterr().err
    assert "bascule REST de l'ECRITURE" in err
    assert "quota distinct" in err


def test_succes_du_transport_sans_commentaire_est_refuse(monkeypatch):
    """Le coeur de #22758 : succes rapporte, compte inchange -> refus."""
    gh = _Gh(n=7)
    gh.post_lands = False
    monkeypatch.setattr(clc.subprocess, "run", gh.run)
    with pytest.raises(RuntimeError) as excinfo:
        clc._post_comment(ISSUE, "[CLAIMED] lane x -- y")
    msg = str(excinfo.value)
    assert "n'a pas augmente" in msg
    assert "7 -> 7" in msg
    assert "NON CONSTATEE" in msg


def test_les_deux_transports_d_ecriture_morts_nomment_les_deux(monkeypatch):
    """GraphQL et REST morts -> l'erreur nomme les deux, ecriture NON POSEE."""
    gh = _Gh(n=2)
    gh.gh_comment = "fail"
    gh.rest_post = "fail"
    monkeypatch.setattr(clc.subprocess, "run", gh.run)
    with pytest.raises(RuntimeError) as excinfo:
        clc._post_comment(ISSUE, "[CLAIMED] lane x -- y")
    msg = str(excinfo.value)
    assert "GraphQL puis REST" in msg
    assert "NON POSEE" in msg
    assert gh.n == 2


def test_comptage_impossible_refuse_d_ecrire(monkeypatch):
    """Sans etat de reference, on n'ecrit pas : succes non constatable."""
    gh = _Gh(n=1)
    gh.rest_count = "fail"
    gh.gql_count = "fail"
    monkeypatch.setattr(clc.subprocess, "run", gh.run)
    with pytest.raises(RuntimeError) as excinfo:
        clc._post_comment(ISSUE, "[CLAIMED] lane x -- y")
    msg = str(excinfo.value)
    assert "NON VERIFIABLE" in msg
    assert "refus d'ecrire" in msg
    assert "gql_post" not in gh.kinds()
    assert "rest_post" not in gh.kinds()


def test_comptage_ne_consulte_pas_l_instantane(monkeypatch):
    """La verification mesure a la source, jamais le cache de lecture."""
    calls = []

    def _snapshot_boom(issue):
        calls.append(issue)
        raise AssertionError("l'instantane ne doit pas servir une verification")

    monkeypatch.setattr(clc, "_snapshot_issue_payload", _snapshot_boom)
    gh = _Gh(n=4)
    monkeypatch.setattr(clc.subprocess, "run", gh.run)
    assert clc._issue_comment_count(ISSUE) == 4
    assert calls == []
    assert gh.kinds() == ["rest_count"]
