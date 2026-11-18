"""#22916 -- en mode batch, `NOT_SCOPED` doit rendre BLOCKED, pas ERROR.

Le defaut mesure : `check_issues_batch` capture stdout et stderr dans deux
buffers, puis n'en passait qu'UN au resume
(`_summarize_run_check_output(buf_out.getvalue(), rc)`). Or les deux
verdicts `NOT_SCOPED` de `_run_check` -- le call qui n'a pas declare de
scope (`exit 2`, #12322) et le scope entierement mort (`exit 2`,
#12345 fail-CLOSED) -- partent sur **stderr**. Le resume ne trouvait donc
jamais la phrase et rendait `ERROR`.

Consequence pour l'appelant : une lane lisait `(ERROR)` la ou l'organe
disait « je ne peux pas prouver la disjonction » -- deux situations qui
n'appellent pas le meme geste (re-scoper ses globs vs. attendre). Le
picker, lui, remappe ces codes sur ses verdicts internes depuis #22630 :
un scope casse y devenait indistinguable d'une panne de transport.

Pourquoi le defaut a survecu : les assertions `NOT_SCOPED` du depot
portent TOUTES sur la voie solo et lisent `captured.err`. Aucune ne
traversait le resume, donc aucune ne pouvait voir la perte. Le test
#22684 voisin s'arrete a `code != "FREE"`, que `ERROR` satisfait -- il
protegeait le verdict, pas le diagnostic.

Aucun test ne touche le reseau : `_gh_api` est remplace par un faux et la
racine de l'instantane est redirigee vers `tmp_path`.
"""

import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import check_lane_claim as clc
import gh_snapshot as gs


@pytest.fixture(autouse=True)
def _snapshot_root_isole(tmp_path, monkeypatch):
    """Racine de l'instantane redirigee : jamais le LOCALAPPDATA reel."""
    monkeypatch.setattr(gs, "snapshot_root", lambda: tmp_path / "gh-snapshot")
    yield
    clc.set_snapshot(None)


def _faux_gh_api(responses):
    """Remplace `_gh_api` : rend les reponses fixees, refuse le reste."""
    def fake(path, *, params=""):
        if path in responses:
            return responses[path]
        raise RuntimeError(f"appel gh inattendu: {path} {params}")

    return fake


def _snapshot_avec_claim(monkeypatch, n: int, claim_body: str) -> dict:
    """Instantane construit par la voie de PRODUCTION (#22684).

    `ensure_issue_payloads` range l'issue dans `issues[n]` et ses
    commentaires dans `comments[n]` -- deux cles separees. C'est la forme
    que la production fabrique ; l'injecter a la main dans `issues[n]`
    testerait une forme qui n'existe pas.
    """
    recent = (datetime.now(UTC)
              - timedelta(hours=1)).strftime("%Y-%m-%dT%H:%M:%SZ")
    monkeypatch.setattr(gs, "_gh_api", _faux_gh_api({
        f"repos/jsboige/CoursIA/issues/{n}":
            {"number": n, "title": f"T{n}", "labels": [],
             "updated_at": recent, "state": "open"},
        f"repos/jsboige/CoursIA/issues/{n}/comments":
            [{"body": claim_body,
              "created_at": recent, "updated_at": recent,
              "user": {"login": "jsboige"}, "html_url": "u"}],
    }))
    snap = {"issues": {}, "comments": {}, "prs": {}, "checks": {}, "meta": {}}
    snap, _calls = gs.ensure_issue_payloads("jsboige/CoursIA", [n], snap, 600)
    return snap


# --- le resume lui-meme : les deux moities de la paire -------------------


def test_resume_voit_not_scoped_emis_sur_stderr():
    """#22916 -- `NOT_SCOPED` dans le texte rend BLOCKED, pas ERROR."""
    # La phrase telle que `_run_check` l'emet : `print(..., file=sys.stderr)`
    # juste avant `return 2` (#12345, scope entierement mort).
    stderr = ("\nNOT_SCOPED: this call's declared scope is entirely dead "
              "on #42: every glob in `--paths` matches zero tracked files "
              "('**/rien/**').\n")
    assert clc._summarize_run_check_output(stderr, 2) == "BLOCKED"


def test_resume_exit2_sans_phrase_reste_error():
    """Controle negatif : le correctif ne convertit pas TOUT `exit 2`.

    Un `exit 2` sans phrase de verdict est une panne de transport ou un
    scope dont on ne sait rien : il doit rester `ERROR`. Sans cette
    assertion, remplacer le test de substring par un `return "BLOCKED"`
    passerait les deux autres tests de ce fichier.
    """
    assert clc._summarize_run_check_output("", 2) == "ERROR"
    assert clc._summarize_run_check_output(
        "une sortie quelconque, sans ligne-verdict", 2) == "ERROR"


# --- la voie batch bout en bout -----------------------------------------


def test_batch_not_scoped_rend_blocked(monkeypatch):
    """Le scenario de l'issue : claim d'une autre lane, pas de `--paths`."""
    n = 424242
    snap = _snapshot_avec_claim(
        monkeypatch, n, "[CLAIMED] lane myia-po-2099:CoursIA -- test epic-wide")
    clc.set_snapshot(snap)
    monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])

    out = clc.check_issues_batch([str(n)], "myia-ai-01:CoursIA",
                                 from_json=None)
    result = out["results"][str(n)]

    assert result["exit"] == 2          # le verdict de `_run_check` est inchange
    assert result["code"] == "BLOCKED", (
        f"exit 2 avec NOT_SCOPED sur stderr doit rendre BLOCKED, "
        f"obtenu {result['code']!r} (stderr_tail={result['stderr_tail']!r})")
    # La phrase est bien celle du scope, pas un BLOCKED de claim ordinaire :
    # `_run_check` n'emet `NOT_SCOPED` que dans la branche ou un claim
    # d'une AUTRE lane a ete vu, donc ce verdict prouve aussi la lecture.
    assert "branch on the verdict" in result["stderr_tail"]


def test_batch_not_scoped_human_porte_la_phrase(monkeypatch):
    """Le champ `human` doit nommer le verdict, pas afficher `(ERROR)`.

    `human` est ce qu'une lane poste ou lit dans un dossier : `(ERROR)`
    envoie chercher une panne la ou l'organe a rendu un diagnostic.
    """
    n = 424243
    snap = _snapshot_avec_claim(
        monkeypatch, n, "[CLAIMED] lane myia-po-2099:CoursIA -- test epic-wide")
    clc.set_snapshot(snap)
    monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])

    out = clc.check_issues_batch([str(n)], "myia-ai-01:CoursIA",
                                 from_json=None)
    human = out["results"][str(n)]["human"]
    assert human.startswith("NOT_SCOPED"), (
        f"human doit porter la ligne-verdict emise sur stderr, obtenu {human!r}")
    assert human != "(ERROR)"


# --- les deux flux restent distincts ------------------------------------


def test_find_verdict_line_ne_fusionne_pas_les_flux():
    """stdout puis stderr, jamais un melange (#22916).

    Un melange laisserait une ligne de diagnostic sur stderr masquer le
    verdict rendu sur stdout -- l'inverse exact du defaut corrige.
    """
    stdout = "CLEAR: no other lane claims #7"
    stderr = "NOT_SCOPED: bruit de diagnostic"
    assert clc._find_verdict_line(stdout) == stdout
    # Un flux sans verdict ne rend rien, il ne « complete » pas avec l'autre.
    assert clc._find_verdict_line("") == ""
    assert clc._find_verdict_line(stderr) == stderr
    # Et l'ordre d'appel prefere stdout.
    assert (clc._find_verdict_line(stdout)
            or clc._find_verdict_line(stderr)) == stdout
