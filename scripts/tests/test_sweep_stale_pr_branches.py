"""Tests de `scripts/ci/sweep_stale_pr_branches.py` (#16915).

Aucun appel reseau : l'enumeration passe par la couture `run_gh` de l'organe
(chargee la premiere et enregistree dans sys.modules, comme sa propre suite),
la mesure de retard par les references `read_branch_sha`/`read_behind` du
pilote, et la delegation par la couture `run_organ`.

Le contrat verrouille ici :

  * le pilote n'ecrit JAMAIS -- seul `run_organ` invoque l'organe, et il ne
    recoit `--apply` QUE si le pilote l'a recu (dry-run par defaut) ;
  * l'ordre de selection est OLDEST-FIRST (les PRs quietes et agees n'ont
    pas d'autre voie de rattrapage -- lecon mesuree du pr-gate-stale-sweep) ;
  * la selection est bornee par --max-updates, le surplus est DEFERRED nomme ;
  * les exclusions de metadonnees sont NOMMEES et comptees (jamais un
    filtrage muet) ;
  * le plancher DWELL ne se re-arme PAS sur un update-branch de la forme que
    ce balayage produit -- le contrat #16149 que le pilote presuppose, avec
    ses propres fixtures (test de non-regression exigé par l'acceptance).
"""

import importlib.util
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CI_DIR = HERE.parent / "ci"
ORGAN = CI_DIR / "update_stale_pr_branches.py"
PILOT = CI_DIR / "sweep_stale_pr_branches.py"

# L'organe d'abord, enregistre sous son nom d'import : le pilote fait
# `from update_stale_pr_branches import ...` et doit trouver CE module-ci,
# pas une seconde execution de spec.
organ_spec = importlib.util.spec_from_file_location("update_stale_pr_branches", ORGAN)
organ = importlib.util.module_from_spec(organ_spec)
sys.modules.setdefault("update_stale_pr_branches", organ)
organ_spec.loader.exec_module(organ)

pilot_spec = importlib.util.spec_from_file_location("sweep_stale_pr_branches", PILOT)
mod = importlib.util.module_from_spec(pilot_spec)
pilot_spec.loader.exec_module(mod)

REPO = "jsboige/CoursIA"


def pr_row(
    number,
    *,
    base="main",
    head=None,
    mergeable="MERGEABLE",
    draft=False,
    fork=False,
    url=None,
):
    return {
        "number": number,
        "isDraft": draft,
        "isCrossRepository": fork,
        "baseRefName": base,
        "headRefOid": head or f"{number:040d}",
        "mergeable": mergeable,
        "url": url or f"https://github.com/{REPO}/pull/{number}",
    }


class FakeGh:
    """Doublure de `run_gh` : rend la reponse GraphQL de `gh pr list`."""

    def __init__(self, rows):
        self.rows = rows

    def __call__(self, args):
        assert args[0] == "pr"
        assert args[args.index("--json") + 1] == mod.LIST_FIELDS
        return json.dumps(self.rows)


def patch_measure(monkeypatch, table, failures=()):
    """Branche les deux lecteurs de retard sur une table par numero de PR."""

    def fake_sha(repo, ref):
        return f"base-{ref}"

    def fake_behind(repo, base_sha, head_sha):
        # La tete encode le numero : {number:040d} -> int(head)
        number = int(head_sha.lstrip("0") or "0")
        if number in failures:
            raise organ.GhError(f"compare muet pour #{number}")
        if number not in table:
            return 0
        return table[number]

    monkeypatch.setattr(mod, "read_branch_sha", fake_sha)
    monkeypatch.setattr(mod, "read_behind", fake_behind)


class OrganCall:
    def __init__(self):
        self.argv = None

    def __call__(self, repo, prs, *, apply, max_updates, state_dir):
        self.argv = {
            "repo": repo,
            "prs": list(prs),
            "apply": apply,
            "max_updates": max_updates,
            "state_dir": state_dir,
        }
        results = [
            {
                "pr": pr,
                "action": "UPDATE",
                "code": "OK",
                "base_kind": "main",
                "updated": True,
                "freshness": "STALE",
                "invalidated": ["checks", "reviews", "dossier"],
            }
            for pr in prs
        ]
        payload = {
            "repo": repo,
            "mode": "apply" if apply else "dry-run",
            "max_updates": max_updates,
            "updates_applied": len(results),
            "results": results,
        }
        return 0, payload, json.dumps(payload)


def run_sweep(monkeypatch, capsys, rows, table, *, extra=(), failures=()):
    monkeypatch.setattr(mod, "run_gh", FakeGh(rows))
    patch_measure(monkeypatch, table, failures=failures)
    call = OrganCall()
    monkeypatch.setattr(mod, "run_organ", call)
    rc = mod.main(list(extra))
    out = json.loads(capsys.readouterr().out)
    return rc, out, call


def test_dry_run_by_default_passes_no_apply(monkeypatch, capsys):
    _, out, call = run_sweep(monkeypatch, capsys, [pr_row(101)], {101: 5})
    assert call.argv["apply"] is False
    assert out["mode"] == "dry-run"
    assert out["organ"]["mode"] == "dry-run"


def test_apply_flag_is_forwarded_to_the_organ_only(monkeypatch, capsys):
    _, _, call = run_sweep(monkeypatch, capsys, [pr_row(7)], {7: 2}, extra=["--apply"])
    assert call.argv["apply"] is True


def test_selection_is_oldest_first_and_capped(monkeypatch, capsys):
    rows = [pr_row(90), pr_row(10), pr_row(50), pr_row(30)]
    table = {90: 4, 10: 9, 50: 1, 30: 2}
    rc, out, call = run_sweep(
        monkeypatch, capsys, rows, table, extra=["--max-updates", "2"]
    )
    # 10 et 30 (les plus anciennes) passees a l'organe ; 50 et 90 deferees.
    assert call.argv["prs"] == [10, 30]
    assert out["selected"] == [10, 30]
    assert out["deferred"] == [50, 90]
    actions = {r["pr"]: r["action"] for r in out["results"]}
    assert actions[50] == "DEFERRED"
    assert actions[90] == "DEFERRED"


def test_metadata_exclusions_are_named_and_counted(monkeypatch, capsys):
    rows = [
        pr_row(1, draft=True),
        pr_row(2, fork=True),
        pr_row(3, mergeable="UNKNOWN"),
        pr_row(4, mergeable="CONFLICTING"),
        pr_row(5),
    ]
    rc, out, _ = run_sweep(monkeypatch, capsys, rows, {})
    assert rc == 0
    assert out["excluded"] == {
        "draft": 1,
        "fork": 1,
        "not_mergeable": 2,
        "up_to_date": 1,
        "behind_unknown": 0,
    }
    assert out["candidates"] == 0
    assert out["organ_invoked"] is False
    assert out["organ"] is None


def test_up_to_date_and_unknown_are_not_candidates(monkeypatch, capsys):
    rows = [pr_row(11), pr_row(12), pr_row(13)]
    table = {11: 0, 13: 7}
    rc, out, call = run_sweep(monkeypatch, capsys, rows, table, failures={12})
    assert out["selected"] == [13]
    assert out["excluded"]["up_to_date"] == 1
    assert out["excluded"]["behind_unknown"] == 1
    # L'inconnue n'est PAS deleguee : fail-closed, re-essayable au prochain
    # balayage -- jamais un « probablement en retard ».
    assert 12 not in call.argv["prs"]


def test_results_carry_the_acceptance_fields_for_every_measured_pr(monkeypatch, capsys):
    rows = [pr_row(21), pr_row(22), pr_row(23, base="feature/stack-base")]
    table = {21: 3, 22: 0, 23: 0}
    rc, out, _ = run_sweep(monkeypatch, capsys, rows, table, extra=["--apply"])
    by_pr = {r["pr"]: r for r in out["results"]}
    # Ligne organe (selectionnee) : les quatre champs de l'acceptance.
    assert by_pr[21]["action"] == "UPDATE"
    assert by_pr[21]["base_kind"] == "main"
    assert by_pr[21]["freshness"] == "STALE"
    assert by_pr[21]["invalidated"] == ["checks", "reviews", "dossier"]
    # Ligne pilote (non selectionnee) : meme contrat de champs, valeurs nulles.
    assert by_pr[22]["action"] == "NOT_SELECTED"
    assert by_pr[22]["base_kind"] == "main"
    assert by_pr[22]["freshness"] is None
    assert by_pr[22]["invalidated"] == []
    # Base empilee : le genre est REPORTE par le pilote, jamais decide ici.
    assert by_pr[23]["base_kind"] == "stacked"


def test_organ_refuse_is_relayed_not_swallowed(monkeypatch, capsys):
    rows = [pr_row(31)]
    table = {31: 6}

    def refusing(repo, prs, **kw):
        payload = {
            "repo": repo,
            "mode": "apply",
            "results": [
                {
                    "pr": prs[0],
                    "action": "REFUSE",
                    "code": "HEAD_MOVED",
                    "base_kind": "main",
                    "freshness": None,
                    "invalidated": [],
                }
            ],
        }
        return 1, payload, json.dumps(payload)

    monkeypatch.setattr(mod, "run_gh", FakeGh(rows))
    patch_measure(monkeypatch, table)
    monkeypatch.setattr(mod, "run_organ", refusing)
    rc = mod.main(["--apply"])
    out = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert out["organ_exit"] == 1
    assert out["results"][0]["action"] == "REFUSE"


def test_enumeration_failure_exits_two(monkeypatch, capsys):
    def broken(args):
        raise organ.GhError("504 sur /pulls")

    monkeypatch.setattr(mod, "run_gh", broken)
    rc = mod.main([])
    out = json.loads(capsys.readouterr().out)
    assert rc == 2
    assert "enumeration illisible" in out["error"]


def test_list_limit_is_transmitted_to_gh(monkeypatch, capsys):
    rows = [pr_row(n) for n in range(1, 5)]
    seen = {}

    def fake_gh(args):
        seen["limit"] = args[args.index("--limit") + 1]
        return json.dumps(rows)

    monkeypatch.setattr(mod, "run_gh", fake_gh)
    patch_measure(monkeypatch, {})
    monkeypatch.setattr(mod, "run_organ", OrganCall())
    mod.main(["--list-limit", "4"])
    out = json.loads(capsys.readouterr().out)
    # La borne vit dans l'appel gh (troncature cote serveur), pas dans une
    # re-implementation locale : la transmettre suffit.
    assert seen["limit"] == "4"
    assert out["list_limit"] == 4


# ---------------------------------------------------------------------------
# Verrou DWELL (#16149) : le contrat que le balayage presuppose. L'acceptance
# #16915 l'exige DANS la suite du pilote -- si merge_dwell regresse et
# re-arme le plancher sur un update-branch, ce fichier rougit en meme temps
# que le gate, et le cron qui vient d'etre cable devient visible comme
# introducteur de la taxe, pas silencieux.
# ---------------------------------------------------------------------------

def test_update_branch_shape_does_not_rearm_dwell():
    dwell_spec = importlib.util.spec_from_file_location(
        "merge_dwell_for_sweep_test", CI_DIR / "merge_dwell.py"
    )
    dwell = importlib.util.module_from_spec(dwell_spec)
    dwell_spec.loader.exec_module(dwell)

    REPO = "jsboige/CoursIA"
    M1 = "c" * 40  # dernier commit COTE PR (l'auteur)
    BASE = "d" * 40  # tete de la base au moment de l'update
    M2 = "e" * 40  # commit de fusion pose par gh pr update-branch

    PR_COMMITTED = "2026-09-20T00:00:00Z"
    UPDATE_COMMITTED = "2026-09-20T04:00:00Z"  # 4 h plus tard

    commits = {
        M1: {
            "parents": [{"sha": "f" * 40}],
            "commit": {
                "committer": {"date": PR_COMMITTED},
                "tree": {"sha": "t" * 40},
            },
        },
        M2: {
            "parents": [{"sha": M1}, {"sha": BASE}],
            "commit": {
                "committer": {"date": UPDATE_COMMITTED},
                "tree": {"sha": "a" * 40},
            },
        },
    }

    def fetch(path):
        # commits/{sha} pour M1 et M2 ; le compare qui prouve « second parent
        # ancetre de la base » (ici par EGALITE directe, le cas update-branch).
        for sha, payload in commits.items():
            if path == f"repos/{REPO}/commits/{sha}":
                return payload
        if path.startswith(f"repos/{REPO}/compare/"):
            return {"status": "behind", "behind_by": 0}
        raise dwell.DwellError(f"path inattendue : {path}")

    def run_git(args):
        # merge-tree rend l'arbre de l'auto-merge : EGAL a l'arbre porte par
        # M2 -> la fusion est PROUVEE content-free et doit etre exempte.
        if args[:2] == ["merge-tree", "--write-tree"]:
            return 0, "a" * 40 + "\n"
        if args[0] == "cat-file":
            return 0, ""
        if args[0] == "merge-base":
            return 0, "f" * 40 + "\n"
        if args[0] == "rev-parse":
            return 0, "false\n"
        return 0, ""

    measured = dwell.last_authoritative_committed_at(
        REPO, M2, BASE, fetch=fetch, run_git=run_git
    )
    assert measured == dwell.parse_iso8601(PR_COMMITTED), (
        "un update-branch content-free doit mesurer le dernier commit AUTEUR, "
        "pas la fusion serveur -- sinon chaque balayage re-arme 120 min de "
        "plancher et #16915 reintroduit la taxe que #16149 a supprimee"
    )


def test_dwell_still_measures_a_substantive_merge():
    """Controle negatif du verrou : une fusion PORTEUSE DE CONTENU (arbre !=
    auto-merge, i.e. une resolution d'auteur) se mesure ELLE-MEME."""
    dwell_spec = importlib.util.spec_from_file_location(
        "merge_dwell_for_sweep_neg", CI_DIR / "merge_dwell.py"
    )
    dwell = importlib.util.module_from_spec(dwell_spec)
    dwell_spec.loader.exec_module(dwell)

    REPO = "jsboige/CoursIA"
    M1, BASE, M2 = "1" * 40, "2" * 40, "3" * 40
    PR_COMMITTED = "2026-09-20T00:00:00Z"
    RESOLVED_AT = "2026-09-20T04:00:00Z"

    commits = {
        M1: {
            "parents": [{"sha": "f" * 40}],
            "commit": {
                "committer": {"date": PR_COMMITTED},
                "tree": {"sha": "t" * 40},
            },
        },
        M2: {
            "parents": [{"sha": M1}, {"sha": BASE}],
            "commit": {
                "committer": {"date": RESOLVED_AT},
                "tree": {"sha": "b" * 40},  # DIFFERENT de l'auto-merge
            },
        },
    }

    def fetch(path):
        for sha, payload in commits.items():
            if path == f"repos/{REPO}/commits/{sha}":
                return payload
        if path.startswith(f"repos/{REPO}/compare/"):
            return {"status": "behind", "behind_by": 0}
        raise dwell.DwellError(f"path inattendue : {path}")

    def run_git(args):
        if args[:2] == ["merge-tree", "--write-tree"]:
            return 0, "a" * 40 + "\n"  # auto-merge != arbre porte par M2
        if args[0] == "cat-file":
            return 0, ""
        if args[0] == "merge-base":
            return 0, "f" * 40 + "\n"
        if args[0] == "rev-parse":
            return 0, "false\n"
        return 0, ""

    measured = dwell.last_authoritative_committed_at(
        REPO, M2, BASE, fetch=fetch, run_git=run_git
    )
    assert measured == dwell.parse_iso8601(RESOLVED_AT)
