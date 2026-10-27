#!/usr/bin/env python3
"""Refresh a PR's stale G-VAR-3 adjacency verdict by re-triggering the check.

## Why this exists

The G-VAR-3 adjacency guard resolves a lane's REAL predecessor from the MERGED
sequence of the lane in a 21-day window (`fetch_merged_prs_since.py --days
21`). The guard re-runs only on `pull_request: synchronize, edited, reopened`
(`always-on-guards.yml` l.57) -- a push to the branch OR a body edit. When the
merged sequence changes (a sibling PR merges and bumps the predecessor), the
guard verdicts go stale: the previously failing `prev_genre` is now resolved
to a different grain, but nothing in the workflow says "recompute", and the
PR stays MERGEABLE=FALSE in the PR gate while it would be MERGEABLE=TRUE if
re-checked.

The founder case (2026-09-01) was the myia-po-2026:CoursIA lane:
`MERGEABLE=FALSE` on 7 PRs whose GRAIN tag (MED/guard, LIGHT/guard, ...) was
in genuine adjacency with #13585 (MED/guard, merged 2026-08-31T18:47:59Z) at
PR-open time. After #13888 (MED/tooling) merged at 2026-09-01T07:13:59Z, the
guard's predecessor resolution moved to tooling -- so the same PRs would now
PASS if re-checked. The `pull_request: synchronize` trigger fires on push, not
on sequence changes, so no automatic refresh happens.

This script automates the manual workaround: simulate the guard locally with
the CURRENT merged sequence, and if the simulated verdict PASSES while the
PR is currently failing on `Always-on guards`, append an idempotent
`<!-- refresh-adj: ISO8601 -->` marker to the body and `gh pr edit
--body-file`. That re-fires the `pull_request: edited` event and the guard
recomputes with the current sequence -- which is now PASS.

## Les deux jambes qui portent l'organe (#22748)

Depuis #22331/#22333 les organes de body ont leur propre workflow, et
l'adjacence y tourne aussi (`scripts/ci/always_on_body_organs.sh:21`). Un
verdict G-VAR-3 perime peut donc tomber sur `Always-on guards -- body`, et
cette jambe etait invisible pour cet organe : elle n'etait resolue nulle
part (le fichier de contenu ne la declare pas) et un filtre la rejetait
explicitement. Le sweep voyait une PR candidate, ne trouvait jamais de jambe
rouge, et se taisait -- #22748 est restee ~12 h rouge.

`adjacency_leg_state()` tranche les deux jambes : le job de CONTENU ne porte
que des organes de contenu, sa causalite est non ambigue ; le job de BODY
porte CINQ organes, et n'est retenu que si ses annotations nomment
l'adjacence. Un rouge `tag_required` / `close_keyword` de la jambe body ne
fait donc jamais editer un corps pour rien.

## What it does NOT do

- It does NOT bypass the G-VAR-3 rule. If the simulated verdict FAILS, the
  script exits non-zero with the reason and does NOT modify the body. The
  rule stays authoritative; the marker is only a refresh, never an override.
- It does NOT modify the body for any reason other than the refresh marker.
  The marker is invisible on GitHub's rendered view and idempotent on
  re-runs: a second invocation finds the marker, replaces the timestamp,
  does not duplicate the line.
- It does NOT touch the underlying code or the substance of the PR. The
  diff stays zero on the source files; only the body SHA changes by the
  one-line append.

## Usage

    python scripts/ci/refresh_stale_adjacency.py --pr 13812 --pr 13869 --pr 13917
    python scripts/ci/refresh_stale_adjacency.py --pr 13812 --dry-run

## Exit codes

  0  -- every PR either passes the simulated guard, or was successfully
       refreshed (marker appended, edit posted).
  1  -- at least one PR fails the simulated guard with a real reason
       (genuine G-VAR-3 adjacency); nothing was modified on those PRs.
  2  -- caller error (gh failure, missing argument).

The marker is exactly one line:

    <!-- refresh-adj: 2026-09-01T09:42:00Z -->

appended at the end of the body, followed by a newline if missing.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

import yaml

# Make the shared extractor + adjacency guard importable from anywhere.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402
from variation_adjacency_guard import (  # noqa: E402
    check,
    parse_override,
    resolve_merged_prev_genre,
    sequence_as_of,
)

MARKER_RE = re.compile(r"<!--\s*refresh-adj:\s*[^>]+\s*-->")
MARKER_PREFIX = "<!-- refresh-adj:"
MARKER_TZ = "%Y-%m-%dT%H:%M:%SZ"
# Prefixe des jobs du workflow `always-on-guards.yml`, resolus a la lecture
# (#22403). Le compte d'organes dans le nom a deja change deux fois ; il ne
# se code pas ici.
GUARDS_JOB_PREFIX = "Always-on guards"
# Marqueur du job d'organes de BODY (#22333) : meme prefixe, autre sujet.
BODY_JOB_MARKER = "body"
# Le job de body vit dans son PROPRE workflow (#22331/#22333) : le resoudre
# depuis `always-on-guards.yml` etait structurellement impossible (#22748).
BODY_WORKFLOW_NAME = "always-on-guards-body.yml"
# Banniere d'agregat du job de body -- `scripts/ci/always_on_body_organs.sh`
# termine par `::error::Organes de body bloquants en echec :$FAILED`. C'est la
# seule surface qui NOMME l'organe tombe (meme doctrine que
# `pick_idle_grain.fetch_check_organs`) : le nom du check-run ne le porte pas.
BODY_ORGAN_BANNER_RE = re.compile(
    r"Organes de body bloquants en echec\s*:\s*([a-z_ ]+)")
# L'organe d'adjacence prefixe son propre verdict `::error::G-VAR-3 ...`.
# Second temoin, lui aussi specifique a l'organe : aucun autre organe de body
# n'emet ce marqueur.
ADJACENCY_ORGAN_MARKER = "G-VAR-3"
# URL d'un check-run Actions : `.../<owner>/<repo>/actions/runs/<run>/job/<id>`.
# Le slug et l'id se lisent de la, sans appel `gh` supplementaire.
_CHECK_JOB_URL_RE = re.compile(
    r"https?://[^/]+/(?P<slug>[^/]+/[^/]+)/actions/runs/\d+/job/(?P<job_id>\d+)")


def now_marker() -> str:
    """Return the current UTC timestamp in the marker format."""
    return f"{MARKER_PREFIX} {datetime.now(timezone.utc).strftime(MARKER_TZ)} -->"


def run_gh(*args: str, check: bool = False) -> subprocess.CompletedProcess:
    """Run a `gh` CLI invocation, return CompletedProcess (stdout=str)."""
    return subprocess.run(
        ["gh", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=check,
    )


def fetch_merged_window(days: int = 21) -> list[dict]:
    """Fetch the merged-window used by the G-VAR-3 guard (21d default)."""
    proc = subprocess.run(
        ["python", "scripts/ci/fetch_merged_prs_since.py", "--days", str(days)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"fetch_merged_prs_since failed: {proc.stderr}")
    return json.loads(proc.stdout)


def get_pr_body(pr_number: int) -> str:
    """Return the current body of `pr_number` as a string."""
    proc = run_gh("pr", "view", str(pr_number), "--json", "body")
    if proc.returncode != 0:
        raise RuntimeError(f"gh pr view #{pr_number} failed: {proc.stderr}")
    data = json.loads(proc.stdout)
    return data.get("body") or ""


def get_pr_comments(pr_number: int) -> list[dict]:
    """Return the {author.login, body} list for `pr_number` (override scan)."""
    proc = run_gh("pr", "view", str(pr_number), "--json", "comments",
                  "--jq", '[.comments[] | {author: .author.login, body: .body}]')
    if proc.returncode != 0:
        return []
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return []


def get_pr_check_rows(pr_number: int) -> list[dict]:
    """Lignes de `gh pr checks` : `{name, conclusion, url}` (#22748).

    L'URL etait deja dans la sortie et etait jetee : elle seule permet de
    remonter a l'id du check-run, donc de lire les annotations qui NOMMENT
    l'organe tombe (`check_run_annotations`).
    """
    proc = run_gh("pr", "checks", str(pr_number))
    rows: list[dict] = []
    for line in proc.stdout.splitlines():
        # Format: NAME<tab>CONCLUSION<tab>DURATION<tab>URL
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        rows.append({
            "name": parts[0],
            "conclusion": parts[1],
            "url": parts[3] if len(parts) > 3 else "",
        })
    return rows


def get_pr_checks(pr_number: int) -> dict[str, str]:
    """Return the current check state of `pr_number` (name -> conclusion)."""
    checks: dict[str, str] = {}
    for row in get_pr_check_rows(pr_number):
        checks[row["name"]] = row["conclusion"]
    return checks


def guard_workflow_path(*, body: bool = False) -> Path:
    """Chemin du workflow des organes de contenu, ou de ceux de body."""
    name = BODY_WORKFLOW_NAME if body else "always-on-guards.yml"
    return Path(__file__).resolve().parents[2] / ".github" / "workflows" / name


def _job_names_in(path: Path) -> list[str]:
    """Noms declares (`name:`) par les jobs d'un fichier de workflow."""
    data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    return [
        n for n in ((job or {}).get("name")
                    for job in (data.get("jobs") or {}).values())
        if isinstance(n, str)
    ]


def content_guard_job_names(workflow_path=None) -> list[str]:
    """Noms des jobs `Always-on guards` du workflow, lus dans le YAML (#22403).

    Le nom etait code en dur (`Always-on guards -- 13 organes, 1 checkout`)
    alors que le job s'appelle `-- 16 organes` : le predicat « le job est
    ROUGE sur cette PR » ne pouvait donc jamais etre vrai, et l'organe se
    taisait -- un silence indiscernable de « rien a rafraichir ».

    Le nom se **lit** desormais a la source (cle `name:` de chaque job), donc
    un renommage du compte d'organes ne rend plus l'organe muet : au pire il
    rend une liste vide, et `RuntimeError` le dit bruyamment au lieu de
    laisser croire a un balayage propre.

    Le filtre est le prefixe `Always-on guards` dans CE workflow uniquement :
    le job de body (`Always-on guards -- body`, #22333) vit dans son propre
    fichier et se resout par `body_guard_job_names()`. Un match par
    sous-chaine sur `gh pr checks` fusionnerait les deux -- cf. le fold de
    check-runs qui a deja produit un faux vert rassurant.

    `BODY_JOB_MARKER` reste donc exclu ICI : si le job de body revenait dans
    ce fichier, l'inclure ferait passer un rouge `close_keyword` pour un
    rouge de contenu. C'est `adjacency_leg_state()` qui porte la distinction
    des deux jambes, pas ce filtre.
    """
    path = Path(workflow_path) if workflow_path else guard_workflow_path()
    resolved = [
        n for n in _job_names_in(path)
        if n.startswith(GUARDS_JOB_PREFIX)
        # #22333 a separe les organes de body dans leur propre job. Il porte le
        # meme prefixe : s'il vivait un jour dans ce fichier, l'inclure ferait
        # rafraichir une PR pour un rouge qui ne dit rien de l'adjacence.
        and BODY_JOB_MARKER not in n
    ]
    if not resolved:
        raise RuntimeError(
            f"aucun job nomme '{GUARDS_JOB_PREFIX}...' dans {path} -- "
            "l'organe refuse de mesurer a l'aveugle (renommage du job ?)")
    return resolved


def body_guard_job_names(workflow_path=None) -> list[str]:
    """Noms des jobs de `always-on-guards-body.yml` (#22748).

    Le job de body **execute l'organe d'adjacence** depuis #22333
    (`scripts/ci/always_on_body_organs.sh:21` : `adjacency) organ_adjacency ;;`).
    Il vit dans son propre fichier : l'exclusion par marqueur de
    `content_guard_job_names()` ne pouvait donc rien y voir, et un verdict
    G-VAR-3 perime tombe sur cette jambe n'etait jamais rafraichi -- #22748
    est restee ~12 h rouge pour cette raison.

    `RuntimeError` sur resolution vide, meme doctrine que la jambe de
    contenu : un renommage du job rendrait l'organe muet, et le silence se
    lirait « rien a rafraichir ».
    """
    path = Path(workflow_path) if workflow_path else guard_workflow_path(body=True)
    resolved = [
        n for n in _job_names_in(path)
        if n.startswith(GUARDS_JOB_PREFIX)
    ]
    if not resolved:
        raise RuntimeError(
            f"aucun job nomme '{GUARDS_JOB_PREFIX}...' dans {path} -- "
            "l'organe refuse de mesurer a l'aveugle (renommage du job ?)")
    return resolved


def check_run_annotations(url: str) -> list[str] | None:
    """Messages d'annotation du check-run designe par `url`, ou None.

    `None` (et non `[]`) distingue « lu, aucune annotation » de « pas pu
    lire » -- le rapport du sweep porte cette difference au lieu de la
    confondre avec « pas d'adjacence » (cf. #11808 : un filtre deconnecte et
    un filtre vide sont indistinguables).
    """
    m = _CHECK_JOB_URL_RE.match(url or "")
    if not m:
        return None
    proc = run_gh(
        "api", f"repos/{m.group('slug')}/check-runs/{m.group('job_id')}/annotations")
    if proc.returncode != 0:
        return None
    try:
        data = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None
    if not isinstance(data, list):
        return None
    return [str((a or {}).get("message") or "") for a in data]


def annotations_name_adjacency(annotations: list[str]) -> bool:
    """Ces annotations attribuent-elles le rouge a l'organe d'adjacence ?"""
    for message in annotations:
        banner = BODY_ORGAN_BANNER_RE.search(message)
        if banner and "adjacency" in banner.group(1).split():
            return True
        if ADJACENCY_ORGAN_MARKER in message:
            return True
    return False


def adjacency_leg_state(pr_number: int,
                        job_names: list[str] | None = None) -> dict:
    """Quelle jambe `Always-on guards` est rouge, et par la faute de qui.

    Rend ``{"failing", "job", "cause"}`` ; ``failing`` est le predicat que
    `refresh_one` consomme, les deux autres champs sont du diagnostic.

    Les deux jambes n'ont pas la meme valeur de preuve :

    * jambe de CONTENU rouge -- causalite non ambigue : ce job ne porte que
      les organes de contenu, dont l'adjacence (`cause: content-job`) ;
    * jambe de BODY rouge -- elle porte CINQ organes (Grain, prev:,
      close-keyword, adjacence, claim). Sans attribution, un rouge
      `close_keyword` ferait editer un body pour rien : churn de la file
      `cancel-in-progress` (#22331) et sweep rapportant un refresh qui ne
      leve rien. La jambe n'est donc retenue que si ses annotations nomment
      l'adjacence (`cause: body-adjacency`) ; sinon `body-other-organ`, ou
      `body-unreadable` si l'API ne rend pas les annotations -- fail-CLOSED,
      dans les deux cas sans ecriture.

    `job_names` force la liste des jambes de contenu (tests, appelants qui
    veulent ignorer la jambe de body).
    """
    if job_names is not None:
        content_names, body_names = job_names, []
    else:
        content_names = content_guard_job_names()
        body_names = body_guard_job_names()
    rows = get_pr_check_rows(pr_number)

    for row in rows:
        if row["name"] in content_names and row["conclusion"] == "fail":
            return {"failing": True, "job": row["name"], "cause": "content-job"}

    for row in rows:
        if row["name"] not in body_names or row["conclusion"] != "fail":
            continue
        annotations = check_run_annotations(row["url"])
        if annotations is None:
            return {"failing": False, "job": row["name"],
                    "cause": "body-unreadable"}
        if annotations_name_adjacency(annotations):
            return {"failing": True, "job": row["name"],
                    "cause": "body-adjacency"}
        return {"failing": False, "job": row["name"],
                "cause": "body-other-organ"}

    return {"failing": False, "job": None, "cause": None}


def is_always_on_guards_failing(pr_number: int,
                               job_names: list[str] | None = None) -> bool:
    """True si une jambe `Always-on guards` est FAIL pour cause d'adjacence."""
    return adjacency_leg_state(pr_number, job_names)["failing"]


def append_marker(body: str, marker: str) -> str:
    """Append `marker` to `body`, idempotent (replaces existing marker)."""
    body = body.rstrip("\n")
    # Strip any previous refresh-adj marker (with the line that carries it)
    body = MARKER_RE.sub("", body).rstrip("\n")
    if not body:
        return f"{marker}\n"
    return f"{body}\n{marker}\n"


def simulate_adjacency(pr_number: int, body: str, merged_window: list[dict]) -> dict:
    """Run the G-VAR-3 guard on `body` against the current `merged_window`.

    Returns the guard verdict dict. This is the SAME computation the CI runs
    (`scripts/ci/variation_adjacency_guard.py --body-file ... --merged-prs-file
    ...`), so a `guard_pass: True` here means the CI will turn green on the
    next re-trigger.
    """
    g = gt.parse_grain_tag(body)
    if g is None:
        # Body has no Grain tag -- a different guard (tag-required) is the
        # cause. Don't refresh.
        return {
            "guard_pass": False,
            "blocking": False,
            "adjacent": False,
            "reason": "no Grain tag in body -- tag-required is the cause, not adjacency",
        }

    override = parse_override(get_pr_comments(pr_number))
    merged_prev = resolve_merged_prev_genre(merged_window, g["lane"])
    verdict = check(body, override=override, merged_prev=merged_prev)
    # #15739 : le verdict simule porte son referentiel comme celui de la CI --
    # contre quelle sequence il a conclu (prev_pr/genre/source + horodatage),
    # pour qu'un lecteur distingue un recalcul frais d'un rouge perime.
    verdict = dict(verdict)
    verdict["prev_source"] = "merged-sequence"
    verdict["sequence_as_of"] = sequence_as_of(merged_window)
    return verdict


def refresh_one(pr_number: int, dry_run: bool, merged_window: list[dict]) -> dict:
    """Run the full refresh cycle for `pr_number`. Returns a status dict.

    L'ordre est deliberé : le verdict d'adjacence est RE-SIMULE avant tout
    acces en ecriture (`simulate_adjacency`), et l'edition du body est
    inconditionnellement gardee par `would_refresh`, qui exige ce
    `guard_pass`. Aucune branche d'ecriture ne peut donc etre atteinte sans
    re-simulation -- c'est la garantie qui rend sur d'ouvrir le
    rafraichissement a la jambe de body (#22748).
    """
    body = get_pr_body(pr_number)
    verdict = simulate_adjacency(pr_number, body, merged_window)
    leg = adjacency_leg_state(pr_number)
    always_on_failing = leg["failing"]
    new_body = append_marker(body, now_marker())
    would_refresh = (
        always_on_failing
        and verdict["guard_pass"]
        and verdict.get("blocking") is not True
    )
    refreshed = False
    if would_refresh and not dry_run:
        # UN SEUL appel, stdin = le nouveau corps. La sonde `--body-file -`
        # SANS stdin (avant #22748) lisait EOF et gh publiait alors un corps
        # VIDE, que le second appel restaurait : deux evenements `edited`, et
        # une fenetre ou le job de body -- qui relit le corps par API a
        # l'execution (#15697) -- pouvait juger `tag_required` sur un corps
        # vide. Le repli fichier ne sert plus qu'au cas ou le `-` est refuse.
        proc = subprocess.run(
            ["gh", "pr", "edit", str(pr_number), "--body-file", "-"],
            input=new_body,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        refreshed = proc.returncode == 0
        if not refreshed and "flag" in (proc.stderr or "").lower():
            tmp = Path(f"/tmp/refresh_body_{pr_number}.md")
            tmp.write_text(new_body, encoding="utf-8")
            proc2 = run_gh("pr", "edit", str(pr_number), "--body-file", str(tmp))
            tmp.unlink(missing_ok=True)
            refreshed = proc2.returncode == 0
    elif would_refresh and dry_run:
        refreshed = True  # virtual: would have been done

    return {
        "pr": pr_number,
        "always_on_failing": always_on_failing,
        # Quelle jambe est rouge et par la faute de qui (#22748) : sans ce
        # champ, un rouge de body non attribuable et un balayage propre
        # rendaient le meme JSON.
        "guard_leg": leg["job"],
        "guard_leg_cause": leg["cause"],
        "guard_pass": verdict["guard_pass"],
        "adjacent": verdict.get("adjacent"),
        "prev_genre": verdict.get("prev_genre"),
        "prev_pr": verdict.get("prev_pr"),
        "reason": verdict.get("reason", ""),
        "would_refresh": would_refresh,
        "refreshed": refreshed,
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--pr", type=int, action="append", required=True,
                   help="PR number to consider (repeatable)")
    p.add_argument("--dry-run", action="store_true",
                   help="Report what would be done without modifying any PR")
    args = p.parse_args(argv)

    try:
        merged_window = fetch_merged_window()
    except RuntimeError as e:
        print(json.dumps({"error": str(e)}), file=sys.stderr)
        return 2

    results = [refresh_one(pr, args.dry_run, merged_window) for pr in args.pr]
    print(json.dumps({"results": results}, indent=2, ensure_ascii=False))

    # Exit 1 if any PR failed the simulated guard with a real reason (the
    # refresh only covers stale-failing verdicts; a fresh failing verdict is
    # not ours to override).
    any_real_fail = any(
        not r["guard_pass"] and not r["always_on_failing"]
        for r in results
    )
    return 1 if any_real_fail else 0


if __name__ == "__main__":
    sys.exit(main())
