#!/usr/bin/env python3
"""Audit des filtres de chemin sur les workflows GitHub Actions.

Genere un rapport JSON + Markdown sur la couverture `pull_request.paths` /
`pull_request.paths-ignore` des workflows sous `.github/workflows/`. Detecte
les workflows sans filtre, classe par categorie (gate requis / advisory /
non-require), et signale les ajouts recents comme regression potentielle.

Issue de reference : #10600 (74 workflows, 0 filtre -> partiellement faux ;
62/72 ont deja un filtre paths/paths-ignore sur main a l'instant).

Sortie :
- JSON : `docs/audit/workflow-path-filters/audit-<sha>.json` (complet)
- Markdown : `docs/audit/workflow-path-filters/audit-<sha>.md` (resume humain)
- Last-known : `docs/audit/workflow-path-filters/latest.json` (le plus recent)

Usage :
    python scripts/notebook_tools/audit_workflow_path_filters.py --audit-dir docs/audit/workflow-path-filters
    python scripts/notebook_tools/audit_workflow_path_filters.py --check-regression <previous.json>
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any

import yaml


# Workflows dont le declenchement non-filtre est DELIBERE (gates requis par
# construction ou advisories bon marche qui doivent voir chaque PR).
# Cette liste est OPT-IN : ajouter un nom ici uniquement apres audit
# (cf. issue #10600 et discussion lane-claim-protocol).
REQUIRED_UNFILTERED_WORKFLOWS: set[str] = {
    # Gates PR (protection de branche)
    "pr-gate.yml",
    # #13384 : fusion des cinq gardes always-on (variation-tag-guard,
    # perimeter-review-guard, fast-lane-shadow, variation-light-genre,
    # lane-claim-guard -- tous dormant) en un seul workflow non filtre qui
    # porte leurs organes metadata + le moteur fast-lane.
    "always-on-guards.yml",
    "translation-guard.yml",
    # #14057 (Vague 2 tranche 1) : fusion des trois gardes metadata always-on
    # (base-not-main-advisory, stale-base-warning, concurrency-conj-guard --
    # tous dormant) en une seule umbrella non filtree qui porte leurs organes.
    "always-on-metadata-guards.yml",
    # Les workflows fusionnes ci-dessus sont DORMANTS (#13384, #14057 :
    # declencheurs pull_request retires, jobs conserves en reference) :
    # retires de cette liste, ils ne declenchent plus sur les PR.
    # catalog-pr-guard.yml retire par #11012 : le workflow n'a jamais tourne sur
    # une PR (0 run pull_request), c'est catalog-drift.yml qui tient la ligne.
    # Secret scan (doit voir chaque PR)
    "secret-scan.yml",
    # Regression guard (doit voir chaque PR)
    "regression-guard.yml",
    # Advisories bon marche
    "repo-size-advisory.yml",
}


# Workflows dont le clone complet (fetch-depth: 0 SANS filter: blob:none) est
# DELIBERE. Un clone partiel (filter: blob:none) ne checkout pas les blobs ;
# tout workflow qui consomme le contenu des blobs de l'historique complet a
# donc besoin du clone complet par construction, et n'est pas une regression.
# Liste OPT-IN : ajouter un nom ici uniquement apres justification ecrite
# (cf. issue #12385, hygiène de checkout de la série clone partiel #11843).
CHECKOUT_HYGIENE_FULL_HISTORY_WORKFLOWS: set[str] = {
    # gitleaks scanne les BLOBS de l'historique git complet. `filter: blob:none`
    # (clone partiel) ne checkout pas les blobs, donc gitleaks ne verrait rien.
    # Un clone complet est requis par construction.
    "secret-scan.yml",
}


def _parse_on_key(data: dict[str, Any]) -> dict[str, Any] | None:
    """Recupere le bloc `on:` d'un workflow YAML.

    PyYAML normalise la cle `on` en `True` (cle booleenne). On essaie
    les deux conventions.
    """
    on = data.get(True)
    if isinstance(on, dict):
        return on
    on = data.get("on")
    if isinstance(on, dict):
        return on
    return None


def _classify_unfiltered(name: str) -> str:
    """Classifie un workflow unfiltered en 'required' ou 'optional'."""
    if name in REQUIRED_UNFILTERED_WORKFLOWS:
        return "required"
    return "optional"  # nouveau, non audite -> a investiguer


def _scan_checkout_steps(jobs: dict[str, Any]) -> tuple[bool, bool, bool]:
    """Scanner les etapes `actions/checkout` de chaque job.

    Retourne (saw_checkout, fetch_depth_0, blob_none) :
      - saw_checkout : au moins une etape `actions/checkout` est presente ;
      - fetch_depth_0 : cette etape porte `fetch-depth: 0` (clone complet) ;
      - blob_none     : cette etape porte `filter: blob:none` (clone partiel).

    Le parametre `filter` et `fetch-depth` vivent tous deux sous le bloc
    `with:` de l'etape checkout (verifie firsthand sur orphaned-delivery-scan.yml
    et slides-composition-advisory.yml).
    """
    saw_checkout = False
    fetch_depth_0 = False
    blob_none = False
    for job in jobs.values():
        if not isinstance(job, dict):
            continue
        steps = job.get("steps") or []
        for step in steps:
            if not isinstance(step, dict):
                continue
            uses = step.get("uses") or ""
            if not uses.startswith("actions/checkout"):
                continue
            saw_checkout = True
            w = step.get("with") or {}
            fd = w.get("fetch-depth")
            if fd is not None and str(fd) == "0":
                fetch_depth_0 = True
            if str(w.get("filter")) == "blob:none":
                blob_none = True
    return saw_checkout, fetch_depth_0, blob_none


def _checkout_hygiene_fields(
    name: str,
    has_pr_trigger_any: bool,
    fetch_depth_0: bool,
    blob_none: bool,
) -> dict[str, Any]:
    """Determine le verdict hygiene-checkout pour un workflow.

    Criteres cumulatifs (issue #12385) : un workflow est NON CONFORME s'il
      1. se declenche sur `pull_request` / `pull_request_target`, ET
      2. porte `fetch-depth: 0`, ET
      3. ne porte PAS `filter: blob:none`, ET
      4. n'est pas dans CHECKOUT_HYGIENE_FULL_HISTORY_WORKFLOWS.

    Eligible = PR-trigger ET fetch-depth:0 (les machines a clone). Parmi elles :
    blob:none -> conforme ; dans la liste d'exclusion -> exclue ; sinon -> non-conforme.
    """
    eligible = has_pr_trigger_any and fetch_depth_0
    if not eligible:
        reason = "no_pr_trigger" if not has_pr_trigger_any else "no_fetch_depth_zero"
        return {"checkout_hygiene_nonconforming": False, "checkout_hygiene_reason": reason}
    if blob_none:
        return {"checkout_hygiene_nonconforming": False, "checkout_hygiene_reason": "conforming_blob_none"}
    if name in CHECKOUT_HYGIENE_FULL_HISTORY_WORKFLOWS:
        return {"checkout_hygiene_nonconforming": False, "checkout_hygiene_reason": "excluded_full_history"}
    return {"checkout_hygiene_nonconforming": True, "checkout_hygiene_reason": "nonconforming_full_clone"}


def _parse_paths(pr_config: dict[str, Any] | list[Any] | None) -> list[str]:
    """Extrait la liste paths/paths-ignore depuis la config pull_request."""
    if pr_config is None or not isinstance(pr_config, dict):
        return []
    paths = pr_config.get("paths") or []
    paths_ignore = pr_config.get("paths-ignore") or []
    if isinstance(paths, str):
        paths = [paths]
    if isinstance(paths_ignore, str):
        paths_ignore = [paths_ignore]
    return list(paths) + [f"!{p}" for p in paths_ignore]


def audit_workflows(workflows_dir: Path) -> dict[str, Any]:
    """Parcourt `.github/workflows/*.yml` et retourne l'audit complet.

    Returns:
        dict avec :
          - workflows : liste de {name, has_pr_trigger, has_filter,
            paths_count, paths_list, classification}
          - summary : totaux filtered/unfiltered/no-pr-trigger/required-unfiltered
    """
    workflows: list[dict[str, Any]] = []

    for fname in sorted(workflows_dir.iterdir()):
        if fname.suffix not in (".yml", ".yaml"):
            continue

        try:
            content = fname.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            workflows.append(
                {
                    "name": fname.name,
                    "has_pr_trigger": False,
                    "has_filter": False,
                    "paths_count": 0,
                    "paths_list": [],
                    "classification": "unreadable",
                    "error": "cannot read file",
                }
            )
            continue

        try:
            data = yaml.safe_load(content)
        except yaml.YAMLError as e:
            workflows.append(
                {
                    "name": fname.name,
                    "has_pr_trigger": False,
                    "has_filter": False,
                    "paths_count": 0,
                    "paths_list": [],
                    "classification": "unreadable",
                    "error": f"yaml error: {e}",
                }
            )
            continue

        if not isinstance(data, dict):
            continue

        on = _parse_on_key(data)
        pr = on.get("pull_request") if on else None
        pr_target = on.get("pull_request_target") if on else None
        has_pr_trigger_any = pr is not None or pr_target is not None

        # Hygiene de checkout : calculee sur tout workflow portant un
        # checkout, independante de la dimension paths (issue #12385).
        jobs = data.get("jobs") or {}
        saw_checkout, fetch_depth_0, blob_none = _scan_checkout_steps(jobs)
        co = _checkout_hygiene_fields(
            fname.name, has_pr_trigger_any, fetch_depth_0, blob_none
        )
        base = {
            "name": fname.name,
            "has_checkout_step": saw_checkout,
            "has_fetch_depth_0": fetch_depth_0,
            "has_blob_none_filter": blob_none,
            **co,
        }

        if pr is None:
            workflows.append(
                {
                    **base,
                    "has_pr_trigger": False,
                    "has_filter": False,
                    "paths_count": 0,
                    "paths_list": [],
                    "classification": "no_pr_trigger",
                }
            )
            continue

        # pr can be None (= all PRs), dict with filter, dict without filter,
        # or a list of dicts (multiple PR triggers).
        if isinstance(pr, list):
            paths_combined: list[str] = []
            for entry in pr:
                if isinstance(entry, dict):
                    paths_combined.extend(_parse_paths(entry))
            has_filter = len(paths_combined) > 0
            paths_list = paths_combined
        elif isinstance(pr, dict):
            paths_list = _parse_paths(pr)
            has_filter = len(paths_list) > 0
        else:
            # pr is None or scalar -> all PRs, no filter
            has_filter = False
            paths_list = []

        workflows.append(
            {
                **base,
                "has_pr_trigger": True,
                "has_filter": has_filter,
                "paths_count": len(paths_list),
                "paths_list": paths_list,
                "classification": (
                    "filtered"
                    if has_filter
                    else _classify_unfiltered(fname.name)
                ),
            }
        )

    _eligible_reasons = {
        "conforming_blob_none",
        "excluded_full_history",
        "nonconforming_full_clone",
    }
    summary = {
        "total": len(workflows),
        "with_pr_trigger": sum(1 for w in workflows if w["has_pr_trigger"]),
        "filtered": sum(
            1 for w in workflows if w["has_pr_trigger"] and w["has_filter"]
        ),
        "unfiltered": sum(
            1
            for w in workflows
            if w["has_pr_trigger"] and not w["has_filter"]
        ),
        "unfiltered_required": sum(
            1
            for w in workflows
            if w["has_pr_trigger"]
            and not w["has_filter"]
            and w["classification"] == "required"
        ),
        "unfiltered_optional": sum(
            1
            for w in workflows
            if w["has_pr_trigger"]
            and not w["has_filter"]
            and w["classification"] == "optional"
        ),
        "no_pr_trigger": sum(1 for w in workflows if not w["has_pr_trigger"]),
        # Hygiene checkout (issue #12385)
        "checkout_hygiene_machines": sum(
            1 for w in workflows if w["checkout_hygiene_reason"] in _eligible_reasons
        ),
        "checkout_hygiene_conforming": sum(
            1
            for w in workflows
            if w["checkout_hygiene_reason"] == "conforming_blob_none"
        ),
        "checkout_hygiene_excluded": sum(
            1
            for w in workflows
            if w["checkout_hygiene_reason"] == "excluded_full_history"
        ),
        "checkout_hygiene_nonconforming": sum(
            1 for w in workflows if w["checkout_hygiene_nonconforming"]
        ),
    }

    return {
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "workflows_dir": str(workflows_dir),
        "summary": summary,
        "workflows": workflows,
    }


def check_regression(
    current: dict[str, Any], previous: dict[str, Any]
) -> list[dict[str, Any]]:
    """Detecte les ajouts recents sans filtre par rapport a un audit anterieur.

    Returns:
        liste de {name, reason} pour chaque regression detectee.
    """
    previous_filtered = {
        w["name"] for w in previous["workflows"] if w["has_pr_trigger"]
    }
    current_unfiltered = {
        w["name"]
        for w in current["workflows"]
        if w["has_pr_trigger"] and not w["has_filter"]
    }

    regressions: list[dict[str, Any]] = []
    # Nouveaux workflows sans filtre (ni dans la liste required)
    for name in current_unfiltered:
        if name not in previous_filtered and name not in REQUIRED_UNFILTERED_WORKFLOWS:
            regressions.append(
                {
                    "name": name,
                    "reason": "newly_added_unfiltered_optional",
                    "explanation": (
                        f"{name} added since previous audit without paths/paths-ignore filter "
                        f"and not in REQUIRED_UNFILTERED_WORKFLOWS whitelist"
                    ),
                }
            )
    # Workflows qui ont perdu leur filtre
    current_filtered = {
        w["name"]
        for w in current["workflows"]
        if w["has_pr_trigger"] and w["has_filter"]
    }
    for name in previous_filtered:
        if (
            name in current_unfiltered
            and name in REQUIRED_UNFILTERED_WORKFLOWS
        ):
            # Was filtered, now unfiltered-required -> check if was in required list
            # actually this means someone REMOVED the filter from a workflow that
            # wasn't on the whitelist originally. Skip if it's currently required.
            continue
        if name in current_unfiltered and name not in REQUIRED_UNFILTERED_WORKFLOWS:
            # Was filtered, now unfiltered-optional -> filter removed!
            previous_filter_status = next(
                (
                    w
                    for w in previous["workflows"]
                    if w["name"] == name
                ),
                None,
            )
            if previous_filter_status and previous_filter_status.get("has_filter"):
                regressions.append(
                    {
                        "name": name,
                        "reason": "filter_removed",
                        "explanation": (
                            f"{name} previously had a filter but filter was removed "
                            f"(now in unfiltered-optional)"
                        ),
                    }
                )
    return regressions


# ---------------------------------------------------------------------------
# Controle positif hygiene-checkout (issue #12385)
# ---------------------------------------------------------------------------

# Workflows volontairement non conformes (PR trigger + fetch-depth: 0 sans
# blob:none) que le detecteur DOIT flagger. Tout le reste du corpus synthetique
# doit rester conforme/exclu. Un 0 de sortie du detecteur ne suffit pas a
# prouver qu'il a regarde : ce jeu de controle le prouve.
_CHECKOUT_HYGIENE_POSITIVE_CONTROL_EXPECTED = {"bad-clone.yml", "bad-target.yml"}


def _synthetic_checkout_workflows_dir(tmp: Path) -> Path:
    """Cree un repertoire de workflows synthetique pour le controle positif.

    Cinq cas couvrent les criteres cumulatifs :
      1. bad-clone.yml    : pull_request + fetch-depth:0 sans blob:none -> NON CONFORME
      2. good-clone.yml   : pull_request + fetch-depth:0 + blob:none      -> conforme
      3. secret-scan.yml  : pull_request + fetch-depth:0, dans l'exclusion -> exclu
      4. push-only.yml    : push + fetch-depth:0, pas de trigger PR        -> hors scope
      5. bad-target.yml   : pull_request_target + fetch-depth:0 sans blob:none -> NON CONFORME
    """
    wf = tmp / "workflows"
    wf.mkdir(parents=True, exist_ok=True)
    (wf / "bad-clone.yml").write_text(
        """name: Bad Clone
on:
  pull_request:
    branches: [main]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
""",
        encoding="utf-8",
    )
    (wf / "good-clone.yml").write_text(
        """name: Good Clone
on:
  pull_request:
    branches: [main]
    paths: ['**']
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
          filter: blob:none
""",
        encoding="utf-8",
    )
    (wf / "secret-scan.yml").write_text(
        """name: Secret Scan
on:
  pull_request:
    branches: [main]
jobs:
  scan:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
""",
        encoding="utf-8",
    )
    (wf / "push-only.yml").write_text(
        """name: Push Only
on:
  push:
    branches: [main]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
""",
        encoding="utf-8",
    )
    (wf / "bad-target.yml").write_text(
        """name: Bad Target
on:
  pull_request_target:
    branches: [main]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
""",
        encoding="utf-8",
    )
    return wf


def _checkout_hygiene_positive_control() -> dict[str, Any]:
    """Controle positif du detecteur hygiene-checkout.

    Construit un corpus synthetique, lance le vrai detecteur dessus, et
    verifie qu'il flagge EXACTEMENT les workflows volontairement non conformes.
    Ce controle tourne dans la meme invocation que l'audit principal : un
    `checkout_hygiene_nonconforming == 0` ne suffit pas a prouver que le
    detecteur a regarde — ici on prouve qu'il sait reconnaitre un contrevenant.
    """
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        wf = _synthetic_checkout_workflows_dir(Path(tmp))
        audit = audit_workflows(wf)
        detected = {
            w["name"]
            for w in audit["workflows"]
            if w.get("checkout_hygiene_nonconforming")
        }
        expected = _CHECKOUT_HYGIENE_POSITIVE_CONTROL_EXPECTED
        return {
            "ran": True,
            "expected": sorted(expected),
            "detected": sorted(detected),
            "ok": detected == expected,
        }


def write_markdown(audit: dict[str, Any], path: Path) -> None:
    """Ecrit un resume Markdown pour revue humaine."""
    s = audit["summary"]
    lines = [
        f"# Audit workflow path-filters",
        f"",
        f"**Generated** : {audit['generated_at']}",
        f"**Workflows dir** : `{audit['workflows_dir']}`",
        f"",
        f"## Summary",
        f"",
        f"| Metrique | Valeur |",
        f"|---|---|",
        f"| Total workflows | {s['total']} |",
        f"| Avec `pull_request` trigger | {s['with_pr_trigger']} |",
        f"| **Avec filtre paths/paths-ignore** | **{s['filtered']}** |",
        f"| Sans filtre | {s['unfiltered']} |",
        f"| - dont required (gates/advisories) | {s['unfiltered_required']} |",
        f"| - dont optional (a investiguer) | {s['unfiltered_optional']} |",
        f"| Sans `pull_request` trigger | {s['no_pr_trigger']} |",
        f"",
        f"## Sans filtre `paths`/`paths-ignore`",
        f"",
    ]

    unfiltered_required = [
        w for w in audit["workflows"] if w["classification"] == "required"
    ]
    unfiltered_optional = [
        w for w in audit["workflows"] if w["classification"] == "optional"
    ]

    if unfiltered_required:
        lines.extend(
            [
                f"### Required (gates/advisories - non-concerne par l'audit)",
                f"",
            ]
        )
        for w in unfiltered_required:
            lines.append(f"- `{w['name']}`")
        lines.append("")

    if unfiltered_optional:
        lines.extend(
            [
                f"### Optional (a investiguer - devrait avoir un filtre)",
                f"",
            ]
        )
        for w in unfiltered_optional:
            lines.append(f"- `{w['name']}`")
        lines.append("")

    lines.extend(
        [
            f"## Avec filtre `paths`/`paths-ignore`",
            f"",
            f"| Workflow | paths_count |",
            f"|---|---|",
        ]
    )
    for w in audit["workflows"]:
        if w["classification"] == "filtered":
            lines.append(f"| `{w['name']}` | {w['paths_count']} |")
    lines.append("")

    # Hygiene de checkout (issue #12385) — serialize la serie clone partiel
    s = audit["summary"]
    lines.extend(
        [
            f"## Hygiene de checkout (fetch-depth: 0 sans filter: blob:none)",
            f"",
            f"| Metrique | Valeur |",
            f"|---|---|",
            f"| Workflows PR clonant sans clone partiel | **{s.get('checkout_hygiene_nonconforming', 0)}** |",
            f"| - conformes (blob:none present) | {s.get('checkout_hygiene_conforming', 0)} |",
            f"| - exclus (clone complet necessaire) | {s.get('checkout_hygiene_excluded', 0)} |",
            f"| Machines a clone (PR trigger + fetch-depth: 0) | {s.get('checkout_hygiene_machines', 0)} |",
            f"",
            f"### Non conformes (a corriger en clone partiel)",
            f"",
        ]
    )
    nonconforming = [
        w for w in audit["workflows"] if w.get("checkout_hygiene_nonconforming")
    ]
    if nonconforming:
        for w in sorted(nonconforming, key=lambda x: x["name"]):
            lines.append(f"- `{w['name']}`")
    else:
        lines.append("_(aucun)_")
    lines.append("")

    pc = audit.get("checkout_hygiene_positive_control")
    if pc:
        lines.extend(
            [
                f"### Controle positif hygiene-checkout",
                f"",
                f"- Ran : `{pc['ran']}`",
                f"- Attendu : `{', '.join(pc['expected'])}`",
                f"- Detecte : `{', '.join(pc['detected']) or '(vide)'}`",
                f"- **{('OK' if pc['ok'] else 'FAIL')}**",
                f"",
            ]
        )

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--workflows-dir",
        default=".github/workflows",
        help="Repertoire des workflows GitHub Actions (default: .github/workflows)",
    )
    parser.add_argument(
        "--audit-dir",
        default="docs/audit/workflow-path-filters",
        help="Repertoire de sortie pour les rapports (default: docs/audit/workflow-path-filters)",
    )
    parser.add_argument(
        "--check-regression",
        metavar="PREVIOUS_JSON",
        help="Verifie les regressions contre un audit anterieur (chemin JSON)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Mode silencieux (sortie console minimale)",
    )

    args = parser.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[2]
    workflows_dir = repo_root / args.workflows_dir
    audit_dir = repo_root / args.audit_dir

    if not workflows_dir.is_dir():
        print(f"ERROR: workflows dir not found: {workflows_dir}", file=sys.stderr)
        return 1

    audit = audit_workflows(workflows_dir)

    # Controle positif hygiene-checkout : tourne dans la MEME invocation.
    # Un 0 de sortie ne suffit pas — on prouve ici que le detecteur sait
    # reconnaitre un contrevenant synthetique (issue #12385).
    audit["checkout_hygiene_positive_control"] = _checkout_hygiene_positive_control()

    # Hash SHA-256 du contenu audit pour nommage deterministe
    audit_json = json.dumps(audit, sort_keys=True)
    sha = hashlib.sha256(audit_json.encode("utf-8")).hexdigest()[:12]
    timestamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    json_path = audit_dir / f"audit-{timestamp}-{sha}.json"
    md_path = audit_dir / f"audit-{timestamp}-{sha}.md"
    latest_json = audit_dir / "latest.json"
    latest_md = audit_dir / "latest.md"

    audit_dir.mkdir(parents=True, exist_ok=True)
    json_path.write_text(
        json.dumps(audit, indent=2, sort_keys=True), encoding="utf-8"
    )
    write_markdown(audit, md_path)
    latest_json.write_text(
        json.dumps(audit, indent=2, sort_keys=True), encoding="utf-8"
    )
    latest_md.write_text(md_path.read_text(encoding="utf-8"), encoding="utf-8")

    s = audit["summary"]
    if not args.quiet:
        print(f"Audit completed: {s['with_pr_trigger']} PR-triggered workflows")
        print(f"  Filtered: {s['filtered']}")
        print(f"  Unfiltered: {s['unfiltered']} (required: {s['unfiltered_required']}, optional: {s['unfiltered_optional']})")
        pc = audit["checkout_hygiene_positive_control"]
        print(f"  Checkout hygiene: {s['checkout_hygiene_nonconforming']} "
              f"nonconforming / {s['checkout_hygiene_machines']} clone machines "
              f"(conforming: {s['checkout_hygiene_conforming']}, "
              f"excluded: {s['checkout_hygiene_excluded']})")
        print(f"  Positive control: {'OK' if pc['ok'] else 'FAIL'} "
              f"(expected {sorted(pc['expected'])}, detected {sorted(pc['detected'])})")
        print(f"  Reports:")
        print(f"    JSON: {json_path}")
        print(f"    MD:   {md_path}")
        print(f"    Latest: {latest_json}, {latest_md}")

    # Positive control failing = le detecteur checkout-hygiene est casse,
    # donc toute conclusion "0 nonconforme" serait fausse. Warn loud et
    # structuré (advisory : ne change PAS le code retour, cf. issue #12385).
    if not audit["checkout_hygiene_positive_control"]["ok"]:
        print(
            "WARNING: checkout-hygiene positive control FAILED — the detector "
            "cannot recognize a synthetic offender, so any '0 nonconforming' "
            "conclusion would be untrustworthy.",
            file=sys.stderr,
        )

    # Regression check
    rc = 0
    if args.check_regression:
        prev_path = Path(args.check_regression)
        if not prev_path.is_file():
            print(
                f"ERROR: previous audit file not found: {prev_path}",
                file=sys.stderr,
            )
            return 1
        previous = json.loads(prev_path.read_text(encoding="utf-8"))
        regressions = check_regression(audit, previous)
        if regressions:
            rc = 1
            print(f"\nREGRESSIONS DETECTED: {len(regressions)}", file=sys.stderr)
            for reg in regressions:
                print(
                    f"  - [{reg['reason']}] {reg['explanation']}",
                    file=sys.stderr,
                )
        else:
            if not args.quiet:
                print("\nNo regressions detected vs previous audit.")

    return rc


if __name__ == "__main__":
    sys.exit(main())
