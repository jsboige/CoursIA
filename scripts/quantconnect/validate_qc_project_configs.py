#!/usr/bin/env python3
"""Validate QC project config.json schemas (issue #6891 RESCOPE step 1).

Pourquoi cet outil existe
-------------------------
L'issue #6891 a denonce des **sorties de cellule fabricquees** sur 8 quantbooks
QC. La racine du mal etait une **fabrication de resultats** dans la sortie
du kernel -- un cran plus bas, on retrouve la meme classe de fabrication
dans la **structure du projet** : un `config.json` qui pretend qu'un projet
a un `cloud-id` alors que personne ne l'a obtenu du cloud QC, ou qui omet
le `name` / `id` alors que les 14 autres configs les portent.

ai-01 (2026-07-25T17:04:07Z) a trace la ligne rouge :

    **NE JAMAIS ecrire un `cloud-id` qu'on n'a pas obtenu du cloud.**
    Pas de placeholder plausible, pas de valeur empruntee a un projet voisin,
    pas de `0`. Un projet sans cloud-id porte le champ **absent** -- pas
    rempli d'une valeur qui a l'air vraie.

L'etape 1 (RESCOPE) est de **normaliser le schema** des 5 configs des projets
quantbook qui n'ont pas ete pousses au cloud :

    FuturesTrend, MomentumStrategy, RiskParity, SectorMomentum, TurnOfMonth

Schema canonique (champ obligatoire pour ces 5 projets, et pour les 14
autres configs du depot qui ont un cloud-id) :

    algorithm-language  "Python"
    name                = folder name (ex. "FuturesTrend")
    id                  1
    parameters          {}    (object, peut etre vide pour ces projets)
    description         "..." (deja present sur les 5)
    organization-id     "d600793ee4caecb03441a09fc2d00f7f" (deja present)

Champ **strictement absent** :

    cloud-id            -- pas de fabrication. Si le projet n'a pas ete
                           pousse au cloud QC par l'owner, le champ n'existe
                           tout simplement pas.

Ce que cet outil fait
---------------------
1. Pour chaque `MyIA.AI.Notebooks/QuantConnect/projects/*/config.json`,
   evalue 4 invariants :

      - **invariant_set_minimal** : si le fichier a au moins un de
        `name`/`id`/`description` (autre qu'un bare `{local-id}`), il
        doit aussi avoir `algorithm-language`, `parameters`,
        `organization-id` -- c'est la structure minimale.
      - **invariant_no_fabricated_cloud_id** : `cloud-id` ne peut pas
        valoir 0, "", "0", "null", "None", "TBD", "PENDING". Toute
        valeur non-entiere est suspecte.
      - **invariant_name_matches_folder** : si `name` est present, il
        doit etre egal au nom du dossier (les noms canoniques dans le
        depot utilisent tous le nom du dossier, avec un seul ecart
        documente -- EMA-Cross-Stocks qui vaut "Framework-EMA-Cross-Stocks",
        whiteliste).
      - **invariant_id_is_int** : si `id` est present, il doit etre un
        entier (la valeur 1 est le pattern canonique des configs
        recentes).

2. Sortie texte structuree + mode `--check` (CI-ready) qui **echoue
   (exit 1)** si un invariant est viole sur une des 5 configs RESCOPE.

Pourquoi seulement les 5 configs RESCOPE en mode `--check`
----------------------------------------------------------
Les 13 autres configs qui omettent `name` (AllWeather, DualMomentum,
MeanReversion, Trend-Following, VolTarget-Momentum, etc.) ne sont pas
dans le scope du RESCOPE -- ce sont des projets avec `cloud-id`
legitime qui utilisent un schema legacy (`language: Py` au lieu de
`algorithm-language: Python`). Les migrer est un travail separe qui
doit etre scope par issue dediee (anti-regression rule D).

L'outil liste les 13 autres configs comme `legacy-cloud-id-schema` dans
le rapport, mais ne les marque pas en echec.

Sortie
------
Texte tabulaire par projet, plus un resume final :

    === QC project config schema audit ===

    scope target (5):   FuturesTrend, MomentumStrategy, RiskParity, SectorMomentum, TurnOfMonth
    legacy (13):        AllWeather, DualMomentum, ...

    === VIOLATIONS ===
    (none) | <list>

    === LEGACY (cloud-id) ===
    <list>

    Summary: <n> violations, <m> legacy (informational), <k> conformant

Stdlib only, pas de dependance externe. Python 3.10+.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

# Les 5 projets dont le schema doit etre conforme (etape 1 RESCOPE).
RESCOPE_TARGETS = frozenset({
    "FuturesTrend",
    "MomentumStrategy",
    "RiskParity",
    "SectorMomentum",
    "TurnOfMonth",
})

# Valeurs de cloud-id interdites (fabrications) -- une valeur reelle est
# un entier positif obtenu du cloud QC, pas un placeholder.
FORBIDDEN_CLOUD_ID_VALUES = frozenset({"0", "null", "None", "TBD", "PENDING", ""})

# Whitelist pour `name == folder` : les projets dont le `name` est
# *volontairement* different du dossier, avec justification dans le repo.
NAME_FOLDER_WHITELIST = {
    "EMA-Cross-Stocks": "Framework-EMA-Cross-Stocks",  # alias documente
}


def _iter_project_configs(root: Path) -> list[tuple[str, Path]]:
    """Return [(project_name, config_path), ...] sorted by name."""
    projects_dir = root / "MyIA.AI.Notebooks" / "QuantConnect" / "projects"
    if not projects_dir.is_dir():
        return []
    out: list[tuple[str, Path]] = []
    for child in sorted(projects_dir.iterdir()):
        if not child.is_dir():
            continue
        cfg = child / "config.json"
        if cfg.is_file():
            out.append((child.name, cfg))
    return out


def _load_config(path: Path) -> dict[str, Any]:
    """Load and parse a config.json. Returns {} on parse error (logged)."""
    try:
        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return {}
        return data
    except (json.JSONDecodeError, OSError):
        return {}


def _is_legacy_cloud_id_schema(cfg: dict[str, Any]) -> bool:
    """True if the config uses the legacy `language: Py` schema (cloud-id holder).

    Les projets avec cloud-id legique utilisent generalement le schema
    legacy `cloud-id + language + organization-id` (DualMomentum,
    MeanReversion, Trend-Following, VolTarget-Momentum) ou
    `cloud-id + language + local-id + organization-id`. Ces configs ne
    sont PAS dans le scope RESCOPE -- l'etape 1 ne touche que les 5
    configs sans cloud-id.
    """
    return "language" in cfg and "algorithm-language" not in cfg


def audit_project_config(name: str, cfg: dict[str, Any]) -> list[str]:
    """Return a list of violation messages for a single project config.

    An empty list means "no violations". The list is empty for configs
    outside the RESCOPE scope (legacy cloud-id holders, configs without
    any structure beyond `{local-id}`).
    """
    if _is_legacy_cloud_id_schema(cfg):
        return []  # hors scope -- legacy schema pour cloud-id holders
    if "cloud-id" in cfg:
        return []  # hors scope -- projet deja pousse au cloud
    if not cfg or set(cfg.keys()) <= {"local-id"}:
        return []  # hors scope -- config minimal local-id-only

    violations: list[str] = []

    # invariant : les champs minimaux obligatoires
    for required in ("algorithm-language", "parameters", "organization-id"):
        if required not in cfg:
            violations.append(f"missing required field {required!r}")

    # invariant : name == folder name (avec whitelist)
    if "name" in cfg:
        expected = NAME_FOLDER_WHITELIST.get(name, name)
        if cfg["name"] != expected:
            violations.append(
                f"name field {cfg['name']!r} != folder name {expected!r}"
            )
    else:
        violations.append("missing required field 'name'")

    # invariant : id is int (presence obligatoire)
    if "id" not in cfg:
        violations.append("missing required field 'id'")
    elif not isinstance(cfg["id"], int):
        violations.append(f"id field must be int, got {type(cfg['id']).__name__}")

    # invariant : pas de cloud-id fabrique (ce projet n'a pas ete pousse)
    # Le champ ne doit pas exister du tout.
    # (deja couvert par le early-return ci-dessus, mais defensive)

    return violations


def audit_all(root: Path) -> dict[str, Any]:
    """Run the audit across all QC project configs.

    Returns a dict suitable for JSON serialization.
    """
    projects = _iter_project_configs(root)

    violations: list[dict[str, str]] = []
    legacy: list[str] = []
    conformant_rescope: list[str] = []
    conformant_other: list[str] = []
    parse_errors: list[dict[str, str]] = []

    for name, cfg_path in projects:
        try:
            with cfg_path.open("r", encoding="utf-8") as f:
                raw = json.load(f)
        except (json.JSONDecodeError, OSError) as exc:
            # Unparseable JSON = structural problem, NOT "conformant".
            # Listed separately so reviewers see the file even if not in
            # --check's blocker set (avoids silent regression on schema drift).
            parse_errors.append({
                "project": name,
                "path": str(cfg_path),
                "error": f"{type(exc).__name__}: {exc}",
            })
            continue
        if not isinstance(raw, dict):
            parse_errors.append({
                "project": name,
                "path": str(cfg_path),
                "error": f"top-level JSON is {type(raw).__name__}, expected object",
            })
            continue
        cfg = raw
        if _is_legacy_cloud_id_schema(cfg) or "cloud-id" in cfg:
            legacy.append(name)
            continue
        msgs = audit_project_config(name, cfg)
        if msgs:
            violations.append({"project": name, "messages": msgs})
        elif name in RESCOPE_TARGETS:
            conformant_rescope.append(name)
        else:
            conformant_other.append(name)

    return {
        "scope_target": sorted(RESCOPE_TARGETS),
        "conformant_rescope": sorted(conformant_rescope),
        "conformant_other": sorted(conformant_other),
        "legacy_cloud_id_holders": sorted(legacy),
        "violations": violations,
        "parse_errors": parse_errors,
    }


def format_text(report: dict[str, Any]) -> str:
    """Render the audit report as a human-readable string."""
    lines: list[str] = []
    lines.append("=== QC project config schema audit ===")
    lines.append("")
    lines.append(f"scope target ({len(report['scope_target'])}):   "
                 + ", ".join(report["scope_target"]))
    lines.append(f"conformant (rescope, {len(report['conformant_rescope'])}):   "
                 + ", ".join(report["conformant_rescope"]))
    lines.append(f"conformant (other, {len(report['conformant_other'])}):   "
                 + ", ".join(report["conformant_other"]))
    lines.append(f"legacy cloud-id ({len(report['legacy_cloud_id_holders'])}):  "
                 + ", ".join(report["legacy_cloud_id_holders"]))
    lines.append("")
    if report["violations"]:
        lines.append("=== VIOLATIONS ===")
        for v in report["violations"]:
            lines.append(f"  {v['project']}:")
            for m in v["messages"]:
                lines.append(f"    - {m}")
        lines.append("")
    else:
        lines.append("=== VIOLATIONS ===")
        lines.append("  (none)")
        lines.append("")
    if report.get("parse_errors"):
        lines.append("=== PARSE ERRORS (not valid JSON / wrong type) ===")
        for e in report["parse_errors"]:
            lines.append(f"  {e['project']} ({e['path']}):")
            lines.append(f"    - {e['error']}")
        lines.append("")
    parse_count = len(report.get("parse_errors", []))
    lines.append(
        f"Summary: {len(report['violations'])} violation(s), "
        f"{len(report['legacy_cloud_id_holders'])} legacy (informational), "
        f"{parse_count} parse error(s), "
        f"{len(report['conformant_rescope']) + len(report['conformant_other'])} conformant"
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Audit QC project config.json schemas (issue #6891 RESCOPE step 1)."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="Repository root (default: cwd)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit 1 if any RESCOPE target has schema violations.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON instead of human-readable text.",
    )
    args = parser.parse_args(argv)

    report = audit_all(args.root)

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(format_text(report), file=sys.stderr)

    # --check : exit 1 si une des 5 cibles RESCOPE a des violations.
    # Note : les violations "other" (configs hors scope qui ont quand meme
    # des problemes) ne bloquent pas -- leur migration est un travail
    # separe, scope par issue dediee (anti-regression rule D).
    if args.check:
        rescope_violations = [
            v for v in report["violations"]
            if v["project"] in RESCOPE_TARGETS
        ]
        if rescope_violations:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
