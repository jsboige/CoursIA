#!/usr/bin/env python3
"""QuantBook unexecuted-cell audit script (Issue #6891 follow-up).

Pourquoi cet outil existe
-------------------------
L'incident fondateur #6891 a revele 8 quantbook.ipynb avec des sorties
FABRIQUEES (PNG 1x1 de 70 octets + tableaux 'Row N'). Le sweep initial
(#7447 + #7462) a strapppe ces sorties (Stop&Repair compliant) et les a
balisees d'un markdown d'avertissement ``> Sortie strippee ... Re-execution
required``. Mais le balayage a laisse dans l'ombre un **bug-class plus
large** : des quantbooks ont des **cellules code sans execution_count**
(`ec=None`, `outputs=[]`) sans aucune annotation de strippage -- donc
pre-existantes a #6891, jamais signalees, potentiellement encore plus
toxiques (un etudiant ne sait pas que la sortie manque).

L'audit initial etait cible sur la **degenerescence** (figures vides via
`detect_blank_figures.py` + ASCII via `detect_ascii_workaround.py`). Cet
outil couvre l'AUTRE moitie : **l'absence d'execution**. Il DETECTE, il
ne CORRIGE PAS -- la correction = re-executer dans le vrai environnement
(QC Cloud research kernel pour `QuantBook()`, kernel local pour matplotlib)
puis committer la vraie sortie. Stop&Repair, JAMAIS maquiller (regle
secrets-hygiene 6 + sota-not-workaround Prong-A).

Fenetre d'analyse : le CONTENU, pas le chemin
---------------------------------------------
Est un quantbook **tout notebook dont au moins une cellule code instancie
``QuantBook()``** -- c'est ce dont il a besoin (le runtime research QC Cloud)
qui le definit, pas ou il vit ni comment il s'appelle. La fenetre d'origine
etait ``projects/*/quantbook.ipynb``, soit un chemin ET un basename : deux
proxys de la vraie raison. ``--scope projects`` conserve cette ancienne
fenetre pour comparaison ; ``--scope repo`` (defaut) est un sur-ensemble
strict qui scanne les quantbooks canoniques d'abord (ils gardent leur
cross-reference ``config.json``) puis balaye l'arbre par contenu, sans jamais
rescanner ni reclassifier une entree deja vue.

Ce qui est classifie (DETERMINISTE)
-----------------------------------
Pour chaque quantbook ainsi identifie :

  - **HEALTHY**              -- 0 cellule code sans ``execution_count`` ni sortie.
  - **STOP_REPAIR_STRIPPED** -- >=1 cellule code unexec ET >=1 cellule markdown
                                contenant ``Sortie strippee`` / ``FABRICATED``.
                                Deja signalee (scope #6891 fabrication), en attente de re-exec.
  - **STOP_REPAIR_UNEXEC**   -- >=1 cellule code unexec ET >=1 cellule markdown
                                contenant le marqueur dedie ``QC-UNEXEC-TRIAGED``
                                (issue #7575). Bug-class DISTINCT de #6891 : les
                                cellules n'ont JAMAIS ete executees (ce ne sont PAS
                                des sorties fabriquees/stripees). Triees et suivies,
                                en attente d'une re-exec gated (QC Cloud).
  - **PREEXISTING_UNEXEC**   -- >=1 cellule code unexec SANS marqueur (ni strip ni
                                unexec). Nouvelle occurrence non encore triee --
                                celle que ``--check`` flagge en CI.

Le verdict est **conservatif** : toute cellule code **non vide** sans
``execution_count`` ni sortie est attrapee, quel qu'en soit le contenu. Une
cellule qui ne contient qu'un ``def`` ou un helper est donc signalee comme
les autres -- c'est voulu (regle C.2 : un notebook se commite execute de bout
en bout), et le markdown contextuel ne l'en exempte pas : ``_has_strip_marker``
et ``_has_unexec_marker`` **routent** entre les classes STOP_REPAIR_*, ils ne
produisent jamais HEALTHY.

Seul faux positif ecarte : les **cellules vides**, qui satisfont le predicat
par construction sans rien avoir a executer.

Cross-reference avec ``config.json``
------------------------------------
Chaque projet porte un ``config.json`` avec ``cloud-id``. L'outil lit ce
fichier et reporte le statut du cloud-id :
  - **ALIVE**     -- le cloud-id est numerique >0 (pas verifie live via MCP ici).
  - **MISSING**   -- pas de ``config.json`` ou pas de ``cloud-id``.
  - **DEAD**      -- ``cloud-id`` == 0 (placeholder obsolete, signale dans
                     ``quantbooks_execution_status.md`` 2026-05-04).

La verification live (MCP `qc-mcp-lite` `read_project`) est laissee a un
audit ulterieur -- cet outil est **hermetic** (lecture disque seule, aucun
appel reseau) pour rester CPU-only et CI-friendly.

Usage
-----
    python audit_quantbooks_unexec.py                        # tout le depot (par contenu)
    python audit_quantbooks_unexec.py --scope projects       # ancienne fenetre (chemin)
    python audit_quantbooks_unexec.py --project DualMomentum  # un seul projet canonique
    python audit_quantbooks_unexec.py --json                 # sortie machine
    python audit_quantbooks_unexec.py --check                # exit 1 si PREEXISTING_UNEXEC
    python audit_quantbooks_unexec.py --md report.md         # rapport markdown

Exit codes
----------
    0 -- aucun PREEXISTING_UNEXEC (mode non --check) ou succes
    1 -- au moins un PREEXISTING_UNEXEC (--check seulement)
    2 -- erreur (path introuvable, JSON invalide)

Voir aussi
----------
- `detect_blank_figures.py` (#3801 Prong-A, sweep dimension/taille)
- `detect_ascii_workaround.py` (#3801 Prong-A, sweep ASCII)
- `.claude/rules/sota-not-workaround.md` -- vrai outil, pas workaround
- `.claude/rules/secrets-hygiene.md` regle 6 -- Stop&Repair
- #6891 -- incident fondateur (8 quantbook.ipynb QC blank-PNG)
- #7447 + #7462 -- sweep strip (Side A), marqueur Stop&Repair
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


# Mots-cles qui marquent un notebook comme deja signale Stop&Repair (body #6891).
_STRIP_MARKER = re.compile(r"(sortie\s+stripp[e\xe9]e|FABRICATED|blank[\s\-]?PNG)", re.IGNORECASE)

# Marqueur dedie au bug-class #7575 (cellules JAMAIS executees -- distinct de #6891
# qui est des sorties FABRIQUEES puis stripees). Le tag HTML ``QC-UNEXEC-TRIAGED``
# est deliberement unique et non-ambigu : il ne peut pas etre confondu avec le
# marqueur #6891, et ajouter le marqueur sur un quantbook #7575 n'est donc PAS du
# gaming du detecteur (les deux bug-classes ont deux marqueurs distincts).
_UNEXEC_MARKER = re.compile(r"QC-UNEXEC-TRIAGED", re.IGNORECASE)

# Ce qui fait d'un notebook un "quantbook" est ce dont il a BESOIN, pas ou il
# vit ni comment il s'appelle : ``QuantBook()`` n'existe que dans le runtime
# research de QC Cloud. La fenetre d'origine etait ``projects/*/quantbook.ipynb``
# -- un chemin ET un basename -- alors que la pathologie decrite par #7575
# (cellules code jamais executees faute de ce runtime) est une propriete du
# CONTENU. Neuf notebooks la portaient hors fenetre (ESGF-2026/lean-workspace,
# QuantConnect/research, partner-course), donc absents de tout rapport : le
# ``HEALTHY (28)`` se lisait comme un etat de sante global alors qu'il ne
# couvrait qu'un repertoire. Meme predicat que ``validate_pr_notebooks``
# (QUANTBOOK_PATTERN, carve-out H.3) et ``check_cost_metadata`` afin que les
# trois outils repondent la meme chose a "qu'est-ce qu'un notebook QC".
# Voir #7575, #8598.
_QUANTBOOK_PATTERN = re.compile(r"QuantBook\(\)|self\.QuantBook")


def _is_code(cell: dict) -> bool:
    return cell.get("cell_type") == "code"


def _source_text(cell: dict) -> str:
    """Source d'une cellule en texte, que nbformat la stocke en str ou en list."""
    src = cell.get("source", "")
    if isinstance(src, list):
        src = "".join(src)
    return src


def _is_unexecuted_code(cell: dict) -> bool:
    """Cellule code NON VIDE sans execution_count ET sans outputs = JAMAIS executee.

    La clause "non vide" n'est pas cosmetique : une cellule code vide satisfait
    ``ec is None and outputs == []`` par construction -- il n'y a rien a executer,
    donc rien a signaler. Sans ce garde-fou, ``--check`` echoue en CI sur un
    notebook dont les seules cellules "unexec" sont vides, et la seule
    remediation possible serait de les supprimer : un faux positif qui pousse a
    modifier un notebook sain (mesure sur le depot : 1 notebook, 2 cellules).
    """
    if not _is_code(cell):
        return False
    if not _source_text(cell).strip():
        return False
    ec = cell.get("execution_count")
    outs = cell.get("outputs") or []
    return ec is None and len(outs) == 0


def _has_strip_marker(nb: dict) -> bool:
    """Au moins une cellule markdown contient le marqueur Stop&Repair."""
    for c in nb.get("cells", []):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        if _STRIP_MARKER.search(src or ""):
            return True
    return False


def _has_unexec_marker(nb: dict) -> bool:
    """Au moins une cellule markdown contient le marqueur #7575 (unexec triaged)."""
    for c in nb.get("cells", []):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        if _UNEXEC_MARKER.search(src or ""):
            return True
    return False


def _uses_quantbook(nb: dict) -> bool:
    """Au moins une cellule CODE instancie ``QuantBook()`` / ``self.QuantBook``.

    Cellules code seulement : un tutoriel qui *parle* de QuantBook en markdown
    n'a pas besoin du runtime QC Cloud et n'entre donc pas dans la fenetre.
    """
    for c in nb.get("cells", []):
        if not _is_code(c):
            continue
        src = c.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        if _QUANTBOOK_PATTERN.search(src or ""):
            return True
    return False


def _kernel(nb: dict) -> str:
    return nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")


def _config_status(project_dir: Path) -> dict:
    """Lit ``config.json`` du projet et rapporte le statut cloud-id.

    Returns: ``{"has_config": bool, "cloud_id": int|None, "status": str}``
    status in {"ALIVE", "MISSING", "DEAD"}.
    """
    cfg_path = project_dir / "config.json"
    if not cfg_path.exists():
        return {"has_config": False, "cloud_id": None, "status": "MISSING"}
    try:
        with open(cfg_path, encoding="utf-8") as f:
            cfg = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"has_config": True, "cloud_id": None, "status": "MISSING", "error": str(exc)}
    cid = cfg.get("cloud-id")
    if not isinstance(cid, int):
        return {"has_config": True, "cloud_id": None, "status": "MISSING"}
    if cid <= 0:
        return {"has_config": True, "cloud_id": cid, "status": "DEAD"}
    return {"has_config": True, "cloud_id": cid, "status": "ALIVE"}


def scan_notebook(path: Path) -> dict:
    """Return result dict for one quantbook: classification + counts + config."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "path": str(path),
            "error": str(exc),
            "kernel": "?",
            "code_total": 0,
            "code_executed": 0,
            "code_unexecuted": 0,
            "strip_marker": False,
            "unexec_marker": False,
            "classification": "ERROR",
            "config": {"has_config": False, "cloud_id": None, "status": "MISSING"},
        }

    code_total = code_executed = code_unexecuted = 0
    unexecuted_indexes = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if not _is_code(cell):
            continue
        code_total += 1
        if _is_unexecuted_code(cell):
            code_unexecuted += 1
            unexecuted_indexes.append(ci)
        else:
            code_executed += 1

    strip_marker = _has_strip_marker(nb)
    unexec_marker = _has_unexec_marker(nb)

    if code_unexecuted == 0:
        classification = "HEALTHY"
    elif strip_marker:
        classification = "STOP_REPAIR_STRIPPED"
    elif unexec_marker:
        classification = "STOP_REPAIR_UNEXEC"
    else:
        classification = "PREEXISTING_UNEXEC"

    return {
        "path": str(path),
        "kernel": _kernel(nb),
        "code_total": code_total,
        "code_executed": code_executed,
        "code_unexecuted": code_unexecuted,
        "unexecuted_indexes": unexecuted_indexes,
        "strip_marker": strip_marker,
        "unexec_marker": unexec_marker,
        "classification": classification,
        "config": _config_status(path.parent),
        "error": None,
    }


def scan_projects(quant_root: Path) -> list[dict]:
    """Scan every ``*/quantbook.ipynb`` under ``quant_root``."""
    if not quant_root.exists():
        raise FileNotFoundError(f"QuantConnect projects root not found: {quant_root}")
    results = []
    for nb in sorted(quant_root.glob("*/quantbook.ipynb")):
        results.append(scan_notebook(nb))
    return results


def scan_repo(notebooks_root: Path, quant_root: Path) -> list[dict]:
    """Scan tout notebook qui INSTANCIE ``QuantBook()``, ou qu'il vive.

    Sur-ensemble strict de :func:`scan_projects` : les quantbooks canoniques de
    ``quant_root`` sont scannes d'abord (ils conservent leur cross-reference
    ``config.json``), puis le reste de l'arbre est balaye par contenu. Un
    notebook deja vu n'est pas rescanne, donc aucune entree existante n'est
    reclassifiee par l'elargissement.

    ``notebooks_root`` absent n'est pas une erreur ici : le scan canonique est
    rendu seul (rien a elargir). Un chemin errone passe explicitement en
    ``--notebooks-root`` est rejete par :func:`main` (exit 2).
    """
    results = []
    seen: set[Path] = set()
    if quant_root.exists():
        for nb in sorted(quant_root.glob("*/quantbook.ipynb")):
            results.append(scan_notebook(nb))
            seen.add(nb.resolve())

    if not notebooks_root.exists():
        return results

    for nb in sorted(notebooks_root.rglob("*.ipynb")):
        resolved = nb.resolve()
        if resolved in seen:
            continue
        if ".ipynb_checkpoints" in nb.parts:
            continue
        try:
            with open(nb, encoding="utf-8") as f:
                doc = json.load(f)
        except (OSError, json.JSONDecodeError):
            continue  # illisible : hors perimetre de cet audit (pas un quantbook prouve)
        if not _uses_quantbook(doc):
            continue
        results.append(scan_notebook(nb))
        seen.add(resolved)

    return results


# -- reporting --

def _short(path: str, root: Path) -> str:
    """Make path relative to ``root`` for compact reporting."""
    try:
        return str(Path(path).resolve().relative_to(root.resolve()))
    except ValueError:
        return path


def human_report(results: list[dict], root: Path) -> str:
    n_total = len(results)
    by_class: dict[str, list[dict]] = {"HEALTHY": [], "STOP_REPAIR_STRIPPED": [],
                                       "STOP_REPAIR_UNEXEC": [], "PREEXISTING_UNEXEC": [],
                                       "ERROR": []}
    for r in results:
        by_class.setdefault(r["classification"], []).append(r)

    lines = [
        f"QuantBooks scanned   : {n_total}",
        f"  HEALTHY              : {len(by_class['HEALTHY'])}",
        f"  STOP_REPAIR_STRIPPED : {len(by_class['STOP_REPAIR_STRIPPED'])}",
        f"  STOP_REPAIR_UNEXEC   : {len(by_class['STOP_REPAIR_UNEXEC'])}",
        f"  PREEXISTING_UNEXEC   : {len(by_class['PREEXISTING_UNEXEC'])}",
        f"  ERROR                : {len(by_class['ERROR'])}",
        "",
    ]

    if by_class["PREEXISTING_UNEXEC"]:
        lines.append("## PREEXISTING_UNEXEC -- bug-class NOT in body #6891 (needs issue)")
        lines.append("")
        for r in sorted(by_class["PREEXISTING_UNEXEC"], key=lambda x: x["path"]):
            short = _short(r["path"], root)
            cfg = r["config"]
            cfg_str = f"cloud-id={cfg['cloud_id']} [{cfg['status']}]" if cfg["has_config"] else "no config.json"
            lines.append(
                f"  - {short}  kernel={r['kernel']}  unexec={r['code_unexecuted']}/{r['code_total']}  {cfg_str}"
            )
        lines.append("")

    if by_class["STOP_REPAIR_STRIPPED"]:
        lines.append("## STOP_REPAIR_STRIPPED -- body #6891 scope (fabricated outputs stripped), awaits re-execution")
        lines.append("")
        for r in sorted(by_class["STOP_REPAIR_STRIPPED"], key=lambda x: x["path"]):
            short = _short(r["path"], root)
            cfg = r["config"]
            cfg_str = f"cloud-id={cfg['cloud_id']} [{cfg['status']}]" if cfg["has_config"] else "no config.json"
            lines.append(
                f"  - {short}  kernel={r['kernel']}  unexec={r['code_unexecuted']}/{r['code_total']}  {cfg_str}"
            )
        lines.append("")

    if by_class["STOP_REPAIR_UNEXEC"]:
        lines.append("## STOP_REPAIR_UNEXEC -- issue #7575 scope (cells NEVER executed, distinct from #6891), triaged + marked, awaits re-exec")
        lines.append("")
        for r in sorted(by_class["STOP_REPAIR_UNEXEC"], key=lambda x: x["path"]):
            short = _short(r["path"], root)
            cfg = r["config"]
            cfg_str = f"cloud-id={cfg['cloud_id']} [{cfg['status']}]" if cfg["has_config"] else "no config.json"
            lines.append(
                f"  - {short}  kernel={r['kernel']}  unexec={r['code_unexecuted']}/{r['code_total']}  {cfg_str}"
            )
        lines.append("")

    if by_class["HEALTHY"]:
        lines.append(f"## HEALTHY ({len(by_class['HEALTHY'])} quantbooks)")
        lines.append("")

    if by_class["ERROR"]:
        lines.append("## ERROR (unreadable notebooks)")
        for r in by_class["ERROR"]:
            short = _short(r["path"], root)
            lines.append(f"  - {short}: {r.get('error', '?')}")
        lines.append("")

    lines.append(
        "FIX (PREEXISTING_UNEXEC): re-execute unexec cells in the real environment\n"
        "(QC Cloud research kernel for QuantBook, local kernel for matplotlib) and\n"
        "commit the real outputs, then add the QC-UNEXEC-TRIAGED marker (issue #7575)\n"
        "so the notebook moves to STOP_REPAIR_UNEXEC (triaged) instead of staying\n"
        "PREEXISTING_UNEXEC (new, untracked). Stop&Repair, never fabricate --\n"
        "secrets-hygiene 6 + sota-not-workaround Prong-A. See #6891 (fabrication)\n"
        "and #7575 (never-executed, distinct bug-class) for incident context."
    )
    return "\n".join(lines)


def json_report(results: list[dict]) -> str:
    return json.dumps(
        {
            "scanned": len(results),
            "by_class": {
                c: sum(1 for r in results if r["classification"] == c)
                for c in ("HEALTHY", "STOP_REPAIR_STRIPPED", "STOP_REPAIR_UNEXEC",
                          "PREEXISTING_UNEXEC", "ERROR")
            },
            "results": results,
        },
        indent=2,
        ensure_ascii=False,
    )


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--root", default=".",
                        help="Repo root (default: cwd)")
    parser.add_argument("--quant-root",
                        default="MyIA.AI.Notebooks/QuantConnect/projects",
                        help="Path to QC projects dir (relative to --root)")
    parser.add_argument("--notebooks-root", default=None,
                        help="Racine des notebooks pour --scope repo "
                             "(relative a --root, defaut: MyIA.AI.Notebooks)")
    parser.add_argument("--scope", choices=("repo", "projects"), default="repo",
                        help="repo (defaut) : tout notebook instanciant QuantBook(), ou qu'il vive. "
                             "projects : ancienne fenetre quant-root/*/quantbook.ipynb seulement.")
    parser.add_argument("--project", help="Single project name (under --quant-root)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--md", help="Write markdown report to this path")
    parser.add_argument("--check", action="store_true",
                        help="Exit 1 if any PREEXISTING_UNEXEC (CI-ready)")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    quant_root = (root / args.quant_root).resolve()
    if not quant_root.exists():
        print(f"error: quant root not found: {quant_root}", file=sys.stderr)
        return 2

    if args.project:
        nb = quant_root / args.project / "quantbook.ipynb"
        if not nb.exists():
            print(f"error: project quantbook not found: {nb}", file=sys.stderr)
            return 2
        results = [scan_notebook(nb)]
    elif args.scope == "projects":
        results = scan_projects(quant_root)
    else:
        notebooks_root = (root / (args.notebooks_root or "MyIA.AI.Notebooks")).resolve()
        # Un chemin FOURNI qui n'existe pas est une faute de frappe -> exit 2.
        # Le defaut absent (arbre synthetique, checkout partiel) degrade
        # simplement le sweep : on rend les quantbooks canoniques seuls.
        if args.notebooks_root and not notebooks_root.exists():
            print(f"error: notebooks root not found: {notebooks_root}", file=sys.stderr)
            return 2
        results = scan_repo(notebooks_root, quant_root)

    if args.json:
        print(json_report(results))
    else:
        print(human_report(results, root))

    if args.md:
        md_path = Path(args.md)
        if not md_path.is_absolute():
            md_path = root / md_path
        md_path.write_text(human_report(results, root), encoding="utf-8")
        print(f"\nMarkdown report written to {md_path}", file=sys.stderr)

    if args.check:
        pre = sum(1 for r in results if r["classification"] == "PREEXISTING_UNEXEC")
        return 1 if pre > 0 else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
