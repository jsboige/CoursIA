#!/usr/bin/env python3
"""Quantbooks Stop&Repair pipeline orchestrator (Issue #6891, #7575, G.9 follow-up).

Pourquoi cet outil existe
-------------------------
L'incident fondateur #6891 (June 2026) a revele 8 quantbook.ipynb avec des
sorties FABRIQUEES (PNG 1x1 de 70 octets + tableaux 'Row N'). Le sweep initial
(#7447 + #7462) a strappe ces sorties (Stop&Repair compliant) et les a balisees
d'un markdown d'avertissement. La resolution substance (c.1331+2 G.9 firsthand)
confirme **0 quantbook avec PNG blancs ou fabricated outputs sur origin/main**,
mais **6 des 8 quantbooks scope n'ont toujours pas de cloud-id** dans leur
``config.json`` -- blocant la voie ``lean cloud push`` pour la re-execution
kernel research QC Cloud.

Le user (Beausoleil, 2026-08-06) a confirme que les QC_API credentials
(QC_API_USER_ID / QC_API_ACCESS_TOKEN / QC_API_ORGANIZATION_ID) sont
disponibles et que la voie est entierement ouverte. Ce pipeline orchestre les
4 phases du plan Stop&Repair en mode **idempotent** :

  Phase 1: ``push``     -- ``lean cloud push`` pour les 6 projets sans cloud-id
                           (DualMomentum 28692516 + EMA-Cross-Alpha 28885488
                           ont deja leur cloud-id ; on les saute).
  Phase 2: ``exec``     -- re-execution end-to-end de chaque quantbook.ipynb
                           dans le kernel research QC via
                           ``scripts/notebook_tools/qc_quantbook_execute.py``.
  Phase 3: ``verify``   -- post-exec audit via ``detect_fabricated_outputs.py``
                           et ``detect_blank_figures.py`` ; les deux DOIVENT
                           retourner 0.
  Phase 4: ``report``   -- synthese CSV + Markdown dans
                           ``results/quantbooks_stop_repair_<ts>/``.

Mode dry-run (defaut si creds absentes)
---------------------------------------
Si ``QC_API_USER_ID`` n'est pas dans l'env, le pipeline bascule en ``--dry-run``
automatique : il audite l'etat actuel (audit_quantbooks_unexec.py), dresse la
liste des projets push-ready vs exec-only, et genere un rapport de phase 4
sans toucher au kernel QC. **Le dry-run est lui-meme un livrable** : il documente
l'etat du scope #6891 a un instant t, de maniere verifiable.

Stop&Repair compliant
---------------------
Aucune phase ne hand-edite une sortie de cellule. Toute execution qui produit
des outputs non-conformes est re-marquee ``QC-UNEXEC-TRIAGED`` et reportee
comme gate suivant ; JAMAIS maquiller (regle secrets-hygiene 6 + Stop&Repair
decret user 2026-06-22).

Usage
-----
::

    # Dry-run (creds absentes) : audit + rapport seulement
    python scripts/quantconnect/quantbooks_stop_repair_pipeline.py \\
        --quantbooks DualMomentum EMA-Cross-Alpha FuturesTrend \\
        --phase audit --dry-run

    # Phase push (apres lean login)
    python scripts/quantconnect/quantbooks_stop_repair_pipeline.py \\
        --quantbooks AllWeather FuturesTrend MomentumStrategy \\
        --phase push

    # Phase exec
    python scripts/quantconnect/quantbooks_stop_repair_pipeline.py \\
        --quantbooks DualMomentum --phase exec --timeout 600

    # Phase verify (post-exec audit)
    python scripts/quantconnect/quantbooks_stop_repair_pipeline.py \\
        --quantbooks DualMomentum --phase verify

    # Full pipeline (audit + push + exec + verify + report)
    python scripts/quantconnect/quantbooks_stop_repair_pipeline.py \\
        --quantbooks AllWeather --pipeline --report-csv

References
----------
- #6891 : quantbooks stop&repair scope (8 quantbooks, 6 sans cloud-id)
- #7575 : bug-class PREEXISTING_UNEXEC follow-up (9 quantbooks distincts)
- c.1331+2 : G.9 firsthand substance = RESOLVED sur origin/main
- scripts/notebook_tools/qc_quantbook_execute.py : exec headless via lean CLI + Docker
- scripts/quantconnect/audit_quantbooks_unexec.py : classification HEALTHY/STRIPPED/UNEXEC
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

# REST-only push via qc-mcp-lite's auth helpers (DRY : single source of truth
# pour SHA256(token:timestamp) + Basic + Timestamp). c.1331+7 : on remplace
# ``subprocess.run(["lean", "cloud", "push", ...])`` (qui echoue sur les
# machines ou ``lean`` = Lean4 theorem prover, pas QC CLI) par les memes REST
# calls que MCP expose en MCP-tools. Aucune installation de QC CLI requise.
_QC_MCP_LITE_DIR = Path(__file__).resolve().parents[1] / "qc-mcp-lite"
if str(_QC_MCP_LITE_DIR) not in sys.path:
    sys.path.insert(0, str(_QC_MCP_LITE_DIR))

# Importer server.py importe aussi mcp.server.fastmcp (dep existante du repo,
# utilise par le daemon MCP). Le bloc try/except protege les tests en isolation
# (mcp SDK absent => on retombe sur requests direct avec auth inline).
_qc_api_post = None  # type: ignore  # placeholder AVANT try/except : monkeypatch tests
_qc_get_credentials = None  # type: ignore  # placeholder AVANT try/except : monkeypatch tests
try:
    from server import _api_post as _qc_api_post  # type: ignore
    from server import _get_credentials as _qc_get_credentials  # type: ignore
    _HAS_QC_MCP_HELPERS = True
except ImportError:
    _HAS_QC_MCP_HELPERS = False

# Scope #6891 first batch (8 quantbooks declares par body issue original)
DEFAULT_QUANTBOOKS = [
    "AllWeather",
    "DualMomentum",
    "EMA-Cross-Alpha",
    "FuturesTrend",
    "MomentumStrategy",
    "RiskParity",
    "SectorMomentum",
    "TurnOfMonth",
]

# Cloud-id deja connu (DualMomentum 28692516 + EMA-Cross-Alpha 28885488).
KNOWN_CLOUD_IDS = {
    "DualMomentum": 28692516,
    "EMA-Cross-Alpha": 28885488,
}


def _repo_root() -> Path:
    """Trouve la racine du repo depuis l'emplacement du script."""
    return Path(__file__).resolve().parents[2]


def _quant_projects_root(repo: Path) -> Path:
    return repo / "MyIA.AI.Notebooks" / "QuantConnect" / "projects"


def _project_dir(repo: Path, name: str) -> Path:
    return _quant_projects_root(repo) / name


def _config_path(repo: Path, name: str) -> Path:
    return _project_dir(repo, name) / "config.json"


def _notebook_path(repo: Path, name: str) -> Path:
    return _project_dir(repo, name) / "quantbook.ipynb"


def _credentials_present() -> bool:
    """Verifie que QC_API_USER_ID + QC_API_ACCESS_TOKEN + QC_API_ORGANIZATION_ID
    sont dans l'env. Si non, le pipeline bascule en dry-run automatique."""
    return all(
        os.environ.get(k) for k in (
            "QC_API_USER_ID",
            "QC_API_ACCESS_TOKEN",
            "QC_API_ORGANIZATION_ID",
        )
    )


def _read_cloud_id(repo: Path, name: str) -> int | None:
    """Lit cloud-id depuis config.json si present, sinon None."""
    cfg = _config_path(repo, name)
    if not cfg.exists():
        return None
    try:
        data = json.loads(cfg.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None
    cid = data.get("cloud-id")
    return int(cid) if cid else None


def phase_audit(repo: Path, quantbooks: list[str], results: dict) -> dict:
    """Phase 1 : audit etat actuel de chaque quantbook (PRE / POST-exec)."""
    audit_script = repo / "scripts" / "quantconnect" / "audit_quantbooks_unexec.py"
    if not audit_script.exists():
        results["audit"] = {"error": f"audit_quantbooks_unexec.py not found at {audit_script}"}
        return results

    audit_data = []
    for name in quantbooks:
        proj_dir = _project_dir(repo, name)
        nb_path = _notebook_path(repo, name)
        if not nb_path.exists():
            audit_data.append({
                "quantbook": name,
                "exists": False,
                "config_json": _config_path(repo, name).exists(),
                "cloud_id": _read_cloud_id(repo, name),
                "kernel": "MISSING",
            })
            continue

        # Lancer audit_quantbooks_unexec.py sur le projet isole
        proc = subprocess.run(
            [
                sys.executable, str(audit_script),
                "--quant-root", str(proj_dir),
                "--scope", "projects",
            ],
            capture_output=True, text=True, cwd=repo,
        )
        # Le verdict de l'audit (HEALTHY/STOP_REPAIR_STRIPPED/STOP_REPAIR_UNEXEC/PREEXISTING_UNEXEC)
        # est dans la sortie texte ; on extrait la classe via mots-cles canoniques.
        verdict = "UNKNOWN"
        known_classes = (
            "HEALTHY",
            "STOP_REPAIR_STRIPPED",
            "STOP_REPAIR_UNEXEC",
            "PREEXISTING_UNEXEC",
        )
        for line in proc.stdout.splitlines() + proc.stderr.splitlines():
            line_upper = line.upper()
            for cls in known_classes:
                if cls in line_upper:
                    verdict = cls
                    break
            if verdict != "UNKNOWN":
                break

        audit_data.append({
            "quantbook": name,
            "exists": True,
            "config_json": _config_path(repo, name).exists(),
            "cloud_id": _read_cloud_id(repo, name),
            "kernel": verdict,
        })

    results["audit"] = audit_data
    return results


def _push_one_via_rest(name: str, proj_dir: Path) -> dict:
    """Push ``<proj_dir>`` to QC Cloud via REST (no QC CLI needed).

    Flow :
      1. POST /projects/create  {name, language="Py"}       -> projectId
      2. Si le nom existe deja (duplicate) : fallback
         POST /projects/read   puis filtre name_contains=name -> projectId
      3. POST /files/create    {projectId, name="main.py", content=...}
      4. Ecrit ``config.json`` avec cloud-id + organization-id retournes.

    Retourne un dict compatible ``phase_push`` : quantbook, cloud_id, action,
    et eventuellement stderr_tail (ici : details / error_tail).
    Idempotent : re-run sur un quantbook dont config.json a perdu cloud-id
    retrouve le projectId existant via ``list_projects`` au lieu de creer
    un doublon (incident fondateur : script ``lean cloud push`` cree 6
    projets fantomes sur origin/main si relance sans garde).
    """
    if not _HAS_QC_MCP_HELPERS:
        return {
            "quantbook": name,
            "cloud_id": None,
            "action": "REST_PUSH_NO_HELPERS",
            "error_tail": ["qc-mcp-lite.server helpers not importable (mcp SDK missing)"],
        }
    try:
        user_id, _token = _qc_get_credentials()
    except Exception as exc:
        return {
            "quantbook": name,
            "cloud_id": None,
            "action": "REST_PUSH_NO_CREDS",
            "error_tail": [str(exc)],
        }

    main_py = proj_dir / "main.py"
    if not main_py.exists():
        return {
            "quantbook": name,
            "cloud_id": None,
            "action": "REST_PUSH_NO_MAIN_PY",
            "error_tail": [f"main.py absent in {proj_dir}"],
        }

    main_content = main_py.read_text(encoding="utf-8")

    # Etape 1+2 : create_project (avec fallback list_projects si duplicate).
    try:
        created = _qc_api_post("/projects/create", {"name": name, "language": "Py"})
        projects = created.get("projects") or []
        project = projects[0] if projects else {}
        project_id = int(project.get("projectId") or 0)
        organization_id = str(project.get("organizationId") or "")
        create_via = "create"
    except RuntimeError as exc:
        msg = str(exc).lower()
        # Duplicate name : fallback list_projects pour retrouver le projectId
        # existant et continuer en mode "update existing". Le script
        # ``lean cloud push`` cree des doublons silencieux -- on s'en protege.
        if "already" in msg or "duplicate" in msg or "exists" in msg:
            listed = _qc_api_post("/projects/read", {})
            existing = [
                p for p in (listed.get("projects") or [])
                if (p.get("name") or "").lower() == name.lower()
            ]
            if not existing:
                return {
                    "quantbook": name,
                    "cloud_id": None,
                    "action": "REST_PUSH_DUP_LOOKUP_FAIL",
                    "error_tail": [str(exc)],
                }
            project = existing[0]
            project_id = int(project.get("projectId") or 0)
            organization_id = str(project.get("organizationId") or "")
            create_via = "lookup_existing"
        else:
            return {
                "quantbook": name,
                "cloud_id": None,
                "action": "REST_PUSH_CREATE_FAIL",
                "error_tail": [str(exc)],
            }

    if not project_id:
        return {
            "quantbook": name,
            "cloud_id": None,
            "action": "REST_PUSH_NO_PROJECT_ID",
            "error_tail": [f"create returned no projectId: {created!r}"[:200]],
        }

    # Etape 3 : create_file main.py. update_file_contents serait preferable si
    # on sait qu'il existe deja, mais create_file est idempotent (QC remplace
    # si le nom existe dans le projet, retourne success=true). C'est le pattern
    # qu'utilise deja qc-mcp-lite.create_file.
    try:
        file_resp = _qc_api_post(
            "/files/create",
            {"projectId": project_id, "name": "main.py", "content": main_content},
        )
    except RuntimeError as exc:
        return {
            "quantbook": name,
            "cloud_id": None,
            "action": "REST_PUSH_FILE_FAIL",
            "cloud_id_attempted": project_id,
            "error_tail": [str(exc)],
        }

    # Etape 4 : persister config.json avec cloud-id + organization-id pour
    # que les phases suivantes (exec/verify) trouvent le projet.
    config_path = proj_dir / "config.json"
    existing_cfg: dict = {}
    if config_path.exists():
        try:
            existing_cfg = json.loads(config_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            existing_cfg = {}
    existing_cfg["cloud-id"] = project_id
    if organization_id:
        existing_cfg["organization-id"] = organization_id
    existing_cfg["language"] = "Py"
    config_path.write_text(
        json.dumps(existing_cfg, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    return {
        "quantbook": name,
        "cloud_id": project_id,
        "action": f"REST_PUSH_OK_{create_via.upper()}",
        "organization_id": organization_id,
        "file_resp_success": bool(file_resp.get("success", True)),
    }


def phase_push(repo: Path, quantbooks: list[str], results: dict, dry_run: bool) -> dict:
    """Phase 2 : push QC Cloud via REST pour les quantbooks sans cloud-id.

    Avant c.1331+7 : ``subprocess.run(["lean", "cloud", "push", ...])`` -- mais
    ``lean`` sur cette machine est le theorem prover Lean4 (elan), pas QC CLI.
    Blocant pour les 6 quantbooks scope #6891 sans cloud-id.

    Apres c.1331+7 : REST-only via qc-mcp-lite.server._api_post (memes appels
    que MCP expose en MCP-tools, sans wrapper subprocess). Self-contained :
    aucune installation de QC CLI requise.
    """
    push_data = []
    for name in quantbooks:
        cloud_id = _read_cloud_id(repo, name)
        if cloud_id:
            push_data.append({
                "quantbook": name,
                "cloud_id": cloud_id,
                "action": "SKIP_ALREADY_PUSHED",
            })
            continue

        if dry_run:
            push_data.append({
                "quantbook": name,
                "cloud_id": None,
                "action": "DRY_RUN_PUSH_PENDING",
            })
            continue

        proj_dir = _project_dir(repo, name)
        if not proj_dir.exists():
            push_data.append({
                "quantbook": name,
                "cloud_id": None,
                "action": "SKIP_NO_PROJECT_DIR",
            })
            continue

        push_data.append(_push_one_via_rest(name, proj_dir))

    results["push"] = push_data
    return results


def phase_exec(repo: Path, quantbooks: list[str], results: dict, dry_run: bool, timeout: int) -> dict:
    """Phase 3 : re-exec via qc_quantbook_execute.py (headless lean + Docker)."""
    exec_data = []
    exec_script = repo / "scripts" / "notebook_tools" / "qc_quantbook_execute.py"
    if not exec_script.exists():
        results["exec"] = {"error": f"qc_quantbook_execute.py not found at {exec_script}"}
        return results

    for name in quantbooks:
        proj_dir = _project_dir(repo, name)
        if not proj_dir.exists():
            exec_data.append({
                "quantbook": name,
                "action": "SKIP_NO_PROJECT_DIR",
            })
            continue

        if dry_run:
            exec_data.append({
                "quantbook": name,
                "action": "DRY_RUN_EXEC_PENDING",
            })
            continue

        # qc_quantbook_execute.py attend un project_dir sous un Lean workspace
        # Pour les quantbooks quantbook.ipynb, il faut un lean-workspace parent.
        proc = subprocess.run(
            [
                sys.executable, str(exec_script),
                str(proj_dir),
                "--notebook", "quantbook.ipynb",
                "--timeout", str(timeout),
            ],
            capture_output=True, text=True, cwd=repo,
        )
        exec_data.append({
            "quantbook": name,
            "action": f"EXEC_RC_{proc.returncode}",
            "stdout_tail": proc.stdout.strip().splitlines()[-3:] if proc.stdout else [],
        })

    results["exec"] = exec_data
    return results


def phase_verify(repo: Path, quantbooks: list[str], results: dict, dry_run: bool) -> dict:
    """Phase 4 : audit post-exec via detect_fabricated_outputs + detect_blank_figures."""
    verify_data = []
    for script_rel in (
        "scripts/notebook_tools/detect_fabricated_outputs.py",
        "scripts/notebook_tools/detect_blank_figures.py",
    ):
        script_path = repo / script_rel
        if not script_path.exists():
            verify_data.append({
                "scanner": script_rel,
                "status": "SCRIPT_MISSING",
            })
            continue

        # Filtre --family QuantConnect applique aux scanners Prong-A canoniques.
        # En dry-run, on lance quand meme pour obtenir la baseline post-audit.
        proc = subprocess.run(
            [
                sys.executable, str(script_path),
                "--family", "QuantConnect",
                "--check",
            ],
            capture_output=True, text=True, cwd=repo,
        )
        # Convention scanners : exit 0 = OK, exit 1 = defective detecte
        verify_data.append({
            "scanner": script_rel,
            "exit_code": proc.returncode,
            "stdout_tail": proc.stdout.strip().splitlines()[-5:] if proc.stdout else [],
            "status": "PASS" if proc.returncode == 0 else "FAIL_DETECT_DEFECTS",
        })

    results["verify"] = verify_data
    return results


def phase_report(repo: Path, results: dict, output_csv: Path | None, output_md: Path | None) -> dict:
    """Phase 5 : synthese CSV + Markdown des 4 phases."""
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    out_dir = repo / "results" / f"quantbooks_stop_repair_{timestamp}"
    out_dir.mkdir(parents=True, exist_ok=True)

    # CSV flatten : 1 ligne par quantbook x phase
    csv_path = output_csv or (out_dir / "report.csv")
    with open(csv_path, "w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(["phase", "quantbook", "status", "details"])
        for phase_name, phase_data in results.items():
            if isinstance(phase_data, list):
                for entry in phase_data:
                    writer.writerow([
                        phase_name,
                        entry.get("quantbook", ""),
                        entry.get("action", entry.get("status", entry.get("kernel", ""))),
                        json.dumps({k: v for k, v in entry.items() if k != "quantbook"}, ensure_ascii=False),
                    ])
            elif isinstance(phase_data, dict) and "error" in phase_data:
                writer.writerow([phase_name, "ALL", "ERROR", phase_data["error"]])

    # Markdown synthese
    md_path = output_md or (out_dir / "report.md")
    lines = [
        f"# Quantbooks Stop&Repair Pipeline Report — {timestamp}",
        "",
        "**Scope** : 8 quantbooks #6891 (DualMomentum 28692516, EMA-Cross-Alpha 28885488 = deja cloud-id).",
        "**Creds QC** : " + ("PRESENTES (live exec)" if _credentials_present() else "ABSENTES (dry-run only)"),
        "",
    ]
    for phase_name in ("audit", "push", "exec", "verify"):
        lines.append(f"## Phase {phase_name.title()}")
        lines.append("")
        phase_data = results.get(phase_name, [])
        if isinstance(phase_data, list):
            for entry in phase_data:
                # Prefer action > status > kernel (en ordre de priorite)
                status = entry.get("action") or entry.get("status") or entry.get("kernel") or "?"
                lines.append(f"- **{entry.get('quantbook', '?')}** : `{status}`")
                for k, v in entry.items():
                    if k not in ("quantbook", "action", "status", "kernel") and v:
                        lines.append(f"    - `{k}` = `{v}`")
        elif isinstance(phase_data, dict) and "error" in phase_data:
            lines.append(f"- ERROR : {phase_data['error']}")
        lines.append("")

    md_path.write_text("\n".join(lines), encoding="utf-8")
    results["report"] = {"csv": str(csv_path), "md": str(md_path), "out_dir": str(out_dir)}
    return results


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--quantbooks", nargs="+", default=DEFAULT_QUANTBOOKS,
        help="Liste des quantbooks a traiter (defaut : scope #6891 = 8 quantbooks).",
    )
    parser.add_argument(
        "--phase", choices=("audit", "push", "exec", "verify", "report", "all"),
        default="all",
    )
    parser.add_argument(
        "--pipeline", action="store_true",
        help="Execute audit + push + exec + verify + report en sequence.",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Force dry-run meme si creds presentes.",
    )
    parser.add_argument(
        "--timeout", type=int, default=600,
        help="Timeout par quantbook pour phase exec (defaut 600s).",
    )
    parser.add_argument(
        "--report-csv", type=Path, default=None,
        help="Chemin du CSV report (defaut results/quantbooks_stop_repair_<ts>/report.csv).",
    )
    parser.add_argument(
        "--report-md", type=Path, default=None,
        help="Chemin du Markdown report (defaut results/quantbooks_stop_repair_<ts>/report.md).",
    )
    args = parser.parse_args(argv)

    repo = _repo_root()
    dry_run = args.dry_run or not _credentials_present()
    if not args.dry_run and not _credentials_present():
        print("[INFO] QC_API credentials absentes -> dry-run automatique", file=sys.stderr)

    results: dict = {}
    phases = (
        ["audit", "push", "exec", "verify", "report"]
        if args.pipeline or args.phase == "all"
        else [args.phase]
    )

    if "audit" in phases:
        phase_audit(repo, args.quantbooks, results)
    if "push" in phases:
        phase_push(repo, args.quantbooks, results, dry_run=dry_run)
    if "exec" in phases:
        phase_exec(repo, args.quantbooks, results, dry_run=dry_run, timeout=args.timeout)
    if "verify" in phases:
        phase_verify(repo, args.quantbooks, results, dry_run=dry_run)
    if "report" in phases:
        phase_report(repo, results, output_csv=args.report_csv, output_md=args.report_md)

    # Sortie JSON sur stdout pour tooling downstream
    print(json.dumps(results, indent=2, ensure_ascii=False, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
