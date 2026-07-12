#!/usr/bin/env python3
"""
Gestionnaire de sessions d'amelioration de series de notebooks.

Usage:
    python scripts/series_progress_manager.py list
    python scripts/series_progress_manager.py status <series_id>
    python scripts/series_progress_manager.py cancel <series_id>
    python scripts/series_progress_manager.py resume <series_id>
    python scripts/series_progress_manager.py report <series_id>
"""

import json
import sys
from pathlib import Path
from datetime import datetime
from typing import Optional


PROGRESS_DIR = Path(".claude/progress")


def list_sessions():
    """Lister toutes les sessions actives."""
    if not PROGRESS_DIR.exists():
        print("Aucune session active.")
        return

    sessions = list(PROGRESS_DIR.glob("*-progress.json"))

    if not sessions:
        print("Aucune session active.")
        return

    print(f"\n{'='*60}")
    print("SESSIONS D'AMELIORATION DE SERIES")
    print(f"{'='*60}\n")

    for session_file in sessions:
        with open(session_file) as f:
            data = json.load(f)

        stats = data.get("statistics", {})
        series_id = data.get("series_id", "unknown")
        workflow = data.get("workflow", "unknown")
        updated = data.get("updated_at", "unknown")

        completed = stats.get("completed", 0)
        total = stats.get("total", 0)
        failed = stats.get("failed", 0)

        status = "EN COURS" if completed < total else "TERMINE"
        if failed > 0:
            status += f" ({failed} echecs)"

        print(f"ID: {series_id}")
        print(f"   Workflow: {workflow}")
        print(f"   Progression: {completed}/{total} notebooks")
        print(f"   Status: {status}")
        print(f"   Derniere MAJ: {updated}")
        print()


def show_status(series_id: str):
    """Afficher le statut detaille d'une session."""
    session_file = find_session(series_id)

    if not session_file:
        print(f"Session non trouvee: {series_id}")
        return

    with open(session_file) as f:
        data = json.load(f)

    print(f"\n{'='*60}")
    print(f"SESSION: {data.get('series_id')}")
    print(f"{'='*60}\n")

    print(f"Target: {data.get('target_path')}")
    print(f"Workflow: {data.get('workflow')}")
    print(f"Debut: {data.get('started_at')}")
    print(f"Derniere MAJ: {data.get('updated_at')}")

    stats = data.get("statistics", {})
    print(f"\n--- Statistiques ---")
    print(f"Total: {stats.get('total', 0)}")
    print(f"Completes: {stats.get('completed', 0)}")
    print(f"En cours: {stats.get('in_progress', 0)}")
    print(f"En attente: {stats.get('pending', 0)}")
    print(f"Echoues: {stats.get('failed', 0)}")

    print(f"\n--- Notebooks ---")
    for nb_name, nb_data in data.get("notebooks", {}).items():
        status = nb_data.get("status", "unknown")
        status_icon = {"completed": "[OK]", "in_progress": "[..]", "pending": "[--]", "failed": "[!!]"}.get(status, "[??]")

        score_info = ""
        if status == "completed":
            initial = nb_data.get("initial_score", "-")
            final = nb_data.get("final_score", "-")
            score_info = f" (score: {initial} -> {final})"
        elif status == "failed":
            score_info = f" (erreur: {nb_data.get('error', 'unknown')[:50]})"

        print(f"  {status_icon} {nb_name}{score_info}")


def cancel_session(series_id: str):
    """Annuler une session."""
    session_file = find_session(series_id)

    if not session_file:
        print(f"Session non trouvee: {series_id}")
        return

    # Creer un backup
    backup_file = session_file.with_suffix(".json.cancelled")
    session_file.rename(backup_file)

    print(f"Session annulee: {series_id}")
    print(f"Backup: {backup_file}")


def generate_report(series_id: str):
    """Generer un rapport markdown pour une session."""
    session_file = find_session(series_id)

    if not session_file:
        print(f"Session non trouvee: {series_id}")
        return

    with open(session_file) as f:
        data = json.load(f)

    report = f"""# Rapport d'Amelioration de Serie

**Serie**: {data.get('target_path')}
**Workflow**: {data.get('workflow')}
**Date debut**: {data.get('started_at')}
**Date fin**: {data.get('updated_at')}

## Resume

| Metrique | Valeur |
|----------|--------|
| Notebooks totaux | {data['statistics'].get('total', 0)} |
| Completes | {data['statistics'].get('completed', 0)} |
| Echoues | {data['statistics'].get('failed', 0)} |

## Details par notebook

| Notebook | Score initial | Score final | Status |
|----------|--------------|-------------|--------|
"""

    for nb_name, nb_data in data.get("notebooks", {}).items():
        status = nb_data.get("status", "unknown")
        if status == "completed":
            initial = nb_data.get("initial_score", "-")
            final = nb_data.get("final_score", "-")
            report += f"| {nb_name} | {initial} | {final} | OK |\n"
        elif status == "failed":
            report += f"| {nb_name} | - | - | ERREUR |\n"
        elif status == "in_progress":
            report += f"| {nb_name} | - | - | EN COURS |\n"

    report_file = Path(f".claude/reports/{series_id}-report.md")
    report_file.parent.mkdir(parents=True, exist_ok=True)
    report_file.write_text(report, encoding="utf-8")

    print(f"Rapport genere: {report_file}")
    print("\n" + report)


def find_session(series_id: str) -> Optional[Path]:
    """Trouver le fichier de session par son ID."""
    if not PROGRESS_DIR.exists():
        return None

    for session_file in PROGRESS_DIR.glob("*-progress.json"):
        with open(session_file) as f:
            data = json.load(f)
            if data.get("series_id") == series_id:
                return session_file

    return None


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return

    command = sys.argv[1]

    if command == "list":
        list_sessions()
    elif command == "status":
        if len(sys.argv) < 3:
            print("Usage: python series_progress_manager.py status <series_id>")
            return
        show_status(sys.argv[2])
    elif command == "cancel":
        if len(sys.argv) < 3:
            print("Usage: python series_progress_manager.py cancel <series_id>")
            return
        cancel_session(sys.argv[2])
    elif command == "resume":
        if len(sys.argv) < 3:
            print("Usage: python series_progress_manager.py resume <series_id>")
            return
        print(f"Pour reprendre la session {sys.argv[2]}, utilisez l'agent series-improver avec resume=true")
    elif command == "report":
        if len(sys.argv) < 3:
            print("Usage: python series_progress_manager.py report <series_id>")
            return
        generate_report(sys.argv[2])
    else:
        print(f"Commande inconnue: {command}")
        print(__doc__)


if __name__ == "__main__":
    main()
