"""
Checkpoint registry for ML Training Pipeline.

Scans checkpoints/ directory for all model runs, builds a REGISTRY.md
summary with hyperparams, metrics, and data hashes.

Usage:
    python registry_update.py                 # Update REGISTRY.md
    python registry_update.py --check         # Check for issues (no write)
    python registry_update.py --json          # Output as JSON
"""

import json
import sys
from datetime import datetime
from pathlib import Path

CHECKPOINTS_DIR = Path(__file__).resolve().parent.parent / "checkpoints"
REGISTRY_PATH = Path(__file__).resolve().parent.parent / "REGISTRY.md"


def scan_checkpoints(checkpoints_dir: Path) -> list[dict]:
    """Scan all checkpoint directories and collect metadata."""
    entries = []

    if not checkpoints_dir.exists():
        return entries

    for model_type_dir in sorted(checkpoints_dir.iterdir()):
        if not model_type_dir.is_dir():
            continue

        for ckpt_dir in sorted(model_type_dir.iterdir()):
            if not ckpt_dir.is_dir():
                continue

            meta_file = ckpt_dir / "metadata.json"
            if not meta_file.exists():
                entries.append({
                    "model_type": model_type_dir.name,
                    "timestamp": ckpt_dir.name,
                    "status": "MISSING_METADATA",
                    "path": str(ckpt_dir.relative_to(checkpoints_dir.parent)),
                })
                continue

            try:
                metadata = json.loads(meta_file.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                entries.append({
                    "model_type": model_type_dir.name,
                    "timestamp": ckpt_dir.name,
                    "status": "INVALID_JSON",
                    "path": str(ckpt_dir.relative_to(checkpoints_dir.parent)),
                })
                continue

            # Check model file exists
            model_files = list(ckpt_dir.glob("model.*"))
            has_model = len(model_files) > 0

            entry = {
                "model_type": metadata.get("model_type", model_type_dir.name),
                "timestamp": metadata.get("timestamp", ckpt_dir.name),
                "status": "OK" if has_model else "MISSING_MODEL",
                "data_hash": metadata.get("data_hash", ""),
                "hyperparams": metadata.get("hyperparams", {}),
                "metrics": metadata.get("metrics", {}),
                "architecture": metadata.get("architecture", {}),
                "files": [f.name for f in ckpt_dir.iterdir() if f.is_file()],
                "path": str(ckpt_dir.relative_to(checkpoints_dir.parent)),
            }
            entries.append(entry)

    return entries


def build_registry_markdown(entries: list[dict]) -> str:
    """Build REGISTRY.md content from checkpoint entries."""
    lines = [
        "# Checkpoint Registry",
        "",
        f"Auto-generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        "",
        f"Total checkpoints: {len(entries)}",
        "",
    ]

    # Group by model type
    by_type = {}
    for e in entries:
        mt = e["model_type"]
        by_type.setdefault(mt, []).append(e)

    for model_type, model_entries in sorted(by_type.items()):
        lines.append(f"## {model_type}")
        lines.append("")
        lines.append(f"Checkpoints: {len(model_entries)}")
        lines.append("")

        for e in sorted(model_entries, key=lambda x: x["timestamp"], reverse=True):
            status_icon = {"OK": "OK", "MISSING_MODEL": "WARN", "MISSING_METADATA": "ERR", "INVALID_JSON": "ERR"}
            icon = status_icon.get(e["status"], "?")

            lines.append(f"### {e['timestamp']} [{icon}]")
            lines.append("")

            if e["data_hash"]:
                lines.append(f"- Data hash: `{e['data_hash']}`")

            if e["metrics"]:
                metrics_str = ", ".join(f"{k}={v}" for k, v in sorted(e["metrics"].items())[:6])
                lines.append(f"- Metrics: {metrics_str}")

            if e["architecture"]:
                arch_str = ", ".join(f"{k}={v}" for k, v in sorted(e["architecture"].items()))
                lines.append(f"- Architecture: {arch_str}")

            if e["hyperparams"]:
                hp = e["hyperparams"]
                hp_str = ", ".join(
                    f"{k}={v}" for k, v in sorted(hp.items())
                    if k in ("symbol", "device", "hidden_size", "d_model", "nhead", "num_layers", "epochs", "num_episodes")
                )
                if hp_str:
                    lines.append(f"- Config: {hp_str}")

            lines.append(f"- Files: {', '.join(e['files'])}")
            lines.append("")

    # Issues section
    issues = [e for e in entries if e["status"] != "OK"]
    if issues:
        lines.append("## Issues")
        lines.append("")
        for e in issues:
            lines.append(f"- **{e['status']}**: {e['path']}")
        lines.append("")

    return "\n".join(lines)


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Update checkpoint registry")
    parser.add_argument("--check", action="store_true", help="Check only, don't write")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    entries = scan_checkpoints(CHECKPOINTS_DIR)

    if not entries:
        print("No checkpoints found.")
        if not args.check:
            print("REGISTRY.md not updated (no data).")
        sys.exit(0)

    if args.json:
        print(json.dumps(entries, indent=2))
        return

    issues = [e for e in entries if e["status"] != "OK"]
    print(f"Found {len(entries)} checkpoints in {CHECKPOINTS_DIR}")
    if issues:
        print(f"Issues: {len(issues)}")
        for e in issues:
            print(f"  {e['status']}: {e['path']}")

    if args.check:
        if issues:
            sys.exit(1)
        return

    content = build_registry_markdown(entries)
    REGISTRY_PATH.write_text(content, encoding="utf-8")
    print(f"Registry written: {REGISTRY_PATH}")


if __name__ == "__main__":
    main()
