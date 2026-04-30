"""
Validate the ML Training Pipeline package.

Runs --dry-run on all training scripts to verify:
1. All dependencies are importable
2. Synthetic data generation works
3. Training loop completes without error
4. Checkpoints are saved correctly
5. Metadata files are valid JSON with expected fields

Usage:
    python validate_training_package.py
    python validate_training_package.py --verbose
    python validate_training_package.py --script train_classification.py
"""

import json
import subprocess
import sys
import time
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent

TRAINING_SCRIPTS = [
    "train_classification.py",
    "train_lstm.py",
    "train_transformer.py",
    "train_dqn_rl.py",
]

REQUIRED_METADATA_FIELDS = [
    "timestamp",
    "model_type",
    "hyperparams",
    "metrics",
    "data_hash",
    "files",
]


def check_imports(script_name: str) -> list[str]:
    """Check that required imports are available for a given script."""
    errors = []

    core_imports = ["numpy", "pandas"]
    for mod in core_imports:
        try:
            __import__(mod)
        except ImportError:
            errors.append(f"Missing core dependency: {mod}")

    if script_name == "train_classification.py":
        try:
            import sklearn  # noqa: F401
        except ImportError:
            errors.append("Missing: scikit-learn (pip install scikit-learn)")
        try:
            import joblib  # noqa: F401
        except ImportError:
            errors.append("Missing: joblib (pip install joblib)")

    if script_name in ("train_lstm.py", "train_transformer.py", "train_dqn_rl.py"):
        try:
            import torch  # noqa: F401
        except ImportError:
            errors.append("Missing: torch (pip install torch)")

    return errors


def run_dry_run(script_path: Path, verbose: bool = False) -> dict:
    """Run a training script with --dry-run and capture results."""
    cmd = [sys.executable, str(script_path), "--dry-run"]
    start = time.time()

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=300,
        cwd=str(script_path.parent),
    )
    elapsed = time.time() - start

    return {
        "returncode": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr,
        "elapsed": round(elapsed, 2),
        "success": result.returncode == 0,
    }


def find_latest_checkpoint(checkpoint_dir: Path) -> Path | None:
    """Find the most recent checkpoint directory."""
    if not checkpoint_dir.exists():
        return None

    checkpoints = sorted(checkpoint_dir.iterdir(), key=lambda p: p.name, reverse=True)
    return checkpoints[0] if checkpoints else None


def validate_checkpoint(ckpt_dir: Path, script_name: str) -> list[str]:
    """Validate checkpoint directory structure and metadata."""
    errors = []

    if not ckpt_dir or not ckpt_dir.exists():
        return ["No checkpoint directory found"]

    # Check metadata.json
    meta_file = ckpt_dir / "metadata.json"
    if not meta_file.exists():
        errors.append("Missing metadata.json in checkpoint")
        return errors

    try:
        metadata = json.loads(meta_file.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        errors.append(f"Invalid metadata.json: {e}")
        return errors

    # Check required fields
    for field in REQUIRED_METADATA_FIELDS:
        if field not in metadata:
            errors.append(f"Missing metadata field: {field}")

    # Check model file exists
    model_files = list(ckpt_dir.glob("model.*"))
    if not model_files:
        errors.append("No model file found in checkpoint")

    # Check data_hash is not empty
    if metadata.get("data_hash") == "":
        errors.append("Empty data_hash in metadata")

    # Check metrics are present
    if "metrics" in metadata and not isinstance(metadata["metrics"], dict):
        errors.append("metrics should be a dict")

    return errors


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Validate ML Training Pipeline")
    parser.add_argument("--verbose", "-v", action="store_true", help="Show full output")
    parser.add_argument("--script", help="Validate single script only")
    args = parser.parse_args()

    scripts_to_test = [args.script] if args.script else TRAINING_SCRIPTS
    results = {}
    all_passed = True

    print("=" * 60)
    print("ML Training Pipeline - Validation")
    print("=" * 60)

    # Phase 1: Import checks
    print("\n[Phase 1] Dependency checks")
    for script_name in scripts_to_test:
        errors = check_imports(script_name)
        if errors:
            print(f"  FAIL {script_name}: {errors}")
            all_passed = False
        else:
            print(f"  OK   {script_name}")

    # Phase 2: Dry-run execution
    print("\n[Phase 2] Dry-run execution")
    for script_name in scripts_to_test:
        script_path = SCRIPTS_DIR / script_name
        if not script_path.exists():
            print(f"  SKIP {script_name}: file not found")
            continue

        result = run_dry_run(script_path, verbose=args.verbose)
        results[script_name] = result

        status = "OK" if result["success"] else "FAIL"
        print(f"  {status}  {script_name} ({result['elapsed']}s)")

        if args.verbose or not result["success"]:
            if result["stdout"]:
                for line in result["stdout"].strip().split("\n"):
                    print(f"        {line}")
            if result["stderr"]:
                for line in result["stderr"].strip().split("\n"):
                    print(f"        STDERR: {line}")

        if not result["success"]:
            all_passed = False

    # Phase 3: Checkpoint validation
    print("\n[Phase 3] Checkpoint validation")
    checkpoint_dirs = {
        "train_classification.py": SCRIPTS_DIR.parent / "checkpoints" / "classification",
        "train_lstm.py": SCRIPTS_DIR.parent / "checkpoints" / "lstm",
        "train_transformer.py": SCRIPTS_DIR.parent / "checkpoints" / "transformer",
        "train_dqn_rl.py": SCRIPTS_DIR.parent / "checkpoints" / "dqn",
    }

    for script_name in scripts_to_test:
        if script_name not in results or not results[script_name]["success"]:
            print(f"  SKIP {script_name}: dry-run failed")
            continue

        ckpt_base = checkpoint_dirs.get(script_name)
        if not ckpt_base:
            continue

        ckpt_dir = find_latest_checkpoint(ckpt_base)
        errors = validate_checkpoint(ckpt_dir, script_name)

        if errors:
            print(f"  FAIL {script_name}: {errors}")
            all_passed = False
        else:
            print(f"  OK   {script_name} checkpoint valid")

    # Summary
    print("\n" + "=" * 60)
    if all_passed:
        print("ALL CHECKS PASSED - Pipeline ready for GPU training")
    else:
        print("SOME CHECKS FAILED - Review errors above")
        sys.exit(1)


if __name__ == "__main__":
    main()
