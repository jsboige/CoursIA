"""bootstrap_bank.py — ingère les JSON de mesures existants au banc v1.

Sources ingérées :
1. `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bakeoff_small/results/**/*.json` (chatterbox c.1462, pocket_tts c.17661)
2. `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bakeoff_large/results/**/metrics.json` (banc_phase_a0.py)
3. `G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-*/**/*-metrics.json` (re-rendus UAT)

Usage (depuis la racine du dépôt ou un worktree) :
    python prosody_lab/bootstrap_bank.py --bank prosody_lab/bake_bank.jsonl \\
        [--dry-run]

Le script :
- scanne récursivement les sources ;
- déduit (motor, extract) depuis le chemin ;
- invoque bake_append.py sur chaque ligne ;
- skippe les erreurs en mode --continue (par défaut).

Idempotent : un run déjà présent (clé (motor, extract, sha256_prefix, seed, ts))
est sauté sans erreur.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

PROSODY_LAB_ROOT = Path(__file__).resolve().parent

# Racines des sources
SOURCES = [
    ("bakeoff_small", PROSODY_LAB_ROOT / "bakeoff_small" / "results"),
    ("bakeoff_large", PROSODY_LAB_ROOT / "bakeoff_large" / "results"),
]
# GDrive-mount A0-review (Windows)
GDrive_REVIEW = Path(r"G:/Mon Drive/MyIA/Projets/BibliothequesSonores")


def _detect_extract(path: Path) -> str | None:
    """Déduit (A|B|C...) depuis le nom de fichier `A__xxx.json` ou `B__xxx.json`."""
    m = re.match(r"^([A-E])__", path.stem)
    if m:
        return m.group(1)
    # sinon, scanne le parent
    for p in [path.stem, path.parent.name]:
        m = re.match(r"^([A-E])(?:__|-|$)", p)
        if m:
            return m.group(1)
    return None


def _detect_motor(path: Path) -> str:
    """Déduit le moteur depuis le chemin (segment parent le plus proche)."""
    # ex. bakeoff_small/results/chatterbox_mtl_v3/...json
    p = path
    while p.parent != p:
        parent = p.parent.name
        # Si le parent matche un moteur connu, on l'utilise
        if parent in {"chatterbox_mtl_v3", "pocket_tts", "cosyvoice3", "zonos",
                      "qwen3_tts_customvoice", "qwen3_tts_1_7b_customvoice"}:
            return parent
        p = p.parent
    return path.parent.name  # fallback


def _gdrive_metrics_files() -> list[Path]:
    """Liste les `*-metrics.json` sous BibliothequesSonores/A0-review-*."""
    if not GDrive_REVIEW.exists():
        return []
    out = []
    for review_dir in GDrive_REVIEW.glob("A0-review-*"):
        out.extend(review_dir.glob("*-metrics.json"))
    return out


def _gdrive_extract_from_stem(stem: str) -> str | None:
    """Décode extract depuis un nom de fichier A0-review.

    Patterns observés :
    - A0C-cosyvoice3-metrics → extract=A
    - A0C-qwen3tts-customvoice-metrics → extract=A
    - A0C-zonos-chunked-metrics → extract=A
    - A0C-...-chunked-metrics → A
    Pas d'exemple B dans A0-review au 2026-10-07 ; le pattern A est dominant.
    """
    if not stem.startswith("A0"):
        return None
    # Tout préfixe "A0[A-E]" → extract=A (canonique)
    m = re.match(r"^A0([A-E])", stem)
    if m:
        return m.group(1)
    return None


def _gdrive_motor_from_stem(stem: str) -> str | None:
    """Décode motor depuis `A0C-<motor>-...-metrics`."""
    s = stem
    # Strip préfixe A0[A-E][-_]?
    s = re.sub(r"^A0[A-E][-_]?", "", s)
    # Strip suffixe -metrics, -chunked-metrics, -chunked
    s = re.sub(r"-(?:chunked-)?(?:chunked-)?metrics$", "", s)
    s = re.sub(r"-chunked$", "", s)
    s = s.strip("-_")
    return s if s else None


def _ingest_via_append(args: list[str]) -> tuple[int, str]:
    """Invoque bake_append.py en sous-processus et retourne (rc, stderr)."""
    proc = subprocess.run(
        [sys.executable, str(PROSODY_LAB_ROOT / "bake_append.py"), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    return proc.returncode, (proc.stderr or "")


def _gather_metrics_files() -> list[tuple[Path, str, str | None, str]]:
    """Scanne les sources et retourne (path, source_tag, extract, motor).

    Cas particulier : `bake_results.json` (bakeoff_small/results/<motor>/)
    contient un tableau `results` avec 1 entrée par extrait. On l'expand en
    N fichiers virtuels suffixés `#extract=<X>` pour le bootstrap, mais
    l'écriture reste dans le fichier source.
    """
    out = []
    for source_tag, root in SOURCES:
        if not root.exists():
            continue
        for p in root.rglob("*.json"):
            # Cas bake_results.json (multi-extract) — on l'expand.
            if p.name == "bake_results.json":
                try:
                    data = json.load(open(p, encoding="utf-8"))
                except Exception as e:
                    print(f"  [SKIP] bake_results illisible : {p} : {e}",
                          file=sys.stderr)
                    continue
                motor = data.get("cell") or _detect_motor(p)
                for r in data.get("results", []):
                    ex = r.get("extract")
                    if not ex:
                        continue
                    out.append((p, source_tag, ex, motor))
                continue
            ex = _detect_extract(p)
            mo = _detect_motor(p)
            if ex is None:
                print(f"  [SKIP] Pas d'extract détecté : {p}", file=sys.stderr)
                continue
            out.append((p, source_tag, ex, mo))
    for p in _gdrive_metrics_files():
        ex = _gdrive_extract_from_stem(p.stem)
        mo = _gdrive_motor_from_stem(p.stem)
        if ex is None or not mo:
            print(f"  [SKIP] Pas de motor/extract détecté : {p}", file=sys.stderr)
            continue
        out.append((p, "gdrive", ex, mo))
    return out


def _expand_per_extract(path: Path) -> list[tuple[str, dict]]:
    """Pour bake_results.json : retourne [(extract, per_extract_dict), ...]."""
    if path.name != "bake_results.json":
        return [("", path)]
    out = []
    data = json.load(open(path, encoding="utf-8"))
    base = {
        "motor": data.get("cell") or _detect_motor(path),
        "license": data.get("license"),
        "size": data.get("size"),
    }
    for r in data.get("results", []):
        ex = r.get("extract")
        if not ex:
            continue
        merged = {**base, **r}
        out.append((ex, merged))
    return out


def _ingest_one(args, path, ex, dry_run=None):
    """Ingest une métrique unique. Pour multi-extract, écrit d'abord un JSON temporaire."""
    metrics_to_pass = path
    tmp_metrics = None
    if path.name == "bake_results.json":
        # Récupère le dict correspondant à cet extract et l'écrit dans un tmp
        for x, d in _expand_per_extract(path):
            if x == ex:
                tmp_metrics = path.parent / f".__bootstrap_tmp_{ex}.json"
                tmp_metrics.write_text(json.dumps(d, ensure_ascii=False),
                                       encoding="utf-8")
                metrics_to_pass = tmp_metrics
                break
    append_args = [
        "--bank", args.bank,
        "--metrics", str(metrics_to_pass),
        "--motor", args.motor,
        "--extract", ex,
        "--source-path", str(path),
    ]
    if args.dry_run:
        append_args.append("--dry-run")
    rc, err = _ingest_via_append(append_args)
    if tmp_metrics and tmp_metrics.exists():
        tmp_metrics.unlink()
    return rc, err


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--bank", required=True, help="Banc JSONL cible.")
    p.add_argument("--dry-run", action="store_true")
    p.add_argument("--continue-on-error", action="store_true", default=True,
                   help="Skippe les erreurs sans interrompre (défaut).")
    args = p.parse_args()

    files = _gather_metrics_files()
    print(f"Source files trouvés : {len(files)}", file=sys.stderr)

    successes, skipped, failed = 0, 0, 0
    for path, source_tag, ex, mo in files:
        append_args = [sys.executable, str(PROSODY_LAB_ROOT / "bake_append.py"),
                       "--bank", args.bank,
                       "--metrics", str(path),
                       "--motor", mo, "--extract", ex,
                       "--source-path", str(path)]
        if args.dry_run:
            append_args.append("--dry-run")
        # Pour le cas multi-extract, on prépare un fichier temporaire
        metrics_to_pass = path
        tmp = None
        if path.name == "bake_results.json":
            for x, d in _expand_per_extract(path):
                if x == ex:
                    tmp = path.parent / f".__bootstrap_tmp_{ex}.json"
                    tmp.write_text(json.dumps(d, ensure_ascii=False),
                                   encoding="utf-8")
                    metrics_to_pass = tmp
                    break
        append_args = [
            "--bank", args.bank,
            "--metrics", str(metrics_to_pass),
            "--motor", mo, "--extract", ex,
            "--source-path", str(path),
        ]
        if args.dry_run:
            append_args.append("--dry-run")
        rc, err = _ingest_via_append(append_args)
        if tmp and tmp.exists():
            tmp.unlink()
        if rc == 0:
            successes += 1
            print(f"  [OK] {source_tag} {path.name} (extract={ex})", file=sys.stderr)
        elif rc == 4:
            skipped += 1
            print(f"  [SKIP-DUP] {source_tag} {path.name} (extract={ex})",
                  file=sys.stderr)
        else:
            failed += 1
            print(f"  [FAIL rc={rc}] {source_tag} {path.name} (extract={ex}): "
                  f"{err.strip()[:200]}", file=sys.stderr)
            if not args.continue_on_error:
                return rc

    print(f"\nRésumé : OK={successes}, SKIP-DUP={skipped}, FAIL={failed}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())