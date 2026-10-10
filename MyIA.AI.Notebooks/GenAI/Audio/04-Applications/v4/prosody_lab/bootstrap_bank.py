"""bootstrap_bank.py — ingère les JSON de mesures existants au banc v1 (couche #19722).

Porté sur le socle durci mergé par #19820 : la découverte des sources et le
mapping des champs étendus (fidélité, prosodie, traçabilité moteur) vivent ici ;
l'écriture, la validation de schéma et l'upsert par (motor, extract, seed) sont
délégués à bake_append.py de main (CLI --run, JSON inline).

Sources ingérées :
1. `prosody_lab/bakeoff_small/results/**/*.json` (chatterbox c.1462, pocket_tts c.17661)
2. `prosody_lab/bakeoff_large/results/**/metrics.json` (banc_phase_a0.py)
3. `G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-*/**/*-metrics.json` (re-rendus UAT)

Usage (depuis la racine du dépôt ou un worktree) :
    python MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bootstrap_bank.py \\
        --bank <banc.json> [--dry-run] [--source bakeoff_small]

Idempotent : l'upsert de bake_append.py par (motor, extract, seed) remplace un
run de même clé au lieu de le dupliquer.
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import subprocess
import sys
from pathlib import Path

PROSODY_LAB_ROOT = Path(__file__).resolve().parent
BAKE_APPEND = PROSODY_LAB_ROOT / "bake_append.py"

# Racines des sources
SOURCES = [
    ("bakeoff_small", PROSODY_LAB_ROOT / "bakeoff_small" / "results"),
    ("bakeoff_large", PROSODY_LAB_ROOT / "bakeoff_large" / "results"),
]
# GDrive-mount A0-review (Windows)
GDrive_REVIEW = Path(r"G:/Mon Drive/MyIA/Projets/BibliothequesSonores")

# Champs du socle main
_SOCLE_KEYS = [
    "seed", "wer", "rtf", "vram_mb", "duration_s",
    "voice_stable", "hallu_per_100_syl", "inserted_words", "omitted_segments",
    "asr_models", "notes",
]
# Champs étendus #19722 (optionnels dans le schéma)
_EXTENDED_KEYS = [
    "motor_size_b", "motor_license", "wer_model",
    "load_s", "wallclock_total_s", "extract_text_chars",
    "extract_text_sha256_prefix", "prosody_st_range", "prosody_cv",
    "prosody_velocity", "prosody_verdict", "fidelity_added_words",
    "fidelity_omitted_segments_3plus", "voice_consistent",
    "language", "speaker", "instruct",
]


def _detect_extract(path: Path) -> str | None:
    """Déduit (A|B|C...) depuis le nom de fichier `A__xxx.json` ou `B__xxx.json`."""
    m = re.match(r"^([A-E])__", path.stem)
    if m:
        return m.group(1)
    for p in [path.stem, path.parent.name]:
        m = re.match(r"^([A-E])(?:__|-|$)", p)
        if m:
            return m.group(1)
    return None


def _detect_motor(path: Path) -> str:
    """Déduit le moteur depuis le chemin (segment parent snake_case le plus proche)."""
    p = path
    while p.parent != p:
        parent = p.parent.name
        if parent not in {"results", "prosody_lab"} and not parent.startswith("."):
            if re.match(r"^[a-z0-9_]+$", parent):
                return parent
        p = p.parent
    return "unknown"


def _gdrive_metrics_files() -> list[Path]:
    """Liste les `*-metrics.json` sous BibliothequesSonores/A0-review-*."""
    if not GDrive_REVIEW.exists():
        return []
    out: list[Path] = []
    for review_dir in GDrive_REVIEW.glob("A0-review-*"):
        out.extend(review_dir.glob("*-metrics.json"))
    return out


def _gdrive_extract_from_stem(stem: str) -> str | None:
    """Décode extract depuis un nom de fichier A0-review : campagne A0 = extrait A.

    Terrain (2026-10-10, A0-review-2026100{6,7}) : tous les stems `A0C-*`
    portent l'ouverture de Boule de Suif, l'extrait A de la campagne A0. Le « C »
    de « A0C » appartient au nom de campagne, ce n'est pas une lettre d'extrait
    — l'ancien regex `^A0([A-E])` décodait « C » à tort (contradiction interne
    de la version #19722 : la docstring disait A, la regex disait C, le texte
    source tranche).
    """
    return "A" if stem.startswith("A0") else None


def _gdrive_motor_from_stem(stem: str) -> str | None:
    """Décode motor depuis `A0C-<motor>-...-metrics`."""
    s = re.sub(r"^A0[A-E][-_]?", "", stem)
    s = re.sub(r"-(?:chunked-)?(?:chunked-)?metrics$", "", s)
    s = re.sub(r"-chunked$", "", s)
    return s.strip("-_") or None


def _load_metrics(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        print(f"  [SKIP] illisible : {path} : {e}", file=sys.stderr)
        return None


def _gather_metrics_files() -> list[tuple[Path, str, str | None, str]]:
    """Scanne les sources et retourne (path, source_tag, extract, motor).

    `bake_results.json` contient un tableau `results` (1 entrée par extrait) :
    expansé en N tuples partageant le même path.
    """
    out: list[tuple[Path, str, str | None, str]] = []
    for source_tag, root in SOURCES:
        if not root.exists():
            continue
        for p in root.rglob("*.json"):
            if p.name == "bake_results.json":
                try:
                    data = json.loads(p.read_text(encoding="utf-8"))
                except Exception as e:
                    print(f"  [SKIP] bake_results illisible : {p} : {e}", file=sys.stderr)
                    continue
                motor = data.get("cell") or _detect_motor(p)
                for r in data.get("results", []):
                    ex = r.get("extract")
                    if ex:
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
    """Pour bake_results.json : retourne [(extract, per_extract_dict), ...].

    Les métadonnées moteur du conteneur (cell/license/size) sont fusionnées dans
    chaque entrée.
    """
    out: list[tuple[str, dict]] = []
    data = json.loads(path.read_text(encoding="utf-8"))
    base = {
        "motor": data.get("cell") or _detect_motor(path),
        "motor_license": data.get("license"),
        "motor_size_b": data.get("size"),
    }
    for r in data.get("results", []):
        ex = r.get("extract")
        if ex:
            out.append((ex, {**base, **r}))
    return out


# Enum asr_models du schéma v1 (mapping id long -> court)
_ASR_ENUM = ["tiny", "base", "small", "medium",
             "large-v1", "large-v2", "large-v3", "distil-large-v3"]
_LANGUAGE_NAMES = {"french": "fr", "english": "en", "français": "fr"}


def _flatten_gdrive(m: dict) -> dict:
    """Aplatit un metrics.json A0-review (re-rendus UAT GDrive).

    Ces fichiers portent des sous-dicts (`wer.wer` + `wer.model`, `seed.base`,
    `prosody.*`, `synth.*`) que le schéma v1 attend à plat. Seules les
    correspondances sûres sont mappées ; `synth.model` (id HF) est conservé
    sous `synth_model` pour traçabilité (additionalProperties).
    """
    out = dict(m)
    wer = m.get("wer")
    if isinstance(wer, dict):
        out["wer"] = wer.get("wer")
        model = wer.get("model") or ""
        if model:
            out.setdefault("wer_model", model)
            short = model.removeprefix("faster-whisper-")
            if short in _ASR_ENUM:
                out.setdefault("asr_models", [short])
    seed = m.get("seed")
    if isinstance(seed, dict):
        out["seed"] = seed.get("base")
    prosody = m.get("prosody")
    if isinstance(prosody, dict):
        if isinstance(prosody.get("duration_s"), (int, float)):
            out.setdefault("duration_s", prosody["duration_s"])
        if isinstance(prosody.get("melodic_span_p5p95_st"), (int, float)):
            out.setdefault("prosody_st_range", prosody["melodic_span_p5p95_st"])
        if prosody.get("melody_verdict") in ("EXPRESSIVE", "INSUFFICIENT", "FLAT"):
            out.setdefault("prosody_verdict", prosody["melody_verdict"])
        if "voice_verdict" in prosody:
            out.setdefault("voice_consistent",
                           prosody.get("voice_verdict") == "CONSISTENT")
    synth = m.get("synth")
    if isinstance(synth, dict):
        if isinstance(synth.get("duration_s"), (int, float)):
            out.setdefault("duration_s", synth["duration_s"])
        if isinstance(synth.get("rtf"), (int, float)):
            out.setdefault("rtf", synth["rtf"])
        if isinstance(synth.get("vram_peak_gb"), (int, float)):
            out.setdefault("vram_mb", int(round(synth["vram_peak_gb"] * 1024)))
        if synth.get("language"):
            lang = str(synth["language"])
            out.setdefault("language", _LANGUAGE_NAMES.get(lang.lower(), lang))
        for k in ("speaker", "instruct"):
            if synth.get(k) is not None:
                out.setdefault(k, synth[k])
        if synth.get("model"):
            out["synth_model"] = synth["model"]
    return out


def _normalize_motor(motor: str) -> str:
    """Uniformise la graphie d'un moteur en snake_case.

    Le même moteur arrive sous deux formes selon la campagne : `chatterbox_mtl_v3`
    (bakeoff) et `chatterbox-mtl-v3` (stem GDrive A0-review). Sans uniformisation,
    l'upsert par (motor, extract, seed) laisse deux lignes pour un seul moteur et
    le cumul cross-campagne — la raison d'être du banc — est cassé.
    """
    return motor.strip().replace("-", "_")


def _metrics_to_run(path: Path, metrics: dict, motor: str, extract: str) -> dict:
    """Mappe un dict métriques source vers un run complet (socle + étendus).

    Les champs absents de la source ne sont pas posés (le schéma les veut
    optionnels) ; les clés du sous-dict `metrics` des fichiers bakeoff_large /
    per-extrait sont aplaties d'abord.
    """
    flat = dict(metrics)
    nested = metrics.get("metrics")
    if isinstance(nested, dict):
        for k, v in nested.items():
            flat.setdefault(k, v)

    # Normalisations de types hétérogènes entre campagnes :
    # `size` des bake_results.json porte un label humain ("0.5B") ;
    # `g_st_range`/`g_cv` des bakeoff_* sont les champs prosodie du schéma.
    if isinstance(flat.get("motor_size_b"), str):
        m = re.search(r"([0-9]+(?:\.[0-9]+)?)", flat["motor_size_b"])
        flat["motor_size_b"] = float(m.group(1)) if m else None
    for src_key, dst_key in (("g_st_range", "prosody_st_range"),
                             ("g_cv", "prosody_cv")):
        if dst_key not in flat and isinstance(flat.get(src_key), (int, float)):
            flat[dst_key] = flat[src_key]

    src = str(path.relative_to(PROSODY_LAB_ROOT)) \
        if PROSODY_LAB_ROOT in path.parents else str(path)
    run: dict = {
        "schema_version": "v1",
        "ts": flat.get("ts") or datetime.datetime.now(datetime.timezone.utc)
              .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "machine": flat.get("machine") or "myia-po-2027",
        "motor": _normalize_motor(motor),
        "extract": extract,
        "seed": flat.get("seed") if isinstance(flat.get("seed"), int) else 42,
        "duration_s": flat.get("duration_s"),
        "notes": (flat.get("notes") or f"bootstrap:{path.name}")[:200],
        "source_path": src,
    }
    for key in _SOCLE_KEYS + _EXTENDED_KEYS:
        if key in flat and flat[key] is not None:
            run[key] = flat[key]
    if run.get("duration_s") is None:
        # requis par le schéma main : valeur nulle refusée par validate_run
        run["duration_s"] = 0.0
        run["notes"] = (run["notes"] + " ; duration_s inconnue")[:200]
    return run


def _ingest_run(bank: Path, run: dict, dry_run: bool) -> tuple[int, str]:
    """Pousse un run vers bake_append.py de main (CLI --run, JSON inline)."""
    args = [sys.executable, str(BAKE_APPEND),
            "--bank", str(bank), "--run", json.dumps(run, ensure_ascii=False)]
    if dry_run:
        args.append("--dry-run")
    proc = subprocess.run(args, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    return proc.returncode, (proc.stderr or proc.stdout or "")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--bank", required=True, help="Fichier banc cible (JSON).")
    p.add_argument("--dry-run", action="store_true",
                   help="Valide et affiche sans écriture.")
    p.add_argument("--source",
                   choices=["bakeoff_small", "bakeoff_large", "gdrive", "all"],
                   default="all", help="Limite l'ingestion à une source.")
    args = p.parse_args()

    files = _gather_metrics_files()
    if args.source != "all":
        files = [f for f in files if f[1] == args.source]
    print(f"Source files trouvés : {len(files)}", file=sys.stderr)

    successes, skipped, failed = 0, 0, 0
    for path, source_tag, ex, mo in files:
        if path.name == "bake_results.json":
            entries = _expand_per_extract(path)
        else:
            data = _load_metrics(path)
            entries = [(ex or "", data)] if isinstance(data, dict) else []
        for entry_ex, metrics in entries:
            extract_id = entry_ex or ex
            if not extract_id:
                skipped += 1
                continue
            if source_tag == "gdrive":
                metrics = _flatten_gdrive(metrics)
            run = _metrics_to_run(path, metrics, mo, extract_id)
            rc, err = _ingest_run(Path(args.bank), run, args.dry_run)
            if rc == 0:
                successes += 1
            else:
                failed += 1
                print(f"  [ERR] {path.name} ({mo}/{extract_id}) : {err.strip()[:200]}",
                      file=sys.stderr)
    print(f"ok={successes} skip={skipped} err={failed}"
          + (" (dry-run)" if args.dry_run else ""), file=sys.stderr)
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
