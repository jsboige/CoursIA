"""bake_append.py — append (ou valider) un run au banc de référence TTS.

Usage (depuis la racine du dépôt ou un worktree) :
    python prosody_lab/bake_append.py --bank prosody_lab/bake_bank.jsonl \\
        --metrics path/to/metrics.json \\
        --machine myia-po-2023 \\
        --motor qwen3_tts_1_7b_customvoice \\
        --extract A \\
        [--seed 0] \\
        [--motor-license Apache-2.0] \\
        [--dry-run]

Le banc est un fichier JSONL (une ligne par run), append-only par défaut.
La validation utilise `jsonschema` si disponible ; à défaut, un validateur
interne couvrant les champs requis et les types.

Idempotence : la clé d'unicité est (motor, extract, extract_text_sha256_prefix, seed, ts).
Un run avec exactement la même clé est refusé (exit 4) — pas d'écrasement
silencieux. Pour ré-mesurer un même couple (motor, extract, seed), incrémenter
le `ts` (ou ajouter `notes` distinctement).
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import socket
import sys
from pathlib import Path

# Chemins relatifs — à appeler depuis la racine du dépôt ou un worktree.
PROSODY_LAB_ROOT = Path(__file__).resolve().parent
SCHEMA_PATH = PROSODY_LAB_ROOT / "bank_schema_v1.json"


def _load_schema() -> dict:
    if not SCHEMA_PATH.exists():
        raise SystemExit(f"Schéma introuvable : {SCHEMA_PATH}. "
                         f"bake_append.py doit vivre à côté de bank_schema_v1.json.")
    with open(SCHEMA_PATH, encoding="utf-8") as f:
        return json.load(f)


def _ts_now() -> str:
    """Timestamp ISO 8601 UTC, suffixe Z."""
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _sha256_prefix(text: str, n: int = 16) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:n]


def _infer_machine() -> str:
    """Déduit l'identité machine depuis COMPUTERNAME (mieux que hostname,
    cf. CLAUDE.md global)."""
    name = os.environ.get("COMPUTERNAME") or socket.gethostname() or "unknown"
    mapping = {
        "MACHINE-PO2023": "myia-po-2023",
        "MACHINE-PO2024": "myia-po-2024",
        "MACHINE-PO2025": "myia-po-2025",
        "MACHINE-PO2026": "myia-po-2026",
        "MACHINE-PO2027": "myia-po-2027",
        "MACHINE-AI01": "myia-ai-01",
        "MACHINE-WEB2": "myia-web2",
    }
    return mapping.get(name.upper(), name.lower())


def _parse_size_b(s: str | float | int | None) -> float | None:
    """Convertit "1.7B", "100M", "0.5B" en milliards (float). None si non parsable."""
    if s is None:
        return None
    if isinstance(s, (int, float)):
        return float(s)
    if not isinstance(s, str):
        return None
    s = s.strip().upper()
    try:
        if s.endswith("B"):
            return float(s[:-1])
        if s.endswith("M"):
            return float(s[:-1]) / 1000.0
        if s.endswith("K"):
            return float(s[:-1]) / 1_000_000.0
        return float(s)
    except ValueError:
        return None


def _coerce_metrics(metrics: dict) -> dict:
    """Adapte un metrics.json (chat-bakeoff ou A0-review) au schéma v1.

    Stratégie : mapping direct pour les noms évidents, défaut à null pour les
    champs non couverts par le source. Les champs de fidélité ne sont pas
    calculés ici — ils doivent venir d'un audit ASR croisé (gate pré-UAT
    #17586) ou être passés explicitement.
    """
    out = {"schema_version": "v1", "ts": _ts_now(), "machine": _infer_machine()}

    # Champs directs
    direct_keys = {
        "motor": "motor",
        "motor_size_b": "motor_size_b",
        "size": "motor_size_b",
        "license": "motor_license",
        "extract": "extract",
        "seed": "seed",
        "speaker": "speaker",
        "instruct": "instruct",
        "language": "language",
        "wer": "wer",
        "wer_model": "wer_model",
        "rtf": "rtf",
        "vram_peak_gb": "vram_mb",  # GO → MO
        "duration_s": "duration_s",
        "load_s": "load_s",
        "wallclock_total_s": "wallclock_total_s",
    }
    for src, dst in direct_keys.items():
        if src in metrics and metrics[src] is not None:
            v = metrics[src]
            # Cas particulier : wer peut être {wer, hyp, model} → on extrait .wer
            if src == "wer" and isinstance(v, dict):
                v = v.get("wer")
            # Cas particulier : seed peut être {base, per_chunk} → on extrait .base
            if src == "seed" and isinstance(v, dict):
                v = v.get("base")
            # Conversion GB→MB si on lit vram_peak_gb
            if src == "vram_peak_gb" and isinstance(v, (int, float)):
                v = float(v) * 1024.0
            # Parse "1.7B" / "100M" pour motor_size_b
            if src in {"size", "motor_size_b"}:
                v = _parse_size_b(v)
            out[dst] = v

    # Prosodie imbriquée
    prosody = metrics.get("prosody") or metrics.get("metrics") or {}
    if isinstance(prosody, dict):
        if "g_st_range" in prosody:
            out["prosody_st_range"] = prosody["g_st_range"]
        if "g_cv" in prosody:
            out["prosody_cv"] = prosody["g_cv"]
        if "g_velocity" in prosody:
            out["prosody_velocity"] = prosody["g_velocity"]
        if "g_verdict" in prosody:
            out["prosody_verdict"] = prosody["g_verdict"]

    # Texte de référence (extract_text_sha256_prefix + chars)
    text = metrics.get("text") or metrics.get("extract_text")
    if text:
        out["extract_text_sha256_prefix"] = _sha256_prefix(text)
        out["extract_text_chars"] = len(text)

    return out


def _validate_locally(record: dict, schema: dict) -> list[str]:
    """Validateur interne minimaliste : couvre required + types principaux.

    Renvoie la liste des erreurs (vide = OK). Le validateur jsonschema est
    préféré quand disponible ; celui-ci est le filet de sécurité.
    """
    errs = []
    for req in schema.get("required", []):
        if req not in record:
            errs.append(f"champ requis manquant : {req!r}")
    props = schema.get("properties", {})
    for k, v in record.items():
        if k not in props:
            errs.append(f"champ non autorisé par le schéma : {k!r}")
        spec = props.get(k, {})
        if "const" in spec and v != spec["const"]:
            errs.append(f"{k!r} doit valoir {spec['const']!r}, reçu {v!r}")
        if "enum" in spec and v is not None and v not in spec["enum"]:
            errs.append(f"{k!r} doit être dans {spec['enum']!r}, reçu {v!r}")
        if spec.get("type") == "integer" and not isinstance(v, int):
            errs.append(f"{k!r} doit être un entier, reçu {type(v).__name__}")
        if spec.get("type") == "number" and not isinstance(v, (int, float)):
            errs.append(f"{k!r} doit être un nombre, reçu {type(v).__name__}")
        if spec.get("type") == "string" and not isinstance(v, str):
            errs.append(f"{k!r} doit être une chaîne, reçu {type(v).__name__}")
        if spec.get("type") == "boolean" and not isinstance(v, bool):
            errs.append(f"{k!r} doit être un booléen, reçu {type(v).__name__}")
    return errs


def _validate_jsonschema(record: dict, schema: dict) -> list[str]:
    """Validateur jsonschema (si dispo). Renvoie [] si OK."""
    try:
        import jsonschema
    except ImportError:
        return []  # validateur interne prend le relais
    v = jsonschema.Draft7Validator(schema)
    return [f"{'/'.join(map(str, e.path))}: {e.message}" for e in v.iter_errors(record)]


def _key(record: dict) -> tuple:
    """Clé d'idempotence (motor, extract, sha256_prefix, seed). Le `ts` est
    un horodatage, pas une clé — deux mesures du même couple (même moteur,
    même extrait, même texte de référence, même graine) doivent collisionner,
    sinon le banc se remplirait de doublons à chaque ré-exécution."""
    return (
        record["motor"],
        record["extract"],
        record.get("extract_text_sha256_prefix", ""),
        record.get("seed"),
    )


def _existing_keys(bank_path: Path) -> set[tuple]:
    keys = set()
    if not bank_path.exists():
        return keys
    with open(bank_path, encoding="utf-8") as f:
        for ln in f:
            ln = ln.strip()
            if not ln:
                continue
            try:
                rec = json.loads(ln)
                keys.add(_key(rec))
            except json.JSONDecodeError:
                continue
    return keys


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--bank", required=True, help="Chemin du banc JSONL (créé si absent).")
    p.add_argument("--metrics", required=True, help="metrics.json source à ingérer.")
    p.add_argument("--machine", default=None, help="Override machine (sinon inféré).")
    p.add_argument("--motor", required=True, help="Identifiant du moteur TTS.")
    p.add_argument("--extract", required=True, choices=["A", "B", "C", "D", "E"],
                   help="Identifiant de l'extrait.")
    p.add_argument("--seed", type=int, default=None)
    p.add_argument("--motor-license", default=None)
    p.add_argument("--notes", default=None)
    p.add_argument("--source-path", default=None,
                   help="Chemin source (traçabilité bootstrap).")
    p.add_argument("--dry-run", action="store_true",
                   help="Valide sans écrire.")
    args = p.parse_args()

    schema = _load_schema()
    metrics_path = Path(args.metrics)
    if not metrics_path.exists():
        print(f"metrics.json introuvable : {metrics_path}", file=sys.stderr)
        return 2
    with open(metrics_path, encoding="utf-8") as f:
        metrics = json.load(f)

    record = _coerce_metrics(metrics)
    # Overrides CLI
    if args.machine:
        record["machine"] = args.machine
    record["motor"] = args.motor
    record["extract"] = args.extract
    if args.seed is not None:
        record["seed"] = args.seed
    if args.motor_license:
        record["motor_license"] = args.motor_license
    if args.notes:
        record["notes"] = args.notes
    if args.source_path:
        record["source_path"] = args.source_path

    # Validation jsonschema d'abord (plus stricte), validateur interne en filet
    errs = _validate_jsonschema(record, schema)
    if not errs:
        errs = _validate_locally(record, schema)
    if errs:
        print("Validation échouée :", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        return 3

    bank_path = Path(args.bank)
    bank_path.parent.mkdir(parents=True, exist_ok=True)

    # Idempotence
    existing = _existing_keys(bank_path)
    k = _key(record)
    if k in existing:
        print(f"Run déjà présent dans le banc (clé : motor={k[0]}, "
              f"extract={k[1]}, sha256_prefix={k[2][:8]}…, seed={k[3]}).",
              file=sys.stderr)
        return 4

    if args.dry_run:
        print(json.dumps(record, ensure_ascii=False, indent=2))
        print("Dry-run : pas d'écriture.", file=sys.stderr)
        return 0

    with open(bank_path, "a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")
    print(f"Run ajouté au banc : {bank_path}")
    print(f"  motor={record['motor']} extract={record['extract']} "
          f"wer={record.get('wer')} rtf={record.get('rtf')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())