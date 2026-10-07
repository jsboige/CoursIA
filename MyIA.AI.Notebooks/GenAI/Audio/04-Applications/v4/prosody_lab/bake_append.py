"""bake_append.py -- append (upsert) un run au banc de reference TTS.

Schéma : bank_schema_v1.json. Cle d'unicite : (motor, extract, seed). Idempotent :
re-append avec la meme cle REMPLACE l'ancien run (meme ts/machine corriges).

Usage :
    # Append un run isole :
    python bake_append.py --bank runs/bake_bank.json --run '
    {
      "ts": "2026-10-08T01:00:00Z",
      "machine": "myia-po-2027",
      "motor": "chatterbox_mtl_v3",
      "extract": "A",
      "seed": 42,
      "wer": 0.4179,
      "duration_s": 17.4,
      "rtf": 2.51,
      "vram_mb": 3072,
      "voice_stable": true,
      "asr_models": ["tiny"],
      "notes": "bakeoff_small/chatterbox_mtl_v3 (PR #17661)"
    }'

    # Append depuis un fichier JSON (un seul objet ou liste) :
    python bake_append.py --bank runs/bake_bank.json --file runs/seed_run.json

    # Ingestion depuis un repertoire bakeoff_small (le run s_bake_results.json + fichiers A__/B__) :
    python bake_append.py --bank runs/bake_bank.json --ingest-bakeoff-small \\
        --root MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bakeoff_small

    # Append + post-validation (default : valide le schema avant ecriture) :
    python bake_append.py --bank runs/bake_bank.json --run '{...}' --dry-run

Codes de retour :
    0 = succes (run ajoute ou remplace)
    1 = erreur de validation (schema)
    2 = chemin invalide
    3 = IO erreur
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA_VERSION = "v1"
DEFAULT_BANK = Path("runs/bake_bank.json")
THIS_DIR = Path(__file__).resolve().parent
SCHEMA_PATH = THIS_DIR / f"bank_schema_{SCHEMA_VERSION}.json"


def load_schema() -> dict:
    if not SCHEMA_PATH.exists():
        raise FileNotFoundError(f"schema introuvable: {SCHEMA_PATH}")
    return json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))


def load_bank(path: Path) -> list[dict]:
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError(f"bank root doit etre une liste JSON, got {type(data).__name__}")
    return data


def save_bank(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def validate_run(run: dict, schema: dict) -> list[str]:
    """Valide un run contre le schema. Retourne la liste des erreurs (vide = OK)."""
    errs: list[str] = []
    item_schema = schema.get("items", {})
    required = item_schema.get("required", [])
    properties = item_schema.get("properties", {})

    for f in required:
        if f not in run:
            errs.append(f"champ obligatoire absent: {f!r}")

    for fname, fdef in properties.items():
        if fname not in run:
            continue
        val = run[fname]
        ftype = fdef.get("type")
        # "type": [...] is a JSON-Schema union ("number" or "null" -> nullable)
        types = ftype if isinstance(ftype, list) else [ftype]
        if val is None and "null" in types:
            continue
        if val is None:
            errs.append(f"{fname!r}: null non autorise (type={types})")
            continue
        # Type check per type
        ok = False
        for t in types:
            if t == "string" and isinstance(val, str):
                ok = True
                break
            if t == "number" and isinstance(val, (int, float)) and not isinstance(val, bool):
                ok = True
                break
            if t == "integer" and isinstance(val, int) and not isinstance(val, bool):
                ok = True
                break
            if t == "boolean" and isinstance(val, bool):
                ok = True
                break
            if t == "array" and isinstance(val, list):
                ok = True
                break
            if t == "object" and isinstance(val, dict):
                ok = True
                break
        if not ok:
            errs.append(f"{fname!r}: type attendu {types}, got {type(val).__name__}")
            continue
        # enum check
        if "enum" in fdef and val not in fdef["enum"]:
            errs.append(f"{fname!r}: {val!r} hors enum {fdef['enum']}")
        if "minimum" in fdef and isinstance(val, (int, float)) and val < fdef["minimum"]:
            errs.append(f"{fname!r}: {val} < minimum {fdef['minimum']}")
        if "maximum" in fdef and isinstance(val, (int, float)) and val > fdef["maximum"]:
            errs.append(f"{fname!r}: {val} > maximum {fdef['maximum']}")
        # array items enum
        if ftype == "array" and "items" in fdef and isinstance(val, list):
            item_enum = fdef["items"].get("enum")
            if item_enum:
                for j, v in enumerate(val):
                    if v not in item_enum:
                        errs.append(f"{fname!r}[{j}]: {v!r} hors enum {item_enum}")
    return errs


def upsert(bank: list[dict], run: dict) -> tuple[list[dict], str]:
    """Upsert un run dans le banc par cle (motor, extract, seed). Retourne (nouveau_banc, action)."""
    key = ("motor", "extract", "seed")
    for i, row in enumerate(bank):
        if all(row.get(k) == run.get(k) for k in key):
            bank[i] = run
            return bank, "replaced"
    bank.append(run)
    return bank, "appended"


def parse_run_arg(text: str) -> dict:
    """Decode un run depuis un argument --run (JSON inline) ou un fichier JSON."""
    text = text.strip()
    # Heuristique : commence par '{' -> JSON inline, sinon chemin de fichier
    if text.startswith("{"):
        return json.loads(text)
    p = Path(text)
    if not p.exists():
        raise FileNotFoundError(f"fichier JSON introuvable: {p}")
    data = json.loads(p.read_text(encoding="utf-8"))
    if isinstance(data, dict):
        return data
    if isinstance(data, list) and len(data) == 1:
        return data[0]
    raise ValueError(f"fichier doit etre un objet ou une liste a 1 element, got {type(data).__name__}")


def ingest_bakeoff_small(root: Path) -> list[dict]:
    """Ingere les runs depuis bakeoff_small/results/<motor>/bake_results.json
    et bakeoff_small/results/<motor>/<extract>__<motor>.json.

    Mapping :
    - bake_results.json : schema dict contains lists `results` (chatterbox_mtl_v3, etc.)
    - <extract>__<motor>.json : schema par-extrait (pocket_tts, etc.)
    """
    runs: list[dict] = []
    if not root.exists():
        return runs
    # 1) bake_results.json par moteur
    for path in root.glob("*/bake_results.json"):
        motor_dir = path.parent
        motor = motor_dir.name
        data = json.loads(path.read_text(encoding="utf-8"))
        for r in data.get("results", []):
            extract = r.get("extract")
            if not extract:
                continue
            seed_guess = 42  # default bakeoff_small
            # RTF : non mesuré ici, peut être dérivé de duration_s + render_s si dispo
            rtf = None
            duration_s = r.get("duration_s")
            wer = r.get("wer")
            run = {
                "ts": "2026-09-24T00:00:00Z",
                "machine": "myia-po-2027",
                "motor": motor,
                "extract": extract,
                "seed": seed_guess,
                "wer": wer,
                "rtf": rtf,
                "vram_mb": None,
                "duration_s": duration_s,
                "voice_stable": None,
                "hallu_per_100_syl": None,
                "inserted_words": None,
                "omitted_segments": None,
                "asr_models": ["tiny"] if wer is not None else None,
                "notes": f"bakeoff_small/{motor} (PR #17661)",
            }
            runs.append(run)
    # 2) Fichiers per-extrait (pocket_tts et autres sans bake_results.json)
    for path in root.glob("*/*.json"):
        if path.name == "bake_results.json":
            continue
        name = path.stem  # ex: A__pocket_tts
        if "__" not in name:
            continue
        extract, motor = name.split("__", 1)
        if extract not in {"A", "B", "C", "A_long", "B_long"}:
            continue
        data = json.loads(path.read_text(encoding="utf-8"))
        metrics = data.get("metrics", {})
        duration_s = metrics.get("duration_s")
        wer = data.get("wer")
        # Inference : pocket_tts CPU, Whisper-tiny non chargé => wer null
        notes = data.get("wer_explanation") or f"bakeoff_small/{motor} (PR #17661)"
        run = {
            "ts": "2026-09-24T00:00:00Z",
            "machine": "myia-po-2027",
            "motor": motor,
            "extract": extract,
            "seed": 42,
            "wer": wer,
            "rtf": None,
            "vram_mb": None,
            "duration_s": duration_s,
            "voice_stable": None,
            "hallu_per_100_syl": None,
            "inserted_words": None,
            "omitted_segments": None,
            "asr_models": ["tiny"] if wer is not None else None,
            "notes": notes[:200],
        }
        runs.append(run)
    return runs


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--bank", type=Path, default=DEFAULT_BANK,
                   help=f"Chemin du fichier banc (default: {DEFAULT_BANK})")
    p.add_argument("--run", type=str, default=None,
                   help="JSON inline du run, OU chemin vers un fichier .json")
    p.add_argument("--file", type=str, default=None,
                   help="Fichier JSON (objet ou liste)")
    p.add_argument("--ingest-root", dest="ingest_root", type=Path, default=None,
                   help="Repertoire a ingerer (bakeoff_small/results ou autre). Le script decouvre bake_results.json et <extract>__<motor>.json.")
    p.add_argument("--machine", type=str, default="myia-po-2027",
                   help="Lane si non specifiee dans le run (default: myia-po-2027)")
    p.add_argument("--dry-run", action="store_true",
                   help="Valide et affiche sans ecriture")
    p.add_argument("--strict", action="store_true",
                   help="Echoue sur warning d'inference (RTF/seed/notes)")
    args = p.parse_args()

    schema = load_schema()

    new_runs: list[dict] = []
    if args.run:
        new_runs.append(parse_run_arg(args.run))
    if args.file:
        fpath = Path(args.file)
        data = json.loads(fpath.read_text(encoding="utf-8"))
        if isinstance(data, list):
            new_runs.extend(data)
        else:
            new_runs.append(data)
    if args.ingest_root:
        new_runs.extend(ingest_bakeoff_small(args.ingest_root))

    if not new_runs:
        print("Aucun run a append (--run, --file, ou --ingest-root requis)", file=sys.stderr)
        return 2

    # Validation
    validation_errors: list[str] = []
    for i, r in enumerate(new_runs):
        if "machine" not in r:
            r["machine"] = args.machine
        errs = validate_run(r, schema)
        if errs:
            validation_errors.append(f"run[{i}] {r.get('motor', '?')}/{r.get('extract', '?')}: " + "; ".join(errs))

    if validation_errors:
        print("VALIDATION FAILED:", file=sys.stderr)
        for e in validation_errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    if args.dry_run:
        print(f"DRY-RUN : {len(new_runs)} run(s) valide(s). Aucune ecriture.")
        for r in new_runs:
            print(f"  - {r['motor']}/{r['extract']}/seed={r['seed']} wer={r.get('wer')} duration={r.get('duration_s')}s")
        return 0

    # Charger le banc existant + upsert
    bank = load_bank(args.bank)
    counts = {"appended": 0, "replaced": 0}
    for r in new_runs:
        bank, action = upsert(bank, r)
        counts[action] += 1

    save_bank(args.bank, bank)
    print(f"Banc ecrit: {args.bank} ({len(bank)} total, +{counts['appended']} append, ~{counts['replaced']} replace)")
    return 0


if __name__ == "__main__":
    sys.exit(main())