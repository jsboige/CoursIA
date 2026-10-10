"""Validation du corpus a tiers strate 6 (port S6-B, issue #7742).

Miroir du scaffold EPITA ``scripts/coursia_s6b/validate_fables_tier.py``,
adapte au layout CoursIA. Quatre Familles de verifications :

1. **Contrat de schema** -- chaque source du tier public porte les cles
   requises (``extract_definition_v1``) et des ids opaques.
2. **Vie privee** -- le tier references ne porte aucun champ texte ; le tier
   public n'expose aucune trace d'URL ; aucun artefact emis ne porte de texte.
3. **Round-trip chiffre** -- un blob temoin est construit, relu et compare
   dans un repertoire temporaire (rien n'est ecrit dans le depot) : la
   machinerie ``.json.gz.enc`` est prouvee a chaque execution.
4. **Garde anti-depot** -- la garde refuse une source en clair suivie par
   git (verifiee sur un fichier du depot lui-meme, controle positif).

Sortie : verdict JSON opaque-id-only sur stdout. Codes de sortie : 0 = vert,
1 = invariant viole, 2 = usage.

Usage :

    python -m ict.validate_extracts_tiers [--corpus DIR] [--dry-run]

``--dry-run`` saute le round-trip chiffre (et la garde) : verification de
contrat seule, sans derivation de cle (utile en environnement sans
``cryptography``).
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List

from ict import extracts_tiers as et

DRY_RUN_BANNER = "dry-run : contrat seul, round-trip exclu"


def _fail(checks: List[Dict[str, Any]], name: str, detail: str) -> None:
    checks.append({"check": name, "verdict": "FAIL", "detail": detail})


def _ok(checks: List[Dict[str, Any]], name: str, detail: str) -> None:
    checks.append({"check": name, "verdict": "OK", "detail": detail})


def check_public_tier(corpus: Path, checks: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    try:
        defs = et.load_public_definitions(corpus)
    except (ValueError, FileNotFoundError) as exc:
        _fail(checks, "public_schema", str(exc))
        return []
    if not defs:
        _fail(checks, "public_nonempty", "aucune source publique chargee")
    else:
        _ok(
            checks,
            "public_schema",
            f"{len(defs)} source(s), ids opaques, host_parts retires",
        )
    return defs


def check_references_tier(corpus: Path, checks: List[Dict[str, Any]]) -> None:
    try:
        refs = et.load_fetch_references(corpus)
    except (ValueError, FileNotFoundError) as exc:
        _fail(checks, "references_privacy", str(exc))
        return
    if not refs:
        _fail(checks, "references_nonempty", "aucune fiche de reference chargee")
    else:
        _ok(checks, "references_privacy", f"{len(refs)} fiche(s), zero champ texte")


def check_roundtrip(checks: List[Dict[str, Any]]) -> None:
    """Construit, relit et compare un blob temoin hors du depot."""
    definitions: List[Dict[str, Any]] = [
        {
            "source_name": "fable_probe_v1",
            "source_type": "fable",
            "schema": et.EXTRACT_DEFINITION_SCHEMA,
            "host_parts": ["corpus", "probe", "fable_probe_v1"],
            "path": "probe",
            "extracts": [
                {"extract_id": "fable_probe_v1_ext_0", "text": "temoin"}
            ],
        }
    ]
    with tempfile.TemporaryDirectory(prefix="ict_s6b_probe_") as tmp:
        blob_path = Path(tmp) / "probe.json.gz.enc"
        summary = et.build_encrypted_tier(definitions, blob_path, "passphrase-de-probe")
        loaded = et.load_encrypted_definitions(blob_path, passphrase="passphrase-de-probe")
        if summary["n_sources"] == 1 and loaded == definitions:
            _ok(checks, "roundtrip_encrypted", "blob temoin ecrit/relu, payload identique")
        else:
            _fail(checks, "roundtrip_encrypted", "payload relu != payload ecrit")
        # mauvaise passphrase : doit lever InvalidToken, pas corrompre en silence
        try:
            et.load_encrypted_definitions(blob_path, passphrase="mauvaise")
            _fail(checks, "roundtrip_bad_passphrase", "aucune erreur sur mauvaise passphrase")
        except Exception:
            _ok(checks, "roundtrip_bad_passphrase", "mauvaise passphrase levee")


def check_anti_deposit_guard(checks: List[Dict[str, Any]]) -> None:
    """Controle positif : un fichier suivi par git doit etre refuse."""
    # ict/__init__.py : suivi par git des l'origine de la serie (le
    # validateur lui-meme ne l'est qu'une fois commite).
    tracked = Path(__file__).resolve().parent / "__init__.py"
    try:
        et.assert_not_git_tracked(tracked)
        _fail(checks, "anti_deposit_guard", "un fichier suivi par git n'a pas ete refuse")
    except ValueError:
        _ok(checks, "anti_deposit_guard", "un fichier suivi par git est refuse (controle positif)")


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--corpus",
        default=str(Path(__file__).resolve().parent.parent / "corpus"),
        help="repertoire corpus (defaut : corpus/ de la serie)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="contrat seul : pas de derivation de cle, pas de round-trip",
    )
    args = parser.parse_args(argv)
    corpus = Path(args.corpus)

    checks: List[Dict[str, Any]] = []
    public = check_public_tier(corpus, checks)
    check_references_tier(corpus, checks)
    if public:
        summary = et.opaque_summary(public)
        _ok(checks, "public_opaque_summary", json.dumps(summary, ensure_ascii=False))
    if args.dry_run:
        print(DRY_RUN_BANNER)
    else:
        check_roundtrip(checks)
        check_anti_deposit_guard(checks)

    verdict = {
        "schema": "coursia_s6b_validation_v1",
        "corpus": str(corpus),
        "dry_run": args.dry_run,
        "checks": checks,
        "verdict": "PASS" if all(c["verdict"] == "OK" for c in checks) else "FAIL",
    }
    print(json.dumps(verdict, ensure_ascii=False, indent=2))
    return 0 if verdict["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
