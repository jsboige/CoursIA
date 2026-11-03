#!/usr/bin/env python3
"""Migration canonique des manifestes de traces historiques au contrat v1.

Pose ``meta['instrument']`` (et ``contract_version`` si absent) dans les
``.npz`` de ``traces/`` dont le manifeste porte les discriminants
d'instrument mais pas la declaration canonique. C'est exactement la
migration que prescrit le ``UserWarning`` retro-compat du contrat
(:issue:`15476` acceptance #4) : « Migrer l'extracteur GPU pour poser
``meta['instrument']`` canoniquement -- le contrat v1 prefere la
declaration explicite a l'inference. » Apres migration, le chargement ne
warn plus : l'anti-melange (acceptance #1) est RENFORCE, la donnee
s'autodeclare au lieu d'etre inferee.

Discriminants (memes regles que ``ict.trace_contract.validate_manifest``,
aucune reimplementation du cote inference -- la valeur stampee est celle
que le contrat infererait, verifiee par revalidation post-ecriture) :

- ``sae_repo`` ou ``sae_k`` presents      -> ``instrument = "sae"``
- ``lens_repo`` / ``lens_kind`` / ``lens_rank`` -> ``instrument = "jlens"``

Les tableaux sont recopies inchanges (verification ``array_equal`` par
cle, dtype inclus) ; seul ``__meta__`` gagne des cles. Le format de
compression d'origine (stocke ou deflate) est preserve.

Usage :

    python scripts/migrate_trace_manifests.py              # dry-run
    python scripts/migrate_trace_manifests.py --apply      # ecrit
    python scripts/migrate_trace_manifests.py --check      # verifie sans ecrire

Idempotent : un manifeste deja declare ``instrument`` n'est pas retouche.
"""
from __future__ import annotations

import argparse
import json
import sys
import warnings
import zipfile
from pathlib import Path

import numpy as np

# Package ict/ depuis le parent du dossier scripts/ (meme cablage que les
# extracteurs, qui vivent au meme niveau).
ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from ict.trace_contract import (  # noqa: E402
    CONTRACT_VERSION,
    INSTRUMENTS,
    enforce_instrument,
    validate_manifest,
)

META_KEY = "__meta__"
TRACES_DIR = ROOT / "traces"

# Statuts rendus par migrate_file.
MIGRATED = "MIGRATED"
DEJA = "DEJA"
SANS_META = "SANS_META"
SANS_DISCRIMINANT = "SANS_DISCRIMINANT"


def read_meta(z: np.lib.npyio.NpzFile) -> dict:
    """Decode le manifeste JSON embarque sous ``__meta__``."""
    return json.loads(str(z[META_KEY]))


def infer_instrument(meta: dict) -> str | None:
    """Instrument declare par les champs specifiques du manifeste.

    Miroir exact de la branche d'inference de ``validate_manifest`` : la
    valeur stampee est celle que le contrat infererait au chargement -- la
    migration ne fait qu'expliciter ce que la trace porte deja.
    """
    if "sae_repo" in meta or "sae_k" in meta:
        return "sae"
    if any(k in meta for k in ("lens_repo", "lens_kind", "lens_rank")):
        return "jlens"
    return None


def _savez_like(path: Path, arrays: dict) -> None:
    """Reecrit le .npz en preservant la compression d'origine."""
    compressed = False
    with zipfile.ZipFile(path) as zf:
        for info in zf.infolist():
            if info.compress_type == zipfile.ZIP_DEFLATED:
                compressed = True
                break
    saver = np.savez_compressed if compressed else np.savez
    saver(path, **arrays)


def migrate_file(path: Path, *, apply: bool = False) -> tuple[str, str, str]:
    """Migre un .npz ; rend (statut, instrument, detail).

    En dry-run (``apply=False``), calcule la decision sans ecrire. Apres
    ecriture, revalidation systEmatique : arrays identiques, manifeste
    complet, et ``validate_manifest`` + ``enforce_instrument`` passent
    SANS aucun warning.
    """
    z = np.load(path, allow_pickle=False)
    try:
        if META_KEY not in z.files:
            return SANS_META, "", "pas de __meta__"
        meta = read_meta(z)
    finally:
        z.close()

    if "instrument" in meta:
        return DEJA, str(meta["instrument"]), "deja declare"

    inst = infer_instrument(meta)
    if inst is None:
        return SANS_DISCRIMINANT, "", (
            "ni instrument ni discriminant (sae_*/lens_*) : "
            "hors perimetre, a trancher a la main"
        )

    if not apply:
        return "TODO", inst, f"stamp instrument={inst!r} + contract_version"

    z = np.load(path, allow_pickle=False)
    try:
        arrays = {name: z[name] for name in z.files}
    finally:
        z.close()

    meta = dict(meta)
    meta["instrument"] = inst
    meta.setdefault("contract_version", CONTRACT_VERSION)
    arrays[META_KEY] = np.array(json.dumps(meta))
    _savez_like(path, arrays)

    # Verification : byte-egalite des tableaux + contrat silencieux.
    z2 = np.load(path, allow_pickle=False)
    try:
        for name, arr in arrays.items():
            if name == META_KEY:
                continue
            if not np.array_equal(z2[name], arr) or z2[name].dtype != arr.dtype:
                raise RuntimeError(
                    f"{path.name}: tableau {name} altere par la reecriture"
                )
        meta2 = read_meta(z2)
    finally:
        z2.close()
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        valide = validate_manifest(meta2, strict=False, expected=inst)
        enforce_instrument(valide, inst)
    if not valide["instrument"] == inst:
        raise RuntimeError(f"{path.name}: instrument non stampé")
    return MIGRATED, inst, "stamp + revalidation sans warning"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--traces-dir", type=Path, default=TRACES_DIR,
        help="dossier des .npz (defaut: traces/ de la serie)",
    )
    parser.add_argument(
        "--apply", action="store_true",
        help="ecrire la migration (defaut: dry-run)",
    )
    parser.add_argument(
        "--check", action="store_true",
        help="verification seule : DEJA attendu partout ou un discriminant existe",
    )
    args = parser.parse_args(argv)

    npz_paths = sorted(args.traces_dir.glob("*.npz"))
    if not npz_paths:
        print(f"aucun .npz sous {args.traces_dir}", file=sys.stderr)
        return 2

    counts: dict[str, int] = {}
    problems = 0
    for path in npz_paths:
        if args.check:
            z = np.load(path, allow_pickle=False)
            try:
                if META_KEY not in z.files:
                    status, inst = SANS_META, ""
                else:
                    meta = read_meta(z)
                    inst = str(meta.get("instrument", ""))
                    status = DEJA if inst in INSTRUMENTS else SANS_DISCRIMINANT
                    if inst not in INSTRUMENTS and infer_instrument(meta) is not None:
                        # discriminant present mais instrument absent : la
                        # migration n'a pas couvert ce fichier.
                        problems += 1
                        status = "MIGRATION_MANQUANTE"
            finally:
                z.close()
            detail = ""
        else:
            status, inst, detail = migrate_file(path, apply=args.apply)
        counts[status] = counts.get(status, 0) + 1
        if status not in (DEJA, SANS_META, SANS_DISCRIMINANT) or args.check:
            print(f"  {status:18s} {inst:6s} {path.name}  {detail}")
        if status == MIGRATED and args.apply and "revalidation sans warning" not in detail:
            problems += 1

    print("--")
    for status, n in sorted(counts.items()):
        print(f"  {status:18s} {n}")
    if args.check:
        print(f"check : {'OK' if problems == 0 else f'{problems} migration(s) manquante(s)'}")
        return 1 if problems else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
