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

Discriminants -- regles du contrat v1, appliquees ici a la lecture hors
ligne du manifeste seul :

- ``track`` commencant par ``P``          -> ``instrument = "jlens_trackp"``
- ``track`` commencant par ``S``          -> ``instrument = "jlens"``
- ``sae_repo`` ou ``sae_k`` presents      -> ``instrument = "sae"``
- ``lens_repo`` / ``lens_kind`` / ``lens_rank`` -> ``instrument = "jlens"``

**Le champ ``track`` prime sur les cles ``lens_*``**, et c'est la raison
d'etre de cette regle : ``ict.jlens_trackP_traces.load_traces`` charge avec
``expected="jlens_trackp"``, si bien qu'un manifeste Track P estampille
``jlens`` par la seule lecture des cles ``lens_*`` fait lever
``enforce_instrument`` -- l'inference par cles ne voit que deux
instruments la ou le contrat en connait trois. Le migrateur ne peut pas
deviner le chargeur ; le manifeste doit donc porter le discriminant qui
le nomme.

Un manifeste sans ``track`` ni cles ``lens_*`` reste hors perimetre : la
valeur dependrait du chargeur, on ne l'invente pas.

Les tableaux sont recopies inchanges (verification ``array_equal`` par
cle, dtype inclus) ; seul ``__meta__`` gagne des cles. Le format de
compression d'origine (stocke ou deflate) est preserve.

Usage :

    python scripts/migrate_trace_manifests.py              # dry-run
    python scripts/migrate_trace_manifests.py --apply      # ecrit
    python scripts/migrate_trace_manifests.py --check      # verifie sans ecrire

Idempotent et auto-correcteur : un manifeste deja declare un ``instrument``
coherent avec ses discriminants n'est pas retouche (``DEJA``) ; un
``instrument`` qui les contredit est reecrit (``CORRIGE``) -- c'est ce qui
repare une migration anterieure qui aurait fige une valeur que seul le
contexte du chargeur pouvait determiner.
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
CORRIGE = "CORRIGE"
DEJA = "DEJA"
SANS_META = "SANS_META"
SANS_DISCRIMINANT = "SANS_DISCRIMINANT"


def read_meta(z: np.lib.npyio.NpzFile) -> dict:
    """Decode le manifeste JSON embarque sous ``__meta__``."""
    return json.loads(str(z[META_KEY]))


def infer_instrument(meta: dict) -> str | None:
    """Instrument declare par les champs specifiques du manifeste.

    Reprend les regles du contrat v1, y compris celle que sa branche
    d'inference par cles ne peut pas exprimer : ``track`` distingue les
    deux instruments J-Lens (``jlens`` pour Track S, ``jlens_trackp`` pour
    Track P). Sans cette primaute, un manifeste Track P serait estampille
    ``jlens`` et le chargement Track P leverait ``enforce_instrument``.
    """
    track = meta.get("track")
    if isinstance(track, str) and track[:1].upper() == "P":
        return "jlens_trackp"
    if isinstance(track, str) and track[:1].upper() == "S":
        return "jlens"
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

    declare = meta.get("instrument")
    inst = infer_instrument(meta)

    if declare is not None:
        declare = str(declare)
        if inst is None or declare == inst:
            return DEJA, declare, "deja declare"
        # Le manifeste se contredit : une migration anterieure a fige une
        # valeur que les discriminants du fichier dementent. On reecrit.
        correction = True
    else:
        correction = False

    if inst is None:
        return SANS_DISCRIMINANT, "", (
            "ni instrument ni discriminant (sae_*/lens_*/track) : "
            "hors perimetre, a trancher a la main"
        )

    if not apply:
        return "TODO", inst, (
            f"corriger instrument -> {inst!r}" if correction
            else f"stamp instrument={inst!r} + contract_version"
        )

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
    statut = CORRIGE if correction else MIGRATED
    detail = "correction + revalidation sans warning" if correction \
        else "stamp + revalidation sans warning"
    return statut, inst, detail


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
                    derive = infer_instrument(meta)
                    if derive is not None and derive != inst:
                        # instrument absent, ou present mais dementi par les
                        # discriminants du fichier (contradiction a corriger).
                        problems += 1
                        status = ("MIGRATION_MANQUANTE"
                                  if inst not in INSTRUMENTS else "CONTREDIT")
            finally:
                z.close()
            detail = ""
        else:
            status, inst, detail = migrate_file(path, apply=args.apply)
        counts[status] = counts.get(status, 0) + 1
        if status not in (DEJA, SANS_META, SANS_DISCRIMINANT) or args.check:
            print(f"  {status:18s} {inst:6s} {path.name}  {detail}")
        if (status in (MIGRATED, CORRIGE) and args.apply
                and "sans warning" not in detail):
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
