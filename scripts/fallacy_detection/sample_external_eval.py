#!/usr/bin/env python3
"""Echantillonnage stratifie du corpus academique pour le test externe humain (issue #20222).

Grain 1 de #20222 (EPIC #17578 tranche C, grand-mere #10355) : produire
l'**instrument** d'evaluation -- l'echantillonneur et son protocole -- sans
attendre ni le merge de la table d'alignement (#20028) ni l'arbitrage user sur
le panel d'evaluateurs (Q25). L'instrument est **corpus-agnostique** : il
consomme tout JSONL aligne portant ``text`` et ``node`` ; quand l'alignement
merge, une seule commande produit l'echantillon reel.

Trois proprietes sont mesurees, pas supposees :

1. **Le plancher par famille est tenu ou l'outil refuse.** Chaque famille de
   premier niveau doit fournir au moins ``--min-per-family`` paires ; une
   famille deficiente fait echouer la commande en nommant les familles
   deficientes et leur taille -- jamais un echantillon silencieusement
   desequilibre.
2. **L'aveugle est structurel, pas conventionnel.** La feuille d'annotation
   emise pour les evaluateurs ne contient **ni** le champ ``node`` **ni** le
   champ ``family`` : la famille de premier niveau est la premiere moitie de
   la reponse attendue, et la cle de correction vit dans un fichier separe,
   les deux etant epingles par SHA-256 dans le manifeste. Un evaluateur qui
   ouvre la feuille ne peut pas voir l'etiquette, meme par accident de colonne.
3. **Le tirage est reproducible et affiche.** Meme graine = meme echantillon
   (identite mesurable par SHA de la feuille) ; le manifeste consigne graine,
   effectifs par famille et les empreintes SHA-256 de la source, de la feuille
   et de la cle.

Allocation : chaque famille recoit d'abord le plancher ``min_per_family``,
puis le reliquat de ``n`` est reparti proportionnellement aux tailles (methode
du plus grand reste), sans jamais depasser la taille d'une famille. Si le
corpus ne peut pas fournir ``n`` paires sous ces contraintes, la commande
echoue en citant le maximum atteignable.

Usage::

    python scripts/fallacy_detection/sample_external_eval.py \
        --input data/academic/aligned.jsonl \
        --out-dir MyIA.AI.Notebooks/GenAI/FallacyDetection/data/external_eval/run1 \
        --n 200 --min-per-family 10 --seed 42 --family-separator "/"
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from pathlib import Path


def sha256_of(path: Path) -> str:
    """Empreinte SHA-256 d'un fichier, lue par blocs (corpus volumineux OK)."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_corpus(input_path: Path, family_separator: str) -> list[dict]:
    """Charge le JSONL aligne ; echoue (fail-closed) sur toute ligne invalide."""
    corpus: list[dict] = []
    with input_path.open(encoding="utf-8") as handle:
        for lineno, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            missing = [f for f in ("text", "node") if f not in record]
            if missing:
                raise SystemExit(
                    f"Ligne {lineno} de {input_path} : champs manquants {missing}. "
                    "Le format attendu est un JSONL aligne portant 'text' et 'node'."
                )
            family = record["node"].split(family_separator)[0].strip()
            if not family:
                raise SystemExit(
                    f"Ligne {lineno} : famille de premier niveau vide pour le noeud "
                    f"'{record['node']}' (separateur '{family_separator}')."
                )
            corpus.append({"text": record["text"], "node": record["node"], "family": family})
    if not corpus:
        raise SystemExit(f"{input_path} : aucun enregistrement charge.")
    return corpus


def allocate(n: int, min_per_family: int, family_sizes: dict[str, int]) -> dict[str, int]:
    """Repartit n items : plancher par famille, puis plus grand reste proportionnel."""
    families = sorted(family_sizes)
    deficient = {f: family_sizes[f] for f in families if family_sizes[f] < min_per_family}
    if deficient:
        detail = ", ".join(f"{f}={k}" for f, k in deficient.items())
        raise SystemExit(
            f"Plancher {min_per_family}/famille intenable : {detail}. "
            "Echantillon refuse -- elargir le corpus ou baisser le plancher."
        )
    allocation = {f: min_per_family for f in families}
    remaining = n - sum(allocation.values())
    if remaining < 0:
        raise SystemExit(
            f"n={n} inferieur au plancher total {sum(allocation.values())} "
            f"({len(families)} familles x {min_per_family})."
        )
    headroom = {f: family_sizes[f] - allocation[f] for f in families}
    total_headroom = sum(headroom.values())
    if remaining > total_headroom:
        raise SystemExit(
            f"n={n} intenable : maximum atteignable = "
            f"{sum(allocation.values()) + total_headroom} "
            f"(planchers + reliquats disponibles)."
        )
    if remaining == 0:
        # Aucun reliquat a repartir (n egale la somme des planchers, ou chaque
        # famille est deja saturee) : la repartition est complete. Sans ce
        # retour, la repartition proportionnelle diviserait par un reliquat nul.
        return allocation
    # Plus grand reste sur les headrooms : chaque famille gagne sa part entiere,
    # les plus gros restes absorbent les arrondis perdus.
    quotas = {f: headroom[f] * remaining / total_headroom for f in families}
    for f in families:
        allocation[f] += int(quotas[f])
    leftover = remaining - sum(int(quotas[f]) for f in families)
    by_remainder = sorted(families, key=lambda f: (quotas[f] % 1), reverse=True)
    for f in by_remainder[:leftover]:
        allocation[f] += 1
    return allocation


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--input", required=True, type=Path, help="JSONL aligne (champs text, node)")
    parser.add_argument("--out-dir", required=True, type=Path, help="repertoire de sortie (sheet/key/manifest)")
    parser.add_argument("--n", type=int, default=200, help="taille totale de l'echantillon (defaut 200)")
    parser.add_argument("--min-per-family", type=int, default=10, help="plancher par famille de 1er niveau (defaut 10)")
    parser.add_argument("--seed", type=int, default=42, help="graine du tirage (defaut 42)")
    parser.add_argument("--family-separator", default="/", help="separateur de chemin du noeud (defaut '/')")
    args = parser.parse_args(argv)

    corpus = load_corpus(args.input, args.family_separator)
    by_family: dict[str, list[dict]] = {}
    for record in corpus:
        by_family.setdefault(record["family"], []).append(record)
    allocation = allocate(args.n, args.min_per_family, {f: len(v) for f, v in by_family.items()})

    rng = random.Random(args.seed)
    picked: list[dict] = []
    for family in sorted(by_family):
        # Tri par empreinte du texte : l'ordre de tir ne depend que du contenu,
        # pas de l'ordre de lecture du fichier source.
        pool = sorted(by_family[family], key=lambda r: hashlib.sha256(r["text"].encode()).hexdigest())
        picked.extend(rng.sample(pool, allocation[family]))
    rng.shuffle(picked)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    sheet_path = args.out_dir / "sheet.jsonl"
    key_path = args.out_dir / "key.jsonl"
    with sheet_path.open("w", encoding="utf-8") as sheet, key_path.open("w", encoding="utf-8") as key:
        for record in picked:
            # Identifiant adresse par le contenu (noeud + texte), volontairement
            # opaque : un identifiant qui afficherait la graine la donnerait a
            # lire a l'evaluateur, et la graine suffit a rejouer le tirage sur un
            # corpus public. L'identifiant ne revele donc ni graine ni rang.
            item_id = "eval-" + hashlib.sha256(
                f"{record['node']}\x00{record['text']}".encode()
            ).hexdigest()[:12]
            # La feuille ne porte NI le noeud NI sa famille : la famille de
            # premier niveau est la premiere moitie de la reponse attendue, et
            # la laisser sur la feuille rendrait l'alpha branche circulaire.
            # Elle vit dans la cle, ou elle sert a la stratification.
            sheet.write(json.dumps({"item_id": item_id, "text": record["text"]},
                                   ensure_ascii=False) + "\n")
            key.write(json.dumps({"item_id": item_id, "family": record["family"], "node": record["node"]},
                                 ensure_ascii=False) + "\n")

    manifest = {
        "issue": 20222,
        "seed": args.seed,
        "n": len(picked),
        "min_per_family": args.min_per_family,
        "per_family_counts": allocation,
        "source": {"path": str(args.input), "sha256": sha256_of(args.input)},
        "sheet_sha256": sha256_of(sheet_path),
        "key_sha256": sha256_of(key_path),
        "note": "Feuille sheet.jsonl = aveugle (ni noeud ni famille) ; cle key.jsonl = correction, a garder hors des mains des evaluateurs.",
    }
    manifest_path = args.out_dir / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    counts = ", ".join(f"{f}={allocation[f]}" for f in sorted(allocation))
    print(f"Echantillon {len(picked)} items ({counts})")
    print(f"Feuille (aveugle) : {sheet_path}")
    print(f"Cle (correction)  : {key_path}")
    print(f"Manifeste         : {manifest_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
