#!/usr/bin/env python3
"""Tirage de l'echantillon d'evaluation humaine du corpus academique aligne.

Critere 1 de l'issue #20222 (etape 3 de la tranche C, EPIC #17578/#10355) :
un echantillon de paires (texte academique, noeud de taxonomie Argumentum),
stratifie par famille de premier niveau, graine fixee, empreinte SHA-256
consignee.

Source de population : l'artefait de reference ``aligned_corpus.jsonl``,
produit par ``build_aligned_eval_corpus.py`` (ponts declares, exclusions
consignees, adjudications PARTIAL, unicite (texte, noeud) garantie a
l'emission). Le tirage ne reconstruit PLUS le join : avant l'unification, il
portait une seconde implementation du chainon (rollup propre, exclusions
propres) qui divergeait du builder -- 257 paires contre 225, deux populations
pour un meme protocole. Desormais la population du tirage EST le corpus
commis, et le test ``test_population_egale_corpus_aligne`` epingle
``population == len(aligned_corpus.jsonl)`` : la derive revient au prochain
changement de regle cote builder, elle ne peut plus naitre cote tirage.

Seul lookup residuel : le verdict d'alignement (DIRECT/PARTIAL), que l'artefait
n'enregistre pas, est retrouve dans la table d'alignement
(logic_mafalda_to_argumentum.csv) par l'identifiant QUE l'artefait porte deja
-- ``source_label`` pour les correspondances exactes, la cible du pont dans
``match`` ("bridge:<L2>") pour les ponts declares. Ce lookup ne reimplemente
aucune regle du builder : il lit une colonne de la table source, clee par un
champ de l'artefact.

Unite d'annotation : la paire (texte, noeud), dedupliquee par le builder a
l'emission (deux libelles d'un meme texte qui roulent vers le meme noeud ne
produisent qu'une paire ; les libelles fusionnes vivent dans ``source_labels``
cote artefact).

Strates : la strate d'evaluation est le croisement (famille Argumentum x
verdict d'alignement). Le tirage par defaut cible les strates DIRECT (le
critere evalue qu'un humain RETROUVE l'etiquette) puis complete par PARTIAL
sous contrainte de plancher par famille. Les lignes NOT_FOUND n'entrent jamais
dans le corpus (exclues par le builder).

Sorties :
  --out-sample  : JSONL, une paire par ligne -- references (fichier gold,
                  numero de ligne 1-based, libelle corpus, inventaire, noeud,
                  famille, verdict, type de correspondance), JAMAIS le texte
                  lui-meme (pas de derivation CC-BY-SA, le texte se re-lit
                  depuis le corpus sous NOTICE) ;
  --out-manifest: JSON -- graine, SHA-256 de l'echantillon, comptes par
                  strate, population joinable totale, bornes atteintes.

Usage :
  python scripts/fallacy_detection/draw_evaluation_sample.py \
      --seed 42 --out-sample sample.jsonl --out-manifest manifest.json
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import random
import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DATA_ACademic = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/academic"
ALIGNMENT_CSV = DATA_ACademic / "logic_mafalda_to_argumentum.csv"
ALIGNED_CORPUS = DATA_ACademic / "aligned/aligned_corpus.jsonl"
JOIN_REPORT = DATA_ACademic / "aligned/join_report.json"
GOLD_FILE = "MAFALDA/gold_standard_dataset.jsonl"

# Seuils du protocole (issue #20222, critere 1) et bornes atteignables
# mesurees sur le corpus aligne commis (225 paires, mesure au 2026-11-08) :
#   population joinable 225 paires (texte x noeud, dedup a l'emission) >=
#   les 200 exigees ; Influence joint en DIRECT (30) et PARTIAL adjuge (11) ;
#   Tricherie est absente de la population (aucune paire source ne roule vers
#   elle) -- borne consignee dans le manifest.
TARGET_TOTAL = 200
FAMILY_FLOOR = 10


def load_alignment() -> dict[str, dict]:
    with open(ALIGNMENT_CSV, encoding="utf-8") as f:
        return {r["academic_label"]: r for r in csv.DictReader(f)}


def _table_key(rec: dict) -> str:
    """Cle de table d'un enregistrement du corpus aligne : le libelle source
    pour une correspondance exacte, la cible du pont pour un pont declare."""
    if rec["match"] == "exact":
        return rec["source_label"]
    return rec["match"].split(":", 1)[1]


def load_pairs(corpus_path: Path, alignment: dict[str, dict]) -> list[dict]:
    """Charge la population depuis l'artefait de reference.

    Le texte verbatim n'est JAMAIS reporte dans les paires : seules les
    references sortent (le texte se re-lit depuis le corpus sous NOTICE).
    Le verdict d'alignement est retrouve dans la table par l'identifiant que
    l'artefait porte (cf. _table_key) ; une cle absente de la table est une
    incoherence artefact/table, elle echoue bruyamment plutot que de produire
    une paire sans verdict.
    """
    rollup_ci = {" ".join(k.lower().split()): v for k, v in alignment.items()}
    pairs: list[dict] = []
    with open(corpus_path, encoding="utf-8") as f:
        for line in f:
            rec = json.loads(line)
            row = rollup_ci[" ".join(_table_key(rec).lower().split())]
            family, node = rec["node"].split("/", 1)
            pairs.append({
                "source_file": GOLD_FILE,
                "line_index": rec["gold_line"],  # 1-based, cf. builder
                "corpus_label": rec["source_label"],
                "inventory_label": _table_key(rec),
                "node": node,
                "family": family,
                "verdict": row["verdict"],
                "match": rec["match"],
            })
    return pairs


def _prorata_quotas(remaining: int, sizes: dict[str, int]) -> dict[str, int]:
    """Repartition proportionnelle deterministe des sieges restants.

    Methode du plus fort reste a la D'Hondt : chaque siege va a la strate
    qui maximise taille/(sieges_deja_pris + 1), donc le quota final suit la
    proportion des restes de chaque famille. Plafonne par construction a la
    population de chaque strate (une strate epuisee ne recoit plus rien).
    Egalites tranchees par cle triee : deux runs memes entrees donnent le
    meme quota, graine mise a part.
    """
    quotas = {k: 0 for k in sizes}
    for _ in range(remaining):
        best_k = None
        best_rate = -1.0
        for k in sorted(sizes):
            if quotas[k] >= sizes[k]:
                continue
            rate = sizes[k] / (quotas[k] + 1)
            if rate > best_rate:
                best_k, best_rate = k, rate
        if best_k is None:
            break  # toutes les strates sont epuisees
        quotas[best_k] += 1
    return quotas


def stratified_draw(pairs: list[dict], seed: int, total: int, floor: int) -> list[dict]:
    """Tirage stratifie deterministe (famille x verdict).

    Ordre de priorite : strates DIRECT d'abord (jusqu'au plancher par famille,
    puis au prorata), complement PARTIAL ensuite. Les strates NOT_FOUND ne
    sont jamais tirees : le builder les exclut du corpus, et leur etiquette
    n'est de toute facon pas censee etre retrouvable.
    """
    rng = random.Random(seed)
    strata: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for p in pairs:
        strata[(p["family"], p["verdict"])].append(p)
    for members in strata.values():
        members.sort(key=lambda p: (p["source_file"], p["line_index"], p["node"]))
        rng.shuffle(members)

    direct = {k: v for k, v in strata.items() if k[1] == "DIRECT"}
    partial = {k: v for k, v in strata.items() if k[1] == "PARTIAL"}
    picked: list[dict] = []

    familles_direct = defaultdict(list)
    for (fam, _v), members in direct.items():
        familles_direct[fam].extend(members)

    # 1. plancher par famille sur les strates DIRECT (dans la limite de la
    # population -- une famille sous le plancher est prise en entier, la
    # borne est consignee, pas maquillee).
    for fam in sorted(familles_direct):
        members = familles_direct[fam]
        take = min(floor, len(members))
        picked.extend(members[:take])

    # 2. completer vers le total au prorata des strates DIRECT restantes :
    #    chaque famille recoit un quota proportionnel a son reste, pas un
    #    remplissage sequentiel qui servirait les premieres familles tri
    #    et laisserait les dernieres vides.
    remaining = total - len(picked)
    if remaining > 0:
        leftovers = {
            fam: familles_direct[fam][min(floor, len(familles_direct[fam])):]
            for fam in sorted(familles_direct)
        }
        quotas = _prorata_quotas(remaining, {f: len(v) for f, v in leftovers.items()})
        for fam in sorted(leftovers):
            picked.extend(leftovers[fam][: quotas[fam]])
        remaining -= sum(quotas.values())
        # 3. si DIRECT epuise, complement PARTIAL (documente dans le manifest).
        if remaining > 0:
            ppool: list[dict] = []
            for key in sorted(partial):
                ppool.extend(partial[key])
            picked.extend(ppool[: min(remaining, len(ppool))])

    picked.sort(key=lambda p: (p["source_file"], p["line_index"], p["node"]))
    return picked


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=42, help="graine du tirage (consignee)")
    parser.add_argument("--total", type=int, default=TARGET_TOTAL,
                        help=f"cible de paires (défaut {TARGET_TOTAL})")
    parser.add_argument("--floor", type=int, default=FAMILY_FLOOR,
                        help=f"plancher par famille (défaut {FAMILY_FLOOR})")
    parser.add_argument("--corpus", type=Path, default=ALIGNED_CORPUS,
                        help="corpus aligne de reference (défaut : artefact commis)")
    parser.add_argument("--out-sample", type=Path, required=True)
    parser.add_argument("--out-manifest", type=Path, required=True)
    parser.add_argument("--report-only", action="store_true",
                        help="mesure la population et sort le manifest, sans echantillon")
    args = parser.parse_args(argv)

    alignment = load_alignment()
    pairs = load_pairs(args.corpus, alignment)

    strata_counts = Counter((p["family"], p["verdict"]) for p in pairs)
    family_counts = Counter(p["family"] for p in pairs)

    sample: list[dict] = []
    if not args.report_only:
        sample = stratified_draw(pairs, args.seed, args.total, args.floor)
        with open(args.out_sample, "w", encoding="utf-8") as f:
            for p in sample:
                f.write(json.dumps(p, ensure_ascii=False) + "\n")
        sample_sha = sha256_file(args.out_sample)
    else:
        sample_sha = None

    manifest = {
        "issue": 20222,
        "seed": args.seed,
        "target_total": args.total,
        "family_floor": args.floor,
        "corpus_source": str(args.corpus),
        "population_joinable": len(pairs),
        "population_par_famille": dict(sorted(family_counts.items())),
        "population_par_strate": {
            f"{fam} x {verdict}": n for (fam, verdict), n in sorted(strata_counts.items())
        },
        # Les exclusions (nothing, to clean, L2 sans inventaire, PARTIAL non
        # adjugees) vivent dans le rapport du builder : le tirage ne les
        # recalcule plus, il renvoie a la source.
        "exclusions_amont": str(JOIN_REPORT),
        "echantillon_taille": len(sample),
        "echantillon_par_famille": dict(sorted(Counter(p["family"] for p in sample).items())),
        "echantillon_par_verdict": dict(sorted(Counter(p["verdict"] for p in sample).items())),
        "echantillon_sha256": sample_sha,
        "bornes": {
            "critere_200_atteint": len(sample) >= 200,
            "familles_sous_plancher": sorted(
                f for f, n in Counter(p["family"] for p in sample).items() if n < args.floor
            ),
            "familles_absentes_de_la_population": sorted(
                set(al["best_famille"] for al in alignment.values()) - set(family_counts)
            ),
        },
    }
    with open(args.out_manifest, "w", encoding="utf-8") as f:
        json.dump(manifest, f, ensure_ascii=False, indent=2)

    print(json.dumps({
        "population": len(pairs),
        "echantillon": len(sample),
        "sha256": sample_sha,
        "critere_200": manifest["bornes"]["critere_200_atteint"],
        "familles_sous_plancher": manifest["bornes"]["familles_sous_plancher"],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
