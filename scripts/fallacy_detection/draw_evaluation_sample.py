#!/usr/bin/env python3
"""Tirage de l'echantillon d'evaluation humaine du corpus academique aligne.

Critere 1 de l'issue #20222 (etape 3 de la tranche C, EPIC #17578/#10355) :
un echantillon de paires (texte academique, noeud de taxonomie Argumentum),
stratifie par famille de premier niveau, graine fixee, empreinte SHA-256
consignee.

Unite d'annotation : la paire (texte, noeud). Un texte multi-etiquete produit
une paire par libelle de sophisme DISTINCT qu'il porte ; deux libelles qui
roulent vers le meme noeud (ex. appeal to anger et appeal to pity, tous deux
-> Appeal to emotion) ne produisent QU'UNE paire -- l'evaluateur juge « ce
texte illustre-t-il le noeud X » une fois par noeud.

Chainon de jointure (trois niveaux, tous SOURCES) :
  1. libelle corpus MAFALDA (minuscule, fin) -> classe L2 du papier
     (Helwe et al. 2023, arXiv:2311.09761, Figure 2 -- le papier definit
     L1 = Pathos/Ethos/Logos, L2 = les classes fines ; les libelles du corpus
     SONT les classes L2 du papier) ;
  2. classe L2 papier -> inventaire consolide du script d'alignement
     (align_academic_to_argumentum.py, liste MAFALDA_L2 a 23 classes) -- la
     consolidation suit les mots-cles du script (ex. alias « ad populum » de
     Appeal to popularity, ligne 140) et le regroupement Pathos du papier
     (les sous-emotions -> Appeal to emotion) ;
  3. inventaire -> noeud Argumentum via logic_mafalda_to_argumentum.csv
     (verdict DIRECT / PARTIAL / NOT_FOUND, PR #20315).

Strates : la strate d'evaluation est le croisement (famille Argumentum x
verdict d'alignement). Le tirage par defaut cible les strates DIRECT (le
critere evalue qu'un humain RETROUVE l'etiquette ; une paire dont
l'alignement meme est NOT_FOUND n'a pas d'etiquette a retrouver) puis
complete par PARTIAL sous contrainte de plancher par famille.

Sorties :
  --out-sample  : JSONL, une paire par ligne -- references (fichier, index de
                  ligne, libelle corpus, inventaire, noeud, famille, verdict),
                  JAMAIS le texte lui-meme (pas de derivation CC-BY-SA, le
                  texte se re-lit depuis le corpus sous NOTICE) ;
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
CORPUS_FILES = [
    "MAFALDA/gold_standard_dataset.jsonl",
    "MAFALDA/user_study_examples_with_labels.jsonl",
]

# Etiquettes portees par le corpus mais exclues par conception : 'nothing'
# (pas un sophisme) et 'to clean' (artefact de nettoyage du jeu amont,
# absent des guidelines d'annotation -- verifie sur la copie archivee
# « MAFALDA Annotation Guidelines », gisement GDrive).
EXCLUDED_LABELS = {"nothing", "to clean"}

# Rollup libelle corpus -> inventaire consolide du script d'alignement.
# Source par entree :
#   - DIRECT : le libelle corpus est le meme libelle que l'inventaire
#     (casse pres) ;
#   - PAPER-FIG2 : regroupement Pathos du papier (Helwe 2023, Figure 2) --
#     les sous-emotions sont des enfants L2 de Appeal to Emotion ;
#   - SCRIPT-KW : mot-cle/alias de l'inventaire (align_academic_to_argumentum.py,
#     liste MAFALDA_L2) ;
#   - ETHOS : attaque du locuteur (papier, categorie Ethos de la Figure 2).
CORPUS_TO_INVENTORY = {
    "slippery slope": ("Slippery slope", "DIRECT"),
    "hasty generalization": ("Hasty generalization", "DIRECT"),
    "false analogy": ("False analogy", "DIRECT"),
    "circular reasoning": ("Circular reasoning", "DIRECT"),
    "appeal to fear": ("Appeal to fear", "DIRECT"),
    "appeal to nature": ("Appeal to nature", "DIRECT"),
    "appeal to tradition": ("Appeal to tradition", "DIRECT"),
    "fallacy of division": ("Fallacy of division", "DIRECT"),
    "equivocation": ("Equivocation", "DIRECT"),
    "straw man": ("Straw man", "DIRECT"),
    "ad hominem": ("Ad hominem", "DIRECT"),
    "appeal to pity": ("Appeal to emotion", "PAPER-FIG2"),
    "appeal to anger": ("Appeal to emotion", "PAPER-FIG2"),
    "appeal to positive emotion": ("Appeal to emotion", "PAPER-FIG2"),
    "appeal to ridicule": ("Appeal to emotion", "PAPER-FIG2"),
    "ad populum": ("Appeal to popularity", "SCRIPT-KW"),
    "appeal to (false) authority": ("Appeal to authority", "SCRIPT-KW"),
    "causal oversimplification": ("Causal fallacy", "SCRIPT-KW"),
    "false causality": ("False cause", "SCRIPT-KW"),
    "guilt by association": ("Ad hominem", "ETHOS"),
    "tu quoque": ("Ad hominem", "ETHOS"),
    "false dilemma": ("Fallacy of logic", "SCRIPT-KW"),
}

# Libelles L2 du papier SANS pendant dans l'inventaire consolide : le papier
# (Figure 2) compte « Appeal to Worse Problem » parmi ses classes L2, mais la
# consolidation a 23 classes de align_academic_to_argumentum.py n'en retient
# pas -- ces paires sont non joinables PAR CONSTRUCTION et le manifest les
# signale a part (elles ne relevent d'aucun noeud Argumentum).
PAPER_L2_SANS_INVENTAIRE = {"appeal to worse problems"}

# Seuils du protocole (issue #20222, critere 1) et bornes atteignables
# mesurees sur le corpus in-repo (220 textes, mesure au 2026-10-23) :
#   population joinable 257 paires (texte x noeud) >= les 200 exigees ;
#   Influence ne joint qu'en PARTIAL (sa strate DIRECT n'existe pas dans la
#   population) ; Tricherie est absente de la population joinable (aucun
#   libelle corpus ne roule vers elle) -- bornes consignees dans le manifest.
TARGET_TOTAL = 200
FAMILY_FLOOR = 10


def load_alignment() -> dict[str, dict]:
    with open(ALIGNMENT_CSV, encoding="utf-8") as f:
        return {r["academic_label"]: r for r in csv.DictReader(f)}


def build_pairs(alignment: dict[str, dict]) -> tuple[list[dict], Counter, Counter]:
    """Construit la population joinable : une paire (texte, noeud) dedupliquee
    par noeud, plus les compteurs de libelles non joinables (pour le rapport).

    Le lookup rollup est insensible a la casse : le corpus melange les
    graphies ('appeal to ridicule' et 'Appeal to Ridicule' sont deux ecritures
    du meme libelle L2 du papier).
    """
    rollup_ci = {k.lower(): v for k, v in CORPUS_TO_INVENTORY.items()}
    pairs: dict[tuple[str, int, str], dict] = {}
    unjoinable: Counter = Counter()
    unaligned_inventory: Counter = Counter()
    for rel in CORPUS_FILES:
        path = DATA_ACademic / rel
        with open(path, encoding="utf-8") as f:
            for idx, line in enumerate(f):
                doc = json.loads(line)
                labels = {lab for _, _, lab in doc["labels"]}
                seen_nodes: set[str] = set()
                for lab in sorted(labels):
                    if lab in EXCLUDED_LABELS:
                        continue
                    entry = rollup_ci.get(lab.lower())
                    if entry is None:
                        unjoinable[lab.lower()] += 1
                        continue
                    inv, _source = entry
                    al = alignment.get(inv)
                    if al is None:
                        unaligned_inventory[inv] += 1
                        continue
                    node = al["best_name"]
                    if node in seen_nodes:
                        continue  # dedup par noeud : une paire par (texte, noeud)
                    seen_nodes.add(node)
                    pairs[(rel, idx, node)] = {
                        "source_file": rel,
                        "line_index": idx,
                        "corpus_label": lab,
                        "inventory_label": inv,
                        "node": node,
                        "family": al["best_famille"],
                        "verdict": al["verdict"],
                    }
    return list(pairs.values()), unjoinable, unaligned_inventory


def stratified_draw(pairs: list[dict], seed: int, total: int, floor: int) -> list[dict]:
    """Tirage stratifie deterministe (famille x verdict).

    Ordre de priorite : strates DIRECT d'abord (jusqu'au plancher par famille,
    puis au prorata), complement PARTIAL ensuite. Les strates NOT_FOUND ne
    sont jamais tirees : leur etiquette n'est pas censee etre retrouvable.
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

    # 2. compler vers le total au prorata des strates DIRECT restantes.
    remaining = total - len(picked)
    if remaining > 0:
        pool: list[dict] = []
        for fam in sorted(familles_direct):
            pool.extend(familles_direct[fam][min(floor, len(familles_direct[fam])):])
        take = min(remaining, len(pool))
        picked.extend(pool[:take])
        remaining -= take
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
    parser.add_argument("--out-sample", type=Path, required=True)
    parser.add_argument("--out-manifest", type=Path, required=True)
    parser.add_argument("--report-only", action="store_true",
                        help="mesure la population et sort le manifest, sans echantillon")
    args = parser.parse_args(argv)

    alignment = load_alignment()
    pairs, unjoinable, unaligned = build_pairs(alignment)

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
        "population_joinable": len(pairs),
        "population_par_famille": dict(sorted(family_counts.items())),
        "population_par_strate": {
            f"{fam} x {verdict}": n for (fam, verdict), n in sorted(strata_counts.items())
        },
        "libelles_exclus": sorted(EXCLUDED_LABELS),
        "paper_l2_sans_inventaire": {
            lab: n for lab, n in sorted(unjoinable.items()) if lab in PAPER_L2_SANS_INVENTAIRE
        },
        "libelles_non_joinables": {
            lab: n for lab, n in sorted(unjoinable.items())
            if lab not in PAPER_L2_SANS_INVENTAIRE
        },
        "inventaire_sans_alignement": dict(unaligned),
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
