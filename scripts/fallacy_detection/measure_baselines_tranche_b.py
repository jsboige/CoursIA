"""Baselines de la Phase 3 (gate de #17578, EPIC #10355) sur le corpus tranche B.

Ce que mesure ce script
-----------------------
L'instrument canonique `baseline_branch_detection.py` (meme repertoire) mesure
les baselines du gate — majoritaire, aleatoire, lexicale TF-IDF + centroide,
a regles — avec plis groupes par scenario, et quantifie l'ecart de fuite
entre plis groupes et plis naifs. Il refuse **nommement** un niveau dont le
support par etiquette est sous le plancher de 2.

Sur le corpus commite (280 paires de validation), le niveau « noeud » est
refuse : 280 etiquettes pour 280 paires, support maximal 1. Le gate de Phase 3
exige une exactitude a la feuille exacte, donc il demande un corpus ou chaque
noeud porte plusieurs paires.

Ce script **rejoue l'instrument tel quel** (aucune reimplementation) sur le
corpus tranche B, et ajoute la seule chose qui manquait : la mesure de l'effet
de la **decision de filtre encore ouverte chez ai-01** — filtrer le corpus sur
le taux de round-trip, ou livrer le corpus complet avec ce taux en metadonnee.
Les deux cotes sont mesurees, pour que la reference du gate tienne whichever
arbitrage.

Sortie
------
Un agregat JSON (`--json`) et un rapport markdown (`--md`) : par variante
(split x filtre) et par niveau, la structure du corpus, les baselines, l'ecart
de fuite, et — pour un niveau refuse — le message de refus verbatim.

Usage :
    python scripts/fallacy_detection/measure_baselines_tranche_b.py \\
        --corpus-dir "G:/Mon Drive/MyIA/IA/teacher-corpus-17578" \\
        --out-dir scripts/fallacy_detection/results
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import baseline_branch_detection as organ  # noqa: E402  (organe canonique du gate)

#: Le filtre mesure : on ne garde que les paires dont le round-trip a reussi.
#: Le champ `roundtrip` est porte par le corpus ; il n'est pas calcule ici.
CRITERE_FILTRE = "roundtrip == true"

#: (cle de variante, split, filtre applique)
VARIANTES = [
    ("train_complet", "train_fr.jsonl", False),
    ("train_roundtrip", "train_fr.jsonl", True),
    ("val_complet", "val_fr.jsonl", False),
    ("val_roundtrip", "val_fr.jsonl", True),
]

NIVEAUX = ("branch", "node")

#: Racine du depot (le pilote est dans scripts/fallacy_detection/).
RACINE = Path(__file__).resolve().parents[2]


#: Prefixe logique des derives ecrites hors du depot (corpus filtre) : leur
#: chemin reel est un chemin de poste et ne doit jamais etre committe.
PREFIXE_DERIVE = "corpus-filtre"


def chemin_publie(path: str | Path) -> str:
    """Rend un chemin publiable : relatif au depot s'il y est, sinon tel quel.

    Un chemin de poste (`C:/dev/...`, `C:/Users/<utilisateur>/...`) ne doit
    jamais etre committe : seul le chemin relatif au depot, ou un chemin de
    gisement partage, est publiable. Un derive ecrit sous le repertoire
    personnel de l'utilisateur (le corpus filtre) est designe par un nom
    logique, son nom de fichier seul.
    """
    p = Path(path)
    if not p.is_absolute():
        return p.as_posix()
    try:
        return p.resolve().relative_to(RACINE).as_posix()
    except ValueError:
        pass
    try:
        p.resolve().relative_to(Path.home())
    except ValueError:
        # Gisement partage (hors du poste) : publiable tel quel.
        return p.as_posix()
    return f"{PREFIXE_DERIVE}/{p.name}"


def assainir_rapport(rapport: dict) -> dict:
    """Remplace les chemins de poste par leur forme publiable."""
    rapport = dict(rapport)
    corpus = rapport.get("corpus")
    if isinstance(corpus, dict) and "path" in corpus:
        rapport["corpus"] = dict(corpus, path=chemin_publie(corpus["path"]))
    lexique = rapport.get("lexicon")
    if isinstance(lexique, dict) and isinstance(lexique.get("taxonomies"), list):
        rapport["lexicon"] = dict(
            lexique, taxonomies=[chemin_publie(t) for t in lexique["taxonomies"]]
        )
    return rapport


def assainir_agregat(agregat: dict) -> dict:
    """Assainit l'agregat entier (rapports et sources)."""
    agregat = dict(agregat)
    variantes = []
    for variante in agregat["variantes"]:
        variante = dict(variante)
        source = variante.get("source")
        if isinstance(source, dict) and "path" in source:
            variante["source"] = dict(source, path=chemin_publie(source["path"]))
        niveaux = {}
        for level, mesure in variante["niveaux"].items():
            rapport = mesure.get("rapport")
            if rapport is not None:
                mesure = dict(mesure, rapport=assainir_rapport(rapport))
            niveaux[level] = mesure
        variante["niveaux"] = niveaux
        variantes.append(variante)
    agregat["variantes"] = variantes
    return agregat


def filtrer_corpus(source: Path, destination: Path) -> tuple[int, int]:
    """Ecrit le corpus filtre (round-trip reussi) ; rend (conservees, lues)."""
    conservees = lues = 0
    with source.open(encoding="utf-8") as handle, destination.open("w", encoding="utf-8") as out:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            lues += 1
            if record.get("roundtrip"):
                out.write(json.dumps(record, ensure_ascii=False) + "\n")
                conservees += 1
    return conservees, lues


def mesurer(corpus_path: Path, level: str, folds: int, draws: int, seed: int,
            taxonomies: list[Path] | None = None) -> dict:
    """Rejoue l'organe ; un niveau refuse est rendu verbatim, jamais masque."""
    try:
        report = organ.run(corpus_path, level, folds, draws, seed, taxonomies)
    except SystemExit as refus:
        return {"level": level, "refuse": True, "message": str(refus)}
    return {"level": level, "refuse": False, "rapport": report}


def resumer(variante: dict) -> dict:
    """Sous-ensemble stable des mesures, pour la comparaison des variantes."""
    rapport = variante.get("rapport")
    if rapport is None:
        return {"level": variante["level"], "refuse": True, "message": variante.get("message")}
    baselines = rapport["baselines"]
    return {
        "level": variante["level"],
        "refuse": False,
        "structure": rapport["structure"],
        "node_level": rapport["node_level"],
        "folds_identical": rapport["folds_identical"],
        "baselines": {
            "majority_grouped": baselines["majority_grouped"]["macro_f1_mean"],
            "random_grouped": baselines["random_grouped"]["macro_f1_mean"],
            "rules_full": baselines["rules_full"]["macro_f1"],
            "lexical_centroid_grouped": baselines["lexical_centroid_grouped"]["macro_f1_mean"],
            "lexical_centroid_naive": baselines["lexical_centroid_naive"]["macro_f1_mean"],
        },
        "leakage": rapport["leakage"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--corpus-dir", required=True, type=Path,
                        help="repertoire du corpus tranche B (train_fr.jsonl, val_fr.jsonl)")
    parser.add_argument("--out-dir", required=True, type=Path,
                        help="repertoire de sortie (JSON + rapport markdown)")
    parser.add_argument("--folds", type=int, default=5)
    parser.add_argument("--random-draws", type=int, default=200)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--taxonomy", action="append", default=None,
                        help="CSV de taxonomie (defaut : les deux taxonomies Argumentum)")
    parser.add_argument("--assainir-json", type=Path, default=None,
                        help="assainit un agregat deja produit (chemins de poste -> chemins publiables)")
    args = parser.parse_args()

    if args.assainir_json is not None:
        agregat = json.loads(args.assainir_json.read_text(encoding="utf-8"))
        assaini = assainir_agregat(agregat)
        args.assainir_json.write_text(
            json.dumps(assaini, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"Aggregat assaini : {args.assainir_json}")
        rapport = args.assainir_json.with_suffix(".md")
        rapport.write_text(rendre_rapport(assaini), encoding="utf-8")
        print(f"Rapport regenere : {rapport}")
        return 0

    taxonomies = [Path(p) for p in args.taxonomy] if args.taxonomy else None

    if not args.corpus_dir.is_dir():
        print(f"repertoire de corpus introuvable : {args.corpus_dir}", file=sys.stderr)
        return 2

    args.out_dir.mkdir(parents=True, exist_ok=True)
    # Le corpus filtre est un derive : il vit hors du depot, il n'est pas commite.
    work_dir = Path(tempfile.mkdtemp(prefix="fallacy-tranche-b-"))
    corpus_dir = work_dir / "corpus"

    variantes = []
    for cle, nom_fichier, filtre in VARIANTES:
        source = args.corpus_dir / nom_fichier
        if not source.exists():
            print(f"corpus introuvable : {source}", file=sys.stderr)
            return 2
        if filtre:
            # Le corpus filtree est un derive : il vit hors du depot, il n'est pas commite.
            corpus_dir.mkdir(parents=True, exist_ok=True)
            chemin = corpus_dir / nom_fichier.replace(".jsonl", "_roundtrip.jsonl")
            conservees, lues = filtrer_corpus(source, chemin)
            critere = CRITERE_FILTRE
        else:
            chemin = source
            conservees = lues = None
            critere = None
        entree = {
            "variante": cle,
            "split": nom_fichier,
            "filtre": critere,
            "source": {"path": str(source).replace("\\", "/"),
                       "sha256": organ.sha256_of(source)},
            "lignes_lues": lues,
            "lignes_conservees": conservees,
            "niveaux": {},
        }
        for level in NIVEAUX:
            print(f"[{cle}] niveau {level} ...", flush=True)
            entree["niveaux"][level] = mesurer(chemin, level, args.folds,
                                                args.random_draws, args.seed, taxonomies)
            resume = resumer(entree["niveaux"][level])
            if resume["refuse"]:
                print(f"    refuse : {resume['message']}")
            else:
                b = resume["baselines"]
                print(f"    lexicale groupee {b['lexical_centroid_grouped']} | "
                      f"aleatoire {b['random_grouped']} | fuite {resume['leakage']['gap']}")
        variantes.append(entree)

    agregat = {
        "issue": "Phase 3 gate (tranche de #17578, EPIC #10355) — corpus tranche B",
        "instrument": "scripts/fallacy_detection/baseline_branch_detection.py (rejoue tel quel)",
        "graine": args.seed,
        "plis": args.folds,
        "tirages_aleatoires": args.random_draws,
        "variantes": variantes,
    }
    agregat = assainir_agregat(agregat)
    json_path = args.out_dir / "baselines_tranche_b.json"
    json_path.write_text(json.dumps(agregat, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    md_path = args.out_dir / "baselines_tranche_b.md"
    md_path.write_text(rendre_rapport(agregat), encoding="utf-8")
    print(f"\nAgregat : {json_path}")
    print(f"Rapport : {md_path}")
    return 0


def rendre_rapport(agregat: dict) -> str:
    """Rapport markdown : une ligne par variante et par niveau."""
    lignes = [
        "# Baselines de la Phase 3 — corpus tranche B",
        "",
        "Fichier généré par `scripts/fallacy_detection/measure_baselines_tranche_b.py` — "
        "ne pas éditer à la main.",
        "",
        f"Instrument : `{agregat['instrument']}`. Graine {agregat['graine']}, "
        f"{agregat['plis']} plis groupes par scenario, "
        f"{agregat['tirages_aleatoires']} tirages aleatoires.",
        "",
        "| Variante | Niveau | Lignes | Etiquettes | Support | Groupes | "
        "Majoritaire | Aleatoire | Lexicale groupee | Lexicale naive | Regles | Fuite |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for variante in agregat["variantes"]:
        for level in NIVEAUX:
            resume = resumer(variante["niveaux"][level])
            if resume["refuse"]:
                lignes.append(
                    f"| {variante['variante']} | {level} | {resume.get('message', '')} | | | | | | | | | |"
                )
                continue
            structure = resume["structure"]
            b = resume["baselines"]
            lignes.append(
                f"| {variante['variante']} | {level} | {structure['rows']} | "
                f"{structure['labels']} | {structure['support_min']}-{structure['support_max']} | "
                f"{structure['groups']} | {b['majority_grouped']} | {b['random_grouped']} | "
                f"{b['lexical_centroid_grouped']} | {b['lexical_centroid_naive']} | "
                f"{b['rules_full']} | {resume['leakage']['gap']} |"
            )
    lignes.append("")
    return "\n".join(lignes)


if __name__ == "__main__":
    raise SystemExit(main())
