"""Runner de la chaine d'etiquetage humour par LLM local (#26911, etape 2).

Execute la campagne, ecrit les artefacts, et publie les mesures :

* **bras A** — le banc humour du depot (120 instances, annotation de
  reference commitee) : le LLM local etiquete a l'aveugle, l'accord est
  mesure **contre la reference** (kappa de Cohen, via l'instrument existant
  ``ict/humor_agreement.py``) ;
* **bras B** — un echantillon de controle **relu independamment** (ordre des
  categories inverse, regle de departage reformulee, graine distincte) :
  l'accord mesure est un **auto-accord intra-modele**, compare a la bande
  du hasard (l'instrument la calcule par permutation) ;
* **bras C** — des paraphrases generees par le modele : donnees **augmentees**,
  marquees comme telles et **tenues hors du jeu d'evaluation** ;
* **bras D** — un corpus **a licence permissive** (CC0-1.0), telecharge au
  moment de l'execution et jamais recopie dans le depot : la chaine y est
  exercee hors de la langue du banc, et ces items sont eux aussi exclus du
  jeu d'evaluation.

Sorties :

* ``<out-dir>/annotations.jsonl`` — enregistrements au format de
  ``ict.humor_agreement.read_annotations_jsonl`` (**hors depot**) ;
* ``<results>`` — rapport JSON (mesures, traces, verifications) **dans** le
  depot, sans le texte des items etrangers.

Usage (machine locale, endpoint vLLM de la flotte) :

    python scripts/run_humor_llm_chain.py \\
        --env-file ../../GenAI/.env --out-dir .tmp/humor_chain
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import humor_llm_chain as chain  # noqa: E402
from ict.humor_agreement import (  # noqa: E402
    agreement_report,
    chance_kappa_distribution,
    cohen_kappa,
    read_annotations_jsonl,
)

#: Corpus a licence permissive, telecharge a l'execution (jamais vendorise).
CC0_DATASET = "artemsnegirev/dialogs_from_jokes"
CC0_LICENCE = "CC0-1.0"
CC0_URL = (
    "https://huggingface.co/datasets/"
    "artemsnegirev/dialogs_from_jokes/resolve/main/dataset.json"
)

#: Racine du depot : ce runner vit dans
#: ``<racine>/MyIA.AI.Notebooks/IIT/ICT-Series/scripts/``. Le scratch par
#: defaut en decoule -- aucun chemin de poste n'est ecrit en dur.
REPO_ROOT = Path(__file__).resolve().parents[4]

#: Repertoire de travail par defaut : scratch **du depot** (gitignore),
#: partage par toutes les machines de la flotte.
DEFAULT_OUT_DIR = REPO_ROOT / ".tmp" / "humor_chain"

#: Source des instances dont l'etiquette de reference est posee par une
#: **heuristique de categorie** Argumentum (et non par un jugement humain).
#: La regle vit dans le module : ``ict.humor_llm_chain.ARGUMENTUM_SOURCE``.
ARGUMENTUM_SOURCE = chain.ARGUMENTUM_SOURCE


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-url", default=chain.DEFAULT_BASE_URL)
    parser.add_argument("--model", default=chain.DEFAULT_MODEL)
    parser.add_argument(
        "--env-file",
        default="../../GenAI/.env",
        help="fichier .env portant la cle du endpoint (aucune valeur en dur)",
    )
    parser.add_argument("--key-name", default="VLLM_API_KEY")
    parser.add_argument("--seed", type=int, default=chain.DEFAULT_SEED)
    parser.add_argument("--temperature", type=float, default=chain.DEFAULT_TEMPERATURE)
    parser.add_argument("--top-p", type=float, default=chain.DEFAULT_TOP_P)
    parser.add_argument("--max-tokens", type=int, default=chain.DEFAULT_MAX_TOKENS)
    parser.add_argument("--timeout", type=float, default=chain.DEFAULT_TIMEOUT)
    parser.add_argument(
        "--population",
        choices=("split", "stratified"),
        default="split",
        help=(
            "split : tous les items a etiquette humaine + un echantillon "
            "stratifie de la population a etiquette heuristique (population "
            "par defaut). stratified : echantillon stratifie sur le corpus "
            "entier (population de la premiere campagne, conservee pour la "
            "mesure de sensibilite)"
        ),
    )
    parser.add_argument(
        "--per-label",
        type=int,
        default=8,
        help="items par etiquette (population 'stratified')",
    )
    parser.add_argument(
        "--arg-per-label",
        type=int,
        default=3,
        help=(
            "items par etiquette tires dans la population a etiquette "
            "heuristique (Argumentum) ; cette population n'est pas un "
            "jugement du texte, elle sert de contraste"
        ),
    )
    parser.add_argument(
        "--manual-limit",
        type=int,
        default=0,
        help="0 = tous les items a etiquette humaine (population de reference)",
    )
    parser.add_argument("--control-size", type=int, default=20)
    parser.add_argument("--augment-size", type=int, default=10)
    parser.add_argument("--cc0-size", type=int, default=20)
    parser.add_argument("--cc0-control-size", type=int, default=10)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--out-dir", default=str(DEFAULT_OUT_DIR))
    parser.add_argument(
        "--results",
        default=os.path.join(
            os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            "ict",
            "results",
            "humor_llm_chain_c26911.json",
        ),
    )
    parser.add_argument("--skip-cc0", action="store_true")
    parser.add_argument(
        "--reuse-annotations",
        default=None,
        help=(
            "recalcule le rapport a partir d'un annotations.jsonl deja "
            "produit, sans rappeler le modele (re-analyse hors ligne)"
        ),
    )
    return parser.parse_args()


# --------------------------------------------------------------------------- #
# Corpus CC0 (licence permissive, telecharge a l'execution)
# --------------------------------------------------------------------------- #


def fetch_cc0(cache_dir: Path, size: int) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Telecharge le corpus CC0 et rend (items, provenance).

    Le fichier est ecrit dans ``cache_dir`` (hors depot par defaut) ; aucun
    texte n'est recopie dans le depot.
    """
    cache_dir.mkdir(parents=True, exist_ok=True)
    target = cache_dir / "dialogs_from_jokes.dataset.json"
    if not target.is_file():
        with urllib.request.urlopen(CC0_URL, timeout=300) as response:
            target.write_bytes(response.read())
    digest = hashlib.sha256(target.read_bytes()).hexdigest()

    items: list[dict[str, Any]] = []
    with target.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle):
            line = line.strip()
            if not line:
                continue
            payload = json.loads(line)
            turns = payload.get("turns", "")
            if not isinstance(turns, str):
                turns = " ".join(str(part) for part in turns)
            text = " ".join(turns.split())
            if not text:
                continue
            items.append({"id": f"cc0-{line_no:06d}", "texte": text})
            if len(items) >= size:
                break
    provenance = {
        "dataset": CC0_DATASET,
        "licence": CC0_LICENCE,
        "url": CC0_URL,
        "sha256": digest,
        "local_copy": chain.portable_pointer(target),
        "vendored_in_repo": False,
        "language": "ru",
        "note": (
            "corpus de blagues en russe : il exerce la chaine (trace, controle, "
            "augmentation) hors de la langue du banc ; il ne fournit aucune "
            "reference et n'entre pas dans le jeu d'evaluation"
        ),
    }
    return items, provenance


# --------------------------------------------------------------------------- #
# Mesures
# --------------------------------------------------------------------------- #


def agreement_over_shared(
    records: list[dict[str, Any]],
    first: str,
    second: str,
    *,
    corpus: str | None = None,
) -> dict[str, Any]:
    """Accord entre deux annotateurs sur les items partages + bande du hasard.

    ``corpus`` filtre les enregistrements consideres. Le filtre est
    **obligatoire** en pratique : les deux bras du banc et les deux bras du
    corpus CC0 portent les memes noms d'annotateur, donc sans filtre un
    kappa "du banc" melangerait des items francais et des items russes --
    deux populations sans commune mesure.
    """
    subset = [
        record
        for record in records
        if corpus is None or record.get("corpus") == corpus
    ]
    by_annotator: dict[str, dict[str, str]] = {}
    for record in subset:
        by_annotator.setdefault(record["annotator"], {})[record["id"]] = record["label"]
    labels_a_map = by_annotator.get(first, {})
    labels_b_map = by_annotator.get(second, {})
    shared = sorted(set(labels_a_map) & set(labels_b_map))
    if not shared:
        return {"n": 0, "kappa": None, "undefined_reason": "aucun item partage"}
    labels_a = [labels_a_map[item] for item in shared]
    labels_b = [labels_b_map[item] for item in shared]
    summary = cohen_kappa(labels_a, labels_b, categories=list(chain.taxonomy_labels()))
    chance = chance_kappa_distribution(labels_a, labels_b)
    summary["items"] = shared
    summary["corpus"] = corpus
    summary["chance_band"] = {
        "mean": chance["mean"],
        "p95": chance["p95"],
        "max": chance["max"],
        "n_draws": chance["n_draws"],
        "seed": chance["seed"],
    }
    summary["above_chance_p95"] = (
        summary["kappa"] is not None
        and chance["p95"] is not None
        and summary["kappa"] > chance["p95"]
    )
    return summary


def agreement_by_source(
    records: list[dict[str, Any]],
    corpus: list[dict[str, Any]],
    annotator_name: str,
) -> dict[str, Any]:
    """Accord contre la reference, **par origine de l'etiquette de reference**.

    Les 120 instances du banc n'ont pas toutes la meme origine de label :
    les 60 ``arg-*`` viennent d'une **heuristique de categorie** Argumentum
    (lisible dans la justification portee par chaque instance), les 30
    blagues manuelles, les 20 declarations factuelles et les 10 edge cases
    sont **reposes a la main**. Un accord global melange deux populations
    de labels heterogenes : la rupture est donc mesuree separement, par
    source de corpus ET par origine du label (heuristique / manuel).
    """
    labels_of = {str(item["id"]): str(item["label"]) for item in corpus}
    source_of = {str(item["id"]): str(item.get("source", "?")) for item in corpus}
    predicted = {
        str(record["id"]): str(record["label"])
        for record in records
        if record["annotator"] == annotator_name
    }

    def groups() -> dict[str, list[str]]:
        by_source: dict[str, list[str]] = {}
        by_origin: dict[str, list[str]] = {}
        for item_id, source in source_of.items():
            if item_id not in predicted:
                continue
            by_source.setdefault(source, []).append(item_id)
            origin = "heuristique-argumentum" if item_id.startswith("arg-") else "manuel"
            by_origin.setdefault(origin, []).append(item_id)
        return {"par_source_de_corpus": by_source, "par_origine_du_label": by_origin}

    out: dict[str, Any] = {}
    for dimension, mapping in groups().items():
        bucket: dict[str, Any] = {}
        for key, item_ids in sorted(mapping.items()):
            item_ids.sort()
            summary = cohen_kappa(
                [predicted[item_id] for item_id in item_ids],
                [labels_of[item_id] for item_id in item_ids],
                categories=list(chain.taxonomy_labels()),
            )
            summary["items"] = item_ids
            bucket[key] = summary
        out[dimension] = bucket
    return out


def predicted_distribution(records: list[dict[str, Any]]) -> dict[str, int]:
    """Effectifs des etiquettes predites, par categorie de la taxonomie.

    Une distribution **monochrome** (toute une categorie) explique un
    kappa negatif sans qu'il faille blaimer le modele : elle dit que
    l'annotateur ne discrimine pas, pas qu'il se trompe. C'est un controle
    de lecture du chiffre, pas un ornement.
    """
    counts: dict[str, int] = {}
    for record in records:
        label = str(record["label"])
        counts[label] = counts.get(label, 0) + 1
    return dict(sorted(counts.items()))


def reference_distribution(
    corpus: list[dict[str, Any]], records: list[dict[str, Any]]
) -> dict[str, int]:
    """Effectifs des etiquettes de reference, **sur le meme sous-ensemble**."""
    ids = {str(record["id"]) for record in records}
    counts: dict[str, int] = {}
    for item in corpus:
        if str(item["id"]) in ids:
            label = str(item["label"])
            counts[label] = counts.get(label, 0) + 1
    return dict(sorted(counts.items()))


def main() -> int:
    args = parse_args()
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    api_key = chain.read_env_value(args.env_file, args.key_name)
    if api_key is None:
        raise SystemExit(
            f"cle {args.key_name} absente de {args.env_file} : "
            "aucune valeur n'est codee en dur (regle secrets-hygiene)"
        )

    annotator = chain.LocalLLMAnnotator(
        base_url=args.base_url,
        model=args.model,
        api_key=api_key,
        seed=args.seed,
        temperature=args.temperature,
        top_p=args.top_p,
        max_tokens=args.max_tokens,
        timeout=args.timeout,
    )

    # -- banc (reference commitee) --------------------------------------- #
    from ict.humor_pairs import load_corpus_dur

    corpus = load_corpus_dur()
    reference = {str(item["id"]): str(item["label"]) for item in corpus}
    if args.population == "split":
        sample, manual_sample, heuristic_sample = chain.build_evaluation_sample(
            corpus,
            arg_per_label=args.arg_per_label,
            manual_limit=args.manual_limit,
            seed=args.seed,
        )
    else:
        # Population de la premiere campagne (rubric v1) : echantillon stratifie
        # sur le corpus entier. Conservee pour que la sensibilite
        # d'operationalisation soit rejouable avec le meme code.
        sample = chain.sample_stratified(
            corpus,
            label_of=lambda item: str(item["label"]),
            per_label=args.per_label,
            seed=args.seed,
        )
        manual_sample = []
        heuristic_sample = []
    composition = chain.sample_composition(sample)
    print(
        f"banc : {len(corpus)} instances, echantillon {len(sample)} "
        f"(population {args.population} : {composition})"
    )

    name_p1 = f"vllm:{args.model}:p1"
    name_p2 = f"vllm:{args.model}:p2"
    name_aug = f"vllm:{args.model}:aug"

    # La relecture de controle change TOUT ce qui est trace : prompt (ordre
    # inverse, regle de departage reformulee) et graine. La temperature
    # reste a 0 : chaque passe est rejouable a l'identique.
    annotator_control = chain.LocalLLMAnnotator(
        base_url=args.base_url,
        model=args.model,
        api_key=api_key,
        seed=args.seed + 1,
        temperature=args.temperature,
        top_p=args.top_p,
        max_tokens=args.max_tokens,
        timeout=args.timeout,
    )

    cc0_provenance: dict[str, Any] | None = None
    records_cc0: list[dict[str, Any]] = []
    records_cc0_p2: list[dict[str, Any]] = []

    if args.reuse_annotations:
        # Re-analyse hors ligne : le rapport est recalcule a partir des
        # enregistrements deja produits, sans rappeler le modele. Les
        # annotations restent ce qu'elles sont ; seule la mesure est refaite.
        all_records = read_annotations_jsonl(args.reuse_annotations)
        print(f"re-analyse : {len(all_records)} enregistrements relus")
        records_p1 = [
            record
            for record in all_records
            if record["annotator"] == name_p1
            and record.get("corpus") == "humour_banc"
            and record.get("variant") == "principal"
        ]
        records_cc0 = [
            record
            for record in all_records
            if record["annotator"] == name_p1
            and record.get("corpus") == CC0_DATASET
            and record.get("variant") == "principal"
        ]
        records_cc0_p2 = [
            record
            for record in all_records
            if record["annotator"] == name_p2
            and record.get("corpus") == CC0_DATASET
            and record.get("variant") == "controle"
        ]
        cached = Path(args.reuse_annotations).parent / "dataset.provenance.json"
        if cached.is_file():
            cc0_provenance = json.loads(cached.read_text(encoding="utf-8"))
            # Le cache peut dater d'une campagne anterieure : son pointeur
            # est renormalise ici, pour que le rapport republie ne porte
            # jamais le chemin du siege qui a produit la campagne.
            cc0_provenance["local_copy"] = chain.portable_pointer(
                cc0_provenance.get("local_copy", "")
            )
    else:
        records_p1 = chain.annotate_items(
            sample,
            annotator,
            annotator_name=name_p1,
            variant="principal",
            corpus="humour_banc",
            label_of=lambda item: str(item["label"]),
            workers=args.workers,
        )
        print(f"bras A : {len(records_p1)} items etiquetes")

        # L'echantillon de controle est tire au sort **a graine fixe** : un
        # simple tri par id selectionnerait d'abord les ids "arg-*", donc un
        # sous-ensemble de provenance unique -- l'auto-accord mesure ne
        # decrirait alors qu'une seule population d'items.
        control_rng = random.Random(args.seed + 2)
        control_size = min(args.control_size, len(sample))
        control_items = control_rng.sample(list(sample), control_size)
        records_p2 = chain.annotate_items(
            control_items,
            annotator_control,
            annotator_name=name_p2,
            variant="controle",
            corpus="humour_banc",
            workers=args.workers,
        )
        print(f"bras B : {len(records_p2)} items relus (controle)")

        records_aug = chain.augment_items(
            random.Random(args.seed + 3).sample(
                list(sample), min(args.augment_size, len(sample))
            ),
            annotator,
            annotator_name=name_aug,
            corpus="humour_banc",
            workers=args.workers,
        )
        print(f"bras C : {len(records_aug)} paraphrases (augmentees)")

        all_records = records_p1 + records_p2 + records_aug

        # -- bras D : corpus permissive ----------------------------------- #
        if not args.skip_cc0:
            cc0_items, cc0_provenance = fetch_cc0(out_dir, args.cc0_size)
            records_cc0 = chain.annotate_items(
                cc0_items,
                annotator,
                annotator_name=name_p1,
                variant="principal",
                corpus=CC0_DATASET,
                in_evaluation_set=False,
                workers=args.workers,
            )
            cc0_control = cc0_items[: args.cc0_control_size]
            records_cc0_p2 = chain.annotate_items(
                cc0_control,
                annotator_control,
                annotator_name=name_p2,
                variant="controle",
                corpus=CC0_DATASET,
                in_evaluation_set=False,
                workers=args.workers,
            )
            all_records += records_cc0 + records_cc0_p2
            print(f"bras D : {len(records_cc0)} items CC0 (dont {len(records_cc0_p2)} relus)")

    # -- invariant : les augmentees hors du jeu d'evaluation ------------- #
    evaluation_set = chain.build_evaluation_set(all_records)
    augmented_ids = {
        str(record["id"]) for record in all_records if record["source"] == chain.SOURCE_AUGMENTED
    }
    evaluation_ids = {str(record["id"]) for record in evaluation_set}
    invariant = {
        "augmented_count": len(augmented_ids),
        "evaluation_count": len(evaluation_ids),
        "intersection": sorted(augmented_ids & evaluation_ids),
        "holds": not (augmented_ids & evaluation_ids),
    }

    # -- ecriture des artefacts ------------------------------------------ #
    jsonl_path = out_dir / "annotations.jsonl"
    if not args.reuse_annotations:
        written = chain.write_campaign(all_records, jsonl_path)
        reread = read_annotations_jsonl(jsonl_path)
        print(f"annotations : {written} ecrits, {len(reread)} relus par l'instrument")
        if cc0_provenance is not None:
            (out_dir / "dataset.provenance.json").write_text(
                json.dumps(cc0_provenance, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
    else:
        print("re-analyse : artefacts non reecrits")

    # Les paraphrasees ne sont pas des annotations : elles portent une
    # sentinelle de format ("augmentation"), pas une categorie de la
    # taxonomie. Elles restent dans le JSONL (la provenance doit etre
    # visible) mais n'entrent pas dans le rapport d'accord.
    annotation_records = [
        record for record in all_records if record["source"] == chain.SOURCE_REAL
    ]
    report = agreement_report(
        annotation_records,
        reference=reference,
        categories=list(chain.taxonomy_labels()),
    )
    self_agreement_banc = agreement_over_shared(
        all_records, name_p1, name_p2, corpus="humour_banc"
    )
    cc0_self_agreement = None
    if records_cc0_p2:
        cc0_self_agreement = agreement_over_shared(
            all_records, name_p1, name_p2, corpus=CC0_DATASET
        )

    served_models = sorted(
        {str(record.get("served_model", "")) for record in all_records if record.get("served_model")}
    )
    results = {
        "issue": "#26911",
        "step": "etape 2 -- chaine de preparation par le LLM local",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "trace": {
            **annotator.trace(),
            "control_trace": annotator_control.trace(),
            "served_models": served_models,
            "variants": {
                "principal": "rubric dans l'ordre canonique de la taxonomie",
                "controle": "rubric inverse + regle de departage reformulee (relecture)",
            },
            "annotators": [name_p1, name_p2, name_aug],
            "determinism": (
                "temperature 0 : chaque passe est rejouable a l'identique ; "
                "la variabilite de la relecture vient du prompt et de la graine, "
                "pas du tirage"
            ),
        },
        "corpora": {
            "humour_banc": {
                "source": "GameTheory/humour_banc/humour_corpus.json (commite dans le depot)",
                "population": len(corpus),
                "sample": len(sample),
                "sample_composition": composition,
                "population_mode": args.population,
                "reference_nature": chain.reference_nature(corpus),
                "reference": "annotation de reference commitee dans le depot",
            },
            "cc0": cc0_provenance,
        },
        "measures": {
            "vs_reference_banc": report["vs_reference"],
            "vs_reference_by_source": agreement_by_source(
                records_p1, corpus, name_p1
            ),
            "self_agreement_banc": self_agreement_banc,
            "self_agreement_cc0": cc0_self_agreement,
            "token_cost": report["token_cost"],
            "n_records": report["n_records"],
            "n_items": report["n_items"],
            "predicted_distribution": predicted_distribution(records_p1),
            "reference_distribution": reference_distribution(corpus, records_p1),
        },
        "provenance_invariant": invariant,
        "artifacts": {
            "annotations_jsonl": chain.portable_pointer(jsonl_path),
            "annotations_jsonl_in_repo": False,
        },
        "limits": [
            "l'accord contre la reference est un accord modele/annotation de reference, "
            "pas un accord entre annotateurs humains ; il n'est interpretable que sur "
            "la population a etiquette humaine (blagues manuelles, declarations "
            "factuelles, edge cases)",
            "la population arg-* porte une etiquette produite par une heuristique de "
            "categorie sur des scenarios tronques : son texte ne contient pas la "
            "blague, l'etiquette n'y est pas derivable ; l'accord mesure sur cette "
            "population decrit un decalage de methode, pas une performance",
            "l'auto-accord mesure est intra-modele (relecture du meme modele avec un "
            "prompt different) : il ne remplace pas la campagne multi-annotateurs "
            "de #12756",
            "le corpus CC0 est en russe : il exerce la chaine, il n'evalue rien",
            "la taxonomie de reference est elle-meme un juggement de l'effet "
            "communicationnel, pas une verite de terrain : un.item sans marqueur "
            "d'effet comique peut rester un humour reussi pour un lecteur, et le "
            "kappa mesure une convergence de jugements, pas une justesse",
        ],
    }

    results_path = Path(args.results)
    results_path.parent.mkdir(parents=True, exist_ok=True)
    results_path.write_text(
        json.dumps(results, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"rapport : {results_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
