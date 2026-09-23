#!/usr/bin/env python3
"""Constructeur du dataset de Phase 2 (EPIC #10355) : produit cartesien
Scenarii x taxonomie Argumentum, equilibre et decoupe en splits etanches.

Cadrage owner (2026-08-22, rapporte sur #10355 par la lane du corpus) :
« CoursIA a besoin de tout le materiel, toutes les taxonomies en entier (pas
juste les cartes), ainsi que tous les scenarii pour faire le produit cartesien
et produire un dataset volumineux et equilibre. »

L'unite est donc une **paire** ``(scenario, noeud)`` : un noeud de la taxonomie
des sophismes (1407 hors racine) ou des vertus (222 hors racine), place dans une
mise en situation du paquet Scenarii (167). Le module ne genere aucun texte : il
decide QUELLES paires entrent dans le dataset, dans QUEL split, et rend le
prompt qu'un LLM enseignant recevra (tranche B). Trois decisions y sont
mesurables et testees :

1. **Equilibrage a deux niveaux.** Les familles n'ont pas la meme taille
   (sophismes : 420 noeuds pour ``Influence``, 89 pour ``Abus de langage``). On
   alloue a chaque noeud un poids ``n_f ** -alpha`` (``n_f`` = taille de sa
   famille). Le total d'une famille vaut alors ``n_f ** (1 - alpha)`` a une
   constante pres, et le quota d'un noeud ``n_f ** -alpha`` : le desequilibre
   entre familles vaut ``r ** (1 - alpha)``, celui entre noeuds ``r ** alpha``,
   avec ``r = n_max / n_min``. **Leur produit vaut ``r`` quel que soit alpha**
   (aux arrondis entiers pres) : on ne peut pas equilibrer a la fois les
   familles et les noeuds, on choisit seulement ou placer le desequilibre.
   ``alpha = 0.5`` minimise le pire des deux (``sqrt(r)`` de chaque cote) ; c'est
   le defaut parce que le gate de Phase 3 evalue les deux niveaux (feuille
   exacte ET branche de 1er niveau).
2. **Splits etanches par scenario.** Les scenarii sont partitionnes en
   train/val/test (stratifies par categorie) : un scenario de test n'apparait
   jamais a l'entrainement. Chaque noeud apparait une fois en validation et
   ``test_per_node`` fois en test, pour que l'evaluation par feuille couvre les
   1629 etiquettes.
3. **Anti-circularite.** Le prompt n'utilise que le titre et la definition du
   noeud, jamais ses champs ``example_*`` : le texte genere ne peut pas etre une
   recopie d'une ligne du corpus (ecueil nomme par la lane Argumentum le
   2026-08-21 : « un modele qui restitue example_en du noeud 1207 n'a pas
   detecte un sophisme, il a retrouve une ligne »).

Les noeuds sont cles par ``PK`` et les scenarii par ``path``, jamais par
libelle (trois familles de vertus ont ete renommees en aout 2026).

Usage::

    python -m fallacy_detection.cartesian_dataset_builder --out <dossier>
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import random
import re
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Optional

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fallacy_detection.argumentum_taxonomy_explorer import _load_nodes  # noqa: E402

_REPO_ROOT = Path(__file__).resolve().parents[2]
_ARG_DATA = _REPO_ROOT / "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data"
DEFAULT_FALLACIES = _ARG_DATA / "argumentum_fallacies_taxonomy.csv"
DEFAULT_VIRTUES = _ARG_DATA / "argumentum_virtues_taxonomy.csv"
DEFAULT_SCENARII = (
    _REPO_ROOT / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/argumentum_scenarii_cards.csv"
)

# Copie verbatim de `Cards/Scenarii/Argumentum Scenarii - Cards.csv` au commit
# epingle du sous-module Argumentum (cf NOTICE-SCENARII).
SCENARII_UPSTREAM_COMMIT = "0ab05d66576a1007c3952a67e2dd1eaf8f9b502c"
SCENARII_BLOB_SHA1 = "9f20eb808a1d22c9c1a5dd1b96460b0d6a23db60"

LANGS = ("fr", "en", "ru", "pt", "ar", "es", "zh", "fa")
LANG_NAMES = {
    "fr": "French", "en": "English", "ru": "Russian", "pt": "Portuguese",
    "ar": "Arabic", "es": "Spanish", "zh": "Chinese", "fa": "Persian",
}
SPLITS = ("train", "val", "test")
CSV_COLUMNS = (
    "pair_id", "split", "polarity", "node_pk", "family", "depth", "is_leaf",
    "scenario_path",
)


def git_blob_sha1(path: Path) -> str:
    """SHA-1 de blob git (``git hash-object``) d'un fichier, sans appel a git."""
    data = Path(path).read_bytes()
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


# --------------------------------------------------------------------------
# Chargement
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Node:
    """Un noeud de taxonomie, cle stable ``F<pk>`` ou ``V<pk>``."""

    polarity: str  # "fallacy" | "virtue"
    pk: int
    path: str
    depth: int
    family: str
    is_leaf: bool

    @property
    def key(self) -> str:
        return ("F" if self.polarity == "fallacy" else "V") + str(self.pk)


@dataclass(frozen=True)
class Scenario:
    path: str
    category: str
    title: str


def _leaf_flags(paths: Iterable[str]) -> set[str]:
    """Chemins qui sont le parent d'au moins un autre chemin."""
    return {p.rsplit(".", 1)[0] for p in paths if "." in p}


def load_fallacies(csv_path: Path = DEFAULT_FALLACIES) -> list[Node]:
    """Sophismes hors racine (PK 0), via le chargeur de l'explorateur natif."""
    raw = [n for n in _load_nodes(Path(csv_path)) if n.pk > 0 and n.famille]
    parents = _leaf_flags(n.path for n in raw)
    return [Node("fallacy", n.pk, n.path, n.depth, n.famille, n.path not in parents)
            for n in raw]


def load_virtues(csv_path: Path = DEFAULT_VIRTUES) -> list[Node]:
    """Vertus hors racine (pk 0). Schema different des sophismes (`pk`, `family_fr`)."""
    with open(csv_path, encoding="utf-8-sig", newline="") as f:
        rows = [r for r in csv.DictReader(f)
                if (r.get("pk") or "").strip().isdigit() and int(r["pk"]) > 0]
    parents = _leaf_flags(r["path"].strip() for r in rows)
    return [Node("virtue", int(r["pk"]), r["path"].strip(), int(r["depth"]),
                 r["family_fr"].strip(), r["path"].strip() not in parents)
            for r in rows]


def load_scenarios(csv_path: Path = DEFAULT_SCENARII,
                   expected_sha1: Optional[str] = SCENARII_BLOB_SHA1) -> list[Scenario]:
    """Scenarii, apres verification que la copie est bien celle de l'amont epingle."""
    if expected_sha1 is not None:
        got = git_blob_sha1(Path(csv_path))
        if got != expected_sha1:
            raise ValueError(
                f"copie Scenarii divergente de l'amont : blob {got} != {expected_sha1} "
                "(resynchroniser depuis le sous-module, ne pas editer a la main)")
    with open(csv_path, encoding="utf-8-sig", newline="") as f:
        rows = list(csv.DictReader(f))
    return [Scenario(r["path"].strip(), r["category"].strip(), r["title"].strip())
            for r in rows]


EXAMPLE_MIN_LEN = 25
_TAGGED_LINE = re.compile(r"^\[[^\]]+\]\s*(.*)$")


def _definition(text: str) -> str:
    """Definition utilisable dans un prompt.

    Au commit amont epingle, une cellule (``desc_fa`` du noeud F944) porte la
    carte entiere en trois lignes etiquetees ``[nom]`` / ``[explication]`` /
    ``[exemple]``, exemple compris. On n'en garde que la ligne d'explication (la
    deuxieme) ; ``load_texts`` refuse ensuite toute definition qui contiendrait
    encore un exemple.
    """
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    tagged = [_TAGGED_LINE.match(ln) for ln in lines]
    if len(lines) == 3 and all(tagged):
        return tagged[1].group(1).strip()
    return text


def load_texts(fallacies_csv: Path = DEFAULT_FALLACIES, virtues_csv: Path = DEFAULT_VIRTUES,
               scenarii_csv: Path = DEFAULT_SCENARII) -> dict:
    """Index des textes multilingues, pour le rendu des prompts.

    ``{"nodes": {key: {lang: (titre, definition, [exemples])}}, "scenarios": {path: row}}``.
    Les exemples ne servent qu'au controle d'anti-circularite, jamais au prompt :
    un titre ou une definition qui en contient un leve ``ValueError``.
    """
    nodes: dict[str, dict] = {}
    with open(fallacies_csv, encoding="utf-8-sig", newline="") as f:
        for r in csv.DictReader(f):
            if not r["PK"].strip().isdigit():
                continue
            nodes["F" + r["PK"].strip()] = {
                lg: (r.get(f"text_{lg}", "").strip(), _definition(r.get(f"desc_{lg}", "").strip()),
                     [r.get(c, "").strip() for c in (f"example_{lg}", f"example_{lg}_bis",
                                                     f"political_example_{lg}")])
                for lg in LANGS}
    with open(virtues_csv, encoding="utf-8-sig", newline="") as f:
        for r in csv.DictReader(f):
            if not r["pk"].strip().isdigit():
                continue
            nodes["V" + r["pk"].strip()] = {
                lg: (r.get(f"title_{lg}", "").strip(),
                     _definition(r.get(f"description_{lg}", "").strip()),
                     [r.get(f"remark_{lg}", "").strip()])
                for lg in LANGS}
    for key, langs in nodes.items():
        for lg, (title, definition, examples) in langs.items():
            if any(len(e) >= EXAMPLE_MIN_LEN and (e in title or e in definition)
                   for e in examples):
                raise ValueError(f"{key} [{lg}] : un exemple du noeud figure dans son titre "
                                 "ou sa definition, le prompt le transmettrait")
    with open(scenarii_csv, encoding="utf-8-sig", newline="") as f:
        scen = {r["path"].strip(): r for r in csv.DictReader(f)}
    return {"nodes": nodes, "scenarios": scen}


# --------------------------------------------------------------------------
# Splits de scenarii
# --------------------------------------------------------------------------

def split_scenarios(scenarios: list[Scenario], fractions=(0.70, 0.15, 0.15),
                    seed: int = 0) -> dict[str, str]:
    """Partition des scenarii en train/val/test, stratifiee par categorie.

    Chaque categorie de 3 scenarii ou plus donne au moins un scenario a val et a
    test. Deterministe : l'ordre ne depend que de ``seed`` et des chemins.
    """
    _, f_val, f_test = fractions
    by_cat: dict[str, list[str]] = defaultdict(list)
    for s in scenarios:
        by_cat[s.category].append(s.path)
    out: dict[str, str] = {}
    for cat in sorted(by_cat):
        paths = sorted(by_cat[cat])
        random.Random(f"{seed}:{cat}").shuffle(paths)
        n = len(paths)
        n_val = max(1, round(n * f_val)) if n >= 3 else 0
        n_test = max(1, round(n * f_test)) if n >= 3 else 0
        for i, p in enumerate(paths):
            out[p] = "val" if i < n_val else "test" if i < n_val + n_test else "train"
    return out


# --------------------------------------------------------------------------
# Allocation equilibree
# --------------------------------------------------------------------------

def allocate_counts(nodes: list[Node], budget: int, alpha: float) -> dict[str, int]:
    """Quota d'entrainement par noeud, poids ``n_f ** -alpha`` (plus grands restes).

    Chaque noeud recoit au moins une paire. ``budget`` est le total vise pour
    ces noeuds ; l'arrondi au plus grand reste le respecte exactement tant que
    ``budget >= len(nodes)``.
    """
    fam_size = Counter(n.family for n in nodes)
    weights = {n.key: fam_size[n.family] ** (-alpha) for n in nodes}
    total_w = sum(weights.values())
    raw = {k: budget * w / total_w for k, w in weights.items()}
    counts = {k: max(1, int(v)) for k, v in raw.items()}
    missing = budget - sum(counts.values())
    if missing > 0:
        order = sorted(raw, key=lambda k: (-(raw[k] - int(raw[k])), k))
        for k in order[:missing]:
            counts[k] += 1
    return counts


def imbalance(nodes: list[Node], counts: dict[str, int]) -> dict:
    """Rapports max/min au niveau famille et au niveau noeud."""
    fam_tot: Counter = Counter()
    for n in nodes:
        fam_tot[n.family] += counts[n.key]
    per_node = [counts[n.key] for n in nodes]
    sizes = Counter(n.family for n in nodes)
    return {
        "family_ratio": max(fam_tot.values()) / min(fam_tot.values()),
        "node_ratio": max(per_node) / min(per_node),
        "size_ratio": max(sizes.values()) / min(sizes.values()),
        "family_totals": dict(sorted(fam_tot.items(), key=lambda kv: -kv[1])),
    }


# --------------------------------------------------------------------------
# Construction des paires
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Pair:
    pair_id: str
    split: str
    polarity: str
    node_pk: int
    family: str
    depth: int
    is_leaf: bool
    scenario_path: str


def _pick_least_used(pool: list[str], usage: Counter, k: int, rng: random.Random) -> list[str]:
    """``k`` scenarii distincts parmi les moins utilises (egalites tirees au sort)."""
    ranked = sorted(pool, key=lambda p: (usage[p], rng.random()))
    chosen = ranked[:k]
    for p in chosen:
        usage[p] += 1
    return chosen


def build_pairs(nodes: list[Node], scen_split: dict[str, str], budgets: dict[str, int],
                alpha: float = 0.5, val_per_node: int = 1, test_per_node: int = 2,
                seed: int = 0) -> list[Pair]:
    """Paires (scenario, noeud) des trois splits.

    ``budgets`` fixe le total d'entrainement par polarite (``fallacy``/``virtue``).
    Un noeud ne voit jamais deux fois le meme scenario dans un split, et les
    scenarii d'un split sont consommes de facon uniforme (moins utilise d'abord).
    """
    pools = {s: sorted(p for p, sp in scen_split.items() if sp == s) for s in SPLITS}
    quota: dict[str, int] = {}
    for pol, budget in budgets.items():
        sub = [n for n in nodes if n.polarity == pol]
        quota.update(allocate_counts(sub, budget, alpha))
    per_split = {"train": quota,
                 "val": {n.key: val_per_node for n in nodes},
                 "test": {n.key: test_per_node for n in nodes}}
    rng = random.Random(seed)
    order = sorted(nodes, key=lambda n: n.key)
    rng.shuffle(order)
    pairs: list[Pair] = []
    for split in SPLITS:
        usage: Counter = Counter({p: 0 for p in pools[split]})
        for n in order:
            k = per_split[split][n.key]
            if k > len(pools[split]):
                raise ValueError(f"{n.key}: {k} paires demandees, {len(pools[split])} "
                                 f"scenarii dans le split {split}")
            for sp in _pick_least_used(pools[split], usage, k, rng):
                pairs.append(Pair(f"{split}-{n.key}-{sp}", split, n.polarity, n.pk,
                                  n.family, n.depth, n.is_leaf, sp))
    pairs.sort(key=lambda p: (SPLITS.index(p.split), p.polarity, p.family, p.node_pk,
                              p.scenario_path))
    return pairs


def leak_report(pairs: list[Pair], nodes: list[Node]) -> dict:
    """Controles d'etancheite et de couverture ; tout doit valoir 0 ou True."""
    scen_by_split = {s: {p.scenario_path for p in pairs if p.split == s} for s in SPLITS}
    keys = {n.key for n in nodes}

    def key(p: Pair) -> str:
        return ("F" if p.polarity == "fallacy" else "V") + str(p.node_pk)

    covered = {s: {key(p) for p in pairs if p.split == s} for s in SPLITS}
    pair_keys = Counter((key(p), p.scenario_path) for p in pairs)
    return {
        "scenario_overlap": {f"{a}&{b}": len(scen_by_split[a] & scen_by_split[b])
                             for a, b in (("train", "val"), ("train", "test"), ("val", "test"))},
        "labels_missing": {s: len(keys - covered[s]) for s in SPLITS},
        "duplicate_pairs": sum(1 for c in pair_keys.values() if c > 1),
    }


def scenario_usage(pairs: list[Pair]) -> dict:
    """Min/max d'utilisation des scenarii par split (uniformite du tirage)."""
    out = {}
    for s in SPLITS:
        c = Counter(p.scenario_path for p in pairs if p.split == s)
        out[s] = {"scenarios": len(c), "min": min(c.values()), "max": max(c.values())}
    return out


# --------------------------------------------------------------------------
# Prompt de l'enseignant (tranche B)
# --------------------------------------------------------------------------

_SCEN_FIELDS = {"title": "titre", "smoothTalker": "baratineur", "drawer": "piocheur",
                "context": "contexte", "issue": "enjeu"}


def _scen_field(row: dict, field: str, lang: str) -> str:
    if lang == "en":
        return row[field].strip()
    if lang == "fr":
        return row[_SCEN_FIELDS[field]].strip()
    return row[f"{field}_{lang}"].strip()


def render_prompt(pair: Pair, texts: dict, lang: str = "en") -> str:
    """Consigne donnee au LLM enseignant pour une paire, dans la langue ``lang``.

    La consigne est en anglais ; seule la reponse attendue est dans ``lang``. Le
    noeud n'est decrit que par son titre et sa definition : ses exemples ne
    sont jamais transmis (anti-circularite).

    Les roles suivent le jeu : pour un sophisme, le baratineur (``smoothTalker``)
    parle au piocheur (``drawer``) ; pour une vertu, c'est le piocheur qui lui
    repond, puisque le baratineur a pour consigne de defendre une these intenable.
    """
    key = ("F" if pair.polarity == "fallacy" else "V") + str(pair.node_pk)
    title, definition, _ = texts["nodes"][key][lang]
    row = texts["scenarios"][pair.scenario_path]
    talker = _scen_field(row, "smoothTalker", lang)
    drawer = _scen_field(row, "drawer", lang)
    if pair.polarity == "fallacy":
        speaker, listener, what = talker, drawer, "commits the fallacy"
    else:
        speaker, listener, what = drawer, talker, "shows the argumentative virtue"
    return (
        f"Scenario: {_scen_field(row, 'title', lang)}\n"
        f"Context: {_scen_field(row, 'context', lang)} {_scen_field(row, 'issue', lang)}\n"
        f"Speaker: {speaker}. Listener: {listener}.\n"
        f"Task: write, in {LANG_NAMES[lang]}, 2 to 4 sentences said by the speaker to the "
        f"listener, in which the speaker {what} \"{title}\" ({definition}). "
        "Do not name it and do not explain it: the reader must recognise it."
    )


def prompt_contains_example(pair: Pair, texts: dict, lang: str,
                            min_len: int = EXAMPLE_MIN_LEN) -> bool:
    """Vrai si un champ exemple du noeud (>= ``min_len`` caracteres) figure dans le prompt."""
    key = ("F" if pair.polarity == "fallacy" else "V") + str(pair.node_pk)
    prompt = render_prompt(pair, texts, lang)
    return any(len(e) >= min_len and e in prompt for e in texts["nodes"][key][lang][2])


# --------------------------------------------------------------------------
# Ecriture
# --------------------------------------------------------------------------

def split_csv_bytes(pairs: list[Pair], split: str) -> bytes:
    """Contenu CSV d'un split (UTF-8, LF, colonnes CSV_COLUMNS), octet pour octet stable."""
    buf = io.StringIO(newline="")
    w = csv.DictWriter(buf, fieldnames=CSV_COLUMNS, lineterminator="\n")
    w.writeheader()
    for pr in pairs:
        if pr.split == split:
            row = asdict(pr)
            row["is_leaf"] = int(pr.is_leaf)
            w.writerow(row)
    return buf.getvalue().encode("utf-8")


def write_splits(pairs: list[Pair], out_dir: Path) -> dict[str, Path]:
    """Ecrit ``train.csv``/``val.csv``/``test.csv`` dans ``out_dir``."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    paths = {}
    for s in SPLITS:
        p = out_dir / f"{s}.csv"
        p.write_bytes(split_csv_bytes(pairs, s))
        paths[s] = p
    return paths


def build_manifest(pairs: list[Pair], nodes: list[Node], params: dict, sources: dict) -> dict:
    """Parametres, sources (SHA de blob) et comptes : ce qui rend le dataset rejouable.

    ``files`` porte le SHA-256 de chaque split : ``train.csv`` n'est pas committe
    (il se regenere a l'identique en moins d'une seconde), c'est ce hash qui
    l'epingle.
    """
    counts = Counter(p.split for p in pairs)
    files = {f"{s}.csv": {"rows": counts[s],
                          "sha256": hashlib.sha256(split_csv_bytes(pairs, s)).hexdigest()}
             for s in SPLITS}
    train_counts: Counter = Counter()
    for p in pairs:
        if p.split == "train":
            train_counts[("F" if p.polarity == "fallacy" else "V") + str(p.node_pk)] += 1
    balance = {pol: imbalance([n for n in nodes if n.polarity == pol], train_counts)
               for pol in ("fallacy", "virtue")}
    return {
        "params": params,
        "sources": sources,
        "files": files,
        "counts": {s: counts[s] for s in SPLITS},
        "nodes": dict(Counter(n.polarity for n in nodes)),
        "balance_train": {pol: {k: (round(v, 4) if isinstance(v, float) else v)
                                for k, v in b.items()} for pol, b in balance.items()},
        "leaks": leak_report(pairs, nodes),
        "scenario_usage": scenario_usage(pairs),
    }


DEFAULT_PARAMS = {"alpha": 0.5, "budgets": {"fallacy": 12000, "virtue": 2000},
                  "fractions": [0.70, 0.15, 0.15], "val_per_node": 1, "test_per_node": 2,
                  "seed": 0}


def build(params: dict = DEFAULT_PARAMS, fallacies_csv: Path = DEFAULT_FALLACIES,
          virtues_csv: Path = DEFAULT_VIRTUES, scenarii_csv: Path = DEFAULT_SCENARII):
    """Chaine complete : (noeuds, scenarii, split des scenarii, paires, manifeste)."""
    nodes = load_fallacies(fallacies_csv) + load_virtues(virtues_csv)
    scenarios = load_scenarios(scenarii_csv)
    scen_split = split_scenarios(scenarios, tuple(params["fractions"]), params["seed"])
    pairs = build_pairs(nodes, scen_split, params["budgets"], params["alpha"],
                        params["val_per_node"], params["test_per_node"], params["seed"])
    sources = {
        "fallacies_blob_sha1": git_blob_sha1(fallacies_csv),
        "virtues_blob_sha1": git_blob_sha1(virtues_csv),
        "scenarii_blob_sha1": git_blob_sha1(scenarii_csv),
        "scenarii_upstream_commit": SCENARII_UPSTREAM_COMMIT,
    }
    return nodes, scenarios, scen_split, pairs, build_manifest(pairs, nodes, params, sources)


def write_manifest(manifest: dict, out_dir: Path) -> Path:
    """Ecrit ``manifest.json`` en LF quel que soit l'OS (octets stables d'une machine a l'autre)."""
    path = Path(out_dir) / "manifest.json"
    path.write_bytes((json.dumps(manifest, indent=1, ensure_ascii=False) + "\n").encode("utf-8"))
    return path


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, required=True, help="dossier de sortie des CSV")
    ap.add_argument("--alpha", type=float, default=DEFAULT_PARAMS["alpha"])
    ap.add_argument("--seed", type=int, default=DEFAULT_PARAMS["seed"])
    args = ap.parse_args(argv)
    params = dict(DEFAULT_PARAMS, alpha=args.alpha, seed=args.seed)
    _, _, _, pairs, manifest = build(params)
    write_splits(pairs, args.out)
    write_manifest(manifest, args.out)
    print(json.dumps({"counts": manifest["counts"], "leaks": manifest["leaks"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
