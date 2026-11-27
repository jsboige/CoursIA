#!/usr/bin/env python3
"""Générateur seedé du corpus de faits fictifs PT-22 (issue #27376, volet A, étape E1).

Scellé de référence : ``docs/genai/pt16-sleep-dreaming-pre-enregistrement.md``,
section « Corpus de faits et stades » : 60 faits fictifs « sujet -> attribut »,
40 train, 20 held-out, ces derniers jamais entraînés ni rejoués.

Le corpus est figé avant le module d'entraînement. Principes posés d'avance :

* **Quatre créneaux** (la relation portée par la question) : ville de naissance,
  langue natale, roman écrit, entreprise fondée. Chaque créneau a son gabarit de
  question et la morphologie de ses réponses. Dix faits train et cinq held-out par
  créneau, quel que soit l'ordre de tirage.
* **Des noms inventés, composés de syllabes** : les sujets sont des noms de personne
  (prénom et nom), les attributs des noms propres dont la forme dépend du créneau.
* **Train et held-out ne partagent aucune syllabe** : chaque réservoir est coupé en
  deux moitiés par la graine, le train tire dans la première, le held-out dans la
  seconde. Les réservoirs sont disjoints deux à deux, donc un fait held-out ne
  partage ni nom ni syllabe avec un fait train.
* **Une seule graine** (``SEED``) : deux exécutions rendent des octets identiques.

Le fichier produit, ``pt22_facts.json``, est l'artefact qui fait foi. ``--check`` le
régénère en mémoire, exige l'identité octet pour octet, puis contrôle les invariants
structurels sur le fichier relu.

Ce générateur ne charge aucun modèle : l'écart des noms avec le pré-entraînement se
mesure par la sonde S0 (``pt22_s0_probe.py``).

Usage, depuis la racine du dépôt ::

    python MyIA.AI.Notebooks/GenAI/PostTraining/assets/pt22_facts_generator.py
    python MyIA.AI.Notebooks/GenAI/PostTraining/assets/pt22_facts_generator.py --check
    python MyIA.AI.Notebooks/GenAI/PostTraining/assets/pt22_facts_generator.py --stdout
"""

from __future__ import annotations

import argparse
import json
import random
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SEED = 27376
ISSUE = 27376
SCHEMA = "pt22-facts/v1"
SEALED_DOC = "docs/genai/pt16-sleep-dreaming-pre-enregistrement.md"
OUT_NAME = "pt22_facts.json"

TRAIN = "train"
HELDOUT = "held-out"
N_TRAIN_PER_SLOT = 10
N_HELDOUT_PER_SLOT = 5
N_TRAIN = 4 * N_TRAIN_PER_SLOT
N_HELDOUT = 4 * N_HELDOUT_PER_SLOT
ID_PREFIX = "pt22-"


# --- Réservoirs de syllabes ---------------------------------------------------
# Un même syllabe n'appartient jamais à deux réservoirs (contrôle à l'exécution) :
# la coupure train / held-out d'un réservoir vaut donc pour tout le corpus.

GIVEN_HEADS = (
    "Vel", "Kor", "Tha", "Zan", "Mir", "Ryn", "Sov", "Lyr", "Kae", "Dru",
    "Tav", "Nal", "Osk", "Idr", "Bry", "Hal", "Tor", "Yr", "Sef", "Kay",
    "Ulm", "Mey", "Fen", "Aro", "Teg", "Vor", "Ily", "Sko", "Rhe", "Dun",
    "Gav", "Ilv", "Jor", "Kel", "Lo", "Mur", "Ner", "Pyr", "Quen", "Sel",
)
GIVEN_TAILS = (
    "rin", "dek", "eth", "lin", "tas", "vern", "ith", "na", "lai", "ri",
    "sa", "ren", "dak", "vi", "thos", "mel", "tur", "ont", "ick", "ys",
    "ane", "ob", "ull", "ert", "av", "ex", "il", "or", "um", "ath",
    "arn", "eld", "im", "ok", "us", "ael", "ur", "en", "ol", "ard",
)
SURNAME_HEADS = (
    "Mor", "Kal", "Dra", "Sarn", "Bel", "Lun", "Rok", "Maz", "Orm", "Pel",
    "Quil", "Ras", "Sil", "Thar", "Ulv", "Vas", "Wen", "Yal", "Zor", "Bran",
    "Cav", "Dorn", "Elg", "Fal", "Gor", "Hul", "Ist", "Jav", "Kars", "Lor",
    "Mev", "Nuv", "Orb", "Prav", "Ruv", "Skel", "Corv", "Deln", "Fars", "Halv",
)
SURNAME_TAILS = (
    "kai", "dax", "mer", "thir", "vane", "linn", "dal", "ris", "noth", "gar",
    "myr", "sen", "tar", "vex", "loth", "mund", "fay", "rinn", "salv", "dunn",
    "har", "esk", "mon", "nard", "pol", "roth", "stan", "tir", "und", "vale",
    "wenn", "yar", "dil", "net", "brin", "cors", "quay", "daer", "olm", "ust",
)
CITY_HEADS = (
    "Sor", "Thal", "Vey", "Ost", "Narv", "Pell", "Rusk", "Torv", "Vand", "Zarn",
    "Brek", "Drev", "Gald", "Kerv", "Skar", "Farn", "Ond", "Tolv", "Grell", "Misk",
    "Ylf", "Zeph", "Corl", "Hult",
)
CITY_MIDS = (
    "dor", "len", "mar", "vin", "hol", "ast", "ber", "nil",
    "tyr", "gan", "uld", "rif", "osh", "myl", "erv", "tond",
)
CITY_ENDINGS = (
    "dale", "ton", "ford", "burg", "haven", "field", "mere", "wick",
    "stad", "mark", "fell", "holm", "gard", "by", "shaw", "crest",
)
LANG_HEADS = (
    "Qar", "Zhe", "Tal", "Vesh", "Kesh", "Lom", "Nyr", "Orv", "Rhun", "Syl",
    "Urm", "Wyn", "Aun", "Brel", "Cyr", "Fael", "Hyl", "Jal", "Parn", "Sav",
    "Tarn", "Uzo", "Vhal", "Zhur",
)
LANG_SUFFIXES = (
    "ish", "ic", "ese", "ari", "ani", "ean",
    "ian", "orr", "ali", "oth", "uvi", "uri",
)
TITLE_HEADS = (
    "Cir", "Dael", "Fyl", "Gwyn", "Hesper", "Ivr", "Kriv", "Lorn",
    "Nev", "Ondr", "Quill", "Rav", "Skarn", "Ter", "Umbr", "Vayl",
    "Weth", "Xan", "Yvor", "Zyr", "Ambr", "Bery", "Cael", "Drav",
)
TITLE_TAILS = (
    "ora", "iel", "ine", "ash", "ura", "ama",
    "oris", "yss", "une", "yrr", "avel", "quor",
)
COMPANY_HEADS = (
    "Nor", "Vax", "Zen", "Cra", "Gal", "Hav", "Jux", "Kox",
    "Lum", "Nex", "Ovr", "Pra", "Quin", "Rho", "Syt", "Tev",
    "Ulx", "Van", "Wex", "Yor", "Zyl", "Brix", "Cort", "Delt",
)
COMPANY_SUFFIXES = (
    "ix", "ova", "tek", "dyn", "ara", "ona",
    "is", "ent", "ary", "igo", "ell", "ox",
)

# Noms refusés après lecture (collision avec un nom ou un lieu réel, forme maladroite).
# Un refus est une donnée du générateur : il change le tirage, donc le corpus.
REJECTED_NAMES: dict[str, str] = {
    "vanara": "terme sanskrit réel (peuple simiesque du Ramayana)",
    "deltona": "ville réelle de Floride",
    "noris": "marque et banque réelles (Noris, Norisbank)",
    "havona": "planète de fiction du cycle Fondation (Asimov)",
    "lumix": "marque d'appareils photo (Panasonic)",
    "keshian": "dénonyme de fiction (saga Riftwar, Feist)",
    "craent": "forme maladroite (suite crae-)",
    "zenona": "prénom réel (polonais), mal venu comme nom d'entreprise",
}


@dataclass(frozen=True)
class Slot:
    """Un créneau : son nom, son gabarit de question, les réservoirs de ses attributs."""

    name: str
    question: str
    pools: tuple[tuple[str, ...], ...]


SLOTS = (
    Slot("birthplace", "In which city was {subject} born?",
         (CITY_HEADS, CITY_MIDS, CITY_ENDINGS)),
    Slot("native_language", "What is {subject}'s native language?",
         (LANG_HEADS, LANG_SUFFIXES)),
    Slot("novel", "Which novel did {subject} write?",
         (TITLE_HEADS, TITLE_TAILS)),
    Slot("company", "Which company did {subject} found?",
         (COMPANY_HEADS, COMPANY_SUFFIXES)),
)

_ALL_POOLS = (
    (GIVEN_HEADS, GIVEN_TAILS, SURNAME_HEADS, SURNAME_TAILS)
    + tuple(pool for slot in SLOTS for pool in slot.pools)
)

_VOWELS = "aeiouy"
_VOWEL_RUN = re.compile(rf"[{_VOWELS}]{{3,}}")
_CONSONANT_RUN = re.compile(rf"[^{_VOWELS}]{{4,}}")
_TRIPLE_LETTER = re.compile(r"(.)\1\1")
# Écran de forme : séquences vulgaires ou blessantes, en anglais comme en français,
# cherchées comme sous-chaînes du nom en minuscules.
_BAD_SUBSTRINGS = (
    "fuck", "shit", "cunt", "rape", "nazi", "porn", "piss", "dick", "anus", "anal",
    "penis", "cum", "kkk", "satan", "hitler", "putain", "merde", "bitch", "slut",
    "whore", "nigg", "fag", "dyke", "spic", "kike", "retard", "suic", "kill", "murd",
    "negr", "pede", "bite", "chier", "foutre", "cock", "twat", "prick", "wank",
    "clit", "erect", "orgas", "horny", "nude", "hh", "ww",
)
_MIN_LEN = 5
_MAX_LEN = 12
_MAX_DRAWS = 100_000


def _is_wellformed(name: str) -> bool:
    """Contrôle de forme : longueur, suites de voyelles ou consonantes, écran de séquences."""
    low = name.lower()
    if not _MIN_LEN <= len(low) <= _MAX_LEN:
        return False
    if _VOWEL_RUN.search(low) or _CONSONANT_RUN.search(low) or _TRIPLE_LETTER.search(low):
        return False
    if any(bad in low for bad in _BAD_SUBSTRINGS):
        return False
    return True


def _check_pools() -> None:
    """Chaque réservoir est sans doublon, et deux réservoirs ne partagent aucune syllabe."""
    seen: dict[str, str] = {}
    for pool in _ALL_POOLS:
        if len(set(pool)) != len(pool):
            raise ValueError(f"réservoir avec doublon : {pool}")
        for syllable in pool:
            key = syllable.lower()
            if key in seen:
                raise ValueError(f"syllabe {syllable!r} partagée avec {seen[key]!r}")
            seen[key] = syllable
            if any(bad in key for bad in _BAD_SUBSTRINGS):
                raise ValueError(f"syllabe {syllable!r} heurte l'écran de forme")
    for pool in _ALL_POOLS:
        if len(pool) % 2:
            raise ValueError(f"réservoir de taille impaire : {pool[0]}... ({len(pool)})")


def _shuffle(rng: random.Random, items: tuple[str, ...]) -> list[str]:
    """Mélange de Fisher-Yates sur ``randrange`` seul (stable d'une version de Python à l'autre)."""
    out = list(items)
    for i in range(len(out) - 1, 0, -1):
        j = rng.randrange(i + 1)
        out[i], out[j] = out[j], out[i]
    return out


def _halves(rng: random.Random, pool: tuple[str, ...]) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Coupe un réservoir en deux moitiés : la première sert le train, la seconde le held-out."""
    mixed = _shuffle(rng, pool)
    cut = len(mixed) // 2
    return tuple(mixed[:cut]), tuple(mixed[cut:])


def _draw(rng: random.Random, pools: tuple[tuple[str, ...], ...], count: int,
          taken: set[str]) -> list[tuple[str, ...]]:
    """Tire ``count`` noms uniques et bien formés ; renvoie leurs syllabes et les ajoute à ``taken``."""
    out: list[tuple[str, ...]] = []
    for _ in range(_MAX_DRAWS):
        if len(out) == count:
            return out
        parts = tuple(pool[rng.randrange(len(pool))] for pool in pools)
        name = "".join(parts).lower()
        if name in taken or name in REJECTED_NAMES or not _is_wellformed(name):
            continue
        taken.add(name)
        out.append(parts)
    raise RuntimeError(f"tirage épuisé avant {count} noms pour {pools[0][0]}...")


def _cap(name: str) -> str:
    return name[0].upper() + name[1:]


def build(seed: int = SEED) -> dict[str, Any]:
    """Construit le corpus : dictionnaire prêt à sérialiser."""
    _check_pools()
    rng = random.Random(seed)
    given_halves = (_halves(rng, GIVEN_HEADS), _halves(rng, GIVEN_TAILS))
    surname_halves = (_halves(rng, SURNAME_HEADS), _halves(rng, SURNAME_TAILS))
    names: dict[str, dict[str, list[tuple[str, ...]]]] = {}
    for split in (TRAIN, HELDOUT):
        half = 0 if split == TRAIN else 1
        count = N_TRAIN if split == TRAIN else N_HELDOUT
        givens = _draw(rng, (given_halves[0][half], given_halves[1][half]), count, set())
        surnames = _draw(rng, (surname_halves[0][half], surname_halves[1][half]), count, set())
        names[split] = {"given": givens, "surname": surnames}
    attributes: dict[str, dict[str, list[tuple[str, ...]]]] = {}
    for slot in SLOTS:
        split_pools = [_halves(rng, pool) for pool in slot.pools]
        attributes[slot.name] = {}
        for split in (TRAIN, HELDOUT):
            half = 0 if split == TRAIN else 1
            count = N_TRAIN_PER_SLOT if split == TRAIN else N_HELDOUT_PER_SLOT
            pools = tuple(sp[half] for sp in split_pools)
            attributes[slot.name][split] = _draw(rng, pools, count, set())

    facts: list[dict[str, Any]] = []
    for split, per_slot, total in ((TRAIN, N_TRAIN_PER_SLOT, N_TRAIN),
                                   (HELDOUT, N_HELDOUT_PER_SLOT, N_HELDOUT)):
        for i in range(total):
            slot = SLOTS[i // per_slot]
            given = names[split]["given"][i]
            surname = names[split]["surname"][i]
            parts = attributes[slot.name][split][i % per_slot]
            subject = f"{_cap(''.join(given))} {_cap(''.join(surname))}"
            attribute = _cap("".join(parts))
            question = slot.question.format(subject=subject)
            facts.append({
                "id": f"{ID_PREFIX}{len(facts) + 1:03d}",
                "split": split,
                "slot": slot.name,
                "subject": subject,
                "subject_parts": [*given, *surname],
                "attribute": attribute,
                "attribute_parts": list(parts),
                "question": question,
                "prompt": f"Question: {question}\nAnswer:",
                "target": f" {attribute}",
            })
    return {
        "schema": SCHEMA,
        "issue": ISSUE,
        "sealed_doc": SEALED_DOC,
        "generator": Path(__file__).name,
        "seed": seed,
        "description": (
            "60 faits fictifs « sujet -> attribut » pour l'étude PT-22 : 40 train, "
            "20 held-out (jamais entraînés, jamais rejoués). Quatre créneaux de dix "
            "faits train et cinq held-out. Noms inventés, composés de syllabes ; "
            "aucune syllabe n'est partagée entre un fait train et un fait held-out."
        ),
        "format": {
            "prompt": "« Question: » + question + « \\nAnswer: »",
            "target": "une espace, puis l'attribut",
            "order": "les 40 faits train (ids 001 a 040), puis les 20 faits held-out (ids 041 a 060)",
            "held-out": "prompts fixes, ordre fixe ; jamais entraînés, jamais rejoués",
        },
        "slots": [
            {
                "slot": slot.name,
                "question_template": slot.question,
                "train": N_TRAIN_PER_SLOT,
                "held-out": N_HELDOUT_PER_SLOT,
            }
            for slot in SLOTS
        ],
        "counts": {"train": N_TRAIN, "held-out": N_HELDOUT, "total": N_TRAIN + N_HELDOUT},
        "facts": facts,
    }


def render(doc: dict[str, Any]) -> str:
    return json.dumps(doc, indent=2, ensure_ascii=False) + "\n"


def check_doc(doc: dict[str, Any]) -> list[str]:
    """Invariants structurels du corpus ; renvoie la liste des manques (vide = conforme)."""
    problems: list[str] = []
    facts = doc.get("facts", [])
    by_slot = {slot["slot"]: slot["question_template"] for slot in doc.get("slots", [])}
    ids = [fact["id"] for fact in facts]
    if len(facts) != N_TRAIN + N_HELDOUT or len(set(ids)) != len(facts):
        problems.append(f"attendu {N_TRAIN + N_HELDOUT} faits d'identifiants distincts, lu {len(facts)}")
    if ids != [f"{ID_PREFIX}{i:03d}" for i in range(1, len(facts) + 1)]:
        problems.append("identifiants non consécutifs dans l'ordre du fichier")
    splits = [fact["split"] for fact in facts]
    if splits != [TRAIN] * N_TRAIN + [HELDOUT] * N_HELDOUT:
        problems.append("blocs train puis held-out non respectés")

    per_slot: dict[tuple[str, str], int] = {}
    for fact in facts:
        per_slot[(fact["split"], fact["slot"])] = per_slot.get((fact["split"], fact["slot"]), 0) + 1
    for name in by_slot:
        if per_slot.get((TRAIN, name)) != N_TRAIN_PER_SLOT:
            problems.append(f"{name} : {per_slot.get((TRAIN, name))} faits train, attendu {N_TRAIN_PER_SLOT}")
        if per_slot.get((HELDOUT, name)) != N_HELDOUT_PER_SLOT:
            problems.append(f"{name} : {per_slot.get((HELDOUT, name))} faits held-out, attendu {N_HELDOUT_PER_SLOT}")

    subjects = [fact["subject"] for fact in facts]
    surnames = [subject.split(" ")[-1] for subject in subjects]
    attributes = [fact["attribute"] for fact in facts]
    for label, names in (("sujet", subjects), ("nom de famille", surnames), ("attribut", attributes)):
        if len(set(names)) != len(names):
            problems.append(f"{label}s non uniques")

    syllables: dict[str, set[str]] = {TRAIN: set(), HELDOUT: set()}
    for fact in facts:
        template = by_slot.get(fact["slot"], "")
        subject, attribute = fact["subject"], fact["attribute"]
        parts = [*fact.get("subject_parts", []), *fact.get("attribute_parts", [])]
        if "".join(fact.get("subject_parts", [])).lower() != subject.replace(" ", "").lower():
            problems.append(f"{fact['id']} : subject_parts ne recomposent pas le sujet")
        if _cap("".join(fact.get("attribute_parts", []))) != attribute:
            problems.append(f"{fact['id']} : attribute_parts ne recomposent pas l'attribut")
        if fact["question"] != template.format(subject=subject) or fact["question"].count(subject) != 1:
            problems.append(f"{fact['id']} : question incohérente avec le gabarit du créneau")
        if fact["prompt"] != f"Question: {fact['question']}\nAnswer:" or fact["target"] != f" {attribute}":
            problems.append(f"{fact['id']} : prompt ou cible incohérents")
        for name in (subject.split(" ")[0], subject.split(" ")[-1], attribute):
            if name.lower() in REJECTED_NAMES or not _is_wellformed(name):
                problems.append(f"{fact['id']} : nom {name!r} refusé ou mal formé")
        split = fact["split"]
        if split in syllables:
            syllables[split].update(piece.lower() for piece in parts)
    shared = syllables[TRAIN] & syllables[HELDOUT]
    if shared:
        problems.append(f"syllabes partagées entre train et held-out : {sorted(shared)}")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Générateur du corpus de faits fictifs PT-22.")
    parser.add_argument("--check", action="store_true",
                        help="régénère en mémoire, exige l'identité octet pour octet, contrôle les invariants")
    parser.add_argument("--stdout", action="store_true", help="imprime le JSON sur la sortie standard")
    parser.add_argument("--out", type=Path, default=None, help=f"chemin de sortie (défaut : {OUT_NAME} à côté du script)")
    args = parser.parse_args(argv)

    text = render(build())
    if args.stdout:
        sys.stdout.write(text)
        return 0
    out = args.out or Path(__file__).resolve().parent / OUT_NAME
    if args.check:
        if not out.exists():
            print(f"ABSENT : {out.name} n'existe pas")
            return 1
        on_disk = out.read_bytes()
        if on_disk != text.encode("utf-8"):
            print(f"DERIVE : {out.name} diffère de la régénération (graine {SEED})")
            return 1
        problems = check_doc(json.loads(on_disk.decode("utf-8")))
        for problem in problems:
            print(f"INVARIANT : {problem}")
        if problems:
            return 1
        print(f"OK : {out.name} identique à la régénération, invariants tenus ({N_TRAIN + N_HELDOUT} faits)")
        return 0
    out.write_bytes(text.encode("utf-8"))
    print(f"ECRIT : {out} ({N_TRAIN + N_HELDOUT} faits, graine {SEED})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
