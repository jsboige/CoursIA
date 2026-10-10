#!/usr/bin/env python3
"""Generation du corpus enseignant de Phase 2 (EPIC #10355, issue #17578).

La tranche A (``cartesian_dataset_builder``) decide *quelles* paires
``(scenario, noeud)`` entrent dans le dataset et rend le prompt qu'un LLM
enseignant recevra ; elle ne produit aucun texte. Ce module est la **tranche B** :
il fait tourner le maitre sur ces prompts et **mesure** ce qu'il rend.

Trois proprietes sont mesurees, pas supposees :

1. **Le maitre rend un texte.** Une generation vide, ou trop courte pour porter
   les 2-4 phrases demandees, est **regeneree** : le plancher ``min_tokens``
   signale une sortie degeneree, il ne la filtre pas en silence.
2. **La circularite est nulle, et verifiee sur la SORTIE.** Le prompt ne
   transmet jamais les champs ``example_*`` du noeud (propriete de la tranche A) ;
   ce module verifie que le texte produit n'en contient pas non plus. Compter
   seulement sur la conception du prompt supposerait le resultat.
3. **Le texte est reclassable sur son propre noeud.** Chaque generation passe un
   **controle aller-retour** : un second passage, a temperature nulle, choisit le
   noeud parmi le noeud cible et ``k`` distracteurs de meme polarite. Le verdict
   est la **majorite de ``votes`` tours** : mesure faite sur 24 paires, environ
   la moitie des echecs d'un tir unique est de la variance d'echantillonnage
   (generation a temperature non nulle), donc un tir unique jetterait du bon
   texte.

Le client HTTP est **injecte** (``Teacher``) : les tests font tourner toute la
mecanique sans reseau, et la mesure de tete n'appelle jamais le hub depuis la CI.

Usage::

    python -m fallacy_detection.generate_teacher_corpus --out <dossier> --split val --limit 24
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import random
import re
import sys
import time
import urllib.error
import urllib.request
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Callable, Iterable, Optional, Protocol, Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fallacy_detection import cartesian_dataset_builder as B  # noqa: E402

_REPO_ROOT = Path(__file__).resolve().parents[2]
PHASE2_DIR = _REPO_ROOT / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/phase2"
DEFAULT_OUT = _REPO_ROOT / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher"

DEFAULT_HUB_URL = "http://192.168.0.47:5002/v1/chat/completions"
DEFAULT_MODEL = "qwen3.6-35b-a3b"
DEFAULT_API_KEY_ENV = "VLLM_API_KEY_MEDIUM"

# En dessous, la sortie ne peut pas porter les 2-4 phrases demandees (mesure du
# 2026-10-09 : une paire avait rendu 14 tokens avant de rendre juste au tirage
# suivant). C'est un seuil de *regeneration*, pas de rejet.
MIN_COMPLETION_TOKENS = 25
DEFAULT_MAX_TOKENS = 300
DEFAULT_VOTES = 3
DEFAULT_DISTRACTORS = 5
DEFAULT_RETRIES = 2

_ALPHABET = "ABCDEFGH"

# Un marqueur explicite passe avant tout balayage : « reponse : B », « option C ».
_MARKER = re.compile(r"(?:r[eé]ponse|option|choix|letter|answer)\s*:?\s*([A-H])",
                     re.IGNORECASE)

# Jeton qui est un mot courant en minuscules : « a » (avoir) n'est pas un vote,
# mais « A » majuscule en est un. Le laisser passer faisait lire « … ne
# correspond a aucune option » comme un vote pour le candidat A — un tour rate
# en silence.
_WORD_TOKENS = {"a"}


# --------------------------------------------------------------------------
# Client enseignant
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Reply:
    """Ce qu'un maitre rend pour un prompt."""

    text: str
    completion_tokens: int
    finish_reason: str


class Teacher(Protocol):
    """Interface minimale : deux appels, la generation et le vote de reclassement."""

    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> Reply:
        """Rend une completion pour ``prompt``."""


class HubTeacher:
    """Client du hub vLLM (endpoint compatible OpenAI).

    Le dialecte *thinking* est porte ici et nulle part ailleurs : ce catalogue
    est servi par vLLM, qui lit ``chat_template_kwargs.enable_thinking``. Un
    ``enable_thinking`` au niveau racine est **ignore** et le budget part
    entierement en ``reasoning_tokens`` (contenu vide, ``finish_reason: length``).
    """

    def __init__(self, url: str = DEFAULT_HUB_URL, model: str = DEFAULT_MODEL,
                 api_key: Optional[str] = None, api_key_env: str = DEFAULT_API_KEY_ENV,
                 timeout: float = 180.0, sleep: Callable[[float], None] = time.sleep):
        self.url = url
        self.model = model
        self.api_key = api_key if api_key is not None else os.getenv(api_key_env)
        if not self.api_key:
            raise ValueError(
                f"{api_key_env} absente de l'environnement : le module ne pose aucun "
                "repli litteral (hygiene des secrets).")
        self.timeout = timeout
        self._sleep = sleep

    def complete(self, prompt: str, *, max_tokens: int = DEFAULT_MAX_TOKENS,
                 temperature: float = 0.8) -> Reply:
        body = json.dumps({
            "model": self.model,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": temperature,
            "max_tokens": max_tokens,
            "chat_template_kwargs": {"enable_thinking": False},
        }).encode("utf-8")
        req = urllib.request.Request(self.url, data=body, headers={
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        })
        last: Optional[Exception] = None
        for attempt in range(3):
            try:
                with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                    payload = json.load(resp)
                break
            except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exc:
                last = exc
                if attempt == 2:
                    raise
                self._sleep(2.0 * (attempt + 1))
        else:  # pragma: no cover - la boucle sort par break ou raise
            raise RuntimeError("injoignable") from last
        choice = payload["choices"][0]
        usage = payload.get("usage") or {}
        message = choice.get("message") or {}
        return Reply(
            text=(message.get("content") or "").strip(),
            completion_tokens=int(usage.get("completion_tokens") or 0),
            finish_reason=str(choice.get("finish_reason") or ""),
        )


# --------------------------------------------------------------------------
# Controle aller-retour
# --------------------------------------------------------------------------

def node_key(pair: B.Pair) -> str:
    return ("F" if pair.polarity == "fallacy" else "V") + str(pair.node_pk)


def pick_distractors(key: str, node_keys: Sequence[str], k: int,
                     rng: random.Random) -> list[str]:
    """``k`` noeuds de meme polarite que ``key``, hors ``key`` lui-meme.

    La polarite est respectee : opposer un sophisme a une vertu rendrait le
    controle trivial et ne mesurerait plus la discrimination reelle.
    """
    same = [other for other in node_keys if other[0] == key[0] and other != key]
    if len(same) < k:
        raise ValueError(f"pas assez de noeuds de polarite {key[0]!r} pour {k} distracteurs")
    return rng.sample(same, k)


def build_choice_question(text: str, candidates: Sequence[str], texts: dict,
                          lang: str) -> str:
    """Question de reclassement : le texte, puis les candidats lettres.

    Le libelle et la definition sont tronques : le controle porte sur le
    **choix**, pas sur une lecture exhaustive de la taxonomie.
    """
    lines = []
    for index, key in enumerate(candidates):
        title, definition, _ = texts["nodes"][key][lang]
        lines.append(f"{_ALPHABET[index]}. {title} : {definition[:140]}")
    return (
        f"Voici un texte :\n\n{text}\n\n"
        "Quel sophisme/caractere argumentatif illustre-t-il le mieux ?\n"
        + "\n".join(lines)
        + "\n\nReponds uniquement par la lettre."
    )


def parse_choice(answer: str, candidates: Sequence[str]) -> Optional[str]:
    """Lettre choisie par le maitre, resolue en cle de noeud.

    Deux passes, dans cet ordre : un **marqueur explicite** (``reponse : B``,
    ``option C``), puis un **jeton d'une seule lettre** (``B``, ``b.``, ``(C)``).

    Balayer la reponse caractere par caractere — la premiere version — lisait
    l'article « La » ou le mot « aucune » comme un vote pour le candidat A : sur
    un corpus de plusieurs milliers de paires, ces tours faux se fondent dans le
    taux d'aller-retour sans laisser de trace. Un tour sans lettre exploitable
    rend ``None`` : c'est « non mesure », jamais un vote.

    Le prix de la prudence est assume : une reponse qui serait le seul caractere
    ``a`` minuscule n'est pas comptee, parce qu'elle est indiscernable du verbe
    « a ».
    """
    text = (answer or "").strip()
    if not text:
        return None
    marker = _MARKER.search(text)
    if marker:
        index = _ALPHABET.find(marker.group(1).upper())
        if 0 <= index < len(candidates):
            return candidates[index]
    for token in text.split():
        stripped = token.strip(".,;:!?)\"'()[]")
        if len(stripped) != 1 or stripped in _WORD_TOKENS:
            continue
        index = _ALPHABET.find(stripped.upper())
        if 0 <= index < len(candidates):
            return candidates[index]
    return None


def majority(picks: Iterable[Optional[str]], target: str) -> Optional[bool]:
    """``True`` si ``target`` est majoritaire, ``False`` si un autre l'est.

    Rend ``None`` quand aucun tour n'a produit de vote exploitable : c'est
    « non mesure », a ne pas confondre avec « rate ».
    """
    usable = [p for p in picks if p is not None]
    if not usable:
        return None
    counts: dict[str, int] = {}
    for pick in usable:
        counts[pick] = counts.get(pick, 0) + 1
    best = max(counts.values())
    winners = [key for key, count in counts.items() if count == best]
    return len(winners) == 1 and winners[0] == target


# --------------------------------------------------------------------------
# Generation d'une paire
# --------------------------------------------------------------------------

@dataclass
class Record:
    """Une generation et ses mesures. Une ligne du corpus."""

    pair_id: str
    split: str
    polarity: str
    node_pk: int
    family: str
    depth: int
    is_leaf: bool
    scenario_path: str
    lang: str
    node_key: str
    text: str
    completion_tokens: int
    finish_reason: str
    attempts: int
    examples: list[str] = field(default_factory=list)

    def example_overlap(self, min_len: int = B.EXAMPLE_MIN_LEN) -> bool:
        """Vrai si le texte rendu contient un champ exemple du noeud.

        C'est la mesure anti-circularite du corpus produit : la propriete est
        verifiee sur la SORTIE, pas deduite de la conception du prompt.
        """
        return any(len(e) >= min_len and e in self.text for e in self.examples)


def generate_one(pair: B.Pair, texts: dict, teacher: Teacher, *, lang: str,
                 rng: random.Random, votes: int = DEFAULT_VOTES,
                 distractors: int = DEFAULT_DISTRACTORS,
                 max_tokens: int = DEFAULT_MAX_TOKENS,
                 min_tokens: int = MIN_COMPLETION_TOKENS,
                 retries: int = DEFAULT_RETRIES) -> tuple[Record, Optional[bool], list[Optional[str]]]:
    """Genere le texte d'une paire, puis le fait reclasser par le meme maitre.

    Rend ``(record, verdict_aller_retour, votes_bruts)``. Le verdict est ``None``
    si aucun tour de vote n'a rendu de lettre exploitable.

    ``min_tokens`` est un **declencheur de regeneration**, pas une garantie :
    quand les ``retries`` sont epuises, le texte court est tout de meme
    **accepte** et entre dans le corpus. Ces cas sont rendus visibles par
    ``n_below_floor`` dans le rapport -- ``n_empty`` ne les compte pas, un
    texte court n'etant pas un texte vide.
    """
    prompt = B.render_prompt(pair, texts, lang=lang)
    reply = teacher.complete(prompt, max_tokens=max_tokens, temperature=0.8)
    attempts = 1
    while (not reply.text or reply.completion_tokens < min_tokens) and attempts <= retries:
        reply = teacher.complete(prompt, max_tokens=max_tokens, temperature=0.8)
        attempts += 1

    key = node_key(pair)
    title, definition, examples = texts["nodes"][key][lang]
    record = Record(
        pair_id=pair.pair_id, split=pair.split, polarity=pair.polarity,
        node_pk=pair.node_pk, family=pair.family, depth=pair.depth,
        is_leaf=pair.is_leaf, scenario_path=pair.scenario_path, lang=lang,
        node_key=key, text=reply.text, completion_tokens=reply.completion_tokens,
        finish_reason=reply.finish_reason, attempts=attempts,
        examples=[e for e in examples if e],
    )
    if not reply.text:
        return record, None, []

    picks: list[Optional[str]] = []
    for _ in range(votes):
        candidates = [key] + pick_distractors(key, list(texts["nodes"]), distractors, rng)
        rng.shuffle(candidates)
        answer = teacher.complete(
            build_choice_question(reply.text, candidates, texts, lang),
            max_tokens=400, temperature=0.0).text
        picks.append(parse_choice(answer, candidates))
    return record, majority(picks, key), picks


# --------------------------------------------------------------------------
# Corpus et rapport
# --------------------------------------------------------------------------

def load_pairs(split: str, phase2_dir: Path = PHASE2_DIR) -> list[B.Pair]:
    """Relit les paires produites par la tranche A, dans l'ordre du CSV."""
    path = Path(phase2_dir) / f"{split}.csv"
    pairs = []
    with open(path, encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle):
            pairs.append(B.Pair(
                pair_id=row["pair_id"], split=row["split"], polarity=row["polarity"],
                node_pk=int(row["node_pk"]), family=row["family"],
                depth=int(row["depth"]), is_leaf=bool(int(row["is_leaf"])),
                scenario_path=row["scenario_path"]))
    return pairs


def stratified_sample(pairs: Sequence[B.Pair], limit: int, rng: random.Random) -> list[B.Pair]:
    """``limit`` paires en round-robin sur les familles, puis par profondeur.

    Un echantillon tire a plat sur-represente les grandes familles ; le
    round-robin garantit que chaque famille est touchee avant qu'une deuxieme
    paire n'en vienne.
    """
    if limit >= len(pairs):
        return list(pairs)
    buckets: dict[str, list[B.Pair]] = {}
    for pair in pairs:
        buckets.setdefault(pair.family, []).append(pair)
    for bucket in buckets.values():
        rng.shuffle(bucket)
    ordered = sorted(buckets)
    sample: list[B.Pair] = []
    index = 0
    while len(sample) < limit:
        family = ordered[index % len(ordered)]
        if buckets[family]:
            sample.append(buckets[family].pop())
        index += 1
        if index > limit * len(ordered) + len(ordered):
            break
    return sample


def summarise(records: Sequence[Record], verdicts: Sequence[Optional[bool]], *,
              min_tokens: int = MIN_COMPLETION_TOKENS) -> dict:
    """Metriques du run. Un verdict ``None`` est compte comme non mesure.

    Deux populations coexistent, et les denominateurs le disent :

    * ``n_pairs`` et ``by_family[<famille>]["n"]`` comptent **toutes** les
      paires, y compris celles dont la generation a echoue (``n_empty``) ;
    * ``mean_completion_tokens`` et ``example_overlap`` ne portent que sur les
      paires **generees** (``n_generated``) : un texte vide n'a pas de longueur
      ni de recouvrement a moyenner, l'inclure comme un zero fausserait les
      deux.

    ``n_below_floor`` compte les paires **generees mais restees sous**
    ``min_tokens`` : le plancher est un declencheur de regeneration, pas une
    garantie, et un run dont les ``retries`` s'epuisent accepte le texte court.
    ``n_empty`` ne les voit pas -- un texte court n'est pas un texte vide --
    donc un rapport qui ne publierait que ``n_empty`` laisserait croire que
    tout ce qui a ete genere respecte le plancher.
    """
    generated = [r for r in records if r.text]
    below_floor = [r for r in generated if r.completion_tokens < min_tokens]
    voted = [v for v in verdicts if v is not None]
    by_family: dict[str, dict[str, int]] = {}
    for record, verdict in zip(records, verdicts):
        cell = by_family.setdefault(record.family, {"n": 0, "hit": 0, "measured": 0})
        cell["n"] += 1
        if verdict is not None:
            cell["measured"] += 1
            cell["hit"] += int(verdict)
    return {
        "n_pairs": len(records),
        "n_generated": len(generated),
        "n_empty": len(records) - len(generated),
        "n_below_floor": len(below_floor),
        "below_floor_pairs": [r.pair_id for r in below_floor],
        "n_regenerated": sum(1 for r in records if r.attempts > 1),
        "mean_completion_tokens": (
            round(sum(r.completion_tokens for r in generated) / len(generated), 1)
            if generated else 0.0),
        "example_overlap": sum(1 for r in generated if r.example_overlap()),
        "roundtrip_measured": len(voted),
        "roundtrip_hits": sum(1 for v in voted if v),
        "roundtrip_rate": (round(sum(1 for v in voted if v) / len(voted), 4) if voted else None),
        "by_family": by_family,
    }


def run(pairs: Sequence[B.Pair], texts: dict, teacher: Teacher, *, lang: str,
        seed: int = 0, votes: int = DEFAULT_VOTES,
        distractors: int = DEFAULT_DISTRACTORS,
        max_tokens: int = DEFAULT_MAX_TOKENS,
        min_tokens: int = MIN_COMPLETION_TOKENS,
        retries: int = DEFAULT_RETRIES,
        checkpoint: Optional[Path] = None,
        progress: Optional[Callable[[int, int], None]] = None,
        stats: Optional[dict] = None) -> tuple[list[Record], list[Optional[bool]]]:
    """Passe chaque paire au maitre, en reprenant depuis ``checkpoint`` si fourni.

    Le checkpoint est ecrit apres **chaque** paire : le run complet des 18 887
    paires dure des heures, une coupure ne doit pas couter le deja-fait.

    La reprise **n'est pas neutre**, et ``stats`` sert a le publier. Le tirage
    des distracteurs consomme ``rng`` dans l'ordre des paires traitees ; une
    reprise repart d'un ``Random(seed)`` neuf et ne rejoue que les paires
    manquantes, donc les distracteurs des paires rejouees different de ceux
    d'un run ininterrompu a ``seed`` egal. Un rapport qui taierait la reprise
    ferait passer deux tirages distincts pour un seul.

    Si ``stats`` est fourni, il est rempli avec ``{"resumed": bool,
    "n_resumed": int, "n_todo": int}`` ; ``n_resumed`` est le nombre de paires
    deja presentes dans le checkpoint, pas le nombre de paires du run.
    """
    records: list[Record] = []
    verdicts: list[Optional[bool]] = []
    done: set[str] = set()
    if checkpoint and Path(checkpoint).exists():
        with open(checkpoint, encoding="utf-8") as handle:
            for line in handle:
                if not line.strip():
                    continue
                row = json.loads(line)
                done.add(row["pair_id"])
                verdicts.append(row.get("roundtrip"))
                records.append(_record_from_row(row))
    todo = [p for p in pairs if p.pair_id not in done]
    if stats is not None:
        stats["resumed"] = bool(records)
        stats["n_resumed"] = len(records)
        stats["n_todo"] = len(todo)
    rng = random.Random(seed)
    handle = open(checkpoint, "a", encoding="utf-8") if checkpoint else None
    try:
        for index, pair in enumerate(todo, start=1):
            record, verdict, _picks = generate_one(
                pair, texts, teacher, lang=lang, rng=rng, votes=votes,
                distractors=distractors, max_tokens=max_tokens,
                min_tokens=min_tokens, retries=retries)
            records.append(record)
            verdicts.append(verdict)
            if handle:
                handle.write(json.dumps(
                    {**asdict(record), "roundtrip": verdict,
                     "example_overlap": record.example_overlap()}, ensure_ascii=False) + "\n")
                handle.flush()
            if progress:
                progress(index, len(todo))
    finally:
        if handle:
            handle.close()
    return records, verdicts


def _record_from_row(row: dict) -> Record:
    return Record(**{k: v for k, v in row.items()
                     if k in Record.__dataclass_fields__})


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--split", default="val", choices=list(B.SPLITS))
    parser.add_argument("--lang", default="fr", choices=list(B.LANGS))
    parser.add_argument("--limit", type=int, default=0, help="0 = toutes les paires du split")
    parser.add_argument("--votes", type=int, default=DEFAULT_VOTES)
    parser.add_argument("--distractors", type=int, default=DEFAULT_DISTRACTORS)
    parser.add_argument("--max-tokens", type=int, default=DEFAULT_MAX_TOKENS)
    parser.add_argument("--min-tokens", type=int, default=MIN_COMPLETION_TOKENS)
    parser.add_argument("--retries", type=int, default=DEFAULT_RETRIES)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--hub-url", default=DEFAULT_HUB_URL)
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--phase2-dir", type=Path, default=PHASE2_DIR)
    args = parser.parse_args(argv)

    texts = B.load_texts()
    pairs = load_pairs(args.split, args.phase2_dir)
    if args.limit:
        pairs = stratified_sample(pairs, args.limit, random.Random(args.seed))
    args.out.mkdir(parents=True, exist_ok=True)
    checkpoint = args.out / f"{args.split}_{args.lang}.jsonl"

    teacher = HubTeacher(url=args.hub_url, model=args.model)
    started = time.time()

    def progress(done: int, total: int) -> None:
        if done % 10 == 0 or done == total:
            print(f"  {done}/{total} ({time.time() - started:.0f}s)", flush=True)

    resume: dict = {}
    records, verdicts = run(
        pairs, texts, teacher, lang=args.lang, seed=args.seed, votes=args.votes,
        distractors=args.distractors, max_tokens=args.max_tokens,
        min_tokens=args.min_tokens, retries=args.retries,
        checkpoint=checkpoint, progress=progress, stats=resume)

    report = {
        "model": args.model, "hub_url": args.hub_url, "split": args.split,
        "lang": args.lang, "seed": args.seed, "votes": args.votes,
        "distractors": args.distractors, "max_tokens": args.max_tokens,
        "min_tokens": args.min_tokens, "retries": args.retries,
        "checkpoint": checkpoint.name,
        "seconds": round(time.time() - started, 1),
        **resume,
        **summarise(records, verdicts, min_tokens=args.min_tokens),
    }
    report_path = args.out / f"report_{args.split}_{args.lang}.json"
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n",
                           encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("by_family", "below_floor_pairs")},
                     indent=2, ensure_ascii=False))
    if report["n_below_floor"]:
        print(f"  {report['n_below_floor']} paire(s) generee(s) sous le plancher "
              f"de {args.min_tokens} tokens -- liste dans {report_path.name}")
    print(f"corpus  : {checkpoint}")
    print(f"rapport : {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
