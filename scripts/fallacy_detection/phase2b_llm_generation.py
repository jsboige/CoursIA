#!/usr/bin/env python3
"""Tranche B (#17578) : generation du texte par LLM enseignant + controle aller-retour.

La tranche A (#17582) a produit un index de paires (scenario, noeud) et le rendu
des prompts. Cette tranche execute l'etape suivante du mandat :

  1. **Generation** -- un LLM Qwen3.6 ecrit, pour chaque paire echantillonnee,
     les 2 a 4 phrases demandees par ``render_prompt`` (le noeud n'y est decrit
     que par titre + definition : anti-circularite par construction).
  2. **Controle aller-retour** -- le meme modele doit reclasser le texte genere
     sur son noeud, parmi K candidats de la meme famille (le vrai + K-1
     distracteurs). Mesure : hit@1 noeud, hit famille.
  3. **Recouvrement ``example_*``** -- Jaccard sur 8-grammes de mots entre le
     texte genere et les exemples du noeud : la generation ne doit pas recopier
     le corpus.

Le jeu genere vit HORS du depot (chemin passe par ``--out``, cite dans la PR) ;
seules les metriques agregees et un manifeste entrent dans le depot.

Moteurs (``--engine``) :

  - ``qwen-cloud``  : Qwen3.6 heberge (endpoint compatible OpenAI, cle
                      ``QWEN_API_KEY`` + ``QWEN_OPENAI_BASE_URL``). Utilise pour
                      le pilote : la cle du vLLM LAN n'est pas provisionnee sur
                      la lane (cf corps de la PR).
  - ``vllm-lan``    : Qwen3.6-35b-a3b auto-heberge (``VLLM_LAN_BASE_URL`` /
                      ``VLLM_LAN_API_KEY``), cible de la pleine echelle -- la
                      spec #17578 demande l'auto-heberge.

Les deux moteurs recoivent ``enable_thinking`` desactive : un modele de
raisonnement consomme sinon l'integralite de ``max_tokens`` en reflexion interne
et rend un contenu vide (mesure c.634, PR #7868).

Reprise : chaque appel est appendu en JSONL ; ``--resume`` saute les pair_id
deja presents. Aucun appel n'est rejoue deux fois.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
import time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))

from cartesian_dataset_builder import (  # noqa: E402
    Pair,
    load_texts,
    render_prompt,
)

DEFAULT_VAL_CSV = REPO / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/phase2/val.csv"

ENGINES = {
    "qwen-cloud": {
        "base_url_env": "QWEN_OPENAI_BASE_URL",
        "key_env": "QWEN_API_KEY",
        "default_base": "https://token-plan.ap-southeast-1.maas.aliyuncs.com/compatible-mode/v1",
        "default_model": "qwen3.6-flash",
        "extra_body": {"enable_thinking": False},
    },
    "vllm-lan": {
        "base_url_env": "VLLM_LAN_BASE_URL",
        "key_env": "VLLM_LAN_API_KEY",
        "default_base": "http://192.168.0.47:5002/v1",
        "default_model": "qwen3.6-35b-a3b",
        "extra_body": {"chat_template_kwargs": {"enable_thinking": False}},
    },
}

RETRY_STATUS = {401, 429, 500, 502, 503, 504}
WORD_RE = re.compile(r"[^\W\d_]+", re.UNICODE)


# ---------------------------------------------------------------------------
# Echantillon stratifie
# ---------------------------------------------------------------------------

def load_pairs(val_csv: Path) -> list[Pair]:
    """Relit l'index de paires commite par la tranche A."""
    import csv

    pairs = []
    with open(val_csv, encoding="utf-8", newline="") as f:
        for r in csv.DictReader(f):
            pairs.append(Pair(
                pair_id=r["pair_id"], split=r["split"], polarity=r["polarity"],
                node_pk=int(r["node_pk"]), family=r["family"], depth=int(r["depth"]),
                is_leaf=r["is_leaf"] == "True", scenario_path=r["scenario_path"],
            ))
    return pairs


def stratified_sample(pairs: list[Pair], n: int, seed: int = 0) -> list[Pair]:
    """``n`` paires proportionnelles aux strates (polarite, famille), tirage determine.

    Chaque strate contribue ``pro rata`` de sa taille (au moins 1 si la strate
    existe et que n le permet) ; l'ordre de sortie est trié par pair_id pour
    que deux executions donnent le meme echantillon.
    """
    strata: dict[tuple[str, str], list[Pair]] = defaultdict(list)
    for p in pairs:
        strata[(p.polarity, p.family)].append(p)
    rng = random.Random(seed)
    total = len(pairs)
    picked: list[Pair] = []
    for key in sorted(strata):
        k = max(1, round(n * len(strata[key]) / total)) if len(strata[key]) else 0
        picked.extend(rng.sample(strata[key], min(k, len(strata[key]))))
    if len(picked) > n:  # arrondis favorables : on rogne les strates les plus larges
        by_size = sorted(strata, key=lambda k: -len(strata[k]))
        i = 0
        while len(picked) > n:
            key = by_size[i % len(by_size)]
            victim = next((p for p in picked if (p.polarity, p.family) == key), None)
            if victim is not None:
                picked.remove(victim)
            i += 1
    return sorted(picked, key=lambda p: p.pair_id)


# ---------------------------------------------------------------------------
# Controle aller-retour : candidats et prompt de reclassement
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CandidateSet:
    """Vrai noeud + distracteurs de la meme famille, tirage determine par pair_id."""

    pair_id: str
    true_key: str
    keys: tuple[str, ...]  # ordre de presentation ; true_key en fait partie

    @property
    def true_index(self) -> int:
        return self.keys.index(self.true_key)


def candidate_set(pair: Pair, keys_by_family: dict[tuple[str, str], list[str]],
                  k: int = 16, seed: int = 0) -> CandidateSet:
    pool = [c for c in keys_by_family[(pair.polarity, pair.family)]
            if c != _node_key(pair)]
    rng = random.Random(f"{seed}:{pair.pair_id}")
    distractors = sorted(rng.sample(pool, min(k - 1, len(pool))))
    keys = list(distractors)
    pos = rng.randrange(len(keys) + 1)
    keys.insert(pos, _node_key(pair))
    return CandidateSet(pair_id=pair.pair_id, true_key=_node_key(pair), keys=tuple(keys))


def _node_key(pair: Pair) -> str:
    return ("F" if pair.polarity == "fallacy" else "V") + str(pair.node_pk)


def roundtrip_prompt(text: str, keys: tuple[str, ...], texts: dict, lang: str) -> str:
    """Consigne de reclassement : le texte + K candidats (titre, definition)."""
    lines = [f"{i + 1}. {_label(key, texts, lang)}" for i, key in enumerate(keys)]
    return (
        "You are labelling an argumentative move. Which single item below does the "
        f"TEXT exemplify? Answer with the item number only.\n\nTEXT (in {lang}):\n{text}\n\n"
        "ITEMS:\n" + "\n".join(lines)
    )


def _label(key: str, texts: dict, lang: str) -> str:
    title, definition, _ = texts["nodes"][key][lang]
    return f"{title} -- {definition}" if definition else title


# ---------------------------------------------------------------------------
# Recouvrement example_*
# ---------------------------------------------------------------------------

def _ngrams(text: str, n: int = 8) -> set[tuple[str, ...]]:
    words = WORD_RE.findall(text.lower())
    return {tuple(words[i:i + n]) for i in range(len(words) - n + 1)}


def example_overlap(text: str, key: str, texts: dict, lang: str, n: int = 8) -> float:
    """Jaccard max entre le texte genere et les exemples du noeud (0 si vide)."""
    a = _ngrams(text, n)
    if not a:
        return 0.0
    best = 0.0
    for ex in texts["nodes"][key][lang][2]:
        b = _ngrams(ex, n)
        if b:
            best = max(best, len(a & b) / len(a | b))
    return best


# ---------------------------------------------------------------------------
# Client LLM
# ---------------------------------------------------------------------------

class LLMClient:
    """Enveloppe retry/backoff autour du SDK OpenAI, moteur-agnostique."""

    def __init__(self, engine: str, model: str | None = None, timeout: float = 60.0):
        from openai import OpenAI  # import tardif : les tests n'ont pas besoin du SDK
        cfg = ENGINES[engine]
        base = os.getenv(cfg["base_url_env"], cfg["default_base"])
        key = os.getenv(cfg["key_env"])
        if not key:
            raise SystemExit(f"cle absente : exportez {cfg['key_env']} (jamais de valeur par defaut)")
        self._client = OpenAI(base_url=base, api_key=key, timeout=timeout)
        self.model = model or cfg["default_model"]
        self.extra_body = dict(cfg["extra_body"])

    def chat(self, prompt: str, *, max_tokens: int, temperature: float) -> str:
        delay = 2.0
        for attempt in range(6):
            try:
                r = self._client.chat.completions.create(
                    model=self.model,
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=max_tokens, temperature=temperature,
                    extra_body=self.extra_body,
                )
                return (r.choices[0].message.content or "").strip()
            except Exception as e:  # 401/429/5xx et timeouts : le hub flappe sous charge
                status = getattr(getattr(e, "response", None), "status_code", None)
                if attempt == 5 or (status is not None and status not in RETRY_STATUS
                                    and "timeout" not in str(e).lower()):
                    raise
                time.sleep(delay)
                delay = min(delay * 2, 30.0)
        raise RuntimeError("inatteignable")


# ---------------------------------------------------------------------------
# Execution
# ---------------------------------------------------------------------------

def run(sample: list[Pair], texts: dict, lang: str, client: LLMClient | None,
        out_dir: Path, k: int, workers: int, resume: bool) -> dict:
    keys_by_family: dict[tuple[str, str], list[str]] = defaultdict(list)
    for key, per_lang in texts["nodes"].items():
        polarity = "fallacy" if key.startswith("F") else "virtue"
        family = _family_of(key, texts)
        keys_by_family[(polarity, family)].append(key)

    gen_path = out_dir / "generation.jsonl"
    rt_path = out_dir / "roundtrip.jsonl"
    done_gen: set[str] = set()
    if resume and gen_path.exists():
        done_gen = {json.loads(l)["pair_id"] for l in gen_path.read_text(encoding="utf-8").splitlines() if l.strip()}
    todo = [p for p in sample if p.pair_id not in done_gen]
    out_dir.mkdir(parents=True, exist_ok=True)

    def one(p: Pair) -> dict:
        prompt = render_prompt(p, texts, lang)
        cs = candidate_set(p, keys_by_family, k=k)
        text = client.chat(prompt, max_tokens=300, temperature=0.7)
        return {"pair_id": p.pair_id, "polarity": p.polarity, "family": p.family,
                "depth": p.depth, "lang": lang, "node_key": cs.true_key,
                "prompt_chars": len(prompt), "generated": text,
                "overlap": round(example_overlap(text, cs.true_key, texts, lang), 4)}

    gen_f = gen_path.open("a", encoding="utf-8")
    if client is not None and todo:
        with ThreadPoolExecutor(max_workers=workers) as ex:
            futs = {ex.submit(one, p): p for p in todo}
            for i, fut in enumerate(as_completed(futs), 1):
                rec = fut.result()
                gen_f.write(json.dumps(rec, ensure_ascii=False) + "\n")
                if i % 20 == 0:
                    gen_f.flush()
    gen_f.close()

    # Controle aller-retour sur TOUT l'echantillon present.
    records = [json.loads(l) for l in gen_path.read_text(encoding="utf-8").splitlines() if l.strip()]
    done_rt: set[str] = set()
    if resume and rt_path.exists():
        done_rt = {json.loads(l)["pair_id"] for l in rt_path.read_text(encoding="utf-8").splitlines() if l.strip()}
    rt_f = rt_path.open("a", encoding="utf-8")
    by_id = {p.pair_id: p for p in sample}
    for rec in records:
        p = by_id[rec["pair_id"]]
        if rec["pair_id"] in done_rt or client is None:
            continue
        cs = candidate_set(p, keys_by_family, k=k)
        rp = roundtrip_prompt(rec["generated"], cs.keys, texts, lang)
        ans = client.chat(rp, max_tokens=8, temperature=0.0)
        m = re.search(r"\d+", ans)
        guess = int(m.group()) if m else -1
        rt_f.write(json.dumps({
            "pair_id": rec["pair_id"], "true_index": cs.true_index, "guess": guess,
            "node_hit": guess == cs.true_index,
            "n_candidates": len(cs.keys), "answer_raw": ans[:24],
        }, ensure_ascii=False) + "\n")
    rt_f.close()
    return aggregate(records, rt_path)


def _family_of(key: str, texts: dict) -> str:
    """Famille du noeud depuis ``texts`` (le CSV de paires la porte aussi)."""
    return _FAMILY_CACHE.get(key, "")


_FAMILY_CACHE: dict[str, str] = {}


def prime_family_cache(pairs: list[Pair]) -> None:
    for p in pairs:
        _FAMILY_CACHE[_node_key(p)] = p.family


def aggregate(records: list[dict], rt_path: Path) -> dict:
    rts = {json.loads(l)["pair_id"]: json.loads(l)
           for l in rt_path.read_text(encoding="utf-8").splitlines() if l.strip()}
    n = len(records)
    empty = sum(1 for r in records if not r["generated"].strip())
    node_hits = sum(1 for r in records if rts.get(r["pair_id"], {}).get("node_hit"))
    overlaps = sorted(r["overlap"] for r in records)
    by_pol: dict[str, Counter] = defaultdict(Counter)
    for r in records:
        hit = bool(rts.get(r["pair_id"], {}).get("node_hit"))
        by_pol[r["polarity"]]["n"] += 1
        by_pol[r["polarity"]]["hits"] += hit
    by_fam: dict[str, Counter] = defaultdict(Counter)
    for r in records:
        hit = bool(rts.get(r["pair_id"], {}).get("node_hit"))
        by_fam[(r["polarity"], r["family"])]["n"] += 1
        by_fam[(r["polarity"], r["family"])]["hits"] += hit
    q = lambda arr, p: arr[min(len(arr) - 1, int(p * len(arr)))] if arr else 0.0  # noqa: E731
    return {
        "n": n, "n_roundtrip": len(rts), "empty_generations": empty,
        "node_hit_at_1": round(node_hits / n, 4) if n else None,
        "overlap_mean": round(sum(overlaps) / n, 4) if n else None,
        "overlap_p95": round(q(overlaps, 0.95), 4) if n else None,
        "by_polarity": {k: {"n": v["n"], "hit_rate": round(v["hits"] / v["n"], 4)}
                        for k, v in by_pol.items()},
        "by_family": {f"{k[0][0]}:{k[1]}": {"n": v["n"], "hit_rate": round(v["hits"] / v["n"], 4)}
                      for k, v in sorted(by_fam.items())},
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--engine", choices=sorted(ENGINES), default="qwen-cloud")
    ap.add_argument("--model")
    ap.add_argument("--split-csv", type=Path, default=DEFAULT_VAL_CSV)
    ap.add_argument("--sample", type=int, default=240)
    ap.add_argument("--lang", default="fr")
    ap.add_argument("--k", type=int, default=16)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--out", type=Path, required=True, help="repertoire hors depot du jeu genere")
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--dry-run", action="store_true",
                    help="rend prompts et candidats, n'appelle aucun moteur")
    args = ap.parse_args(argv)

    pairs = load_pairs(args.split_csv)
    prime_family_cache(pairs)
    sample = stratified_sample(pairs, args.sample, args.seed)
    texts = load_texts()

    if args.dry_run:
        keys_by_family: dict[tuple[str, str], list[str]] = defaultdict(list)
        for key in texts["nodes"]:
            polarity = "fallacy" if key.startswith("F") else "virtue"
            fam = next((p.family for p in pairs if _node_key(p) == key), None)
            if fam:
                keys_by_family[(polarity, fam)].append(key)
        for p in sample[:3]:
            cs = candidate_set(p, keys_by_family, args.k)
            print(f"--- {p.pair_id} ({p.polarity}/{p.family}) ---")
            print(render_prompt(p, texts, args.lang))
            print(f"[{len(cs.keys)} candidats, vrai en position {cs.true_index + 1}]")
        print(f"dry-run OK : {len(sample)} paires echantillonnees sur {len(pairs)}")
        return 0

    client = LLMClient(args.engine, args.model)
    metrics = run(sample, texts, args.lang, client, args.out, args.k, args.workers, args.resume)
    manifest = {
        "engine": args.engine, "model": client.model, "lang": args.lang,
        "k_candidates": args.k, "sample": args.sample, "seed": args.seed,
        "split_csv": args.split_csv.name, "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "metrics": metrics,
    }
    (args.out / "metrics.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=1), encoding="utf-8")
    print(json.dumps(manifest, ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
