#!/usr/bin/env python3
"""Accord inter-familles de juges sur le corpus val FR (EPIC #10355, section 2a).

Le seul critere d'etiquette du corpus synthetique aujourd'hui est l'auto-accord
du **generateur** (0,8679, ``report_val_fr.json``) : la meme famille de modeles
(Qwen) qui a produit le texte repond au questionnaire, avec la definition de
l'etiquette visible dans la question. La revue EPITA du 2026-10-22 (c.6344505010)
pose que cet accord ne prouve rien tout seul et demande un juge **d'une autre
famille** : « un accord inter-familles de modeles sur environ 200 paires, avec
intervalle de confiance ».

Cet organe mesure cet accord, sans generer quoi que ce soit :

1. **Tirage apparie** a graine fixe d'environ ``n`` paires sur les 280 du split
   val committé (``val_fr.jsonl``), stratifie proportionnellement par famille.
2. **Le meme questionnaire** que le controle aller-retour du generateur : le
   noeud cible + 5 distracteurs de meme polarite, cadre FR octet pour octet
   identique (reutilisation de ``pick_distractors``, ``build_choice_question``,
   ``parse_choice`` — les organes existants, pas une copie).
3. **Des juges externes** de familles distinctes du generateur et entre elles,
   servis par des endpoints compatibles OpenAI. Le client est **injecte**
   (``Teacher``) : les tests tournent sans reseau.
4. **Contraste gratuit avec l'auto-accord** : le verdict aller-retour du
   generateur vit deja par paire dans le corpus committé (champ ``roundtrip``)
   — le taux restreint au meme sous-ensemble se calcule sans aucun appel.

Reponse non parsable = ``None`` = **non mesure**, jamais un vote rate
(convention de ``parse_choice``). Le taux d'accord porte un intervalle de
confiance Wilson 95 %.

Le rapport JSON est fonde sur un checkpoint rejouable : un run interrompu
reprend ou il etait, et le questionnaire reconstruit est identique parce que
tirage et questions sont des fonctions pures de ``(corpus, n, seed)``. Le
checkpoint est un artefact de run, non committe ; ``--report-only`` le lit
quand il est la (un run **partiel** ne s'efface jamais derriere un rapport
publie), et sinon le rapport committé, qui porte les memes picks dans
``per_pair`` — la relecture marche donc aussi sur un clone frais, sans cle.

Usage::

    python -m fallacy_detection.judge_family_agreement --judges openai,openrouter
    python -m fallacy_detection.judge_family_agreement --probe   # un appel par juge, aucune mesure
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Optional, Protocol, Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fallacy_detection import generate_teacher_corpus as G  # noqa: E402

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = G.DEFAULT_OUT
DEFAULT_CORPUS = DEFAULT_OUT / "val_fr.jsonl"
DEFAULT_SEED = 42
DEFAULT_N_PAIRS = 200
Z_95 = 1.959963984540054  # quantile 0,975 normal : IC bilateral a 95 %

# Catalogue des juges externes : famille declarante, endpoint compatible
# OpenAI, modele par defaut, variable d'environnement portant la cle. La cle ne
# vit JAMAIS en litteral ici (hygiene des secrets) : absente => ``ValueError``.
JUDGE_SPECS: dict[str, dict] = {
    "openai": {
        "family": "GPT (OpenAI)",
        "url": "https://api.openai.com/v1/chat/completions",
        "model": "gpt-4o-mini",
        "api_key_env": "OPENAI_API_KEY",
    },
    "openrouter": {
        "family": "Mistral (OpenRouter)",
        "url": "https://openrouter.ai/api/v1/chat/completions",
        "model": "mistralai/mistral-small-24b-instruct-2501",
        "api_key_env": "OPENROUTER_API_KEY",
    },
}


# --------------------------------------------------------------------------
# Client juge (injectable, sans dialecte vLLM)
# --------------------------------------------------------------------------

class Teacher(Protocol):
    """Meme interface minimale que le generateur : un appel de completion."""

    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> G.Reply:
        """Rend une completion pour ``prompt``."""


class OpenAIJudge:
    """Client d'un endpoint compatible OpenAI, hors dialecte vLLM.

    Contrairement au ``HubTeacher`` du generateur, aucun
    ``chat_template_kwargs`` n'est envoye : ce parametre est compris du vLLM
    maison mais **rejete** par les API publiques (400 unknown parameter). Le
    dialecte thinking reste localise dans le generateur, ou sa docstring le
    place.
    """

    def __init__(self, name: str, url: str, model: str, api_key_env: str,
                 api_key: Optional[str] = None, timeout: float = 120.0,
                 sleep: Callable[[float], None] = time.sleep):
        self.name = name
        self.url = url
        self.model = model
        self.api_key = api_key if api_key is not None else os.getenv(api_key_env)
        if not self.api_key:
            raise ValueError(
                f"{api_key_env} absente de l'environnement : le module ne pose aucun "
                "repli litteral (hygiene des secrets).")
        self.timeout = timeout
        self._sleep = sleep

    def complete(self, prompt: str, *, max_tokens: int = 400,
                 temperature: float = 0.0) -> G.Reply:
        body = json.dumps({
            "model": self.model,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": temperature,
            "max_tokens": max_tokens,
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
            except urllib.error.HTTPError as exc:
                # Un 4xx du serveur ne se retry pas : la requete est mal forme
                # ou la cle refusee, reessayer paie le meme echec.
                detail = exc.read().decode("utf-8", "replace")[:300]
                raise RuntimeError(f"HTTP {exc.code} de {self.name}: {detail}") from exc
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
        return G.Reply(
            text=(message.get("content") or "").strip(),
            completion_tokens=int(usage.get("completion_tokens") or 0),
            finish_reason=str(choice.get("finish_reason") or ""),
        )


# --------------------------------------------------------------------------
# Tirage apparie et questionnaire
# --------------------------------------------------------------------------

def load_corpus(path: Path = DEFAULT_CORPUS) -> list[dict]:
    """Lit le split val committé ; une ligne = une paire {pair_id, node_key, ...}."""
    records = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                records.append(json.loads(line))
    if not records:
        raise ValueError(f"corpus vide : {path}")
    return records


def draw_pairs(records: Sequence[dict], n: int, seed: int) -> list[dict]:
    """Tirage stratifie proportionnel par famille, ordre final par ``pair_id``.

    La stratification par famille rend les taux par famille interpretables
    (une paire de chaque famille a la meme chance d'etre tiree que son poids
    dans le corpus) ; l'ordre final trié rend le tirage rejouable independamment
    de l'ordre des lignes du fichier.
    """
    rng = random.Random(seed)
    by_family: dict[str, list[dict]] = {}
    for record in records:
        by_family.setdefault(record["family"], []).append(record)
    quotas: dict[str, int] = {}
    restes: list[tuple[float, str]] = []
    for family, members in by_family.items():
        exact = n * len(members) / len(records)
        quotas[family] = int(exact)
        restes.append((exact - quotas[family], family))
    # Plus grands restes : on distribue le solde aux familles les plus proches
    # de leur arrondi superieur, tirage aleatoire départage les egalites.
    rng.shuffle(restes)
    for _, family in sorted(restes, key=lambda item: -item[0])[:n - sum(quotas.values())]:
        quotas[family] += 1
    drawn: list[dict] = []
    for family, members in sorted(by_family.items()):
        drawn += rng.sample(members, quotas[family])
    drawn.sort(key=lambda record: record["pair_id"])
    return drawn


@dataclass(frozen=True)
class Question:
    """Une question de reclassement prete a poser : deterministe par paire."""

    pair_id: str
    target: str
    question: str
    candidates: tuple[str, ...]


def build_questions(drawn: Sequence[dict], texts: dict, seed: int,
                    distractors: int = G.DEFAULT_DISTRACTORS,
                    lang: str = "fr") -> list[Question]:
    """Construit le questionnaire de chaque paire tiree.

    Meme consommation de rng que le generateur : un tirage de distracteurs puis
    un shuffle des candidats, par paire, dans l'ordre du tirage (trié par
    ``pair_id``). Une execution reprise reconstruit les memes questions.
    """
    rng = random.Random(seed)
    keys = list(texts["nodes"])
    questions: list[Question] = []
    for record in drawn:
        key = record["node_key"]
        candidates = [key] + list(G.pick_distractors(key, keys, distractors, rng))
        rng.shuffle(candidates)
        questions.append(Question(
            pair_id=record["pair_id"], target=key,
            question=G.build_choice_question(record["text"], candidates, texts, lang),
            candidates=tuple(candidates),
        ))
    return questions


# --------------------------------------------------------------------------
# Agregation
# --------------------------------------------------------------------------

def wilson_ci(hits: int, measured: int, z: float = Z_95) -> Optional[tuple[float, float]]:
    """Intervalle de confiance Wilson 95 % sur une proportion.

    ``None`` quand rien n'est mesure (convention « non mesure », jamais 0/0
    qui serait un taux nul affirme).
    """
    if measured <= 0:
        return None
    p = hits / measured
    z2 = z * z
    denom = 1 + z2 / measured
    center = (p + z2 / (2 * measured)) / denom
    half = z * math.sqrt(p * (1 - p) / measured + z2 / (4 * measured * measured)) / denom
    return (max(0.0, center - half), min(1.0, center + half))


def summarise_picks(picks: Sequence[Optional[str]], targets: Sequence[str],
                    families: Sequence[str]) -> dict:
    """Taux d'accord global et par famille, avec IC Wilson et non-mesures."""
    hits = sum(1 for pick, target in zip(picks, targets) if pick == target)
    measured = sum(1 for pick in picks if pick is not None)
    ci = wilson_ci(hits, measured)
    by_family: dict[str, dict] = {}
    for pick, target, family in zip(picks, targets, families):
        bucket = by_family.setdefault(family, {"n": 0, "measured": 0, "hits": 0})
        bucket["n"] += 1
        if pick is not None:
            bucket["measured"] += 1
            bucket["hits"] += 1 if pick == target else 0
    for bucket in by_family.values():
        family_ci = wilson_ci(bucket["hits"], bucket["measured"])
        bucket["rate"] = (bucket["hits"] / bucket["measured"]) if bucket["measured"] else None
        bucket["ci95"] = list(family_ci) if family_ci else None
    return {
        "n_pairs": len(picks),
        "n_measured": measured,
        "n_unparsed": len(picks) - measured,
        "hits": hits,
        "rate": (hits / measured) if measured else None,
        "ci95_wilson": list(ci) if ci else None,
        "by_family": by_family,
    }


def auto_accord_subset(drawn: Sequence[dict]) -> dict:
    """Taux d'auto-accord du generateur restreint au sous-ensemble tire.

    Le champ ``roundtrip`` vit par paire dans le corpus committé : ce contraste
    ne coute aucun appel. C'est la colonne « meme famille, definition visible »
    face a laquelle lire les juges externes.
    """
    verdicts = [record.get("roundtrip") for record in drawn]
    measured = [v for v in verdicts if v is not None]
    hits = sum(1 for v in measured if v is True)
    ci = wilson_ci(hits, len(measured))
    return {
        "n_pairs": len(drawn),
        "n_measured": len(measured),
        "hits": hits,
        "rate": (hits / len(measured)) if measured else None,
        "ci95_wilson": list(ci) if ci else None,
    }


# --------------------------------------------------------------------------
# Checkpoint et rapport
# --------------------------------------------------------------------------

def sha256_file(path: Path) -> str:
    # Empreinte des octets LF : le depot stocke ces fichiers texte en LF
    # (core.autocrlf normalise a l'ajout), mais un checkout Windows les
    # materialise en CRLF. Hacher le contenu normalise LF rend l'empreinte
    # citée dans le md vérifiable depuis n'importe quel clone, quel que soit
    # le stockage de travail du siège.
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk.replace(b"\r\n", b"\n"))
    return h.hexdigest()


def load_checkpoint(path: Path) -> dict[tuple[str, str], dict]:
    done: dict[tuple[str, str], dict] = {}
    if not path.exists():
        return done
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            done[(row["judge"], row["pair_id"])] = row
    return done


def load_picks_for_report(out_dir: Path,
                          judges: Sequence[str]) -> dict[str, dict[str, Optional[str]]]:
    """Source de picks pour le rapport : checkpoint local, sinon le rapport
    publie.

    Le checkpoint est un artefact de run, non committé (comme celui du
    générateur) ; le rapport ``judge_family_agreement.json``, lui, est committé
    et porte chaque pick dans ``per_pair``. ``--report-only`` lit le checkpoint
    quand il est là (y compris un run **partiel**, jamais un rapport publié
    différent), et sinon le rapport publié — même source, deux emballages.
    """
    picks_by_judge: dict[str, dict[str, Optional[str]]] = {name: {} for name in judges}
    checkpoint = out_dir / "judge_family_agreement.checkpoint.jsonl"
    if checkpoint.exists():
        for (judge_name, pair_id), row in load_checkpoint(checkpoint).items():
            if judge_name in picks_by_judge:
                picks_by_judge[judge_name][pair_id] = row["pick"]
        return picks_by_judge
    report_path = out_dir / "judge_family_agreement.json"
    if not report_path.exists():
        raise FileNotFoundError(
            f"--report-only : ni {checkpoint} ni {report_path} — rien a rejouer.")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    for entry in report["per_pair"]:
        for name, pick in entry["picks"].items():
            if name in picks_by_judge:
                picks_by_judge[name][entry["pair_id"]] = pick
    return picks_by_judge


def run_measurement(judges: dict[str, Teacher], questions: Sequence[Question],
                    out_dir: Path,
                    sleep: Callable[[float], None] = time.sleep) -> dict[str, dict[str, Optional[str]]]:
    """Pose chaque question a chaque juge, checkpoint en ligne apres chaque appel.

    Rend ``{judge: {pair_id: pick}}`` — merge du checkpoint existant et des
    nouveaux appels. Un juge muet sur une paire (erreur reseau non rattrapee)
    reste absent de la map : « non mesure », jamais un vote.
    """
    checkpoint_path = out_dir / "judge_family_agreement.checkpoint.jsonl"
    done = load_checkpoint(checkpoint_path)
    picks: dict[str, dict[str, Optional[str]]] = {
        name: {} for name in judges}
    for (judge_name, pair_id), row in done.items():
        if judge_name in picks:
            picks[judge_name][pair_id] = row["pick"]
    with open(checkpoint_path, "a", encoding="utf-8") as sink:
        for judge_name, judge in judges.items():
            for question in questions:
                if question.pair_id in picks[judge_name]:
                    continue
                reply = judge.complete(question.question, max_tokens=400, temperature=0.0)
                pick = G.parse_choice(reply.text, question.candidates)
                picks[judge_name][question.pair_id] = pick
                sink.write(json.dumps({
                    "judge": judge_name, "pair_id": question.pair_id,
                    "pick": pick, "target": question.target,
                    "completion_tokens": reply.completion_tokens,
                    "finish_reason": reply.finish_reason,
                }, ensure_ascii=False) + "\n")
                sink.flush()
                sleep(0.2)
    return picks


def write_report(out_dir: Path, judges_meta: Sequence[dict],
                 picks: dict[str, dict[str, Optional[str]]],
                 questions: Sequence[Question], drawn: Sequence[dict],
                 corpus_path: Path, params: dict) -> tuple[Path, Path]:
    """Ecrit ``judge_family_agreement.json`` puis son rendu ``.md``.

    Le SHA-256 du JSON ne peut pas vivre dans le JSON lui-meme : il est pose
    dans le rendu markdown, avec celui du corpus d'entree.
    """
    targets = {q.pair_id: q.target for q in questions}
    families = {record["pair_id"]: record["family"] for record in drawn}
    roundtrips = {record["pair_id"]: record.get("roundtrip") for record in drawn}
    pair_ids = [q.pair_id for q in questions]
    report = {
        "schema": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "what": "Accord inter-familles de juges sur le split val FR (section 2a de la revue EPITA, c.6344505010)",
        "corpus": {
            "path": str(corpus_path.relative_to(_REPO_ROOT)).replace("\\", "/"),
            "sha256": sha256_file(corpus_path),
            "n_total": _count_lines(corpus_path),
        },
        "params": params,
        "draw": {
            "pair_ids": pair_ids,
            "family_counts": {family: sum(1 for r in drawn if r["family"] == family)
                              for family in sorted({r["family"] for r in drawn})},
            "polarity_counts": {pol: sum(1 for r in drawn if r["polarity"] == pol)
                                for pol in sorted({r["polarity"] for r in drawn})},
        },
        "judges": [],
        "generator_auto_accord_subset": auto_accord_subset(drawn),
        "per_pair": [
            {"pair_id": pid, "target": targets[pid],
             "family": families[pid],
             "roundtrip": roundtrips[pid],
             "picks": {name: picks[name].get(pid) for name in picks}}
            for pid in pair_ids
        ],
    }
    for meta in judges_meta:
        judge_picks = [picks[meta["name"]].get(pid) for pid in pair_ids]
        summary = summarise_picks(
            judge_picks, [targets[pid] for pid in pair_ids],
            [families[pid] for pid in pair_ids])
        report["judges"].append({**meta, **summary})
    json_path = out_dir / "judge_family_agreement.json"
    # newline="\n" : octets disque == octets du blob git (LF canonique du
    # depot), pour que l'empreinte citee dans le md survive au commit sous
    # core.autocrlf=true (Windows ecrit CRLF par defaut via write_text).
    json_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n",
                         encoding="utf-8", newline="\n")
    md_path = out_dir / "judge_family_agreement.md"
    md_path.write_text(render_markdown(report, json_path), encoding="utf-8")
    return json_path, md_path


def render_markdown(report: dict, json_path: Path) -> str:
    corpus = report["corpus"]
    auto = report["generator_auto_accord_subset"]
    lines = [
        "# Accord inter-familles de juges — split val FR",
        "",
        f"Ce que mesure ce rapport : la section 2a de la revue EPITA (c.6344505010) —",
        f"un juge **d'une autre famille** que le generateur reclasse-t-il les {len(report['draw']['pair_ids'])} paires tirees ?",
        "",
        "## Parametres",
        "",
        f"- corpus : `{corpus['path']}` ({corpus['n_total']} paires, SHA-256 `{corpus['sha256']}`)",
        f"- tirage : graine {report['params']['seed']}, {report['params']['n_pairs']} paires, "
        f"stratifie par famille ({report['draw']['family_counts']})",
        f"- questionnaire : {report['params']['distractors']} distracteurs de meme polarite, "
        f"cadre FR du controle aller-retour, temperature {report['params']['temperature']}",
        "",
        "## Taux d'accord",
        "",
        "| Juge | Famille | Modele | Mesurees | Non parses | Taux | IC Wilson 95 % |",
        "|---|---|---|---|---|---|---|",
    ]
    for judge in report["judges"]:
        ci = judge["ci95_wilson"]
        ci_txt = f"[{ci[0]:.4f} ; {ci[1]:.4f}]" if ci else "non mesure"
        rate = f"{judge['rate']:.4f}" if judge["rate"] is not None else "non mesure"
        lines.append(
            f"| {judge['name']} | {judge['family']} | {judge['model']} | "
            f"{judge['n_measured']}/{judge['n_pairs']} | {judge['n_unparsed']} | "
            f"{rate} | {ci_txt} |")
    auto_ci = auto["ci95_wilson"]
    auto_ci_txt = f"[{auto_ci[0]:.4f} ; {auto_ci[1]:.4f}]" if auto_ci else "non mesure"
    lines += [
        "| generateur (auto-accord, sous-ensemble) | Qwen (vLLM maison) | "
        "celui du corpus | {n}/{total} | 0 | {rate} | {ci} |".format(
            n=auto["n_measured"], total=auto["n_pairs"],
            rate=f"{auto['rate']:.4f}" if auto["rate"] is not None else "non mesure",
            ci=auto_ci_txt),
        "",
        "La ligne « generateur » est le contraste : le taux aller-retour du generateur",
        "**restreint au meme sous-ensemble** (champ `roundtrip` du corpus, aucun appel).",
        "C'est la reference meme-famille-definition-visible face a laquelle lire les",
        "juges externes : un juge externe proche d'elle ne fait que confirmer le",
        "reclassement ; un juge externe bas ne dit pas lequel des deux a tort, il dit",
        "que l'etiquette ne survit pas au changement de famille.",
        "",
        "## Par famille",
        "",
    ]
    judge_names = [judge["name"] for judge in report["judges"]]
    families = sorted({entry["family"] for entry in report["per_pair"]})
    lines.append("| Famille | " + " | ".join(judge_names) + " | generateur |")
    lines.append("|---" * (len(judge_names) + 2) + "|")
    by_judge_family = {judge["name"]: judge["by_family"] for judge in report["judges"]}
    auto_by_family: dict[str, dict] = {}
    for entry in report["per_pair"]:
        bucket = auto_by_family.setdefault(entry["family"], {"measured": 0, "hits": 0})
        if entry["roundtrip"] is not None:
            bucket["measured"] += 1
            bucket["hits"] += 1 if entry["roundtrip"] else 0
    for family in families:
        cells = []
        for name in judge_names:
            bucket = by_judge_family.get(name, {}).get(family)
            cells.append(f"{bucket['hits']}/{bucket['measured']}" if bucket else "-")
        auto_bucket = auto_by_family[family]
        lines.append(f"| {family} | " + " | ".join(cells)
                     + f" | {auto_bucket['hits']}/{auto_bucket['measured']} |")
    lines += [
        "",
        "## Empreintes",
        "",
        f"- corpus d'entree : `{corpus['sha256']}`",
        f"- rapport JSON : `{sha256_file(json_path)}` (`{json_path.name}`)",
        "",
        "Rejouabilite : `python -m fallacy_detection.judge_family_agreement "
        "--report-only` reconstruit ce rapport sans aucun appel ni cle — depuis "
        "le checkpoint local s'il existe, sinon depuis le rapport publie.",
        "",
    ]
    return "\n".join(lines)


def _count_lines(path: Path) -> int:
    with open(path, encoding="utf-8") as f:
        return sum(1 for line in f if line.strip())


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--judges", default="openai,openrouter",
                        help="noms de juges separes par des virgules (catalogue JUDGE_SPECS)")
    parser.add_argument("--n-pairs", type=int, default=DEFAULT_N_PAIRS)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--distractors", type=int, default=G.DEFAULT_DISTRACTORS)
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--model-openai", default=None,
                        help="surcharge du modele du juge openai")
    parser.add_argument("--model-openrouter", default=None,
                        help="surcharge du modele du juge openrouter")
    parser.add_argument("--probe", action="store_true",
                        help="un appel par juge, aucune mesure, aucune ecriture")
    parser.add_argument("--report-only", action="store_true",
                        help="reconstruit le rapport depuis le checkpoint local, ou a "
                        "defaut depuis le rapport publie committé — sans appel, sans cle")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)
    judge_names = [name.strip() for name in args.judges.split(",") if name.strip()]
    unknown = [name for name in judge_names if name not in JUDGE_SPECS]
    if unknown:
        print(f"juges inconnus : {unknown} (catalogue : {sorted(JUDGE_SPECS)})", file=sys.stderr)
        return 2

    texts = G.B.load_texts()
    records = load_corpus(args.corpus)
    drawn = draw_pairs(records, args.n_pairs, args.seed)
    questions = build_questions(drawn, texts, args.seed,
                                distractors=args.distractors)

    judges_meta: list[dict] = []
    for name in judge_names:
        spec = JUDGE_SPECS[name]
        model = (args.model_openai if name == "openai" and args.model_openai
                 else args.model_openrouter if name == "openrouter" and args.model_openrouter
                 else spec["model"])
        judges_meta.append({"name": name, "family": spec["family"],
                            "model": model, "url": spec["url"]})

    # Les clients ne se construisent QUE si un appel est a faire : un
    # ``--report-only`` doit marcher sur une machine sans aucune cle.
    clients: dict[str, Teacher] = {}
    if args.probe or not args.report_only:
        for meta in judges_meta:
            clients[meta["name"]] = OpenAIJudge(
                name=meta["name"], url=meta["url"], model=meta["model"],
                api_key_env=JUDGE_SPECS[meta["name"]]["api_key_env"])

    if args.probe:
        probe_question = questions[0]
        for name, judge in clients.items():
            reply = judge.complete(probe_question.question, max_tokens=50, temperature=0.0)
            pick = G.parse_choice(reply.text, probe_question.candidates)
            print(f"[probe] {name} ({judge.model}) -> {reply.finish_reason} "
                  f"{reply.completion_tokens} tok, pick={pick}, "
                  f"reponse={reply.text[:120]!r}")
        return 0

    args.out_dir.mkdir(parents=True, exist_ok=True)
    if not args.report_only:
        run_measurement(clients, questions, args.out_dir)
    # Rejouer la lecture du checkpoint pour le rapport (run_measurement l'a deja
    # fait en mode mesure ; en --report-only c'est la seule source).
    # Source des picks : checkpoint local (même un run partiel) sinon le
    # rapport publié committé — voir load_picks_for_report.
    picks_by_judge = load_picks_for_report(
        args.out_dir, [meta["name"] for meta in judges_meta])
    params = {
        "seed": args.seed, "n_pairs": len(drawn), "distractors": args.distractors,
        "temperature": 0.0, "max_tokens": 400, "lang": "fr",
    }
    json_path, md_path = write_report(
        args.out_dir, judges_meta, picks_by_judge, questions, drawn,
        args.corpus, params)
    print(f"rapport : {json_path}")
    print(f"rendu   : {md_path}")
    for meta in judges_meta:
        by_judge = picks_by_judge[meta["name"]]
        targets = {q.pair_id: q.target for q in questions}
        families = {r["pair_id"]: r["family"] for r in drawn}
        summary = summarise_picks(
            [by_judge.get(q.pair_id) for q in questions],
            [targets[q.pair_id] for q in questions],
            [families[q.pair_id] for q in questions])
        rate = f"{summary['rate']:.4f}" if summary["rate"] is not None else "non mesure"
        print(f"[{meta['name']}] {summary['hits']}/{summary['n_measured']} "
              f"mesurees ({summary['n_unparsed']} non parses) = {rate}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
