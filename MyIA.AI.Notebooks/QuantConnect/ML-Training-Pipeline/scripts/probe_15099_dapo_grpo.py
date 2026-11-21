"""Probe #15099-B : GRPO (TRL) + QLoRA sur DAPO-Math-17k — MiniCPM5-2B vs Qwen3.5-0.8B.

Port borne de la recette DAPO 2-etapes sur RTX 3090, generation via HF
transformers (vLLM natif non disponible sous Windows ; lecon probe A #15099).
Lecons #13596 : cap de steps NON lineaire (max_steps fixe, jamais laisse a -1),
logging_steps=1 <= MAX_STEPS, save uniquement a la fin (adapters hors repo).

Modes :
  selftest  : tests unitaires du matcher de reponses (exit 1 si echec)
  smoke     : boucle complete 3 steps + eval reduite (validation end-to-end GPU)
  run       : run borne complet (un modele x une seed)
  summarize : agrege les runs -> tableau multi-seed + courbes PNG + verdict
  baseline  : eval SEULE du modele de base, sans training (#15294 : mesure du
              critere d'accessibilite AVANT tout run GRPO — casting DAPO)

Datasets (--dataset, protocole identique, seule la couche donnees/reward change) :
  dapo   : BytedTsinghua-SIA/DAPO-Math-17k (cache HF local, 1 791 700 lignes =
           17 917 problemes uniques x 100 repliques ; dedup par extra_info.index)
  xlam   : Salesforce/xlam-function-calling-60k (#15294 retenu 1 — aiguillage/outils,
           reward JSON deterministe, tier 1B assume). Gated HF : sans acces, lancer
           hermes (substitut documente dans P15294_SMALL_MODEL_RL_DATASETS.md).
  hermes : NousResearch/hermes-function-calling-v1 singleturn (substitut effectif du
           xlam gated ; meme forme de tache, ground truth = blocs <tool_call>)
  gsm8k  : openai/gsm8k split train (#15294 bras controle — grade-school non competitif)
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import re
import statistics
import sys
import os
import time
from pathlib import Path
from typing import Any

REPO_RESULTS = Path(__file__).resolve().parent / "results" / "m19_minicpm5_grpo"
BASELINE_RESULTS = Path(__file__).resolve().parent / "results" / "p15294_accessibility"
# Racine des artefacts lourds (adapters, sorties) : hors dépôt. Surchargeable par
# variable d'environnement, car le chemin `D:/Dev/...` code en dur echouait sur
# les sieges qui n'ont pas de disque D: (le run echouait sur `mkdir` avant meme
# de produire une mesure) -- defaut inchange pour les sieges qui l'utilisent.
RUNS_ROOT = Path(os.environ.get("PROBE15099_RUNS_ROOT", "D:/Dev/probe15099_runs"))
DATASET_SNAPSHOT_GLOB = (
    "datasets--BytedTsinghua-SIA--DAPO-Math-17k/snapshots/*/data/dapo-math-17k.parquet"
)
XLAM_SNAPSHOT_GLOB = "datasets--Salesforce--xlam-function-calling-60k/snapshots/*"
HERMES_SNAPSHOT_GLOB = "datasets--NousResearch--hermes-function-calling-v1/snapshots/*"
GSM8K_SNAPSHOT_GLOB = "datasets--openai--gsm8k/snapshots/*/main"

MAX_STEPS = 100
EVAL_N_PROMPTS = 40
EVAL_GENS = 4
TRAIN_POOL = 4000
SPLIT_SEED = 15099

# Mode par defaut : non-thinking (les 2 modeles pensent >1024 tok sur DAPO —
# budget incompatible ; DAPO papier entraine egalement des modeles non-thinking).
CHAT_KWARGS: dict[str, Any] = {}
MAX_COMPLETION = 384
# Geometrie de reference du protocole DAPO : 8 sequences par micro-batch x 4
# accumulations = 32 completions par pas d'optimiseur = 4 prompts x 8
# generations par round. Toute autre geometrie doit etre annoncee.
REFERENCE_EFFECTIVE_BATCH = 32

MODELS: dict[str, dict[str, str]] = {
    "minicpm5": {
        "path_glob": "models--openbmb--MiniCPM5-2B/snapshots/*",
        "label": "MiniCPM5-2B",
        # eos_token du tokenizer = </s> (id 1) mais le template de chat
        # termine les tours par <|im_end|> (id 130073, present dans
        # generation_config, absent de special_tokens_map). TRL 1.12 lit
        # l'EOS de generation, la detection de troncature ET le masque de
        # perte depuis tokenizer.eos_token_id uniquement : sans alignement,
        # aucune completion n'est vue "terminee" -> clipped_ratio=1 et
        # mask_truncated_completions annule la perte (smoke 08/10 :
        # loss/grad/entropy = 0).
        "eos_token": "<|im_end|>",
        "tier": "0.8-2B",
    },
    "qwen35": {
        "path_glob": "models--Qwen--Qwen3.5-0.8B/snapshots/*",
        "label": "Qwen3.5-0.8B",
        "tier": "0.8-2B",
    },
    # Etage >= 8-9B demande par #15293 (review user de #15249 : le casting
    # 0.8B/2B est errone pour un exercice de raisonnement mathematique).
    # Poids deja en cache local sur po-2024 — l'arm ne demande aucun
    # telechargement, ce que la disponibilite intermittente de huggingface.co
    # rend necessaire (cf corps de PR).
    "qwen3_8b": {
        "path_glob": "models--Qwen--Qwen3-8B/snapshots/*",
        "label": "Qwen3-8B",
        "tier": "8-14B",
    },
    # Second backbone de l'etage >= 8-9B (#15293), sur le GPU 2 d'ai-01.
    # Le glob suit le depot HF `Qwen/Qwen3-14B` (instruct, non-Base) : c'est
    # le nom annonce par ai-01 dans le DM du 2026-10-05. Les poids sont
    # telecharges par la machine qui execute (ai-01), pas par po-2024.
    "qwen3_14b": {
        "path_glob": "models--Qwen--Qwen3-14B/snapshots/*",
        "label": "Qwen3-14B",
        "tier": "8-14B",
    },
}

# Etages de taille compares par #15293 ("tableau comparatif 0.8B/2B vs 8-9B").
# L'ordre est significatif : le plus petit d'abord.
TIERS: tuple[str, ...] = ("0.8-2B", "8-14B")


def hf_hub_dir() -> Path:
    """Racine du cache HF, variable d'environnement d'abord.

    Le chemin par defaut (`~/.cache/huggingface/hub`) n'est PAS une constante :
    les sieges de la flotte positionnent `HF_HOME` (ex. `D:/hf-cache/huggingface`)
    ou `HF_HUB_CACHE`. Le chemin code en dur levait alors "aucun snapshot HF
    pour ... (lancer hf download)" alors que le cache etait plein -- le run se
    bloquait sur un telechargement qui n'avait rien a telecharger, et le
    message invitait a un contournement (re-telecharger) au lieu d'un
    diagnostic (le cache etait ailleurs). On respecte donc l'environnement,
    avec le chemin par defaut en repli.
    """
    explicit = os.environ.get("HF_HUB_CACHE")
    if explicit:
        return Path(explicit)
    home = os.environ.get("HF_HOME")
    if home:
        return Path(home) / "hub"
    return Path.home() / ".cache" / "huggingface" / "hub"


def find_hf_snapshot(glob_pattern: str) -> Path:
    hub = hf_hub_dir()
    matches = sorted(hub.glob(glob_pattern))
    if not matches:
        raise FileNotFoundError(
            f"aucun snapshot HF pour {glob_pattern} dans {hub} "
            "(HF_HOME / HF_HUB_CACHE pointent-ils sur le cache qui porte les poids ?)"
        )
    return matches[-1]


# ---------------------------------------------------------------------------
# Reward : extraction + comparaison deterministe de la reponse finale
# ---------------------------------------------------------------------------

_ANSWER_TAG = re.compile(r"Answer:\s*\$([^$]+)\$", re.IGNORECASE)
_BOXED = re.compile(r"\\boxed\{((?:[^{}]|\{[^{}]*\})+)\}")
_NUMBER = re.compile(r"-?\d+(?:\.\d+)?(?:\s*/\s*-?\d+(?:\.\d+)?)?")


def extract_answer(text: str) -> str | None:
    """Extrait la reponse finale : 'Answer: $X$' (consigne DAPO), puis \\boxed, puis dernier nombre."""
    tags = _ANSWER_TAG.findall(text)
    if tags:
        return tags[-1].strip()
    boxed = _BOXED.findall(text)
    if boxed:
        return boxed[-1].strip()
    nums = _NUMBER.findall(text)
    return nums[-1].strip() if nums else None


def normalize_answer(ans: str) -> str:
    a = ans.strip()
    a = a.replace("\\!", "").replace("\\,", "").replace(" ", "")
    a = a.replace("\\dfrac", "\\frac").replace("\\tfrac", "\\frac")
    a = a.replace("{,}", "").replace(",", "").replace("\\$", "").replace("$", "")
    a = a.rstrip("%").rstrip(".")
    m = re.fullmatch(r"\\frac\{(-?\d+)\}\{(-?\d+)\}", a)
    if m:  # \frac{3}{4} -> 3/4 avant la suppression generique des accolades
        a = f"{m.group(1)}/{m.group(2)}"
    a = a.replace("{", "").replace("}", "")
    try:
        f = float(a)
        return str(int(f)) if f == int(f) and "." not in a else str(f)
    except ValueError:
        return a


def _to_float(s: str) -> float | None:
    m = re.fullmatch(r"(-?\d+(?:\.\d+)?)/(-?\d+(?:\.\d+)?)", s)
    try:
        if m:
            d = float(m.group(2))
            return float(m.group(1)) / d if d != 0 else None
        return float(s)
    except (ValueError, ZeroDivisionError):
        return None


def answers_match(pred: str | None, golden: str) -> bool:
    if pred is None:
        return False
    p, g = normalize_answer(pred), normalize_answer(golden)
    if p == g:
        return True
    fp, fg = _to_float(p), _to_float(g)
    return fp is not None and fg is not None and math.isclose(fp, fg, rel_tol=1e-6)


def dapo_reward(
    prompts: list[Any],
    completions: list[Any],
    ground_truth: list[str],
    **_kwargs: Any,
) -> list[float]:
    """Reward binaire DAPO : 1.0 si la reponse extraite egale le ground truth."""

    def content(c: Any) -> str:
        if isinstance(c, list) and c and isinstance(c[0], dict):
            return c[-1].get("content", "")
        return str(c)

    return [
        1.0 if answers_match(extract_answer(content(c)), gt) else 0.0
        for c, gt in zip(completions, ground_truth, strict=True)
    ]


# ---------------------------------------------------------------------------
# Donnees
# ---------------------------------------------------------------------------


def load_dapo_split() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Deduplique le parquet (17 917 problemes uniques) et split train/eval fixe."""
    import pandas as pd

    parquet = find_hf_snapshot(DATASET_SNAPSHOT_GLOB)
    df = pd.read_parquet(parquet, columns=["prompt", "reward_model", "extra_info"])
    df["ground_truth"] = df["reward_model"].apply(lambda r: r.get("ground_truth", ""))
    df["uid"] = df["extra_info"].apply(lambda r: r.get("index", ""))
    df = df.drop_duplicates(subset="uid").reset_index(drop=True)
    df = df.sample(frac=1.0, random_state=SPLIT_SEED).reset_index(drop=True)

    def rows(frame: pd.DataFrame) -> list[dict[str, Any]]:
        return [
            {"prompt": list(p), "ground_truth": str(gt)}
            for p, gt in zip(frame["prompt"], frame["ground_truth"], strict=True)
        ]

    eval_rows = rows(df.iloc[:EVAL_N_PROMPTS])
    train_rows = rows(df.iloc[EVAL_N_PROMPTS : EVAL_N_PROMPTS + TRAIN_POOL])
    # TRL 1.12 ne tronque plus les prompts : filtre des outliers longs (~1000 tok)
    train_rows = [r for r in train_rows if len(r["prompt"][-1]["content"]) <= 3000]
    return train_rows, eval_rows


# ---------------------------------------------------------------------------
# Datasets #15294 : xlam-function-calling-60k (aiguillage) et GSM8K (controle).
# Protocole identique au DAPO (memes constantes, meme split fixe) ; seule la
# couche prompt/reward change. Critere de calibration : docs/P15294_*.md.
# ---------------------------------------------------------------------------

_XLAM_SYSTEM = (
    "You are a function calling assistant. Use the function signatures provided "
    "inside <tools></tools> XML tags to answer the user's question."
)
_XLAM_INSTRUCTION = (
    "\n\nReply with the function call(s) only, as JSON "
    '({"name": ..., "arguments": {...}}), no prose.'
)


def _coerce_numeric_strings(value: Any) -> Any:
    """xlam melange "2" et 2 dans les arguments : coercion deterministe des deux cotes."""
    if isinstance(value, dict):
        return {k: _coerce_numeric_strings(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_coerce_numeric_strings(v) for v in value]
    if isinstance(value, str):
        s = value.strip()
        try:
            return int(s)
        except ValueError:
            try:
                return float(s)
            except ValueError:
                return s
    return value


def canonical_calls(value: Any) -> str:
    """Forme canonique d'un appel ou d'une liste d'appels (cles triees, sep compacts)."""
    calls = value if isinstance(value, list) else [value]
    return json.dumps(
        _coerce_numeric_strings(calls), sort_keys=True, separators=(",", ":"),
        ensure_ascii=False,
    )


def extract_json_call(text: str) -> Any | None:
    """Premier objet/tableau JSON parsable du texte (fences ``` retirees)."""
    cleaned = re.sub(r"```(?:json)?|```", "", text)
    decoder = json.JSONDecoder()
    for i, ch in enumerate(cleaned):
        if ch in "[{":
            try:
                value, _ = decoder.raw_decode(cleaned[i:])
                return value
            except json.JSONDecodeError:
                continue
    return None


def xlam_match(text: str, ground_truth: str) -> bool:
    pred = extract_json_call(text)
    if pred is None:
        return False
    try:
        return canonical_calls(pred) == canonical_calls(json.loads(ground_truth))
    except json.JSONDecodeError:
        return False


def xlam_reward(
    prompts: list[Any],
    completions: list[Any],
    ground_truth: list[str],
    **_kwargs: Any,
) -> list[float]:
    """Reward binaire xlam : l'appel JSON produit egale (canoniquement) l'appel attendu."""

    def content(c: Any) -> str:
        if isinstance(c, list) and c and isinstance(c[0], dict):
            return c[-1].get("content", "")
        return str(c)

    return [1.0 if xlam_match(content(c), gt) else 0.0
            for c, gt in zip(completions, ground_truth, strict=True)]


def _read_table(snapshot: Path) -> "Any":
    import pandas as pd

    candidates = (
        sorted(snapshot.rglob("*.parquet")) + sorted(snapshot.rglob("*.jsonl"))
        + sorted(snapshot.rglob("*.json"))
    )
    if not candidates:
        raise FileNotFoundError(f"aucun fichier de donnees sous {snapshot}")
    # preference explicite pour le split train (gsm8k/main trie test avant train)
    train_first = [c for c in candidates if "train" in c.name.lower()]
    first = (train_first or candidates)[0]
    if first.suffix == ".parquet":
        return pd.read_parquet(first)
    return pd.read_json(first, lines=True)


def load_xlam_split() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    import json as _json

    df = _read_table(find_hf_snapshot(XLAM_SNAPSHOT_GLOB))
    df = df.sample(frac=1.0, random_state=SPLIT_SEED).reset_index(drop=True)

    def rows(frame: Any) -> list[dict[str, Any]]:
        out = []
        for _, r in frame.iterrows():
            tools, query, answers = str(r["tools"]), str(r["query"]), str(r["answers"])
            if len(query) + len(tools) > 3000:  # meme filtre outliers longs que DAPO
                continue
            out.append({
                "prompt": [
                    {"role": "system", "content": _XLAM_SYSTEM},
                    {"role": "user", "content": f"<tools>{tools}</tools>\n\n{query}{_XLAM_INSTRUCTION}"},
                ],
                "ground_truth": canonical_calls(_json.loads(answers)),
            })
        return out

    eval_rows = rows(df.iloc[:EVAL_N_PROMPTS * 3])[:EVAL_N_PROMPTS]
    train_rows = rows(df.iloc[EVAL_N_PROMPTS * 3 : EVAL_N_PROMPTS * 3 + TRAIN_POOL * 2])[:TRAIN_POOL]
    return train_rows, eval_rows


_HERMES_TOOLCALL_RE = re.compile(r"<tool_call>\s*(\{.*?\})\s*</tool_call>", re.DOTALL)


def load_hermes_split() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Hermes function-calling v1, fichier singleturn (substitut xlam : repo xlam gated).

    Meme forme de tache que xlam : schemas d'outils + requete utilisateur ->
    appel(s) JSON. Ground truth = les blocs <tool_call> du tour assistant.
    """
    snap = find_hf_snapshot(HERMES_SNAPSHOT_GLOB)
    data = json.loads((snap / "func-calling-singleturn.json").read_text(encoding="utf-8"))
    rng = random.Random(SPLIT_SEED)
    rng.shuffle(data)

    def rows(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
        out = []
        for rec in records:
            tools = rec.get("tools")
            if not tools:
                continue
            tools_s = tools if isinstance(tools, str) else json.dumps(tools, ensure_ascii=False)
            conv = rec.get("conversations", [])
            human = next((m["value"] for m in conv if m.get("from") == "human"), None)
            gpt = next((m["value"] for m in conv if m.get("from") == "gpt"), None)
            if not human or not gpt:
                continue
            calls = [json.loads(b) for b in _HERMES_TOOLCALL_RE.findall(gpt)]
            if not calls or any(c is None for c in calls):
                continue
            if len(human) + len(tools_s) > 3000:  # meme filtre outliers longs que DAPO
                continue
            out.append({
                "prompt": [
                    {"role": "system", "content": _XLAM_SYSTEM},
                    {"role": "user", "content": f"<tools>{tools_s}</tools>\n\n{human}{_XLAM_INSTRUCTION}"},
                ],
                "ground_truth": canonical_calls(calls),
            })
        return out

    eval_rows = rows(data[:EVAL_N_PROMPTS * 3])[:EVAL_N_PROMPTS]
    train_rows = rows(data[EVAL_N_PROMPTS * 3 : EVAL_N_PROMPTS * 3 + TRAIN_POOL * 2])[:TRAIN_POOL]
    return train_rows, eval_rows


def load_gsm8k_split() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    df = _read_table(find_hf_snapshot(GSM8K_SNAPSHOT_GLOB))
    df = df.sample(frac=1.0, random_state=SPLIT_SEED).reset_index(drop=True)

    def rows(frame: Any) -> list[dict[str, Any]]:
        out = []
        for _, r in frame.iterrows():
            question, answer = str(r["question"]), str(r["answer"])
            gt = answer.split("####")[-1].strip().replace(",", "")
            out.append({
                "prompt": [{
                    "role": "user",
                    "content": question
                    + "\n\nReason briefly, then end your reply with: Answer: $<number>$",
                }],
                "ground_truth": gt,
            })
        return out

    eval_rows = rows(df.iloc[:EVAL_N_PROMPTS])
    train_rows = rows(df.iloc[EVAL_N_PROMPTS : EVAL_N_PROMPTS + TRAIN_POOL])
    return train_rows, eval_rows


def dapo_match(text: str, ground_truth: str) -> bool:
    return answers_match(extract_answer(text), ground_truth)


DATASETS: dict[str, dict[str, Any]] = {
    "dapo": {"load": load_dapo_split, "match": dapo_match, "reward": dapo_reward,
             "label": "DAPO-Math-17k"},
    "xlam": {"load": load_xlam_split, "match": xlam_match, "reward": xlam_reward,
             "label": "xlam-function-calling-60k"},  # gated HF : substitut = hermes
    "hermes": {"load": load_hermes_split, "match": xlam_match, "reward": xlam_reward,
               "label": "Hermes-function-calling-v1 (singleturn)"},
    "gsm8k": {"load": load_gsm8k_split, "match": dapo_match, "reward": dapo_reward,
              "label": "GSM8K-train"},
}


# ---------------------------------------------------------------------------
# Entrainement GRPO + QLoRA
# ---------------------------------------------------------------------------


def grad_norm_carries(g: float) -> bool:
    """Une observation `grad_norm` porte-t-elle un gradient ?

    `grad_norm` est une NORME de gradient : sa valeur legitime est finie et
    >= 0. Le predicat historique est `g > 0`, qui vaut DEJA False pour un
    `nan` (IEEE-754 : toute comparaison avec NaN est False) et pour une
    valeur negative. Le comportement etait donc correct, mais IMPLICITE --
    il est ecrit ici pour etre fige par le selftest.

    - finie et > 0  : le pas a porte un gradient (vivant).
    - == 0          : aucun gradient porte (signature de la graine 42).
    - negative      : mesure invalide -- une norme ne peut pas etre negative.
    - `nan`         : divergence silencieuse -- ni vivante, ni inexploitable
                      ; elle compte comme une observation (elle a ete tracee)
                      mais jamais comme porteuse.
    - `+inf`        : debordement de la norme -> invalide, pas un signal.
    """
    return math.isfinite(g) and g > 0.0


def no_signal_verdict(grad_norms: list[float], threshold: int) -> dict[str, Any]:
    """Verdict pur : le run a-t-il porte un gradient dans les `threshold` premiers pas ?

    Temoin : `grad_norm`. Mesure sur le bras 8B de #15293 (4 graines, regie
    ai-01 du 2026-10-26) : la graine 42 est nee morte -- `grad_norm` = 0,0
    exact sur ses 12 premieres etapes tracees -- et la graine 7 s'est eteinte
    en cours de run (3 etapes vivantes dans les 20 premieres, 0 dans les 20
    dernieres). Dans les deux cas le PRE-EVAL etait normal (reward 0,05,
    longueur 1 033) : rien ne l'annoncait avant le premier pas. Un `rc=0` ne
    dit rien du signal ; c'est cette mesure qui departage « run termine » de
    « run qui a porte un gradient ».

    Fonction pure du tableau de `grad_norm` observe : le meme code sert au
    callback (arret en cours de run) et au controle a posteriori (verdict
    dans l'artefact), et se teste sans GPU (mode selftest).

    - `threshold <= 0`  : garde desactivee, protocole inchange.
    - moins de `threshold` observations : pas assez de preuves, on ne decide pas.
    - aucune observation porteuse : ABANDON (le run ne portera rien).

    Une observation est PORTEUSE si elle est finie et strictement positive
    (`grad_norm_carries`). Un `nan` (divergence silencieuse), une valeur
    negative ou un `+inf` sont des mesures INVALIDES : ils comptent comme
    observations (ils ont ete traces) mais jamais comme porteuses -- donc un
    run dont les N premieres mesures sont toutes invalides est abandonne
    lui aussi, avec la raison `grad_norm_invalid_on_first_steps`.
    """
    observed = [float(g) for g in grad_norms if g is not None]
    alive = [g for g in observed if grad_norm_carries(g)]
    invalid = [g for g in observed if not grad_norm_carries(g) and g != 0.0]
    verdict: dict[str, Any] = {
        "threshold": threshold,
        "steps_observed": len(observed),
        "steps_alive": len(alive),
        "steps_invalid": len(invalid),
        "abort": False,
        "reason": "",
    }
    if threshold <= 0:
        verdict["reason"] = "disabled"
    elif len(observed) < threshold:
        verdict["reason"] = "not_enough_observations"
    elif not alive:
        verdict["abort"] = True
        verdict["reason"] = ("grad_norm_invalid_on_first_steps" if invalid
                             else "grad_norm_zero_on_first_steps")
    else:
        verdict["reason"] = "signal_alive"
    return verdict


def build_no_signal_guard(threshold: int) -> Any:
    """Callback transformers qui abandonne l'entrainement quand aucun gradient
    n'a porte sur les `threshold` premiers pas.

    Option 2 de la decision de protocole demandee par la regie ai-01 sur
    #15293 (« une garde d'entree sur les premiers pas : seule la mesure
    permet de distinguer une graine morte d'une graine sous pression de
    budget ») — c'est un ajout a l'outillage, donc une PR, pas un geste de
    regie. Mesure d'economie : sur la graine 42, la garde aurait arrete le
    run en quelques minutes au lieu de 6 h 30 de GPU, pour un resultat
    equivalent (zero gradient porte).

    L'arret passe par `control.should_training_stop` : arret PROPRE, sans
    exception -- le run se termine normalement, l'artefact est ecrit, et il
    porte le verdict (les runs arretes n'ont pas de post-eval, ils sont
    exclus du calcul des deltas par mode_summarize).
    """
    from transformers import TrainerCallback

    class _NoSignalGuard(TrainerCallback):
        def __init__(self) -> None:
            self.grad_norms: list[float] = []
            # avant tout log : la garde est armee mais n'a rien observe
            # ("disabled" serait faux ici -- la garde l'est des que threshold > 0).
            self.verdict: dict[str, Any] = {
                "threshold": threshold, "abort": False,
                "reason": "disabled" if threshold <= 0 else "not_enough_observations",
                "steps_observed": 0, "steps_alive": 0}

        def on_log(self, args: Any, state: Any, control: Any,
                   logs: dict[str, Any] | None = None, **kwargs: Any) -> Any:
            logs = logs or {}
            g = logs.get("grad_norm")
            if g is None:
                # pas de grad_norm dans ce log : ce pas ne dit rien du signal
                return control
            try:
                value = float(g)
            except (TypeError, ValueError):
                # mesure illisible : on ne leve pas le callback -- une exception
                # ici tuerait un run de 6 h 30 de GPU pour un probleme de log.
                # La mesure est traitee comme invalide, donc comme non
                # porteuse ; un run dont toutes les mesures sont illisibles est
                # abandonne avec la raison "invalid".
                value = float("nan")
            self.grad_norms.append(value)
            self.verdict = no_signal_verdict(self.grad_norms, threshold)
            if self.verdict["abort"]:
                control.should_training_stop = True
            return control

    return _NoSignalGuard()


def build_trainer(
    model_key: str, seed: int, steps: int, train_rows: list[dict[str, Any]],
    reward_fn: Any = dapo_reward, dataset_key: str = "dapo",
    per_device_batch: int = 8, grad_accum: int = 4,
):
    import torch
    from datasets import Dataset
    from peft import LoraConfig
    from transformers import AutoTokenizer, BitsAndBytesConfig
    from trl import GRPOConfig, GRPOTrainer

    model_path = find_hf_snapshot(MODELS[model_key]["path_glob"])
    tokenizer = AutoTokenizer.from_pretrained(str(model_path))
    eos_override = MODELS[model_key].get("eos_token")
    if eos_override is not None:
        # aligne l'EOS tokenizer sur le terminateur reel du template (cf MODELS)
        tokenizer.eos_token = eos_override
    if tokenizer.pad_token_id is None:
        tokenizer.pad_token = tokenizer.eos_token

    quant_cfg = BitsAndBytesConfig(
        load_in_4bit=True,
        bnb_4bit_quant_type="nf4",
        bnb_4bit_use_double_quant=True,
        bnb_4bit_compute_dtype=torch.bfloat16,
    )
    peft_cfg = LoraConfig(
        r=16,
        lora_alpha=32,
        lora_dropout=0.05,
        target_modules="all-linear",
        task_type="CAUSAL_LM",
    )
    cfg = GRPOConfig(
        output_dir=str(RUNS_ROOT / f"{model_key}_{dataset_key}_seed{seed}" / "trainer_out"),
        seed=seed,
        # device_map explicite, jamais "auto". Sous 4-bit SANS
        # llm_int8_enable_fp32_cpu_offload, le chemin d'offload d'accelerate est
        # mort par construction : des qu'un module part sur CPU, le quantizer bnb
        # leve « Some modules are dispatched on the CPU or the disk » AVANT tout
        # entrainement -- mesure sur l'arm 8B (#15293), qui tient pourtant sur 8 Go
        # (5,78 GiB, 4717,9 M parametres tous sur cuda:0) et echouait sur "auto".
        # Forcer le GPU rend l'echec honnete : un modele qui ne tient pas OOM au
        # lieu de lever une erreur opaque.
        model_init_kwargs=dict(device_map={"": 0}),
        max_steps=steps,  # cap NON lineaire (lecon #13596)
        learning_rate=2e-5,
        warmup_steps=5,
        lr_scheduler_type="constant_with_warmup",
        # Geometrie du protocole. Deux invariants portent la mesure :
        #   (1) `per_device_train_batch_size * gradient_accumulation_steps`
        #       completions par pas d'optimiseur (32 = 4 prompts x 8 generations) ;
        #   (2) le round de generation vaut
        #       `per_device * num_processes * steps_per_generation`, avec
        #       `steps_per_generation = gradient_accumulation_steps` (defaut TRL),
        #       donc 32 completions = 4 prompts de 8 generations.
        # Diviser la micro-batch et doubler l'accumulation laisse les DEUX
        # invariants inchanges : seule la taille du tenseur de logits du
        # backward est divise. C'est le levier mesure contre l'OOM de la leg
        # 1024 (#15099) -- l'allocateur `expandable_segments`, leve par
        # PyTorch, est refuse sur ce poste Windows.
        per_device_train_batch_size=per_device_batch,
        gradient_accumulation_steps=grad_accum,  # 32 completions/step = 4 prompts x 8 generations
        num_generations=8,
        max_completion_length=MAX_COMPLETION,
        temperature=1.0,
        top_p=1.0,
        loss_type="dapo",
        epsilon=0.2,
        epsilon_high=0.28,  # clip-higher DAPO
        beta=0.0,  # pas de penalite KL / ref model (recette DAPO)
        mask_truncated_completions=True,
        scale_rewards="group",
        bf16=True,
        gradient_checkpointing=True,
        logging_steps=1,  # <= MAX_STEPS (lecon #13596)
        save_strategy="no",
        report_to=[],
        use_cache=False,
        chat_template_kwargs=dict(CHAT_KWARGS),
    )
    trainer = GRPOTrainer(
        model=str(model_path),
        reward_funcs=reward_fn,
        args=cfg,
        train_dataset=Dataset.from_list(train_rows),
        processing_class=tokenizer,
        quantization_config=quant_cfg,
        peft_config=peft_cfg,
    )
    return trainer, model_path


def _generate_eval(
    model: Any, tokenizer: Any, eval_rows: list[dict[str, Any]], seed: int,
    match_fn: Any = dapo_match,
) -> dict[str, float]:
    """Generation n=EVAL_GENS par prompt eval, reward par le matcher du dataset."""
    import torch

    gen_seed = seed * 1000 + 7
    rewards: list[float] = []
    lengths: list[int] = []
    device = next(model.parameters()).device
    model.eval()
    with torch.no_grad():
        for i, row in enumerate(eval_rows):
            torch.manual_seed(gen_seed + i)
            enc = tokenizer.apply_chat_template(
                row["prompt"],
                add_generation_prompt=True,
                return_tensors="pt",
                return_dict=True,  # transformers 5.x : dict {input_ids, attention_mask}
                **CHAT_KWARGS,
            )
            enc = {k: v.to(device) for k, v in enc.items()}
            n_in = enc["input_ids"].shape[1]
            out = model.generate(
                **enc,
                max_new_tokens=MAX_COMPLETION,
                do_sample=True,
                temperature=1.0,
                top_p=1.0,
                pad_token_id=tokenizer.pad_token_id,
                num_return_sequences=EVAL_GENS,
            )
            texts = tokenizer.batch_decode(out[:, n_in:], skip_special_tokens=True)
            for t in texts:
                rewards.append(1.0 if match_fn(t, row["ground_truth"]) else 0.0)
                lengths.append(len(t))
    return {
        "n_gens": float(len(rewards)),
        "reward_mean": sum(rewards) / len(rewards),
        "length_mean": sum(lengths) / max(1, len(lengths)),
    }


def evaluate(
    trainer: Any, eval_rows: list[dict[str, Any]], seed: int,
    match_fn: Any = dapo_match,
) -> dict[str, float]:
    return _generate_eval(trainer.model, trainer.processing_class, eval_rows, seed, match_fn)


# ---------------------------------------------------------------------------
# Modes
# ---------------------------------------------------------------------------


def mode_selftest() -> int:
    cases: list[tuple[str, str, bool]] = [
        ("... Answer: $34$", "34", True),
        ("blah\nAnswer: $x = 4, y = 2$", "4,2", False),  # composite non supporte ici (gt numeriques)
        ("The answer is \\boxed{\\frac{3}{4}}", "3/4", True),
        ("Answer: $0.5$", "1/2", True),
        ("Answer: $-3$", "-3", True),
        ("result: 113.", "113", True),
        ("no numbers at all here", "42", False),
        ("Answer: $1{,}000$", "1000", True),
        ("Answer: $x^2+1$", "x^2+1", True),
        ("Answer: $\\frac{1}{2}$.", "0.5", True),
    ]
    fails = [(t, g, answers_match(extract_answer(t), g)) for t, g, want in cases
             if answers_match(extract_answer(t), g) != want]
    for t, g, got in fails:
        print(f"FAIL: extract({t!r}) vs {g!r} -> {got}")
    n_match = len(cases) - len(fails)

    xlam_cases: list[tuple[str, str, bool]] = [
        # egalite canonique : strings numeriques coercées ("2" == 2)
        ('{"name": "f", "arguments": {"x": "2"}}', '{"name": "f", "arguments": {"x": 2}}', True),
        # fences ```json retirees
        ('```json\n{"name": "f", "arguments": {}}\n```', '{"name": "f", "arguments": {}}', True),
        # mauvais arguments
        ('{"name": "f", "arguments": {"x": 1}}', '{"name": "f", "arguments": {"x": 2}}', False),
        # mauvais nom de fonction
        ('{"name": "g", "arguments": {}}', '{"name": "f", "arguments": {}}', False),
        # pas de JSON du tout
        ('je appelle la fonction f', '{"name": "f", "arguments": {}}', False),
        # liste multi-appels, ordre preserve
        ('[{"name": "f", "arguments": {}}, {"name": "g", "arguments": {"y": 1}}]',
         '[{"name": "f", "arguments": {}}, {"name": "g", "arguments": {"y": "1"}}]', True),
        # ordre des cles different = meme forme canonique
        ('{"arguments": {"x": 1}, "name": "f"}', '{"name": "f", "arguments": {"x": 1}}', True),
    ]
    xlam_fails = [(t, g, xlam_match(t, g)) for t, g, want in xlam_cases
                  if xlam_match(t, g) != want]
    for t, g, got in xlam_fails:
        print(f"FAIL: xlam_match({t!r}) vs {g!r} -> {got}")
    n_xlam = len(xlam_cases) - len(xlam_fails)

    # Garde d'entree (#15293) : la decision est une FONCTION PURE, elle se
    # teste sans GPU -- c'est ce qui permet de la valider en CI et de la
    # documenter sans dependre d'un run de 6 h 30 de GPU pour un resultat
    # qu'on sait deja : zero gradient porte.
    guard_cases: list[tuple[list[float], int, bool, str]] = [
        # (grad_norms observes, threshold, abort attendu, raison attendue)
        ([0.0, 0.0, 0.0], 3, True, "grad_norm_zero_on_first_steps"),
        ([0.0, 0.0, 1.4], 3, False, "signal_alive"),
        ([0.0, 0.0], 3, False, "not_enough_observations"),
        ([0.0, 0.0, 0.0], 0, False, "disabled"),
        ([], 3, False, "not_enough_observations"),
        ([0.0, 0.7, 0.0], 3, False, "signal_alive"),
        # un `nan` (divergence silencieuse) n'est PAS porteur, mais compte
        # comme observation : N mesures invalides -> abandon, raison
        # "invalid" -- la raison "zero" serait un motif faux.
        ([float("nan"), float("nan"), float("nan")], 3, True,
         "grad_norm_invalid_on_first_steps"),
        # une valeur negative est une mesure invalide (une norme n'est pas
        # negative) : meme traitement qu'un `nan`.
        ([-1.0, -1.0, -1.0], 3, True, "grad_norm_invalid_on_first_steps"),
        # un `nan` melange a un gradient porteur : le pas a porte, on
        # n'abandonne pas.
        ([1.4, float("nan"), 0.0], 3, False, "signal_alive"),
        # un `nan` ne comble pas le seuil : c'est UNE observation, pas plus.
        ([float("nan"), 0.0], 3, False, "not_enough_observations"),
    ]
    guard_fails = []
    for norms, thr, want_abort, want_reason in guard_cases:
        v = no_signal_verdict(norms, thr)
        if v["abort"] != want_abort or v["reason"] != want_reason:
            guard_fails.append((norms, thr, v))
            print(f"FAIL: no_signal_verdict({norms}, {thr}) -> {v} "
                  f"(attendu abort={want_abort}, reason={want_reason})")
    n_guard = len(guard_cases) - len(guard_fails)

    # Le cache HF n'est pas a l'emplacement par defaut sur tous les sieges :
    # la resolution doit suivre HF_HOME / HF_HUB_CACHE, sinon le harness
    # leve "aucun snapshot HF" sur un cache plein.
    hub_fails = []
    saved_env = {k: os.environ.get(k) for k in ("HF_HOME", "HF_HUB_CACHE")}
    try:
        os.environ.pop("HF_HUB_CACHE", None)
        os.environ["HF_HOME"] = "D:/hf-cache/huggingface"
        if hf_hub_dir() != Path("D:/hf-cache/huggingface/hub"):
            hub_fails.append("HF_HOME")
            print(f"FAIL: hf_hub_dir() avec HF_HOME -> {hf_hub_dir()}")
        os.environ["HF_HUB_CACHE"] = "D:/hf-cache/huggingface/hub"
        if hf_hub_dir() != Path("D:/hf-cache/huggingface/hub"):
            hub_fails.append("HF_HUB_CACHE")
            print(f"FAIL: hf_hub_dir() avec HF_HUB_CACHE -> {hf_hub_dir()}")
    finally:
        for k, v in saved_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v

    # Le CABLAGE du callback : la decision pure est testee ci-dessus, mais
    # l'arret doit aussi se declencher dans le protocole de transformers
    # (`control.should_training_stop`). Verifie sur un faux control.
    wire_fails = []
    wire_total = 0
    wire_skipped = False
    try:
        class _Ctrl:
            should_training_stop = False

        guard = build_no_signal_guard(2)
        ctrl = _Ctrl()
        for _ in range(3):
            guard.on_log(None, None, ctrl, logs={"grad_norm": 0.0})
        wire_total += 1
        if not ctrl.should_training_stop:
            wire_fails.append("should_training_stop")
            print("FAIL: le callback n'a pas arme should_training_stop")

        # un grad_norm > 0 ne doit PAS armer l'arret (pas de faux positif)
        guard_live = build_no_signal_guard(2)
        ctrl_live = _Ctrl()
        guard_live.on_log(None, None, ctrl_live, logs={"grad_norm": 0.0})
        guard_live.on_log(None, None, ctrl_live, logs={"grad_norm": 1.2})
        wire_total += 1
        if ctrl_live.should_training_stop:
            wire_fails.append("faux_positif")
            print("FAIL: arret arme sur un run qui porte un gradient")

        # un log sans grad_norm n'est pas une observation de gradient
        guard_silent = build_no_signal_guard(2)
        ctrl_silent = _Ctrl()
        guard_silent.on_log(None, None, ctrl_silent, logs={"loss": 0.0})
        wire_total += 1
        if guard_silent.verdict["steps_observed"] != 0 or ctrl_silent.should_training_stop:
            wire_fails.append("log_sans_grad_norm")
            print("FAIL: un log sans grad_norm a ete compte comme observation")

        # un `nan` (divergence silencieuse) doit armer l'arret : il ne porte
        # rien, donc N mesures invalides -> abandon propre.
        guard_nan = build_no_signal_guard(2)
        ctrl_nan = _Ctrl()
        guard_nan.on_log(None, None, ctrl_nan, logs={"grad_norm": float("nan")})
        guard_nan.on_log(None, None, ctrl_nan, logs={"grad_norm": float("nan")})
        wire_total += 1
        if not ctrl_nan.should_training_stop:
            wire_fails.append("nan")
            print("FAIL: arret non arme sur un grad_norm nan (divergence)")
    except ImportError as exc:
        wire_skipped = True
        print(f"selftest: cablage du callback NON teste ({exc}) -- transformers absent")

    # Tableau comparatif par ETAGE de taille (#15293) : la fonction est PURE,
    # elle se teste sans GPU -- c'est ce qui permet de valider le critere
    # "tableau comparatif 0.8B/2B vs 8-9B" avant d'avoir les runs 8-14B.
    tier_fails = []
    tier_total = 0

    def _pm(model_key: str, deltas: list[float]) -> dict[str, Any]:
        n = len(deltas)
        mean = sum(deltas) / n
        std = (sum((d - mean) ** 2 for d in deltas) / n) ** 0.5
        return {"label": MODELS[model_key]["label"], "n_seeds": n,
                "pre_mean": 0.1, "post_mean": 0.1 + mean,
                "delta_mean": mean, "delta_std": std, "deltas": list(deltas)}

    # (a) etage haut nettement meilleur, 2 graines de chaque cote -> BEATS
    per_model = {"minicpm5": _pm("minicpm5", [0.01, 0.02]),
                 "qwen35": _pm("qwen35", [0.00, 0.01]),
                 "qwen3_8b": _pm("qwen3_8b", [0.20, 0.22]),
                 "qwen3_14b": _pm("qwen3_14b", [0.21, 0.19])}
    tbl = build_tier_table(per_model, {k: True for k in per_model})
    tier_total += 1
    if not (tbl["cross_tier"]["comparable"] and tbl["cross_tier"]["beats"]
            and tbl["cross_tier"]["delta_intervals_disjoint"]):
        tier_fails.append("cas_a")
        print("FAIL: etage haut nettement meilleur non detecte :", tbl["cross_tier"])
    tier_total += 1
    if tbl["tiers"]["8-14B"]["n_seeds"] != 4 or tbl["tiers"]["0.8-2B"]["n_seeds"] != 4:
        tier_fails.append("cas_a_nseeds")
        print("FAIL: agregation par etage :", {k: v["n_seeds"] for k, v in tbl["tiers"].items()})

    # (b) un seul cote en 1 graine -> NON comparable (le verdict reste null)
    tbl_b = build_tier_table({"minicpm5": _pm("minicpm5", [0.01, 0.02]),
                               "qwen3_8b": _pm("qwen3_8b", [0.20])},
                              {"minicpm5": True, "qwen3_8b": True})
    tier_total += 1
    if tbl_b["cross_tier"]["comparable"] is not False:
        tier_fails.append("cas_b")
        print("FAIL: etage a 1 graine declare comparable :", tbl_b["cross_tier"])

    # (c) intervalles chevauchants -> disjoint False, BEATS False
    tbl_c = build_tier_table({"minicpm5": _pm("minicpm5", [0.01, 0.03]),
                               "qwen3_8b": _pm("qwen3_8b", [0.02, 0.03])},
                              {"minicpm5": True, "qwen3_8b": True})
    tier_total += 1
    if tbl_c["cross_tier"]["delta_intervals_disjoint"] or tbl_c["cross_tier"]["beats"]:
        tier_fails.append("cas_c")
        print("FAIL: intervalles chevauchants declares disjoints :", tbl_c["cross_tier"])

    # (c bis) intervalles QUI SE TOUCHENT (0.02 vs 0.02) : des intervalles
    # fermes qui se touchent ne sont pas disjoints. Sans epsilon, le bruit
    # flottant (0.020000000000000004 > 0.02) les declarait disjoints.
    tbl_c2 = build_tier_table({"minicpm5": _pm("minicpm5", [0.01, 0.02]),
                                "qwen3_8b": _pm("qwen3_8b", [0.02, 0.03])},
                               {"minicpm5": True, "qwen3_8b": True})
    tier_total += 1
    if tbl_c2["cross_tier"]["delta_intervals_disjoint"]:
        tier_fails.append("cas_c_bis")
        print("FAIL: intervalles qui se touchent declares disjoints :",
              tbl_c2["cross_tier"])

    # (d) une courbe degeneree (pas saine) suffit a bloquer le BEATS
    tbl_d = build_tier_table(per_model, {**{k: True for k in per_model},
                                          "qwen3_14b": False})
    tier_total += 1
    if tbl_d["cross_tier"]["beats"]:
        tier_fails.append("cas_d")
        print("FAIL: BEATS alors qu'une courbe n'est pas saine :", tbl_d["cross_tier"])

    # (e) le rango de taille est le bon pour chaque modele
    tier_total += 1
    for key, want in (("minicpm5", "0.8-2B"), ("qwen35", "0.8-2B"),
                      ("qwen3_8b", "8-14B"), ("qwen3_14b", "8-14B")):
        if MODELS[key].get("tier") != want:
            tier_fails.append(f"tier_{key}")
            print(f"FAIL: tier de {key} = {MODELS[key].get('tier')} (attendu {want})")

    # (f) le tableau markdown porte une ligne par modele
    tier_total += 1
    md = render_comparative_table({"per_model": per_model, "tiers": tbl})
    for label in ("MiniCPM5-2B", "Qwen3-8B", "Qwen3-14B"):
        if label not in md:
            tier_fails.append(f"md_{label}")
            print(f"FAIL: {label} absent du tableau markdown")

    # (g) classification d'un run : graine / smoke / partiel / aborted
    tier_total += 1
    for name, run, want in (
        ("qwen3_8b_seed42.json", {"max_steps": MAX_STEPS}, "seed"),
        ("qwen3_14b_seed0_smoke.json", {"max_steps": 3}, "smoke"),
        ("qwen3_8b_seed1.json", {"max_steps": 40}, "partiel"),
        ("qwen3_8b_seed7.json", {"aborted": True, "max_steps": MAX_STEPS}, "aborted"),
        # Fail-closed : un budget absent ou non positif ne devient jamais une
        # graine comparable par l'application silencieuse de MAX_STEPS.
        ("qwen3_8b_seed8.json", {"post_eval": {"reward_mean": 0.2}}, "exclu"),
        ("qwen3_8b_seed9.json", {"max_steps": 0}, "exclu"),
    ):
        got = classify_run(name, run)
        if got != want:
            tier_fails.append(f"class_{name}")
            print(f"FAIL: classify_run({name}) -> {got} (attendu {want})")

    # (h) axe de saturation : l'organe est consomme, pas reecrit. Les fixtures
    # sont construites pour tomber sur les trois verdicts de l'organe
    # (SIGNAL_NUL / SIGNAL_PARTIEL / SIGNAL_UTILE).
    def _sat_run(model_key: str, seed: int, *, longueur: float,
                 grads: list[float], reward: float = 0.2,
                 zero_std: float = 0.0,
                 pre: float | None = None, post: float | None = None) -> dict[str, Any]:
        artefact: dict[str, Any] = {
            "model_key": model_key, "model": MODELS[model_key]["label"],
            "seed": seed, "max_completion_length": 384,
            "log_history": [
                {"completions/mean_length": longueur,
                 "completions/clipped_ratio": 1.0 if longueur >= 384 else 0.0,
                 "grad_norm": g, "loss": 0.5, "frac_reward_zero_std": zero_std,
                 "reward": reward}
                for g in grads],
        }
        if pre is not None:
            artefact["pre_eval"] = {"reward_mean": pre}
        if post is not None:
            artefact["post_eval"] = {"reward_mean": post}
        return artefact

    run_sature = _sat_run("qwen3_8b", 0, longueur=384.0, grads=[0.0] * 10)
    run_utile = _sat_run("qwen3_8b", 1, longueur=100.0, grads=[0.5] * 10)
    run_partiel = _sat_run("qwen3_8b", 2, longueur=100.0,
                           grads=[0.5, 0.5] + [0.0] * 8)
    axis = build_saturation_axis([run_sature, run_utile, run_partiel])
    tier_total += 1
    if not axis.get("disponible"):
        tier_fails.append("sat_disponible")
        print("FAIL: l'axe de saturation n'est pas disponible :", axis)
    else:
        bras = axis["par_bras"].get("qwen3_8b", {})
        # Le bras suit la graine MEDIANE (regle de l'organe) : trois graines
        # dont les verdicts sont SIGNAL_NUL / SIGNAL_PARTIEL / SIGNAL_UTILE ->
        # mediane = SIGNAL_PARTIEL.
        tier_total += 1
        if bras.get("verdict") != "SIGNAL_PARTIEL":
            tier_fails.append("sat_verdict_median")
            print("FAIL: verdict de bras (mediane) =", bras.get("verdict"),
                  "(attendu SIGNAL_PARTIEL)")
        # fraction des steps saturees : MEDIANE des graines (regle de l'organe)
        # -> sur 1,00 / 0,00 / 0,00 la mediane vaut 0,00 (la moyenne vaudrait
        # 0,33 : c'est exactement la divergence que l'axe evite).
        tier_total += 1
        frac = bras.get("frac_steps_satures")
        if frac is None or abs(frac - 0.0) > 1e-6:
            tier_fails.append("sat_frac_median")
            print("FAIL: frac_steps_satures =", frac, "(attendu 0,0, mediane)")
        # un bras dont toutes les graines saturent -> SIGNAL_NUL
        tier_total += 1
        if build_saturation_axis([run_sature, run_sature])["par_bras"]["qwen3_8b"]["verdict"] != "SIGNAL_NUL":
            tier_fails.append("sat_verdict_nul")
            print("FAIL: un bras 100 % sature n'est pas classe SIGNAL_NUL")
        # l'axe du harness CONCORDE avec la sortie de l'organe lui-meme
        # (`mesurer_fichiers`) : c'est le controle qui interdit au tableau
        # d'afficher un chiffre que l'organe ne produit pas.
        tier_total += 1
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            chemins = []
            for art in (run_sature, run_utile, run_partiel):
                chemin = Path(tmp) / f"{art['model_key']}_seed{art['seed']}.json"
                chemin.write_text(json.dumps(art), encoding="utf-8")
                chemins.append(chemin)
            sat_mod = _saturation_module()
            if sat_mod is not None:
                organe = sat_mod.mesurer_fichiers(chemins)
                axe_ref = build_saturation_axis([run_sature, run_utile, run_partiel],
                                                organe_bras=organe.get("bras"))
                if not axe_ref.get("tous_concordants"):
                    tier_fails.append("sat_concordance")
                    print("FAIL: l'axe du harness diverge de l'organe :", axe_ref["par_bras"])
            else:
                tier_fails.append("sat_organe_absent")
                print("FAIL: l'organe de saturation est introuvable")

        # le tableau markdown porte l'axe de saturation
        tier_total += 1
        md_sat = render_comparative_table({"per_model": per_model, "tiers": tbl})
        if "verdict saturation" not in md_sat:
            tier_fails.append("md_saturation")
            print("FAIL: le tableau markdown ne porte pas la colonne de saturation")

        # --- Axe « reponse au reward » (2e axe du critere 2) ----------------
        # Un batch sans dispersion de reward (`frac_reward_zero_std >= 1`) ne
        # permet aucun gradient d'advantage : c'est la panne du REWARD, et
        # elle est distincte de la panne de l'optimiseur (gradient sature).
        run_degenere = _sat_run("qwen3_8b", 3, longueur=100.0,
                                grads=[0.5] * 10, reward=0.0, zero_std=1.0)
        tier_total += 1
        axe_degenere = build_saturation_axis([run_degenere])
        bras_deg = axe_degenere.get("par_bras", {}).get("qwen3_8b", {})
        if bras_deg.get("frac_steps_sans_signal") is None \
                or abs(bras_deg["frac_steps_sans_signal"] - 1.0) > 1e-6:
            tier_fails.append("reward_sans_signal")
            print("FAIL: frac_steps_sans_signal =",
                  bras_deg.get("frac_steps_sans_signal"), "(attendu 1,0)")
        tier_total += 1
        if bras_deg.get("frac_steps_recompense_nulle") is None \
                or abs(bras_deg["frac_steps_recompense_nulle"] - 1.0) > 1e-6:
            tier_fails.append("reward_nulle")
            print("FAIL: frac_steps_recompense_nulle =",
                  bras_deg.get("frac_steps_recompense_nulle"), "(attendu 1,0)")
        # le tableau markdown porte les deux colonnes de reponse au reward
        tier_total += 1
        if "steps sans signal reward" not in md_sat or "reward nulle" not in md_sat:
            tier_fails.append("md_reward")
            print("FAIL: le tableau markdown ne porte pas les colonnes de reponse au reward")
        # garde de comparabilite du gain par step porteur : un bras dont la
        # mediane des steps porteurs de gradient vaut moins de 1 ne publie
        # pas ce gain (divise par 0,5, il doublerait un gain reel) -- meme
        # regle que l'organe. Deux graines : 0 step porteur et 1 step porteur
        # -> mediane 0,5 -> non comparable.
        tier_total += 1
        run_faible_a = _sat_run("qwen3_8b", 4, longueur=100.0, grads=[0.0],
                                pre=0.1, post=0.3)
        run_faible_b = _sat_run("qwen3_8b", 5, longueur=100.0, grads=[0.5],
                                pre=0.1, post=0.3)
        bras_faible = build_saturation_axis([run_faible_a, run_faible_b])["par_bras"]["qwen3_8b"]
        if bras_faible.get("gain_eval_par_step_avec_gradient") is not None \
                or bras_faible.get("gain_eval_par_step_comparable") is not False:
            tier_fails.append("gain_non_comparable")
            print("FAIL: un gain par step porteur non comparable est publie :",
                  bras_faible.get("gain_eval_par_step_avec_gradient"))
        # ... et il est publie quand la mediane des steps porteurs vaut 1
        tier_total += 1
        run_suffisant = _sat_run("qwen3_8b", 5, longueur=100.0, grads=[0.5] * 3,
                                 pre=0.1, post=0.3)
        bras_suffisant = build_saturation_axis([run_suffisant])["par_bras"]["qwen3_8b"]
        if bras_suffisant.get("gain_eval_par_step_avec_gradient") is None \
                or abs(bras_suffisant["gain_eval_par_step_avec_gradient"] - 0.066667) > 1e-5:
            tier_fails.append("gain_comparable")
            print("FAIL: gain par step porteur =",
                  bras_suffisant.get("gain_eval_par_step_avec_gradient"),
                  "(attendu +0,0667)")

    total_ok = n_match + n_xlam + n_guard + (2 - len(hub_fails))
    total = len(cases) + len(xlam_cases) + len(guard_cases) + 2
    if not wire_skipped:
        # le cablage compte dans le total : sinon la ligne "25/25" et le
        # "(câblage 3/3)" se contredisent et obligent a une addition mentale.
        total_ok += wire_total - len(wire_fails)
        total += wire_total
    total_ok += tier_total - len(tier_fails)
    total += tier_total
    wire_line = ("câblage NON teste" if wire_skipped
                 else f"câblage {wire_total - len(wire_fails)}/{wire_total}")
    print(f"selftest: {total_ok}/{total} pass (dapo {n_match}/{len(cases)}, "
          f"xlam {n_xlam}/{len(xlam_cases)}, garde {n_guard}/{len(guard_cases)}, "
          f"cache-hf {2 - len(hub_fails)}/2, {wire_line}, "
          f"etages {tier_total - len(tier_fails)}/{tier_total})")
    return 1 if (fails or xlam_fails or guard_fails or hub_fails or wire_fails
                 or tier_fails) else 0


def mode_baseline(model_key: str, dataset_key: str) -> dict[str, Any]:
    """Eval seule, sans training : mesure le critere d'accessibilite (#15294, condition 1).

    Evite de construire un trainer (pas besoin de train rows ni de GRPO) :
    charge le modele en 4bit et passe la boucle de generation sur le split eval.
    """
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    from transformers import BitsAndBytesConfig

    ds = DATASETS[dataset_key]
    _, eval_rows = ds["load"]()
    model_path = find_hf_snapshot(MODELS[model_key]["path_glob"])
    t0 = time.time()
    quant_cfg = BitsAndBytesConfig(
        load_in_4bit=True,
        bnb_4bit_quant_type="nf4",
        bnb_4bit_use_double_quant=True,
        bnb_4bit_compute_dtype=torch.bfloat16,
    )
    tokenizer = AutoTokenizer.from_pretrained(str(model_path))
    model = AutoModelForCausalLM.from_pretrained(
        str(model_path), quantization_config=quant_cfg, device_map="cuda",
    )
    ev = _generate_eval(model, tokenizer, eval_rows, SPLIT_SEED, match_fn=ds["match"])
    result = {
        "module": "ML-Training-Pipeline",
        "issue": 15294,
        "mode": "baseline",
        "dataset": dataset_key,
        "dataset_label": ds["label"],
        "chat_mode": "thinking" if not CHAT_KWARGS else "nonthinking",
        "max_completion_length": MAX_COMPLETION,
        "model": MODELS[model_key]["label"],
        "model_key": model_key,
        "model_path": str(model_path),
        "eval": ev,
        "wallclock_s": round(time.time() - t0, 1),
    }
    BASELINE_RESULTS.mkdir(parents=True, exist_ok=True)
    out = BASELINE_RESULTS / f"{dataset_key}_{model_key}.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"[baseline {dataset_key}/{model_key}] accessibilite={ev['reward_mean']:.4f} -> {out}")
    return result


def mode_run(model_key: str, seed: int, steps: int, smoke: bool = False,
             dataset_key: str = "dapo",
             no_signal_threshold: int = 0,
             per_device_batch: int = 8, grad_accum: int = 4) -> dict[str, Any]:
    ds = DATASETS[dataset_key]
    # Self-describing : le budget est la variable du diagnostic de troncature
    # (#15294), il doit etre lisible dans run.log a cote de clipped_ratio.
    print(f"[{model_key} seed{seed}] budget de completion = {MAX_COMPLETION} tokens")
    # La geometrie du protocole est un fait du run, pas une convention : elle
    # est ecrite dans le log ET dans le JSON, pour qu'un tiers puisse verifier
    # que le batch effectif et le round de generation n'ont pas bouge quand la
    # micro-batch a ete divisee (levier OOM de la leg 1024, #15099).
    effective = per_device_batch * grad_accum
    print(f"[{model_key} seed{seed}] geometrie : micro-batch = {per_device_batch} sequences, "
          f"accumulation = {grad_accum}, batch effectif = {effective} completions/pas, "
          f"round = {effective} completions ({effective // 8} prompts x 8 generations)")
    if effective != REFERENCE_EFFECTIVE_BATCH:
        # Garde de comparabilite : changer UN seul des deux leviers change le
        # protocole de mesure sans qu'on le voie dans le resultat. Learnes
        # explicitement, parce qu'un run non comparable ne vaut pas une
        # re-execution de plus.
        print(f"[{model_key} seed{seed}] ATTENTION protocole : batch effectif "
              f"{effective} != reference {REFERENCE_EFFECTIVE_BATCH} "
              f"(8 x 4) -- ce run n'est pas comparable au protocole de reference")
    train_rows, eval_rows = ds["load"]()
    t0 = time.time()
    trainer, model_path = build_trainer(model_key, seed, steps, train_rows,
                                        reward_fn=ds["reward"], dataset_key=dataset_key,
                                        per_device_batch=per_device_batch,
                                        grad_accum=grad_accum)
    if no_signal_threshold > 0:
        # Garde d'entree : si AUCUN des `no_signal_threshold` premiers pas ne
        # porte de gradient, le run s'arrete (option 2 de la decision de
        # protocole de la regie ai-01 sur #15293). Desactive par defaut, donc
        # le protocole des runs deja mesures reste inchange.
        trainer.add_callback(build_no_signal_guard(no_signal_threshold))
        print(f"[{model_key} seed{seed}] garde no-signal active sur "
              f"{no_signal_threshold} premiers pas")

    pre = evaluate(trainer, eval_rows, seed, match_fn=ds["match"])
    print(f"[{model_key} seed{seed}] pre-eval: {pre}")

    trainer.train()

    # Verdict du garde, recalcule sur l'historique COMPLET du trainer : c'est
    # la meme fonction pure que celle du callback, appliquee a toutes les
    # observations (le callback peut s'etre arrete avant la fin).
    observed = [e["grad_norm"] for e in trainer.state.log_history
                if e.get("grad_norm") is not None]
    verdict = no_signal_verdict(observed, no_signal_threshold)
    aborted = bool(verdict["abort"])
    verdict["grad_norms"] = [round(float(g), 6) for g in observed]

    if aborted:
        # Run mort : aucun post-eval (le GPU est encore plus precieux que la
        # mesure), et l'artefact porte le verdict. mode_summarize exclut ces
        # runs des deltas -- un run sans signal ne doit pas entrer dans une
        # moyenne d'eval, sous peine de la fausser.
        post = None
        print(f"[{model_key} seed{seed}] ARRET no-signal : "
              f"{verdict['steps_observed']} pas observes, "
              f"{verdict['steps_alive']} pas porteurs de gradient "
              f"(aucun post-eval mesure)")
    else:
        post = evaluate(trainer, eval_rows, seed, match_fn=ds["match"])
        print(f"[{model_key} seed{seed}] post-eval: {post}")

    run_dir = RUNS_ROOT / f"{model_key}_{dataset_key}_seed{seed}"
    adapter_dir = run_dir / "adapter"
    if not aborted:
        # Un run arrete par la garde n'a rien a sauver : l'adapter d'un run qui
        # n'a porte aucun gradient n'a aucune valeur (et l'ecriture coute du
        # temps machine). Les runs complets, eux, le sauvent comme avant.
        trainer.model.save_pretrained(str(adapter_dir))
        trainer.processing_class.save_pretrained(str(adapter_dir))

    log_history = [
        {k: v for k, v in entry.items() if not k.startswith("_")}
        for entry in trainer.state.log_history
    ]
    result = {
        "module": "ML-Training-Pipeline",
        "issue": 15099 if dataset_key == "dapo" else 15294,
        "dataset": dataset_key,
        "dataset_label": ds["label"],
        "chat_mode": "thinking" if not CHAT_KWARGS else "nonthinking",
        "max_completion_length": MAX_COMPLETION,
        # Geometrie du protocole : elle dit ce que le run a mesure. Une
        # micro-batch divisee ne doit pas se lire comme un protocole change.
        "per_device_train_batch_size": per_device_batch,
        "gradient_accumulation_steps": grad_accum,
        "effective_completions_per_step": effective,
        "generation_batch_size": effective,
        "model": MODELS[model_key]["label"],
        "model_key": model_key,
        "seed": seed,
        "max_steps": steps,
        "model_path": str(model_path),
        "pre_eval": pre,
        "post_eval": post,
        # Verdict de la garde d'entree : `aborted` distingue un run qui a
        # porte un gradient d'un run termine sans signal (le `rc=0` seul ne
        # dit rien du signal -- cf no_signal_verdict).
        "aborted": aborted,
        "no_signal_guard": verdict,
        "log_history": log_history,
        "wallclock_s": round(time.time() - t0, 1),
    }
    out_dir = RUNS_ROOT if smoke else (REPO_RESULTS if dataset_key == "dapo"
                                       else REPO_RESULTS.parent / f"p15294_{dataset_key}_grpo")
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / f"{model_key}_seed{seed}{'_smoke' if smoke else ''}.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"result -> {out}")
    return result


def _saturation_module() -> Any:
    """L'organe de saturation, ou None s'il est introuvable.

    ORGANE-FIRST : la mesure de la saturation du budget et ses seuils
    appartiennent a `scripts/analyse_dapo_saturation.py`. On l'**appelle**,
    on ne le reecrit pas : une copie divergerait en silence et le tableau
    comparatif afficherait des seuils que personne ne pourrait refaire.
    """
    try:
        import analyse_dapo_saturation  # noqa: PLC0415  (import tardif volontaire)
        return analyse_dapo_saturation
    except Exception:
        dossier = str(Path(__file__).resolve().parent)
        if dossier not in sys.path:
            sys.path.insert(0, dossier)
        try:
            import analyse_dapo_saturation  # noqa: PLC0415
            return analyse_dapo_saturation
        except Exception:
            return None


def build_saturation_axis(runs: list[dict[str, Any]],
                          organe_bras: dict[str, Any] | None = None) -> dict[str, Any]:
    """Axe « saturation » du tableau comparatif (#15293, critere 2).

    Les trois axes demandes par l'issue sont « trainabilite, reponse au
    reward, saturation » : les deux premiers sortent de l'eval (pre/post),
    le troisieme sort de l'**organe** `analyse_dapo_saturation.py`, qui
    mesure la fraction de steps saturees (completions tronquees au budget) et
    le verdict par bras.

    Regle de l'organe, reprise telle quelle : les seuils s'appliquent au
    **BRAS** (le `model_key`), pas au lot de fichiers passe en argument. Le
    verdict est donc reporte par bras et **jamais fusionne entre etages**.

    L'agregat d'un bras est la **MEDIANE** de ses graines (regle de l'organe :
    « le bras suit la graine mediane »), pas la moyenne : pour le bras 8B,
    0,64 / 0,65 / 0,83 -> mediane 0,65, moyenne 0,71. Une moyenne afficherait
    un chiffre que l'organe ne produit pas -- d'ou la comparaison explicite
    avec `organe_bras` (la sortie de l'organe lui-meme), et le drapeau
    `concordant` qui dit si les deux concordent.

    FONCTION PURE du point de vue des tests : elle ne lit ni disque ni GPU.
    """
    sat = _saturation_module()
    if sat is None:
        return {"disponible": False,
                "raison": "organe analyse_dapo_saturation introuvable"}
    par_bras: dict[str, list[dict[str, Any]]] = {}
    for run in runs:
        rapport = sat.mesurer(run)
        cle = rapport.get("model_key") or "?"
        par_bras.setdefault(cle, []).append(rapport)
    axes: dict[str, Any] = {}
    for model_key, graines in par_bras.items():
        graines = sorted(graines, key=lambda g: (g.get("graine") is None, g.get("graine")))
        frac = [g.get("frac_steps_satures") for g in graines
                if isinstance(g.get("frac_steps_satures"), (int, float))]
        sans_grad = [g.get("frac_steps_sans_gradient") for g in graines
                     if isinstance(g.get("frac_steps_sans_gradient"), (int, float))]
        vivantes = [g.get("steps_avec_gradient") for g in graines
                    if isinstance(g.get("steps_avec_gradient"), (int, float))]
        # --- Axe « reponse au reward » -------------------------------------
        # Mesures de l'ORGANE, jamais recalculees ici :
        #  - `frac_steps_sans_signal`     : steps dont le batch de reward n'a
        #    aucune dispersion (`frac_reward_zero_std >= 1`) -> aucun gradient
        #    d Advantage possible : le modele ne peut rien apprendre de ce
        #    step, meme si le gradient existe ;
        #  - `frac_steps_recompense_nulle`: steps dont la reward moyenne est
        #    nulle (le modele ne produit aucune reponse correcte) ;
        #  - `gain_eval_par_step_avec_gradient` : gain d'eval **normalise** par
        #    le nombre de steps porteurs de gradient -- sans quoi un bras qui
        #    n'a appris que sur 2 steps parait comparable a un bras qui en a
        #    appris sur 24 (le point 51 de l'organe).
        # Ces trois grandeurs separent deux pannes distinctes : celle de
        # l'OPTIMISEUR (le gradient sature) et celle du REWARD (le batch est
        # degenere). Le tableau ne les confondait pas.
        sans_signal = [g.get("frac_steps_sans_signal") for g in graines
                       if isinstance(g.get("frac_steps_sans_signal"), (int, float))]
        recompense_nulle = [g.get("frac_steps_recompense_nulle") for g in graines
                            if isinstance(g.get("frac_steps_recompense_nulle"), (int, float))]
        gain_normalise = [g.get("gain_eval_par_step_avec_gradient") for g in graines
                          if isinstance(g.get("gain_eval_par_step_avec_gradient"), (int, float))]
        # Meme garde de comparabilite que l'organe : le gain par step porteur
        # n'est publie que si la MEDIANE des steps porteurs de gradient vaut au
        # moins 1 (divise par 0,5, il doublerait un gain reel). Sans cette
        # garde, l'axe afficherait un chiffre que l'organe refuse de publier.
        median_vivantes = statistics.median(vivantes) if vivantes else None
        comparable_gain = median_vivantes is not None and median_vivantes >= 1
        axes[model_key] = {
            "verdict": sat.verdict_bras(graines),
            "n_seeds": len(graines),
            "graines_ids": [g.get("graine") for g in graines],
            "frac_steps_satures": round(statistics.median(frac), 4) if frac else None,
            "frac_steps_sans_gradient": (round(statistics.median(sans_grad), 4)
                                         if sans_grad else None),
            "frac_steps_sans_signal": (round(statistics.median(sans_signal), 4)
                                       if sans_signal else None),
            "frac_steps_recompense_nulle": (round(statistics.median(recompense_nulle), 4)
                                            if recompense_nulle else None),
            "gain_eval_par_step_avec_gradient": (
                round(statistics.median(gain_normalise), 6)
                if gain_normalise and comparable_gain else None),
            "gain_eval_par_step_comparable": bool(comparable_gain),
            # MEDIANE comme l'organe (sans arrondi : sur deux graines elle
            # vaut 1,5 -- un entier l'aurait transforme en 1 et aurait fait
            # diverger l'axe de la sortie de l'organe).
            "steps_avec_gradient": statistics.median(vivantes) if vivantes else None,
            "graines": [
                {"graine": g.get("graine"), "verdict": g.get("verdict"),
                 "frac_steps_satures": g.get("frac_steps_satures"),
                 "frac_steps_sans_gradient": g.get("frac_steps_sans_gradient"),
                 "frac_steps_sans_signal": g.get("frac_steps_sans_signal"),
                 "frac_steps_recompense_nulle": g.get("frac_steps_recompense_nulle"),
                 "steps_avec_gradient": g.get("steps_avec_gradient")}
                for g in graines],
        }
        if organe_bras and model_key in organe_bras:
            reference = organe_bras[model_key]
            axes[model_key]["organe"] = {
                cle: reference.get(cle) for cle in
                ("verdict", "frac_steps_satures", "frac_steps_sans_gradient",
                 "steps_avec_gradient", "gain_eval_par_step_avec_gradient")}
            axes[model_key]["concordant"] = bool(
                reference.get("verdict") == axes[model_key]["verdict"]
                and reference.get("frac_steps_satures") == axes[model_key]["frac_steps_satures"]
                and reference.get("steps_avec_gradient") == axes[model_key]["steps_avec_gradient"]
                and reference.get("gain_eval_par_step_avec_gradient")
                == axes[model_key]["gain_eval_par_step_avec_gradient"])
    return {"disponible": True, "par_bras": axes,
            "source": "scripts/analyse_dapo_saturation.py",
            "tous_concordants": all(a.get("concordant") for a in axes.values())
            if axes else None,
            # Les deux mesures de reponse au reward (`frac_steps_sans_signal`,
            # `frac_steps_recompense_nulle`) viennent de l'ORGANE graine par
            # graine, mais son agregat par bras ne les publie pas : il n'y a
            # donc aucune reference contre laquelle comparer. Elles sont
            # agregees ici avec la MEME regle de mediane que l'organe, et le
            # tableau les presente comme des mesures de l'organe, pas comme
            # un calcul du harness.
            "reponse_au_reward_agreggee_par_l_organe": True}


def _mean_optional(values: list[Any]) -> float | None:
    """Moyenne des valeurs numeriques non nulles ; None si aucune.

    Distincte d'une moyenne sur 0 : « on ne sait pas » et « zero » ne sont
    pas le meme chiffre, et un tableau qui affiche 0,0000 la ou la mesure
    n'existe pas invente une mesure.
    """
    nums = [float(v) for v in values if isinstance(v, (int, float))]
    if not nums:
        return None
    return sum(nums) / len(nums)


def build_tier_table(per_model: dict[str, dict[str, Any]],
                     healthy: dict[str, bool]) -> dict[str, Any]:
    """Tableau comparatif par etage de taille (#15293).

    FONCTION PURE : elle ne lit ni disque ni GPU, donc elle se teste dans
    `selftest` sans attendre un run de plusieurs heures de GPU.

    per_model : {model_key: {"delta_mean", "delta_std", "deltas", "n_seeds", ...}}
    healthy   : {model_key: bool} -- "courbes saines" (post > pre sur chaque
                graine, pas d'effondrement de longueur), verdict de l'analyse
                de courbes.

    Le critere de l'issue est un COMPARATIF d'etages (0.8B/2B vs 8-9B), pas
    une comparaison de paires de modeles : la table par etage est donc
    calculee par-dessus `per_model`, et le verdict inter-etage suit la meme
    regle que la regle par paires (intervalles +-1 std disjoints + courbes
    saines), sans la reecrire.
    """
    tiers: dict[str, Any] = {}
    for tier in TIERS:
        keys = [k for k in sorted(per_model)
                if MODELS.get(k, {}).get("tier") == tier]
        if not keys:
            continue
        pooled: list[float] = []
        for k in keys:
            pooled.extend(per_model[k].get("deltas", []))
        n = len(pooled)
        mean = (sum(pooled) / n) if n else 0.0
        std = ((sum((d - mean) ** 2 for d in pooled) / n) ** 0.5) if n else 0.0
        tiers[tier] = {
            "models": keys,
            "n_models": len(keys),
            "n_seeds": n,
            "delta_mean": mean,
            "delta_std": std,
            "per_model_delta_mean": {k: per_model[k]["delta_mean"] for k in keys},
            "courbes_saines": {k: bool(healthy.get(k, False)) for k in keys},
            "toutes_courbes_saines": all(bool(healthy.get(k, False)) for k in keys),
            "saturation": {
                # Le VERDICT de saturation est par BRAS (regle de l'organe) :
                # il est reporte, jamais fusionne. Seule la fraction des
                # branches est moyennee sur l'etage -- et cette moyenne est
                # nommee comme telle (elle n'est pas un chiffre de l'organe).
                "par_bras": {k: (per_model[k].get("saturation") or {}) for k in keys},
                "frac_satures_moyenne_bras": _mean_optional([
                    ((per_model[k].get("saturation") or {}).get("frac_steps_satures"))
                    for k in keys]),
            },
        }
    cross: dict[str, Any] = {
        "comparable": False,
        "regle": ("comparaison inter-etage : deux etages, >= 2 graines chacun, "
                  "delta moyen de l'etage haut > etage bas avec intervalles "
                  "+-1 std disjoints, et courbes saines des deux cotes"),
    }
    if len(tiers) == 2:
        bas, haut = TIERS
        tb, th = tiers[bas], tiers[haut]
        # Disjointness of CLOSED intervals: two intervals that only touch are
        # NOT disjoint. The strict `>` alone is decided by float noise
        # (0.025-0.005 = 0.020000000000000004 > 0.015+0.005 = 0.02 -> True),
        # so the separation is compared with a relative epsilon. The legacy
        # per-pair rule (identical formula, no epsilon) is left untouched on
        # purpose: the historical verdict must not move.
        hi = th["delta_mean"] - th["delta_std"]
        lo = tb["delta_mean"] + tb["delta_std"]
        eps = 1e-9 * max(1.0, abs(hi), abs(lo))
        disjoint = hi > lo + eps
        seeds_ok = tb["n_seeds"] >= 2 and th["n_seeds"] >= 2
        cross = {
            "comparable": bool(seeds_ok),
            "tier_bas": bas,
            "tier_haut": haut,
            "n_seeds": {bas: tb["n_seeds"], haut: th["n_seeds"]},
            "delta_intervals_disjoint": bool(disjoint),
            "beats": bool(th["toutes_courbes_saines"]
                          and tb["toutes_courbes_saines"] and disjoint),
            "regle": cross["regle"],
        }
    return {"tiers": tiers, "cross_tier": cross}


def render_comparative_table(summary: dict[str, Any]) -> str:
    """Rend le tableau comparatif en markdown (critere "tableau comparatif"
    de #15293) : une ligne par modele, puis le verdict inter-etage.

    Les trois axes demandes par l'issue sont dans le tableau :
    trainabilite (delta eval, et gain **normalise** par step porteur),
    reponse au reward (fraction de steps dont le batch **n'a aucune
    dispersion de reward** -> aucun gradient d'Advantage possible, et
    fraction de steps a recompense nulle), et saturation (fraction de steps
    saturees + verdict PAR BRAS). Les trois viennent de l'organe
    `analyse_dapo_saturation.py` : le harness ne recalcule aucun seuil.
    """
    lines = ["| Modele | Etage | Graines | eval pre | eval post | delta | +- 1 std | courbes saines | steps satures | verdict saturation | steps sans signal reward | reward nulle | gain/step porteuse |",
             "|---|---|---:|---:|---:|---:|---:|---|---:|---|---:|---:|---:|"]
    tiers = summary.get("tiers", {}).get("tiers", {})
    for tier in TIERS:
        t = tiers.get(tier)
        if not t:
            continue
        sat_bras = (t.get("saturation") or {}).get("par_bras", {})
        for k in t["models"]:
            pm = summary["per_model"][k]
            sat = sat_bras.get(k) or {}
            frac = sat.get("frac_steps_satures")
            sans_signal = sat.get("frac_steps_sans_signal")
            reward_nulle = sat.get("frac_steps_recompense_nulle")
            gain_step = sat.get("gain_eval_par_step_avec_gradient")
            lines.append(
                f"| {pm['label']} | {tier} | {pm['n_seeds']} | "
                f"{pm['pre_mean']:.4f} | {pm['post_mean']:.4f} | "
                f"{pm['delta_mean']:+.4f} | {pm['delta_std']:.4f} | "
                f"{'oui' if t['courbes_saines'].get(k) else 'non'} | "
                f"{'n.d.' if frac is None else format(frac, '.2f')} | "
                f"{sat.get('verdict', 'n.d.')} | "
                f"{'n.d.' if sans_signal is None else format(sans_signal, '.2f')} | "
                f"{'n.d.' if reward_nulle is None else format(reward_nulle, '.2f')} | "
                f"{'n.d.' if gain_step is None else format(gain_step, '+.4f')} |")
        frac_tier = (t.get("saturation") or {}).get("frac_satures_moyenne_bras")
        lines.append(f"| **moyenne etage {tier}** | {tier} | {t['n_seeds']} | | | "
                     f"{t['delta_mean']:+.4f} | {t['delta_std']:.4f} | "
                     f"{'oui' if t['toutes_courbes_saines'] else 'non'} | "
                     f"{'n.d.' if frac_tier is None else format(frac_tier, '.2f')} | "
                     f"moyenne sur les bras | | | |")
    cross = summary.get("tiers", {}).get("cross_tier", {})
    lines.append("")
    lines.append(f"Verdict inter-etage ({cross.get('tier_bas', '?')} vs "
                 f"{cross.get('tier_haut', '?')}) : "
                 f"comparable={cross.get('comparable')} · "
                 f"intervalles disjoints={cross.get('delta_intervals_disjoint')} · "
                 f"BEATS={cross.get('beats')}.")
    lines.append("")
    lines.append(f"Regle : {cross.get('regle', '')}")
    lines.append("")
    lines.append("Saturation : `steps satures` est la fraction **mediane** (par "
                 "bras) de steps tronquees au budget de completion, mesuree par "
                 "l'organe `scripts/analyse_dapo_saturation.py` ; le verdict est "
                 "**par bras** (le seuil s'applique au bras, pas au lot de "
                 "graines) et n'est donc pas fusionne entre etages. La ligne "
                 "d'etage est une moyenne de branches, pas un chiffre de "
                 "l'organe.")
    lines.append("")
    lines.append("Reponse au reward : `steps sans signal reward` est la fraction "
                 "de steps dont le batch de reward n'a **aucune dispersion** "
                 "(`frac_reward_zero_std >= 1`) : l'algorithme d Advantage n'a "
                 "rien a y comparer, donc **aucun gradient d'advantage n'y est "
                 "possible** meme si le gradient existe. C'est la panne du "
                 "REWARD, distincte de la panne de l'OPTIMISEUR (le gradient "
                 "sature). `reward nulle` est la fraction de steps dont la "
                 "reward moyenne est nulle (aucune reponse correcte). "
                 "`gain/step porteuse` est le gain d'eval divise par le nombre "
                 "de steps porteurs de gradient, avec la meme garde de "
                 "comparabilite que l'organe (non publie si la mediane des "
                 "steps porteurs vaut moins de 1).")
    return "\n".join(lines) + "\n"


def classify_run(name: str, run: dict[str, Any]) -> str:
    """Classe un run pour l'agregation du `summarize`.

    FONCTION PURE (testable sans GPU).

    - "aborted"  : arret par la garde d'entree (aucun gradient porte) ;
    - "smoke"    : boucle de validation courte (`_smoke`), budget de pas
                   different -> son post-eval n'est pas comparable ;
    - "partiel"  : run interrompu avant le budget complet ;
    - "seed"     : une graine du protocole, la seule comparable ;
    - "exclu"    : budget de pas absent ou invalide, donc incomparable.

    La classification est fail-closed : sans budget entier strictement positif,
    aucune valeur par defaut ne peut faire passer un run pour une graine.

    Pourquoi la distinction compte : un smoke de 3 pas a un delta de 0 PAR
    CONSTRUCTION (post-eval apres 3 pas d'entrainement), et le compter comme
    une graine dilue le delta de son bras -- et, par etage, le verdict
    entier. Un smoke se compte, il ne se melange pas.
    """
    if run.get("aborted") is True:
        return "aborted"
    if "_smoke" in name:
        return "smoke"
    try:
        steps = int(run["max_steps"])
    except (KeyError, TypeError, ValueError):
        return "exclu"
    if steps <= 0:
        return "exclu"
    if steps < MAX_STEPS:
        return "partiel"
    return "seed"


def mode_summarize(dataset_key: str = "dapo") -> int:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    # Meme regle de repertoire que mode run (l.689) : le mode run ecrit deja
    # dans p15294_<dataset>_grpo, mais summarize ne lisait que REPO_RESULTS
    # (m19_minicpm5_grpo, dataset dapo) -- le verdict de paire hermes (#15294)
    # etait inaccessible sans wrapper qui patche la constante.
    results_dir = (REPO_RESULTS if dataset_key == "dapo"
                   else REPO_RESULTS.parent / f"p15294_{dataset_key}_grpo")
    runs = sorted(results_dir.glob("*_seed*.json"))
    if not runs:
        print("aucun run trouve dans", results_dir)
        return 1
    loaded = [(p.name, json.loads(p.read_text(encoding="utf-8"))) for p in runs]
    # Un run arrete par la garde d'entree n'a pas de post-eval : il porte ZERO
    # signal (aucun gradient n'a passe sur les premiers pas) et n'a donc rien
    # a dire sur l'eval. L'inclure dans les deltas fausserait la moyenne --
    # on le liste a part, et on ne calcule que sur les runs scores.
    # Un run sans post-eval mais SANS le drapeau `aborted` (run interrompu pour
    # une autre raison) reste distingue : il n'a pas ete arrete par la garde.
    aborted_runs = [r for _n, r in loaded if r.get("aborted") is True]
    incomplete_runs = [r for _n, r in loaded
                       if r.get("post_eval") is None and r.get("aborted") is not True]
    # Smoke et runs partiels : ils se COMPTENT (liste dediee) mais ne se
    # MELANGENT pas aux graines -- voir `classify_run`.
    smoke_runs = [r for n, r in loaded if classify_run(n, r) == "smoke"]
    partial_runs = [r for n, r in loaded if classify_run(n, r) == "partiel"]
    scored = [r for n, r in loaded
              if classify_run(n, r) == "seed" and r.get("post_eval") is not None]
    by_model: dict[str, list[dict[str, Any]]] = {}
    for r in scored:
        by_model.setdefault(r["model_key"], []).append(r)

    summary: dict[str, Any] = {"runs": [r["model_key"] + f"_seed{r['seed']}" for _n, r in loaded],
                               "aborted_runs": [
                                   {"model_key": r["model_key"], "seed": r["seed"],
                                    "reason": (r.get("no_signal_guard") or {}).get("reason", ""),
                                    "steps_observed": (r.get("no_signal_guard") or {}).get("steps_observed", 0),
                                    "steps_alive": (r.get("no_signal_guard") or {}).get("steps_alive", 0)}
                                   for r in aborted_runs],
                               "runs_sans_post_eval": [
                                   {"model_key": r["model_key"], "seed": r["seed"]}
                                   for r in incomplete_runs],
                               "runs_smoke": [
                                   {"model_key": r["model_key"], "seed": r["seed"],
                                    "max_steps": r.get("max_steps")}
                                   for r in smoke_runs],
                               "runs_partiels": [
                                   {"model_key": r["model_key"], "seed": r["seed"],
                                    "max_steps": r.get("max_steps")}
                                   for r in partial_runs],
                               "per_model": {}, "verdict": None}
    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5))
    # Le trainer nomme la serie d'apres la fn de reward : dapo/gsm8k loggent
    # rewards/dapo_reward/mean, hermes/xlam loggent rewards/xlam_reward/mean.
    # La cle codee en dur (dapo) faisait echouer le plot sur un dir hermes
    # (steps_r vide vs 100 longueurs de completion -> ValueError matplotlib).
    reward_key = f"rewards/{DATASETS[dataset_key]['reward'].__name__}/mean"
    for model_key, rs in by_model.items():
        deltas = [r["post_eval"]["reward_mean"] - r["pre_eval"]["reward_mean"] for r in rs]
        pre = [r["pre_eval"]["reward_mean"] for r in rs]
        post = [r["post_eval"]["reward_mean"] for r in rs]
        mean_d = sum(deltas) / len(deltas)
        std_d = (sum((d - mean_d) ** 2 for d in deltas) / len(deltas)) ** 0.5
        summary["per_model"][model_key] = {
            "label": MODELS[model_key]["label"],
            "n_seeds": len(rs),
            "pre_mean": sum(pre) / len(pre),
            "post_mean": sum(post) / len(post),
            "delta_mean": mean_d,
            "delta_std": std_d,
            "deltas": deltas,
        }
        for r in rs:
            steps_r = [e["step"] for e in r["log_history"] if reward_key in e]
            rew = [e[reward_key] for e in r["log_history"]
                   if reward_key in e]
            ln = [e["completions/mean_length"] for e in r["log_history"]
                  if "completions/mean_length" in e]
            axes[0].plot(steps_r, rew, alpha=0.7, label=f"{model_key} s{r['seed']}")
            axes[1].plot(steps_r[: len(ln)], ln, alpha=0.7)
    axes[0].set_title(f"Reward train ({reward_key})")
    axes[0].set_xlabel("step")
    axes[1].set_title("Longueur moyenne des completions")
    axes[1].set_xlabel("step")
    axes[0].legend(fontsize=7)

    # Axe « saturation » (3e axe du critere 2 de #15293) : il est MESURE par
    # l'organe `scripts/analyse_dapo_saturation.py`, qui possede les seuils et
    # la regle « le verdict est par bras ». On consomme l'organe, on ne le
    # reecrit pas -- ni ses seuils, ni son verdict.
    saturation = build_saturation_axis(scored)
    # La sortie de l'organe est relue et COMPAREE : si l'agregat du harness et
    # celui de l'organe divergent, le tableau le dit (`concordant: false`)
    # au lieu d'afficher un chiffre que personne ne peut refaire.
    sat_mod = _saturation_module()
    if sat_mod is not None:
        noms_scores = {n for n, r in loaded
                       if classify_run(n, r) == "seed" and r.get("post_eval") is not None}
        organe = sat_mod.mesurer_fichiers([p for p in runs if p.name in noms_scores])
        saturation = build_saturation_axis(scored, organe_bras=organe.get("bras"))
    summary["saturation"] = saturation
    if saturation.get("disponible"):
        for model_key, axis in saturation["par_bras"].items():
            if model_key in summary["per_model"]:
                summary["per_model"][model_key]["saturation"] = axis

    def curves_healthy(model_key: str) -> bool:
        rl = [r for r in scored if r["model_key"] == model_key]
        improved = all(r["post_eval"]["reward_mean"] > r["pre_eval"]["reward_mean"] for r in rl)
        def seg(vals):
            n = len(vals)
            return (sum(vals[: n // 4]) / max(1, n // 4), sum(vals[-n // 4:]) / max(1, n // 4))
        no_collapse = True
        for r in rl:
            ln = [e["completions/mean_length"] for e in r["log_history"]
                  if "completions/mean_length" in e]
            if ln:
                a, b = seg(ln)
                if b < 0.8 * a:  # effondrement de longueur > 20 %
                    no_collapse = False
        return improved and no_collapse

    health = {k: curves_healthy(k) for k in summary["per_model"]}

    # Tableau comparatif par ETAGE de taille (#15293) : le critere de l'issue
    # est un comparatif "0.8B/2B vs 8-9B", pas une liste de paires de modeles.
    # La table est pure (aucun GPU) -> elle se teste dans `selftest`.
    summary["tiers"] = build_tier_table(summary["per_model"], health)

    if len(summary["per_model"]) >= 2:
        # La comparaison est desormais N-aire : #15293 demande de rejouer le
        # harnais au-dela de 2B et de dire si le classement tient a cette
        # echelle. Une paire codee en dur interdisait de lire l'etage >= 8-9B.
        pairs: dict[str, Any] = {}
        for a, b in itertools.combinations(sorted(summary["per_model"]), 2):
            pa, pb = summary["per_model"][a], summary["per_model"][b]
            disjoint = (pa["delta_mean"] - pa["delta_std"]
                        > pb["delta_mean"] + pb["delta_std"])
            pairs[f"{a}_vs_{b}"] = {
                "curves_healthy": {a: health[a], b: health[b]},
                "delta_intervals_disjoint": disjoint,
                "beats": bool(health[a] and disjoint),
                "higher_delta": a if pa["delta_mean"] > pb["delta_mean"] else b,
                "rule": (f"BEATS si courbes {MODELS[a]['label']} saines (post>pre par seed, "
                         "pas d'effondrement de longueur) ET delta eval moyen > "
                         f"{MODELS[b]['label']} avec intervalles +-1std disjoints (>=2 seeds par modele)"),
            }
        summary["pairs"] = pairs

        # Forme historique conservee telle quelle (m19) : la re-execution du
        # summarize sur les runs deja committes doit rendre le meme verdict.
        if "minicpm5_vs_qwen35" in pairs:
            legacy = pairs["minicpm5_vs_qwen35"]
            summary["verdict"] = {
                "mini_curves_healthy": health["minicpm5"],
                "qwen_curves_healthy": health["qwen35"],
                "delta_intervals_disjoint": legacy["delta_intervals_disjoint"],
                "beats": legacy["beats"],
                "rule": ("BEATS si courbes MiniCPM5 saines (post>pre par seed, pas d'effondrement de longueur) "
                         "ET delta eval moyen > qwen avec intervalles ±1std disjoints (≥2 seeds par modèle)"),
            }
    fig.tight_layout()
    png = results_dir / "curves.png"
    fig.savefig(png, dpi=130)
    summary_json = results_dir / "summary.json"
    summary_json.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    # Le tableau comparatif en markdown est un livrable de l'issue (#15293) :
    # il est ecrit a cote du JSON, pas calcule a la main.
    table_md = results_dir / "tableau_comparatif.md"
    # newline explicite : sans lui, l'ecriture texte de Windows convertit les
    # \n en \r\n et l'artefact differe d'une machine a l'autre (churn CRLF/LF
    # dans le diff du depot).
    table_md.write_text(render_comparative_table(summary), encoding="utf-8",
                        newline="\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "runs"}, indent=2)[:1500])
    print(f"courbes -> {png} | summary -> {summary_json} | tableau -> {table_md}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("mode", choices=["selftest", "smoke", "run", "summarize", "baseline"])
    ap.add_argument("--model", choices=list(MODELS), default="minicpm5")
    ap.add_argument("--dataset", choices=list(DATASETS), default="dapo",
                    help="jeu de donnees (dapo = probe B #15099 inchangee)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--steps", type=int, default=MAX_STEPS)
    ap.add_argument(
        "--thinking",
        action="store_true",
        help="mode thinking (enable_thinking=True laisse au template, budget completion 1024)",
    )
    ap.add_argument(
        "--max-completion",
        type=int,
        default=None,
        help="budget de completion en tokens (defaut : 384 non-thinking, 1024 avec --thinking) ; "
             "pilote clipped_ratio (fraction de completions tronquees) et, via "
             "mask_truncated_completions, la part du loss qui survit",
    )
    ap.add_argument(
        "--abort-if-no-signal",
        type=int,
        default=0,
        help="garde d'entree : abandonner l'entrainement si AUCUN des N premiers "
             "pas n'a porte de gradient (grad_norm > 0). 0 = desactive, protocole "
             "inchange. Option 2 de la decision de protocole (#15293) : une graine "
             "nee morte coute des heures de GPU sans rien produire -- sur la graine "
             "42 du bras 8B, la garde aurait arrete le run en quelques minutes au "
             "lieu de 6 h 30.",
    )
    ap.add_argument(
        "--per-device-batch",
        type=int,
        default=8,
        help="micro-batch en sequences par forward/backward (defaut : 8). "
             "Diviser ce nombre divise le tenseur de logits du backward ; "
             "pour que la MESURE ne bouge pas, il faut doubler --grad-accum "
             "en meme temps (batch effectif et round de generation inchanges).",
    )
    ap.add_argument(
        "--grad-accum",
        type=int,
        default=4,
        help="accumulation de gradient (defaut : 4). Le batch effectif par "
             "pas d'optimiseur vaut --per-device-batch x --grad-accum ; "
             "le round de generation vaut le meme produit (4 prompts x 8 "
             "generations a 8 x 4).",
    )
    args = ap.parse_args()

    global MAX_COMPLETION
    if not args.thinking:
        CHAT_KWARGS.clear()
        CHAT_KWARGS["enable_thinking"] = False
    else:
        MAX_COMPLETION = 1024
    if args.max_completion is not None:
        # Le budget n'est pas cosmetique : avec mask_truncated_completions=True,
        # une completion qui atteint la borne est RETIREE du loss (#15294 : a
        # 384 tokens, clipped_ratio ~0.94-0.97 laissait un signal quasi nul).
        # Parametrable, le balayage du budget est une commande, pas une edition
        # du source a chaque point de diagnostic.
        MAX_COMPLETION = args.max_completion

    if args.mode == "selftest":
        return mode_selftest()
    if args.mode == "summarize":
        return mode_summarize(args.dataset)
    if args.mode == "baseline":
        mode_baseline(args.model, args.dataset)
        return 0
    steps = 3 if args.mode == "smoke" else args.steps
    global EVAL_N_PROMPTS, TRAIN_POOL
    if args.mode == "smoke":
        EVAL_N_PROMPTS, TRAIN_POOL = 8, 16
    RUNS_ROOT.mkdir(parents=True, exist_ok=True)
    mode_run(args.model, args.seed, steps, smoke=args.mode == "smoke",
             dataset_key=args.dataset,
             no_signal_threshold=args.abort_if_no_signal,
             per_device_batch=args.per_device_batch,
             grad_accum=args.grad_accum)
    return 0


if __name__ == "__main__":
    sys.exit(main())
