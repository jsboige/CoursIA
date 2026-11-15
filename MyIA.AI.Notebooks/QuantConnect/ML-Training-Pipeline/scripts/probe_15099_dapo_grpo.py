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
    },
    "qwen35": {
        "path_glob": "models--Qwen--Qwen3.5-0.8B/snapshots/*",
        "label": "Qwen3.5-0.8B",
    },
    # Etage >= 8-9B demande par #15293 (review user de #15249 : le casting
    # 0.8B/2B est errone pour un exercice de raisonnement mathematique).
    # Poids deja en cache local sur po-2024 — l'arm ne demande aucun
    # telechargement, ce que la disponibilite intermittente de huggingface.co
    # rend necessaire (cf corps de PR).
    "qwen3_8b": {
        "path_glob": "models--Qwen--Qwen3-8B/snapshots/*",
        "label": "Qwen3-8B",
    },
    # Second backbone de l'etage >= 8-9B (#15293), sur le GPU 2 d'ai-01.
    # Le glob suit le depot HF `Qwen/Qwen3-14B` (instruct, non-Base) : c'est
    # le nom annonce par ai-01 dans le DM du 2026-10-05. Les poids sont
    # telecharges par la machine qui execute (ai-01), pas par po-2024.
    "qwen3_14b": {
        "path_glob": "models--Qwen--Qwen3-14B/snapshots/*",
        "label": "Qwen3-14B",
    },
}


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
        per_device_train_batch_size=8,
        gradient_accumulation_steps=4,  # 32 completions/step = 4 prompts x 8 generations
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

    total_ok = n_match + n_xlam + n_guard + (2 - len(hub_fails))
    total = len(cases) + len(xlam_cases) + len(guard_cases) + 2
    if not wire_skipped:
        # le cablage compte dans le total : sinon la ligne "25/25" et le
        # "(câblage 3/3)" se contredisent et obligent a une addition mentale.
        total_ok += wire_total - len(wire_fails)
        total += wire_total
    wire_line = ("câblage NON teste" if wire_skipped
                 else f"câblage {wire_total - len(wire_fails)}/{wire_total}")
    print(f"selftest: {total_ok}/{total} pass (dapo {n_match}/{len(cases)}, "
          f"xlam {n_xlam}/{len(xlam_cases)}, garde {n_guard}/{len(guard_cases)}, "
          f"cache-hf {2 - len(hub_fails)}/2, {wire_line})")
    return 1 if (fails or xlam_fails or guard_fails or hub_fails or wire_fails) else 0


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
             no_signal_threshold: int = 0) -> dict[str, Any]:
    ds = DATASETS[dataset_key]
    # Self-describing : le budget est la variable du diagnostic de troncature
    # (#15294), il doit etre lisible dans run.log a cote de clipped_ratio.
    print(f"[{model_key} seed{seed}] budget de completion = {MAX_COMPLETION} tokens")
    train_rows, eval_rows = ds["load"]()
    t0 = time.time()
    trainer, model_path = build_trainer(model_key, seed, steps, train_rows,
                                        reward_fn=ds["reward"], dataset_key=dataset_key)
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
    loaded = [json.loads(p.read_text(encoding="utf-8")) for p in runs]
    # Un run arrete par la garde d'entree n'a pas de post-eval : il porte ZERO
    # signal (aucun gradient n'a passe sur les premiers pas) et n'a donc rien
    # a dire sur l'eval. L'inclure dans les deltas fausserait la moyenne --
    # on le liste a part, et on ne calcule que sur les runs scores.
    # Un run sans post-eval mais SANS le drapeau `aborted` (run interrompu pour
    # une autre raison) reste distingue : il n'a pas ete arrete par la garde.
    aborted_runs = [r for r in loaded if r.get("aborted") is True]
    incomplete_runs = [r for r in loaded
                       if r.get("post_eval") is None and r.get("aborted") is not True]
    scored = [r for r in loaded if r.get("post_eval") is not None]
    by_model: dict[str, list[dict[str, Any]]] = {}
    for r in scored:
        by_model.setdefault(r["model_key"], []).append(r)

    summary: dict[str, Any] = {"runs": [r["model_key"] + f"_seed{r['seed']}" for r in loaded],
                               "aborted_runs": [
                                   {"model_key": r["model_key"], "seed": r["seed"],
                                    "reason": (r.get("no_signal_guard") or {}).get("reason", ""),
                                    "steps_observed": (r.get("no_signal_guard") or {}).get("steps_observed", 0),
                                    "steps_alive": (r.get("no_signal_guard") or {}).get("steps_alive", 0)}
                                   for r in aborted_runs],
                               "runs_sans_post_eval": [
                                   {"model_key": r["model_key"], "seed": r["seed"]}
                                   for r in incomplete_runs],
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

    if len(summary["per_model"]) >= 2:
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
    print(json.dumps({k: v for k, v in summary.items() if k != "runs"}, indent=2)[:1500])
    print(f"courbes -> {png} | summary -> {summary_json}")
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
             no_signal_threshold=args.abort_if_no_signal)
    return 0


if __name__ == "__main__":
    sys.exit(main())
