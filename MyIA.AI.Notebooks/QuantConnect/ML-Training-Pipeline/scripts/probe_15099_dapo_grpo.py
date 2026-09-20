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
import time
from pathlib import Path
from typing import Any

REPO_RESULTS = Path(__file__).resolve().parent / "results" / "m19_minicpm5_grpo"
BASELINE_RESULTS = Path(__file__).resolve().parent / "results" / "p15294_accessibility"
RUNS_ROOT = Path("D:/Dev/probe15099_runs")  # adapters + artefacts lourds, hors repo
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
}


def find_hf_snapshot(glob_pattern: str) -> Path:
    hub = Path.home() / ".cache" / "huggingface" / "hub"
    matches = sorted(hub.glob(glob_pattern))
    if not matches:
        raise FileNotFoundError(f"aucun snapshot HF pour {glob_pattern} (lancer hf download)")
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

    total_ok, total = n_match + n_xlam, len(cases) + len(xlam_cases)
    print(f"selftest: {total_ok}/{total} pass (dapo {n_match}/{len(cases)}, xlam {n_xlam}/{len(xlam_cases)})")
    return 1 if (fails or xlam_fails) else 0


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
             dataset_key: str = "dapo") -> dict[str, Any]:
    ds = DATASETS[dataset_key]
    train_rows, eval_rows = ds["load"]()
    t0 = time.time()
    trainer, model_path = build_trainer(model_key, seed, steps, train_rows,
                                        reward_fn=ds["reward"], dataset_key=dataset_key)

    pre = evaluate(trainer, eval_rows, seed, match_fn=ds["match"])
    print(f"[{model_key} seed{seed}] pre-eval: {pre}")

    trainer.train()

    post = evaluate(trainer, eval_rows, seed, match_fn=ds["match"])
    print(f"[{model_key} seed{seed}] post-eval: {post}")

    run_dir = RUNS_ROOT / f"{model_key}_{dataset_key}_seed{seed}"
    adapter_dir = run_dir / "adapter"
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


def mode_summarize() -> int:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    runs = sorted(REPO_RESULTS.glob("*_seed*.json"))
    if not runs:
        print("aucun run trouve dans", REPO_RESULTS)
        return 1
    loaded = [json.loads(p.read_text(encoding="utf-8")) for p in runs]
    by_model: dict[str, list[dict[str, Any]]] = {}
    for r in loaded:
        by_model.setdefault(r["model_key"], []).append(r)

    summary: dict[str, Any] = {"runs": [r["model_key"] + f"_seed{r['seed']}" for r in loaded],
                               "per_model": {}, "verdict": None}
    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5))
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
            steps_r = [e["step"] for e in r["log_history"] if "rewards/dapo_reward/mean" in e]
            rew = [e["rewards/dapo_reward/mean"] for e in r["log_history"]
                   if "rewards/dapo_reward/mean" in e]
            ln = [e["completions/mean_length"] for e in r["log_history"]
                  if "completions/mean_length" in e]
            axes[0].plot(steps_r, rew, alpha=0.7, label=f"{model_key} s{r['seed']}")
            axes[1].plot(steps_r[: len(ln)], ln, alpha=0.7)
    axes[0].set_title("Reward train (dapo_reward/mean)")
    axes[0].set_xlabel("step")
    axes[1].set_title("Longueur moyenne des completions")
    axes[1].set_xlabel("step")
    axes[0].legend(fontsize=7)

    if len(summary["per_model"]) >= 2:
        def curves_healthy(model_key: str) -> bool:
            rl = [r for r in loaded if r["model_key"] == model_key]
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
    png = REPO_RESULTS / "curves.png"
    fig.savefig(png, dpi=130)
    summary_json = REPO_RESULTS / "summary.json"
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
    args = ap.parse_args()

    if not args.thinking:
        CHAT_KWARGS.clear()
        CHAT_KWARGS["enable_thinking"] = False
    else:
        global MAX_COMPLETION
        MAX_COMPLETION = 1024

    if args.mode == "selftest":
        return mode_selftest()
    if args.mode == "summarize":
        return mode_summarize()
    if args.mode == "baseline":
        mode_baseline(args.model, args.dataset)
        return 0
    steps = 3 if args.mode == "smoke" else args.steps
    global EVAL_N_PROMPTS, TRAIN_POOL
    if args.mode == "smoke":
        EVAL_N_PROMPTS, TRAIN_POOL = 8, 16
    RUNS_ROOT.mkdir(parents=True, exist_ok=True)
    mode_run(args.model, args.seed, steps, smoke=args.mode == "smoke",
             dataset_key=args.dataset)
    return 0


if __name__ == "__main__":
    sys.exit(main())
