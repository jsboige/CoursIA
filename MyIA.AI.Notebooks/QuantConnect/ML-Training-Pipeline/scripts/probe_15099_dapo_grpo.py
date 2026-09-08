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

Dataset : BytedTsinghua-SIA/DAPO-Math-17k (cache HF local, 1 791 700 lignes =
17 917 problemes uniques x 100 repliques ; dedup par extra_info.index).
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
import time
from pathlib import Path
from typing import Any

REPO_RESULTS = Path(__file__).resolve().parent / "results" / "m19_minicpm5_grpo"
RUNS_ROOT = Path("D:/Dev/probe15099_runs")  # adapters + artefacts lourds, hors repo
DATASET_SNAPSHOT_GLOB = (
    "datasets--BytedTsinghua-SIA--DAPO-Math-17k/snapshots/*/data/dapo-math-17k.parquet"
)

MAX_STEPS = 100
EVAL_N_PROMPTS = 60
EVAL_GENS = 4
TRAIN_POOL = 4000
SPLIT_SEED = 15099

MODELS: dict[str, dict[str, str]] = {
    "minicpm5": {
        "path_glob": "models--openbmb--MiniCPM5-2B/snapshots/*",
        "label": "MiniCPM5-2B",
    },
    "qwen35": {
        "path_glob": "models--Qwen--Qwen3.5-0.8B/snapshots/*",
        "label": "Qwen3.5-0.8B",
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
# Entrainement GRPO + QLoRA
# ---------------------------------------------------------------------------


def build_trainer(model_key: str, seed: int, steps: int, train_rows: list[dict[str, Any]]):
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
        output_dir=str(RUNS_ROOT / f"{model_key}_seed{seed}" / "trainer_out"),
        seed=seed,
        max_steps=steps,  # cap NON lineaire (lecon #13596)
        learning_rate=2e-5,
        warmup_steps=5,
        lr_scheduler_type="constant_with_warmup",
        per_device_train_batch_size=8,
        gradient_accumulation_steps=4,  # 32 completions/step = 4 prompts x 8 generations
        num_generations=8,
        max_completion_length=384,
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
    )
    trainer = GRPOTrainer(
        model=str(model_path),
        reward_funcs=dapo_reward,
        args=cfg,
        train_dataset=Dataset.from_list(train_rows),
        processing_class=tokenizer,
        quantization_config=quant_cfg,
        peft_config=peft_cfg,
    )
    return trainer, model_path


def evaluate(trainer: Any, eval_rows: list[dict[str, Any]], seed: int) -> dict[str, float]:
    """Generation n=EVAL_GENS par prompt eval, reward par le meme matcher."""
    import torch

    gen_seed = seed * 1000 + 7
    rewards: list[float] = []
    lengths: list[int] = []
    model, tokenizer = trainer.model, trainer.processing_class
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
            )
            enc = {k: v.to(device) for k, v in enc.items()}
            n_in = enc["input_ids"].shape[1]
            out = model.generate(
                **enc,
                max_new_tokens=384,
                do_sample=True,
                temperature=1.0,
                top_p=1.0,
                pad_token_id=tokenizer.pad_token_id,
            )
            texts = tokenizer.batch_decode(out[:, n_in:], skip_special_tokens=True)
            for t in texts:
                rewards.append(
                    1.0 if answers_match(extract_answer(t), row["ground_truth"]) else 0.0
                )
                lengths.append(len(t))
    return {
        "n_gens": float(len(rewards)),
        "reward_mean": sum(rewards) / len(rewards),
        "length_mean": sum(lengths) / max(1, len(lengths)),
    }


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
    print(f"selftest: {len(cases) - len(fails)}/{len(cases)} pass")
    return 1 if fails else 0


def mode_run(model_key: str, seed: int, steps: int) -> dict[str, Any]:
    train_rows, eval_rows = load_dapo_split()
    t0 = time.time()
    trainer, model_path = build_trainer(model_key, seed, steps, train_rows)

    pre = evaluate(trainer, eval_rows, seed)
    print(f"[{model_key} seed{seed}] pre-eval: {pre}")

    trainer.train()

    post = evaluate(trainer, eval_rows, seed)
    print(f"[{model_key} seed{seed}] post-eval: {post}")

    adapter_dir = RUNS_ROOT / f"{model_key}_seed{seed}" / "adapter"
    trainer.model.save_pretrained(str(adapter_dir))
    trainer.processing_class.save_pretrained(str(adapter_dir))

    log_history = [
        {k: v for k, v in entry.items() if not k.startswith("_")}
        for entry in trainer.state.log_history
    ]
    result = {
        "module": "ML-Training-Pipeline",
        "issue": 15099,
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
    REPO_RESULTS.mkdir(parents=True, exist_ok=True)
    out = REPO_RESULTS / f"{model_key}_seed{seed}.json"
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

    if "minicpm5" in summary["per_model"] and "qwen35" in summary["per_model"]:
        mini, qwen = summary["per_model"]["minicpm5"], summary["per_model"]["qwen35"]
        healthy = all(
            r["post_eval"]["reward_mean"] > r["pre_eval"]["reward_mean"] for r in loaded
        )
        beats = mini["delta_mean"] > qwen["delta_mean"] and (
            mini["delta_mean"] - mini["delta_std"] > qwen["delta_mean"] + qwen["delta_std"]
        )
        summary["verdict"] = {
            "curves_healthy": healthy,
            "beats": bool(beats and healthy),
            "rule": "BEATS si delta eval moyen mini > qwen avec intervalles ±1std disjoints ET courbes saines",
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
    ap.add_argument("mode", choices=["selftest", "smoke", "run", "summarize"])
    ap.add_argument("--model", choices=list(MODELS), default="minicpm5")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--steps", type=int, default=MAX_STEPS)
    args = ap.parse_args()

    if args.mode == "selftest":
        return mode_selftest()
    if args.mode == "summarize":
        return mode_summarize()
    steps = 3 if args.mode == "smoke" else args.steps
    global EVAL_N_PROMPTS, TRAIN_POOL
    if args.mode == "smoke":
        EVAL_N_PROMPTS, TRAIN_POOL = 8, 16
    RUNS_ROOT.mkdir(parents=True, exist_ok=True)
    mode_run(args.model, args.seed, steps)
    return 0


if __name__ == "__main__":
    sys.exit(main())
