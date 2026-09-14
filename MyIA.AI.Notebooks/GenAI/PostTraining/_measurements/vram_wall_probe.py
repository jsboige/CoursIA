"""Sonde du mur 8 Go -- issue #15633, umbrella #1454 (nomination etage moyen).

Mesure l'enveloppe memoire d'un step GRPO-RLVR sous la recipe EXACTE de PT_11d
(bnb4 nf4 double-quant, LoRA r=8 all-proj, num_generations=8, accum 4,
completion 96, grad checkpointing, bf16, beta=0 -- trl 1.9.2 ; sous trl 1.12,
max_prompt_length a disparu de GRPOConfig : seules les prompts courtes de la
sonde rendent son retrait sans effet sur l'enveloppe) a trois tailles:
Qwen3.5-0.8B (base connue-tenable, PT_11d), Qwen3-1.7B et Qwen3-2B (PT_11c).

Reward constant 0.5 : la sonde mesure l'enveloppe VRAM du step (generation
G=8 + backward LoRA), pas l'apprentissage -- le verifier SymPy est CPU-side et
n'affecte pas la VRAM. Aucun resultat d'entrainement n'est claimable ici.

Un sous-processus par modele : un OOM CUDA n'empoisonne pas les tailles suivantes.
Sortie : une ligne JSON par modele (append au fichier passe en 2e argument).
"""
import json
import sys
import time
import gc


def probe(model_id: str) -> dict:
    import torch
    from datasets import Dataset
    from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
    from trl import GRPOTrainer, GRPOConfig
    from peft import LoraConfig, TaskType

    result = {
        "model": model_id,
        "torch": torch.__version__,
        "gpu": torch.cuda.get_device_name(0),
        "vram_total_gb": round(torch.cuda.get_device_properties(0).total_memory / 2**30, 2),
        "status": None,
        "load_s": None,
        "train_s": None,
        "sec_per_step": None,
        "max_vram_allocated_gb": None,
        "max_vram_reserved_gb": None,
        "steps_done": None,
        "error": None,
    }
    model = None
    try:
        t0 = time.time()
        tok = AutoTokenizer.from_pretrained(model_id)
        bnb = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_compute_dtype=torch.bfloat16,
            bnb_4bit_use_double_quant=True,
        )
        model = AutoModelForCausalLM.from_pretrained(
            model_id, quantization_config=bnb, device_map={"": 0}
        )
        result["load_s"] = round(time.time() - t0, 1)

        prompts = [
            {"prompt": f"Solve: {a} + {b} = ?", "answer": str(a + b)}
            for a, b in [(12, 30), (7, 5), (21, 14), (3, 9), (44, 6), (15, 27), (9, 9), (50, 50)]
        ]
        ds = Dataset.from_list(prompts * 4)

        lora = LoraConfig(
            r=8,
            lora_alpha=16,
            lora_dropout=0.05,
            bias="none",
            task_type=TaskType.CAUSAL_LM,
            target_modules=["q_proj", "k_proj", "v_proj", "o_proj", "gate_proj", "up_proj", "down_proj"],
        )
        cfg = GRPOConfig(
            num_generations=8,
            beta=0.0,
            per_device_train_batch_size=8,
            gradient_accumulation_steps=4,
            learning_rate=5e-6,
            max_steps=3,
            max_completion_length=96,
            logging_steps=1,
            save_strategy="no",
            output_dir="./vram_probe_out",
            seed=0,
            bf16=True,
            report_to=[],
            gradient_checkpointing=True,
        )

        def reward(completions, **kwargs):
            return [0.5] * len(completions)

        torch.cuda.reset_peak_memory_stats()
        t1 = time.time()
        trainer = GRPOTrainer(
            model=model,
            args=cfg,
            train_dataset=ds,
            processing_class=tok,
            peft_config=lora,
            reward_funcs=[reward],
        )
        trainer.train()
        result["train_s"] = round(time.time() - t1, 1)
        result["sec_per_step"] = round((time.time() - t1) / 3, 1)
        result["steps_done"] = 3
        result["max_vram_allocated_gb"] = round(torch.cuda.max_memory_allocated() / 2**30, 3)
        result["max_vram_reserved_gb"] = round(torch.cuda.max_memory_reserved() / 2**30, 3)
        result["status"] = "FIT"
    except torch.cuda.OutOfMemoryError as e:
        result["status"] = "OOM"
        result["error"] = f"torch.cuda.OutOfMemoryError: {e}"[:250]
    except Exception as e:
        result["status"] = "ERROR"
        result["error"] = f"{type(e).__name__}: {e}"[:250]
    finally:
        try:
            if result["max_vram_allocated_gb"] is None and torch.cuda.is_available():
                result["max_vram_allocated_gb"] = round(torch.cuda.max_memory_allocated() / 2**30, 3)
                result["max_vram_reserved_gb"] = round(torch.cuda.max_memory_reserved() / 2**30, 3)
        except Exception:
            pass
        del model
        gc.collect()
        torch.cuda.empty_cache()
    return result


if __name__ == "__main__":
    model_id = sys.argv[1]
    out_path = sys.argv[2]
    r = probe(model_id)
    with open(out_path, "a", encoding="utf-8") as f:
        f.write(json.dumps(r) + "\n")
    print(json.dumps(r, indent=2))
    sys.exit(0 if r["status"] == "FIT" else 2)
