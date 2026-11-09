# -*- coding: utf-8 -*-
"""Validation post-fix du port Chronos (main_finetuned.py) PAR EXECUTION.

Preuve relisible citee par la PR #19622 : ce script s'execute depuis le
dossier du projet et valide les trois points du fix par exécution réelle,
pas par lecture de code :

1. exec du shim d'import REEL (lignes extraites du fichier committé, pas
   recopiées) avec `AlgorithmImports` stubbé (runtime QC indisponible
   localement) ;
2. exec verbatim des lignes `train.logger = getLogger()` /
   `train.logger.setLevel(INFO)` — les deux instructions qui levaient
   NameError pré-fix (méthode de reproduction de l'adjoint, avec
   getLogger/INFO réels cette fois) ;
3. chemin d'entraînement REEL mirant la séquence `_train` du port :
   PandasDataset -> Filter/partial -> ChronosDataset ->
   load_model(chronos-t5-tiny) -> TrainingArguments(max_steps=2) ->
   Trainer.train() -> save_pretrained.

Environnement de référence (run de validation de la PR) : env conda
``bonsai`` — chronos-forecasting 2.3.2, transformers 5.10.2, CPU.

Usage :

    python validate_19622_port.py

Sortie 0 = port validé par exécution ; tout échec sort non-nul. Les
artefacts d'entraînement (2 pas, chronos-t5-tiny) vont dans un répertoire
temporaire hors du dépôt, supprimé à la sortie.
"""
import sys
import tempfile
import shutil
from pathlib import Path

PORT = Path(__file__).resolve().parent / "main_finetuned.py"
OUT = Path(tempfile.mkdtemp(prefix="chrono_val_"))

try:
    src = PORT.read_text(encoding="utf-8")
    lines = src.splitlines()

    # --- 1. extraire la région REELLE des imports du port : de "from scipy.optimize"
    # (l.4, juste après le stub AlgorithmImports) à "from logging import" incluse --
    # shim ET ses dépendances (Path, torch, transformers, gluonts, chronos) exécutés tels quels.
    i_shim = next(i for i, l in enumerate(lines) if l.startswith("from scipy.optimize"))
    i_log = next(i for i, l in enumerate(lines) if l.startswith("from logging import"))
    shim_region = "\n".join(lines[i_shim:i_log + 1])

    stub = (
        "import sys, types\n"
        "_alg = types.ModuleType('AlgorithmImports')\n"
        "_alg.__dict__.update({'QCAlgorithm': object, 'QuantBook': object})\n"
        "sys.modules['AlgorithmImports'] = _alg\n"
    )
    g = {"__file__": str(PORT), "__name__": "main_finetuned_validation"}
    exec(compile(stub + shim_region, str(PORT) + " <shim>", "exec"), g)

    train = g["train"]
    import chronos_training  # doit être LE même module objet que le shim a lié
    assert train is chronos_training, "shim: `train` n'est pas le module vendored"
    print("[1] shim OK : branche vendored exécutée, train IS chronos_training (%s)" % train.__name__)
    assert callable(g["ChronosDataset"]) and callable(g["has_enough_observations"]) and callable(g["load_model"])
    print("[1] trois symboles liés :", g["ChronosDataset"].__module__, "/", g["load_model"].__module__)

    # --- 2. les deux instructions qui levaient NameError, exécutées telles quelles.
    i_logger = next(i for i, l in enumerate(lines) if l.strip() == "train.logger = getLogger()")
    i_level = next(i for i, l in enumerate(lines) if l.strip() == "train.logger.setLevel(INFO)")
    import textwrap
    stmts = textwrap.dedent("\n".join(lines[i_logger:i_level + 1]))
    exec(compile(stmts, str(PORT) + " <logger-binding>", "exec"), g)
    assert train.logger is not None and train.logger.level == 20  # INFO == 20
    print("[2] lignes du binding logger exécutées verbatim : train.logger = %r (level INFO=%d)"
          % (train.logger.name, train.logger.level))

    # --- 3. chemin d'entraînement réel (séquence _train du port, pas de compilation seule).
    import numpy as np
    import pandas as pd
    from functools import partial
    import torch
    from transformers import Trainer, TrainingArguments, set_seed
    from gluonts.dataset.pandas import PandasDataset
    from gluonts.itertools import Filter
    from chronos import ChronosConfig

    set_seed(7, True)
    idx = pd.date_range("2019-01-01", periods=260, freq="D")
    frame = pd.DataFrame({"target": 100.0 + np.cumsum(np.random.default_rng(7).normal(0, 1, 260).cumsum())}, index=idx)
    frame.index.name = "time"

    CONTEXT_LENGTH, PREDICTION_LENGTH, MIN_PAST = 126, 63, 64
    prob = [1.0]
    tok_kwargs = {"low_limit": -15.0, "high_limit": 15.0}

    train_datasets = [
        Filter(
            partial(g["has_enough_observations"], min_length=MIN_PAST + PREDICTION_LENGTH, max_missing_prop=0.9),
            PandasDataset(frame, freq="D"),
        )
    ]
    print("[3] PandasDataset+Filter construits (260 jours synthétiques)")

    model = g["load_model"](
        model_id="amazon/chronos-t5-tiny", model_type="seq2seq", vocab_size=4096,
        random_init=False, tie_embeddings=True, pad_token_id=0, eos_token_id=1,
    )
    chronos_config = ChronosConfig(
        tokenizer_class="MeanScaleUniformBins", tokenizer_kwargs=tok_kwargs,
        n_tokens=4096, n_special_tokens=2, pad_token_id=0, eos_token_id=1,
        use_eos_token=True, model_type="seq2seq",
        context_length=CONTEXT_LENGTH, prediction_length=PREDICTION_LENGTH,
        num_samples=20, temperature=1.0, top_k=50, top_p=1.0,
    )
    model.config.chronos_config = chronos_config.__dict__
    shuffled = g["ChronosDataset"](
        datasets=train_datasets, probabilities=prob,
        tokenizer=chronos_config.create_tokenizer(),
        context_length=CONTEXT_LENGTH, prediction_length=PREDICTION_LENGTH,
        min_past=MIN_PAST, mode="training",
    ).shuffle(shuffle_buffer_length=10)
    print("[3] load_model + ChronosDataset OK (device=%s, tf32=%s)" % (torch.get_default_device(), torch.backends.cuda.matmul.allow_tf32))

    args = TrainingArguments(
        output_dir=str(OUT), per_device_train_batch_size=4, learning_rate=1e-5,
        lr_scheduler_type="linear", warmup_ratio=0.0, optim="adamw_torch_fused",
        logging_strategy="steps", logging_steps=1, save_strategy="no",
        report_to=[], max_steps=2, gradient_accumulation_steps=1,
        dataloader_num_workers=0, tf32=True, torch_compile=False,
        ddp_find_unused_parameters=False, remove_unused_columns=False,
    )
    trainer = Trainer(model=model, args=args, train_dataset=shuffled)
    result = trainer.train()
    model.save_pretrained(OUT)
    steps = int(result.global_step)
    assert steps >= 2, "trainer n'a pas atteint 2 pas"
    losses = [h.get("loss") for h in trainer.state.log_history if h.get("loss") is not None]
    print("[3] Trainer.train() REEL : global_step=%d, losses=%s" % (steps, ["%.3f" % l for l in losses]))
    print("[3] save_pretrained -> %s (config.json=%s)" % (OUT, (OUT / "config.json").exists()))

    print("\nVALIDATION PORT #19622 : PASS (shim exécuté + binding logger exécuté + chemin d'entraînement réel 2 pas)")
finally:
    shutil.rmtree(OUT, ignore_errors=True)
