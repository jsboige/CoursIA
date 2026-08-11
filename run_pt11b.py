"""Run PT-11b notebook via papermill with LOAD_MODEL_AND_TRAIN=True.

Bypasses papermill 2.x CLI limitations: sets CUDA_VISIBLE_DEVICES + PT11B_SEEDS
via os.environ (papermill doesn't support --env).
"""

import argparse
import os
import sys
from pathlib import Path

import papermill as pm


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("seed", type=int, nargs="?", default=42)
    parser.add_argument("--work-dir", default=r"C:/dev/CoursIA-2-c1331x77-multiseed")
    parser.add_argument("--notebook", default="MyIA.AI.Notebooks/GenAI/PostTraining/PT_11b_multiseed_qwen35_4x100.ipynb")
    parser.add_argument("--output-dir-suffix", default="")
    args = parser.parse_args()

    work_dir = Path(args.work_dir).resolve()
    os.chdir(work_dir)

    os.environ["CUDA_VISIBLE_DEVICES"] = "0"
    os.environ["PT11B_SEEDS"] = str(args.seed)

    out_nb = work_dir / f"pt11b_seed_{args.seed}_output{args.output_dir_suffix}.ipynb"
    nb_path = work_dir / args.notebook

    print(f"[runner] work_dir={work_dir}")
    print(f"[runner] notebook={nb_path}")
    print(f"[runner] output={out_nb}")
    print(f"[runner] CUDA_VISIBLE_DEVICES={os.environ['CUDA_VISIBLE_DEVICES']}")
    print(f"[runner] PT11B_SEEDS={os.environ['PT11B_SEEDS']}")

    pm.execute_notebook(
        str(nb_path),
        str(out_nb),
        cwd=str(work_dir),
        log_level="INFO",
        progress_bar=False,
    )
    print(f"[runner] Done. Output notebook: {out_nb}")


if __name__ == "__main__":
    main()