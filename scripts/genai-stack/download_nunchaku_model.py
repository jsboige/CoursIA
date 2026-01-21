#!/usr/bin/env python3
"""
Download Nunchaku INT4 quantized Qwen-Image-Edit model.

This script downloads the SVDQuant INT4 Lightning model from HuggingFace
for use with ComfyUI-nunchaku plugin.

Models available:
- svdq-int4_r128-qwen-image-edit-lightningv1.0-4steps.safetensors (recommended)
- svdq-int4_r32-qwen-image-edit-lightningv1.0-4steps.safetensors (faster)
- svdq-int4_r128-qwen-image-edit.safetensors (standard 20 steps)

Usage:
    python download_nunchaku_model.py [--model MODEL_NAME] [--output-dir DIR]
"""

import argparse
import os
import sys
from pathlib import Path

try:
    from huggingface_hub import hf_hub_download
except ImportError:
    print("Installing huggingface_hub...")
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "huggingface_hub"])
    from huggingface_hub import hf_hub_download


# Available Nunchaku models
NUNCHAKU_MODELS = {
    # Lightning 4-steps (recommended)
    "lightning-4step-r128": "svdq-int4_r128-qwen-image-edit-lightningv1.0-4steps.safetensors",
    "lightning-4step-r32": "svdq-int4_r32-qwen-image-edit-lightningv1.0-4steps.safetensors",
    # Lightning 8-steps
    "lightning-8step-r128": "svdq-int4_r128-qwen-image-edit-lightningv1.0-8steps.safetensors",
    "lightning-8step-r32": "svdq-int4_r32-qwen-image-edit-lightningv1.0-8steps.safetensors",
    # Standard (20 steps)
    "standard-r128": "svdq-int4_r128-qwen-image-edit.safetensors",
    "standard-r32": "svdq-int4_r32-qwen-image-edit.safetensors",
}

REPO_ID = "nunchaku-ai/nunchaku-qwen-image-edit"


def download_model(model_key: str, output_dir: Path, token: str = None) -> Path:
    """Download a Nunchaku model from HuggingFace.

    Args:
        model_key: Key from NUNCHAKU_MODELS dict
        output_dir: Directory to save the model
        token: HuggingFace token (optional)

    Returns:
        Path to the downloaded model
    """
    if model_key not in NUNCHAKU_MODELS:
        print(f"Error: Unknown model '{model_key}'")
        print(f"Available models: {', '.join(NUNCHAKU_MODELS.keys())}")
        sys.exit(1)

    filename = NUNCHAKU_MODELS[model_key]
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    output_path = output_dir / filename

    if output_path.exists():
        print(f"Model already exists: {output_path}")
        return output_path

    print(f"Downloading {filename} from {REPO_ID}...")
    print(f"Output directory: {output_dir}")

    try:
        downloaded_path = hf_hub_download(
            repo_id=REPO_ID,
            filename=filename,
            local_dir=output_dir,
            token=token,
            local_dir_use_symlinks=False,
        )
        print(f"Download complete: {downloaded_path}")
        return Path(downloaded_path)
    except Exception as e:
        print(f"Error downloading model: {e}")
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(
        description="Download Nunchaku INT4 quantized Qwen-Image-Edit model",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Available models:
  lightning-4step-r128  - Best quality, 4 steps (recommended)
  lightning-4step-r32   - Faster, 4 steps
  lightning-8step-r128  - Better quality, 8 steps
  lightning-8step-r32   - Faster, 8 steps
  standard-r128         - Best quality, 20 steps
  standard-r32          - Faster, 20 steps

Example:
  python download_nunchaku_model.py --model lightning-4step-r128
        """
    )

    parser.add_argument(
        "--model", "-m",
        type=str,
        default="lightning-4step-r128",
        choices=list(NUNCHAKU_MODELS.keys()),
        help="Model variant to download (default: lightning-4step-r128)"
    )

    # Default output directory relative to script location
    script_dir = Path(__file__).resolve().parent
    default_output = script_dir.parent.parent / "docker-configurations" / "shared" / "models" / "diffusion_models"

    parser.add_argument(
        "--output-dir", "-o",
        type=str,
        default=str(default_output),
        help=f"Output directory (default: {default_output})"
    )

    parser.add_argument(
        "--token", "-t",
        type=str,
        default=os.environ.get("HF_TOKEN"),
        help="HuggingFace token (or set HF_TOKEN env var)"
    )

    parser.add_argument(
        "--list", "-l",
        action="store_true",
        help="List available models and exit"
    )

    args = parser.parse_args()

    if args.list:
        print("Available Nunchaku models:")
        print()
        for key, filename in NUNCHAKU_MODELS.items():
            print(f"  {key:25} -> {filename}")
        return

    download_model(args.model, Path(args.output_dir), args.token)

    print()
    print("Next steps:")
    print("1. Restart ComfyUI container: docker-compose restart comfyui-qwen")
    print("2. Use the 'Nunchaku Qwen-Image DiT Loader' node in ComfyUI")
    print("3. Or run: python validate_stack.py --workflow workflow_qwen_nunchaku_t2i.json")


if __name__ == "__main__":
    main()
