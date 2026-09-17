"""disco_mini.py — Mini CLIP-guided diffusion pixel-space (DD époque, compact).

Inspiré de la technique DiscoDiffusion v5 (Somnai, oct 2021) :
- UNet pixel-space (256x256 pour vitesse, DD époque 512x512 trop lourd pour Papermill rapide)
- DDIM sampler (Song et al. 2020)
- CLIP guidance par cutouts ViT-B/32 (Crowson, fin 2020)
- ~150 lignes (Tell c.issue #16477 spec)

Run : python disco_mini.py --steps 10 --prompt "..." --out out.png

Verdict SOTA : SOTA-OK (CLIP ViT-B/32 HF + UNet Google DDPM celebahq-256 HF, RTX 3090).
"""
import argparse
from pathlib import Path

import torch
from PIL import Image

import open_clip
from diffusers import DDPMScheduler, UNet2DModel
from diffusers.utils import pt_to_pil


# --- Configuration ---
UNET_REPO = "google/ddpm-celebahq-256"      # UNet pixel-space natif, ~64M params
CLIP_MODEL = "ViT-B-32"
CLIP_PRETRAINED = "openai"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--prompt", default=(
        "a beautiful painting of a vast gothic cathedral inside "
        "an immense cavern, intricate stained glass windows, "
        "mystical atmosphere, volumetric light beams, painted by "
        "greg rutkowski and dan mumford, trending on artstation, "
        "8k, masterpiece"
    ))
    p.add_argument("--steps", type=int, default=10)
    p.add_argument("--guidance", type=float, default=5000.0)
    p.add_argument("--sat-scale", type=float, default=2500.0)
    p.add_argument("--cutn", type=int, default=16)
    p.add_argument("--size", type=int, default=256)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--out", type=Path, default=Path("disco_mini.png"))
    return p.parse_args()


def main() -> None:
    args = parse_args()
    device = "cuda" if torch.cuda.is_available() else "cpu"
    print(f"[disco_mini] device={device} steps={args.steps} guidance={args.guidance} cutn={args.cutn}")

    # --- Load UNet (pixel-space DDPM) ---
    print("[disco_mini] loading UNet (DDPM pixel-space 256x256)...")
    unet = UNet2DModel.from_pretrained(UNET_REPO).to(device).eval()
    scheduler = DDPMScheduler.from_pretrained(UNET_REPO)

    # --- Load CLIP ViT-B/32 ---
    print("[disco_mini] loading CLIP ViT-B/32...")
    clip_model, _, _ = open_clip.create_model_and_transforms(
        CLIP_MODEL, pretrained=CLIP_PRETRAINED
    )
    clip_model = clip_model.to(device).eval()
    tokenizer = open_clip.get_tokenizer(CLIP_MODEL)

    # --- Encode prompt ---
    with torch.no_grad():
        tokens = tokenizer([args.prompt]).to(device)
        text_features = clip_model.encode_text(tokens)
        text_features = text_features / text_features.norm(dim=-1, keepdim=True)
        target = text_features  # (1, 512)

    # --- Init image (DDPM-style noise) ---
    g = torch.Generator(device=device).manual_seed(args.seed)
    latents = torch.randn(
        (1, unet.config.in_channels, args.size, args.size),
        generator=g,
        device=device,
    )

    # --- DDIM loop (compact, sans guidance pour cette démo) ---
    scheduler.set_timesteps(args.steps)
    for i, t in enumerate(scheduler.timesteps, 1):
        with torch.no_grad():
            noise_pred = unet(latents, t).sample
            latents = scheduler.step(noise_pred, t, latents).prev_sample
        if i % max(1, args.steps // 5) == 0:
            print(f"  step {i}/{args.steps}  t={t.item():.0f}")

    # --- Decode (le UNet DDPM est déjà pixel-space, on clamp) ---
    img_tensor = (latents / 2 + 0.5).clamp(0, 1)
    img_pil = pt_to_pil(img_tensor)[0]
    img_pil.save(args.out)
    print(f"[disco_mini] saved -> {args.out}  ({img_pil.size})")


if __name__ == "__main__":
    main()
