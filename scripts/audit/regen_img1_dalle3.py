#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
regen_img1_dalle3.py — REPAIR THE LEGACY ASSET (issue #8624).

Le NB `01-1-OpenAI-DALL-E-3.ipynb` régénère une image via gpt-image-1 puis
l'affiche avec matplotlib. Le filtre non-ASCII du titre (c.916 / PR #8636)
protège la SORTIE du notebook, mais l'asset historique
`MyIA.AI.Notebooks/GenAI/Image/01-Foundation/assets/readme/img1-dalle3.webp`
(committé avant ce fix) garde un glyphe □ cuit dans le bandeau de titre.

L948 ★★ Stop & Repair : on ne scrubbe pas la SORTIE d'une cellule, on répare
la CAUSE + ré-exécute. Ici la cause = image legacy figée dans le `.webp`,
le fix = re-générer l'image via le même pipeline puis re-burn le bandeau
ASCII-only + sauver. SOTA-OK : vraie regen via stack GenAI.

Usage:
    python scripts/audit/regen_img1_dalle3.py            # regen + save
    python scripts/audit/regen_img1_dalle3.py --check   # verify (no regen)
    python scripts/audit/regen_img1_dalle3.py --audit   # quick audit only
"""
from __future__ import annotations

import argparse
import base64
import io
import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
NB_PATH = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-OpenAI-DALL-E-3.ipynb"
ASSET_DIR = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/Image/01-Foundation/assets/readme"
ASSET_PATH = ASSET_DIR / "img1-dalle3.webp"
ENV_PATH = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/.env"

# gpt-image-1 params (calqués sur cell 11 du NB, identique au pipeline pédagogique)
MODEL_NAME = "gpt-image-1"
SIZE = "1024x1024"
QUALITY = "medium"
PROMPT = (
    "A futuristic cityscape at sunset with flying cars, neon lights reflecting on "
    "glass buildings, holographic advertisements, and a diverse crowd of people "
    "walking on illuminated sidewalks. Ultra-detailed, cinematic lighting, 8K quality."
)
TITLE = "Paysage Urbain Futuriste - gpt-image-1"


def _load_env() -> dict[str, str]:
    """Charge le .env GenAI (gitignored) sans dépendre de python-dotenv."""
    env: dict[str, str] = {}
    if not ENV_PATH.exists():
        print(f"[err] .env introuvable : {ENV_PATH}", file=sys.stderr)
        sys.exit(2)
    for line in ENV_PATH.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, v = line.split("=", 1)
        env[k.strip()] = v.strip()
    return env


def _ascii_title(title: str) -> str:
    """Strip non-ASCII (c.916 / PR #8636 pattern) — stop & repair sur glyphe □."""
    return re.sub(r"[^\x00-\x7F]+", " ", title).strip()


def _call_openai_image(api_key: str, prompt: str) -> bytes:
    """POST /v1/images/generations — gpt-image-1 → b64_json PNG bytes."""
    import json
    import urllib.request

    url = "https://api.openai.com/v1/images/generations"
    payload = json.dumps(
        {
            "model": MODEL_NAME,
            "prompt": prompt,
            "n": 1,
            "size": SIZE,
            "quality": QUALITY,
        }
    ).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=payload,
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=120) as resp:
        body = json.loads(resp.read().decode("utf-8"))
    b64 = body["data"][0].get("b64_json")
    if not b64:
        raise RuntimeError(f"Pas de b64_json dans la réponse OpenAI: {body}")
    return base64.b64decode(b64)


def _burn_title(png_bytes: bytes, title: str, out_path: Path) -> None:
    """Re-burn le bandeau de titre via matplotlib (ASCII-only filtre)."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from PIL import Image

    img = Image.open(io.BytesIO(png_bytes)).convert("RGBA")
    fig, ax = plt.subplots(figsize=(12, 8))
    ax.imshow(img)
    ax.axis("off")
    ax.set_title(title, fontsize=16, pad=20)
    fig.tight_layout()
    fig.savefig(out_path, format="webp", bbox_inches="tight", dpi=85)
    plt.close(fig)


def audit() -> int:
    """Vérifie que l'asset existe et n'est pas manifestement cassé (taille)."""
    if not ASSET_PATH.exists():
        print(f"[err] asset absent : {ASSET_PATH}")
        return 1
    size = ASSET_PATH.stat().st_size
    print(f"[ok] asset present : {ASSET_PATH} ({size} bytes)")
    if size < 10_000:
        print(f"[warn] asset suspicieusement petit ({size} bytes)")
        return 2
    return 0


def check() -> int:
    """Audit + vérification qu'on PEUT le regen (clé présente, deps OK)."""
    rc = audit()
    if rc != 0:
        return rc
    env = _load_env()
    api_key = env.get("OPENAI_API_KEY")
    if not api_key or api_key == "<placeholder>":
        print("[err] OPENAI_API_KEY absente ou placeholder dans .env")
        return 3
    print(f"[ok] OPENAI_API_KEY présente (longueur {len(api_key)})")
    try:
        from PIL import Image  # noqa: F401
        import matplotlib  # noqa: F401
        print("[ok] deps PIL + matplotlib disponibles")
    except ImportError as e:
        print(f"[err] dep manquante : {e}")
        return 4
    return 0


def regen() -> int:
    """Regen + save. Idempotent : re-run = re-write."""
    api_key = _load_env().get("OPENAI_API_KEY")
    if not api_key or api_key == "<placeholder>":
        print("[err] OPENAI_API_KEY absente ou placeholder", file=sys.stderr)
        return 3
    print(f"[regen] Appel OpenAI gpt-image-1 size={SIZE} quality={QUALITY}...")
    try:
        png_bytes = _call_openai_image(api_key, PROMPT)
    except Exception as e:
        print(f"[err] Echec API OpenAI : {e}", file=sys.stderr)
        return 5
    print(f"[regen] Image reçue ({len(png_bytes)} bytes PNG)")

    safe_title = _ascii_title(TITLE)
    print(f"[regen] Bandeau titre ASCII-only : {safe_title!r}")
    _burn_title(png_bytes, safe_title, ASSET_PATH)
    final = ASSET_PATH.stat().st_size
    print(f"[ok] asset sauvé : {ASSET_PATH} ({final} bytes)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Regen img1-dalle3.webp (issue #8624).")
    ap.add_argument("--check", action="store_true", help="Vérifier deps + .env")
    ap.add_argument("--audit", action="store_true", help="Audit rapide (taille asset)")
    args = ap.parse_args()
    if args.check:
        return check()
    if args.audit:
        return audit()
    return regen()


if __name__ == "__main__":
    sys.exit(main())
