#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
regen_img1_dalle3.py — REPAIR THE LEGACY ASSETS (issue #8624 + #9348).

Le NB `01-1-OpenAI-DALL-E-3.ipynb` régénère une image via gpt-image-1 puis
l'affiche avec matplotlib. Le filtre non-ASCII du titre (c.916 / PR #8636)
protège la SORTIE du notebook, mais deux assets historiques gardent un glyphe
□ + le libellé legacy « DALL-E 3 » cuit dans le bandeau de titre (committés
avant ce fix) :

- `MyIA.AI.Notebooks/GenAI/Image/01-Foundation/assets/readme/img1-dalle3.webp`
- `MyIA.AI.Notebooks/GenAI/Image/assets/readme/dalle3-cover.webp`

c.928 (PR #8636) a régénéré le premier ; le second est resté legacy (Classe 4
c.973 vision-audit = alt-text incoherent — titre intégré annonce « DALL-E 3 »
alors que le modèle réellement appelé est `gpt-image-1`, vérifiable dans le NB
source cellule 82075ed6 + disclosure `dalle3-gpt-image1-disclosure`). Doctrine
#5780 demande que les deux fichiers soient byte-identique (racine Image README
illustre la figure dans le contexte introductif « 01-Foundation - Modèles de
base » ; 01-Foundation README l'illustre dans le contexte « DALL-E 3 cellule 14
output 3 »).

L948 ★★ Stop & Repair : on ne scrubbe pas la SORTIE d'une cellule, on répare
la CAUSE + ré-exécute. Ici la cause = image legacy figée dans les `.webp`,
le fix = re-générer l'image via le même pipeline puis re-burn le bandeau
ASCII-only + sauver aux DEUX emplacements (byte-identique). SOTA-OK : vraie
regen via stack GenAI (appel OpenAI `gpt-image-1` direct, pas ComfyUI).

Usage:
    python scripts/audit/regen_img1_dalle3.py            # regen + save (BOTH)
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
ASSET_DIR_01F = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/Image/01-Foundation/assets/readme"
ASSET_DIR_ROOT = REPO_ROOT / "MyIA.AI.Notebooks/GenAI/Image/assets/readme"
ASSET_PATHS = [
    ASSET_DIR_01F / "img1-dalle3.webp",
    ASSET_DIR_ROOT / "dalle3-cover.webp",
]
# Rétrocompat — single-path callers (tests, audit script) pointent sur 01-Foundation.
ASSET_PATH = ASSET_PATHS[0]
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
    """Charge le .env GenAI (gitignored) sans dépendre de python-dotenv.

    Look-up multi-origine : si exécuté depuis un worktree qui n'a pas de
    .env propre (cas fréquent — le .env est gitignored et l'API key vit
    sur l'arbre principal), on cherche dans l'ordre :
      1. ENV_PATH canonique (worktree-local)
      2. .env dans REPO_ROOT (souvent worktree → pas de .env)
      3. .env dans les parents successifs de REPO_ROOT
      4. .env dans les siblings de REPO_ROOT (autres worktrees + main repo)
    Les secrets ne doivent JAMAIS transiter par un fichier versionné
    (cf [secrets-hygiene.md] règle HARD).
    """
    env: dict[str, str] = {}
    candidates: list[Path] = []
    candidates.append(ENV_PATH)
    candidates.append(REPO_ROOT / "MyIA.AI.Notebooks/GenAI/.env")
    # Remonter les parents
    cur = REPO_ROOT
    for _ in range(8):
        cur = cur.parent
        candidates.append(cur / "MyIA.AI.Notebooks/GenAI/.env")
    # Siblings de REPO_ROOT (couvre le cas « worktree enfant du main repo »)
    parent = REPO_ROOT.parent
    if parent.exists():
        for sib in parent.iterdir():
            if sib.is_dir():
                candidates.append(sib / "MyIA.AI.Notebooks/GenAI/.env")
    seen = set()
    for p in candidates:
        try:
            rp = p.resolve()
        except OSError:
            continue
        if rp in seen:
            continue
        seen.add(rp)
        if not p.exists() or not p.is_file():
            continue
        for line in p.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, v = line.split("=", 1)
            env.setdefault(k.strip(), v.strip())
        if env:
            print(f"[ok] .env chargé depuis : {p}")
            return env
    print(
        f"[err] .env introuvable (tenté dans {len(seen)} chemins, ex. "
        f"{candidates[0]})",
        file=sys.stderr,
    )
    sys.exit(2)


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
    """Vérifie que les assets existent et ne sont pas manifestement cassés (taille)."""
    rc = 0
    for p in ASSET_PATHS:
        if not p.exists():
            print(f"[err] asset absent : {p}")
            rc = 1
            continue
        size = p.stat().st_size
        print(f"[ok] asset present : {p} ({size} bytes)")
        if size < 10_000:
            print(f"[warn] asset suspicieusement petit ({size} bytes)")
            rc = max(rc, 2)
    return rc


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
    """Regen + save BOTH assets byte-identique. Idempotent : re-run = re-write."""
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
    # Burn le titre et sauver vers TOUS les chemins target (doctrine #5780 byte-identique).
    # On burn dans un buffer BytesIO une seule fois, puis on écrit les bytes identiques
    # vers chaque chemin — garantit byte-identity sans dépendre du timestamp WebP.
    import io as _io
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from PIL import Image

    img = Image.open(io.BytesIO(png_bytes)).convert("RGBA")
    fig, ax = plt.subplots(figsize=(12, 8))
    ax.imshow(img)
    ax.axis("off")
    ax.set_title(safe_title, fontsize=16, pad=20)
    fig.tight_layout()
    webp_buf = _io.BytesIO()
    fig.savefig(webp_buf, format="webp", bbox_inches="tight", dpi=85)
    plt.close(fig)
    webp_bytes = webp_buf.getvalue()
    print(f"[regen] WebP burn ({len(webp_bytes)} bytes) prêt pour distribution multi-cible")

    for p in ASSET_PATHS:
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(webp_bytes)
        final = p.stat().st_size
        print(f"[ok] asset sauvé : {p} ({final} bytes)")
    # Affiche le SHA1 partagé pour confirmer byte-identity (doctrine #5780).
    import hashlib
    sha1 = hashlib.sha1(webp_bytes).hexdigest()
    print(f"[ok] SHA1 byte-identique des 2 assets : {sha1}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Regen img1-dalle3.webp + dalle3-cover.webp (issue #8624 + #9348).")
    ap.add_argument("--check", action="store_true", help="Vérifier deps + .env")
    ap.add_argument("--audit", action="store_true", help="Audit rapide (taille assets)")
    args = ap.parse_args()
    if args.check:
        return check()
    if args.audit:
        return audit()
    return regen()


if __name__ == "__main__":
    sys.exit(main())
