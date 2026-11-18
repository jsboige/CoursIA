#!/usr/bin/env python3
"""Mesure l'empreinte d'encodage d'un environnement Pillow (#20865).

Pourquoi cet organe
--------------------
Les carnets de la serie GenAI/Image citent en prose des **tailles en octets**
produites par l'encodeur de leur environnement (PNG, JPEG, WEBP). Ces tailles
ne sont pas des proprietes de l'image : elles dependent de la version de
Pillow installee, et du moteur de compression qu'elle embarque. Deux
environments qui ne different que par Pillow produisent des octets differents
pour la meme image -- la prose du carnet, elle, ne bouge pas.

La question de #20865 etait « qui fait bouger les tailles : Pillow ou zlib ? ».
Cet organe repond, dans l'environnement courant, en reproduisant les encodages
du carnet sur des images **deterministes** (aucun reseau, aucune graine
externe) et en publiant l'empreinte de l'environnement qui les a produites.

Ce que l'empreinte contient
----------------------------
- la version de Pillow ;
- la version de zlib **embarquee dans Pillow** (``PIL.features.version("zlib")``)
  -- c'est celle qui sérialise reellement les PNG ;
- la version de zlib de l'interpreteur (``zlib.ZLIB_VERSION`` /
  ``zlib.ZLIB_RUNTIME_VERSION``), qui n'intervient que si l'encodeur y recur.

Les deux etant distinctes, la mesure permet de trancher par controle :
meme interpreteur + Pillow differente, puis meme Pillow + interpreteur
differente.

Usage
-----
    python scripts/notebook_tools/measure_image_encoding_env.py            # rapport texte
    python scripts/notebook_tools/measure_image_encoding_env.py --json     # sortie structuree

Sortie : JSON (empreinte + tailles en octets + empreintes SHA-256 des octets
produits) ; le mode texte affiche le tableau lisible.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import zlib
from io import BytesIO
from typing import Any, Dict

# Dimensions et graine reprises telles quelles du carnet
# `GenAI/Image/01-Foundation/01-3-Basic-Image-Operations.ipynb` (cellule 32
# pour le bruit, cellule 38 pour les comparaisons de formats).
IMAGE_SIZE = (800, 600)
NOISE_SEED = 20260906
SD_TARGET_SIZE = (768, 768)

# Encodages mesures : (cle, format, kwargs). PNG est enregistre deux fois car
# `optimize=True` change la taille -- c'est le cas que la prose cite.
ENCODAGES = (
    ("PNG", "PNG", {}),
    ("PNG_OPT", "PNG", {"optimize": True}),
    ("JPEG_Q75", "JPEG", {"quality": 75, "optimize": True}),
    ("JPEG_Q85", "JPEG", {"quality": 85, "optimize": True}),
    ("JPEG_Q95", "JPEG", {"quality": 95, "optimize": True}),
    ("WEBP_Q90", "WEBP", {"quality": 90}),
)


def empreinte_env() -> Dict[str, Any]:
    """Version de l'interpreteur, de zlib et de Pillow (zlib embarque inclus)."""
    env: Dict[str, Any] = {
        "python": sys.version.split()[0],
        "zlib_runtime": zlib.ZLIB_VERSION,
        "zlib_compiled": zlib.ZLIB_RUNTIME_VERSION,
    }
    try:
        from PIL import Image, features

        env["pillow"] = getattr(Image, "__version__", "N/A")
        env["pillow_zlib"] = features.version("zlib")
    except ImportError:
        env["pillow"] = None
        env["pillow_zlib"] = None
    return env


def image_degrade(taille=IMAGE_SIZE, mode: str = "RGB"):
    """Le degrade de repli du carnet (`create_test_image`) : 100 % deterministe."""
    from PIL import Image

    largeur, hauteur = taille
    img = Image.new(mode, (largeur, hauteur))
    pixels = img.load()
    for y in range(hauteur):
        for x in range(largeur):
            r = int((x / largeur) * 255)
            g = int((y / hauteur) * 255)
            pixels[x, y] = (r, g, 128)
    return img


def image_bruit(taille=IMAGE_SIZE, graine: int = NOISE_SEED):
    """Le bruit deterministe du carnet (`random.Random(20260906)`)."""
    from PIL import Image

    rng = random.Random(graine)
    img = Image.new("RGB", taille)
    pixels = img.load()
    largeur, hauteur = taille
    for y in range(hauteur):
        for x in range(largeur):
            pixels[x, y] = (rng.randint(0, 255), rng.randint(0, 255), rng.randint(0, 255))
    return img


def encoder(img, fmt: str, kwargs: Dict[str, Any]) -> bytes:
    from PIL import Image

    a_encoder = img if fmt != "JPEG" or img.mode not in ("RGBA", "LA", "P") else img.convert("RGB")
    buffer = BytesIO()
    a_encoder.save(buffer, format=fmt, **kwargs)
    return buffer.getvalue()


def mesurer() -> Dict[str, Any]:
    """Mesure les encodages du carnet sur les images deterministes."""
    from PIL import Image

    degrade = image_degrade()
    bruit = image_bruit()
    bruit_sd = bruit.resize(SD_TARGET_SIZE, Image.Resampling.LANCZOS)

    cas = {
        "degrade_800x600": degrade,
        "bruit_768x768_sd": bruit_sd,
    }
    resultats: Dict[str, Any] = {}
    for nom_cas, img in cas.items():
        par_encodage = {}
        for cle, fmt, kwargs in ENCODAGES:
            octets = encoder(img, fmt, kwargs)
            par_encodage[cle] = {
                "octets": len(octets),
                "sha256": hashlib.sha256(octets).hexdigest()[:16],
            }
        resultats[nom_cas] = par_encodage
    return {"env": empreinte_env(), "encodages": resultats}


def rapport(mesure: Dict[str, Any]) -> str:
    env = mesure["env"]
    lignes = [
        "Environnement",
        f"  python            : {env['python']}",
        f"  pillow            : {env['pillow']}",
        f"  zlib (interpreteur): runtime {env['zlib_runtime']} / compile {env['zlib_compiled']}",
        f"  zlib (embarque Pillow): {env['pillow_zlib']}",
        "",
    ]
    for nom_cas, par_encodage in mesure["encodages"].items():
        lignes.append(nom_cas)
        for cle, data in par_encodage.items():
            lignes.append(f"  {cle:<10} {data['octets']:>10} octets   sha256:{data['sha256']}")
        lignes.append("")
    return "\n".join(lignes)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--json", action="store_true", help="Sortie JSON structuree")
    args = parser.parse_args()

    mesure = mesurer()
    if args.json:
        print(json.dumps(mesure, indent=2, ensure_ascii=False))
    else:
        print(rapport(mesure))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
