#!/usr/bin/env python
"""Quantification int4 (weight-only, groupes) du modele FishAudio S2-Pro.

L'image officielle `fishaudio/fish-speech` embarque l'outil amont
`tools/llama/quantize.py`. Ce wrapper lui apporte les corrections que
l'outillage d'origine ne fait pas -- chacune mesuree dans l'image :

1. **Construction et chargement sur GPU.** `quantize()` depose le modele sur
   CPU ; or `create_quantized_state_dict()` (mode int4) deplace de toute facon
   chaque matrice de poids sur le CUDA pour l'empaquetage int4
   (`torch.ops.aten._convert_weight_to_int4pack`). Le GPU est donc requis de
   toute facon. On force `device="cuda"` et on construit le modele directement
   sur GPU (`torch.set_default_device`) : sans cela, la construction du modele
   se fait en float32 (les `nn.Linear` par defaut) et le pic memoire depasse
   largement la RAM disponible sur un siege ou la CI tourne.

2. **L'empaquetage int4, reecrit pour torch >= 2.8.** L'amont appelle
   `torch.ops.aten._convert_weight_to_int4pack(codes_int32, ...)`, ecrit pour
   un torch ou l'op acceptait des codes int32. Sur torch 2.8 l'op exige un
   tenseur **uint8** a **deux codes 4 bits par octet**, le code d'indice pair
   etant dans le **nibble haut** ; `scales_and_zeros` doit rester en
   **bfloat16** (en fp32 le noyau rend des valeurs constantes ; en fp16, des
   grandeurs aberrantes). Mesure dans l'image : avec cette disposition, le
   round-trip `pack -> mm` restitue les codes a l'identique (erreur max 0.0) ;
   avec l'ancienne disposition, les codes sortent permutes par paires.

3. **Un seul `model.pth` exploitable.** `quantize()` recopie le dossier source
   dans le dossier quantifie -- shards `.safetensors` et
   `model.safetensors.index.json` compris. Or le chargeur de l'image
   (`BaseTransformer.from_pretrained`) privilegie l'index, puis le shard
   unique, et ne tombe sur `model.pth` qu'en dernier : il chargerait donc les
   poids **bf16 d'origine** et ignorerait la quantification. On retire les
   shards et l'index du dossier de sortie.

4. **Un nom de dossier que le chargeur sait lire.** Le chargeur selectionne
   la branche int4 sur le **nom** du chemin (`if "int4" in str(Path(path))`)
   et en parse le groupsize dans `path.name.split("-")[-2]` (prefixe `g`).
   `quantize.py` produit deja `fs-1.2-int4-g{groupsize}-{timestamp}` : le nom
   est donc deja conforme, et ce wrapper ne fait que le verifier.

Le wrapper **controle** son propre resultat avant d'ecrire : un round-trip
`pack -> mm` sur une matrice de codes connus doit restituer les codes a
l'identique ; sinon il sort en erreur sans produire de checkpoint.

Usage (dans l'image, checkpoints montes sur /app/checkpoints) :

    docker run --rm --gpus '"device=1"' \
      --entrypoint /app/.venv/bin/python \
      -v "$PWD/checkpoints:/app/checkpoints" \
      -v "$PWD/quantize_int4.py:/app/quantize_int4.py:ro" \
      -w /app fishaudio/fish-speech:latest \
      /app/quantize_int4.py --checkpoint-path checkpoints/s2-pro --groupsize 128

Le dossier produit est `checkpoints/fs-1.2-int4-g{groupsize}-{timestamp}/`.
Le decodeur (codec.pth) n'y est pas : `quantize.py` le retire, et le service
continue de le lire via `DECODER_CHECKPOINT_PATH`.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import torch

# Fichiers de poids bf16 a retirer du dossier quantifie : le chargeur de
# l'image les prefere a `model.pth` et chargerait les poids non quantifies.
BF16_WEIGHT_FILES = ("model.safetensors.index.json", "model.safetensors")

INNER_K_TILES = 8


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Quantification int4 weight-only du modele FishAudio S2-Pro."
    )
    parser.add_argument(
        "--checkpoint-path",
        default="checkpoints/s2-pro",
        help="Dossier du checkpoint source (relatif au repertoire de travail).",
    )
    parser.add_argument(
        "--groupsize",
        type=int,
        default=128,
        help="Taille de groupe int4. 32/64/128/256 : seuls groupes acceptes "
        "par l'outil amont.",
    )
    parser.add_argument(
        "--timestamp",
        default=None,
        help="Suffixe horodate du dossier de sortie (defaut : horodatage amont).",
    )
    parser.add_argument(
        "--device",
        default="cuda",
        help="Device de construction et de chargement du modele (cuda|cpu).",
    )
    parser.add_argument(
        "--keep-bf16-shards",
        action="store_true",
        help="Ne pas retirer les shards bf16 du dossier de sortie (debug).",
    )
    return parser.parse_args()


def pack_int4_codes(codes: torch.Tensor, inner_k_tiles: int = INNER_K_TILES) -> torch.Tensor:
    """Empaquette les codes 4 bits non signes pour l'op CUDA de torch >= 2.8.

    L'op attend un uint8 a deux codes par octet, le code d'indice pair dans
    le nibble haut (mesure : round-trip exact avec cette disposition, codes
    permutes par paires avec l'autre).
    """
    out_features, in_features = codes.shape
    pairs = codes.reshape(out_features, in_features // 2, 2).to(torch.int32)
    packed_input = ((pairs[:, :, 0] << 4) | pairs[:, :, 1]).to(torch.uint8)
    return torch.ops.aten._convert_weight_to_int4pack(packed_input.contiguous(), inner_k_tiles)


def verify_packing(groupsize: int, inner_k_tiles: int = INNER_K_TILES, device: str = "cuda") -> float:
    """Round-trip de controle : `pack -> mm` doit restituer les codes exacts.

    Renvoie l'erreur maximale (0.0 attendu). Le noyau dequantifie selon
    `(code - 8) * scale + zero` : avec scale = 1 et zero = 8, il doit rendre
    le code lui-meme.
    """
    out_features, in_features = 16, 128
    codes = (
        torch.arange(in_features, dtype=torch.int32, device=device) % 16
    ).unsqueeze(0).repeat(out_features, 1)

    packed = pack_int4_codes(codes, inner_k_tiles)
    scales_and_zeros = (
        torch.tensor([1.0, 8.0], dtype=torch.bfloat16)
        .expand(in_features // groupsize, out_features, 2)
        .contiguous()
        .to(device)
    )
    x = torch.eye(in_features, dtype=torch.bfloat16, device=device)
    out = torch.ops.aten._weight_int4pack_mm(x, packed, groupsize, scales_and_zeros)
    # out[k, r] = W_dequant[r, k] : la colonne 0 est la ligne 0 dequantifiee.
    error = (out[:, 0].float() - codes[0].float()).abs().max().item()
    return error


def main() -> int:
    args = parse_args()

    if args.device != "cpu" and not torch.cuda.is_available():
        print("[quantize_int4] CUDA indisponible : --device cpu exige", file=sys.stderr)
        return 2

    # Les poids amont sont en bfloat16 : construire le modele en float32
    # (defaut de nn.Linear) doublerait le pic memoire pour rien.
    torch.set_default_dtype(torch.bfloat16)
    if args.device != "cpu":
        # Construction directe sur GPU : les parametres du modele ne sont
        # jamais alloues en RAM hote.
        torch.set_default_device(args.device)

    import tools.llama.quantize as upstream

    original_init_model = upstream.init_model

    def init_model_on_device(*args_, **kwargs):
        kwargs["device"] = args.device
        return original_init_model(*args_, **kwargs)

    upstream.init_model = init_model_on_device

    # Empaquetage corrige (voir le point 2 de la docstring du module).
    def prepare_int4_weight_and_scales_and_zeros(weight_bf16, groupsize, inner_k_tiles=INNER_K_TILES):
        codes, scales_and_zeros = upstream.group_quantize_tensor(
            weight_bf16, n_bit=4, groupsize=groupsize
        )
        return pack_int4_codes(codes, inner_k_tiles), scales_and_zeros

    upstream.prepare_int4_weight_and_scales_and_zeros = (
        prepare_int4_weight_and_scales_and_zeros
    )

    error = verify_packing(args.groupsize, device=args.device)
    print(f"[quantize_int4] controle d'empaquetage : erreur max = {error}")
    if error != 0.0:
        print(
            "[quantize_int4] l'empaquetage int4 ne restitue pas les codes : "
            "aucun checkpoint n'est ecrit",
            file=sys.stderr,
        )
        return 3

    checkpoint_path = Path(args.checkpoint_path)
    timestamp = args.timestamp if args.timestamp else "None"

    print(f"[quantize_int4] source={checkpoint_path} mode=int4 groupsize={args.groupsize}")
    # `quantize` est une commande click : on appelle son callback, pas l'objet
    # Command (qui, lui, attend une liste d'arguments).
    quantize_callback = getattr(upstream.quantize, "callback", upstream.quantize)
    quantize_callback(checkpoint_path, "int4", args.groupsize, timestamp)

    # Le dossier produit porte le nom que le chargeur sait lire.
    suffix = timestamp if timestamp != "None" else _latest_timestamp(checkpoint_path)
    destination = Path(f"checkpoints/fs-1.2-int4-g{args.groupsize}-{suffix}")

    if not destination.exists():
        print(
            f"[quantize_int4] dossier de sortie introuvable : {destination}",
            file=sys.stderr,
        )
        return 1

    if not args.keep_bf16_shards:
        removed = []
        for name in BF16_WEIGHT_FILES:
            path = destination / name
            if path.exists():
                path.unlink()
                removed.append(name)
        for path in sorted(destination.glob("model-*.safetensors")):
            path.unlink()
            removed.append(path.name)
        if removed:
            print(f"[quantize_int4] poids bf16 retires du dossier quantifie : {removed}")

    model_pth = destination / "model.pth"
    if not model_pth.exists():
        print("[quantize_int4] model.pth absent du dossier de sortie", file=sys.stderr)
        return 1

    size_gb = model_pth.stat().st_size / (1024**3)
    print(
        f"[quantize_int4] sortie={destination} model.pth={size_gb:.2f} Go\n"
        f"[quantize_int4] pour charger : LLAMA_CHECKPOINT_PATH={destination}"
    )
    return 0


def _latest_timestamp(checkpoint_path: Path) -> str:
    """Retrouve l'horodatage du dossier que l'outil amont vient d'ecrire."""
    parent = Path("checkpoints")
    candidates = sorted(parent.glob("fs-1.2-int4-g*-*"), key=lambda p: p.stat().st_mtime)
    if not candidates:
        return ""
    return candidates[-1].name.rsplit("-", 1)[-1]


if __name__ == "__main__":
    sys.exit(main())
