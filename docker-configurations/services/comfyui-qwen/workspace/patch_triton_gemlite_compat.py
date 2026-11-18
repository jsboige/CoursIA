#!/usr/bin/env python3
"""Compat triton 3.x / gemlite 0.4.x : le pruner de gemlite est un generateur.

Symptome observe (service comfyui-qwen, noeud ComfyUI-Bonsai-4B-2Bit) :

    File ".../triton/runtime/autotuner.py", line 232, in run
        if len(pruned_configs) == 1:
    TypeError: object of type 'generator' has no len()

Cause racine : gemlite 0.4.6 ecrit ses `early_config_prune` sous forme de fonction
generatrice (`yield triton.Config(...)`), alors que triton 3.8.0 consume le retour
comme une collection **taillee** (`len(pruned_configs)`, `len(pruned_configs) > top_k`,
`pruned_configs[0]`). Le contrat de `early_config_prune` est cote gemlite ; c'est
l'appelant qui materialise.

Le correctif materialise le retour du pruner d'une seule ligne :

    -            pruned_configs = self.early_config_prune(self.configs, self.nargs, **kwargs)
    +            pruned_configs = list(self.early_config_prune(self.configs, self.nargs, **kwargs))

Comportement preserve : le generateur est consomme une fois, dans le meme ordre,
avec le meme contenu ; le chemin "cache hit" de gemlite (un seul `yield` puis
`return`) produit toujours une liste de taille 1, que triton traite par le chemin
"single config, pas de benchmark".

Idempotent : rejouer le script sur un venv deja patche ne change rien (exit 0).
Exit codes : 0 = patche ou deja patche, 2 = echec (layout inconnu, fichier absent).

Usage :
    python3 patch_triton_gemlite_compat.py --venv /workspace/ComfyUI/venv
    python patch_triton_gemlite_compat.py --venv D:/.../workspace/venv
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

NEEDLE = "pruned_configs = self.early_config_prune(self.configs, self.nargs, **kwargs)"
PATCHED = "pruned_configs = list(self.early_config_prune(self.configs, self.nargs, **kwargs))"
RELATIVE = ("lib", "python3.11", "site-packages", "triton", "runtime", "autotuner.py")


def find_targets(venv: Path) -> list[Path]:
    """Cible le(s) autotuner.py de triton dans le venv donne."""
    lib = venv / "lib"
    if not lib.is_dir():
        return []
    return sorted(lib.glob("python*/site-packages/triton/runtime/autotuner.py"))


def patch_file(path: Path) -> str:
    """Retourne 'patched', 'already' ou 'unknown'."""
    text = path.read_text(encoding="utf-8")
    if PATCHED in text:
        return "already"
    if NEEDLE not in text:
        return "unknown"
    patched = text.replace(NEEDLE, PATCHED)
    path.write_text(patched, encoding="utf-8")
    # Verification immediate : le patch doit etre present, et l'ancien texte absent.
    reread = path.read_text(encoding="utf-8")
    if PATCHED not in reread or NEEDLE in reread:
        raise RuntimeError(f"verification post-ecriture echouee sur {path}")
    return "patched"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--venv", required=True, help="racine du venv (contient lib/pythonX.Y/site-packages)")
    args = parser.parse_args(argv)

    venv = Path(args.venv).resolve()
    targets = find_targets(venv)
    if not targets:
        print(f"[triton-gemlite-compat] ERREUR: aucun autotuner.py de triton sous {venv}", file=sys.stderr)
        return 2

    rc = 0
    for target in targets:
        try:
            state = patch_file(target)
        except Exception as exc:  # noqa: BLE001 - rapporte et poursuit sur les autres cibles
            print(f"[triton-gemlite-compat] ECHEC {target}: {exc}", file=sys.stderr)
            rc = 2
            continue
        if state == "unknown":
            # Layout inconnu : ni la forme attendue, ni deja patche. Un triton futur
            # qui deplacerait la ligne doit rendre le boot BRUYANT, pas silencieusement
            # non patche (docstring : exit 2). Le message va sur stderr pour que le
            # `|| echo` de l'entrypoint le relaye comme avertissement de demarrage.
            print(
                f"[triton-gemlite-compat] layout INCONNU: {target} "
                "(needle absent et fichier non deja patche) -- triton a change, patch a reexaminer",
                file=sys.stderr,
            )
            rc = 2
            continue
        print(f"[triton-gemlite-compat] {state}: {target}")

    if rc == 0:
        print("[triton-gemlite-compat] OK")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
