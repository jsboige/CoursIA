"""Fusion d'un adaptateur PEFT dans son modele de base, en bf16 (ICT-25a, #5105).

Le regime de la lecture SAE est **dissocie** : la boucle d'entrainement
(QLoRA : base gelee 4-bit + adaptateurs bf16) ne peut pas servir au
readout. Les SAE Qwen-Scope sont entraines sur le residual stream **pleine
precision** ; un readout en 4-bit mesurerait l'arrondi NF4, pas l'effet du
post-training. Le pre-enregistrement de la campagne 2B
(`docs/ict/ict25a-2b-pre-enregistrement.md`, section 1) demande donc un
**rechargement bf16, base + adaptateurs fusionnes**, et declare ce
rebasculement hors perimetre de la campagne : « il sera traite comme un
besoin d'instrument distinct ».

Ce script est cet instrument. Il :

  1. charge la base en **bf16** (jamais quantifiee) ;
  2. applique l'adaptateur PEFT et le **fusionne** ;
  3. ecrit un **repertoire de modele** que `extract_sae_traces.py --model`
     consomme tel quel (poids + `config.json` + tokenizer) ;
  4. certifie le resultat (empreinte SHA-256 des poids, dtype observe,
     identite de la base et de l'adaptateur).

La garde `assert_bf16_readout` (package `ict/`, testable sans GPU) est
appelee sur la configuration **avant** l'ecriture du certificat : un
resultat quantifie ne peut pas etre certifie.

Les imports `torch` / `transformers` / `peft` sont **locaux** a la fonction
de fusion : le module reste importable sans GPU ni torch, ce qui permet a
ses gardes d'etre testees par la suite de tests de la serie (le runner CI
n'a pas de torch).

Usage (device 2 de `myia-ai-01` ; la charge de commit de l'hote doit passer
sous la barre d'admission de la campagne avant le lancement) :

    CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2 \
      python ict25a_merge_bf16.py --base Qwen/Qwen3.5-2B-Base \
        --adapter D:/Dev/ict25a_adapters/N_s0 --out D:/Dev/ict25a_merged/N_s0

Le nom du repertoire de sortie **entre dans le nom de la trace** produite
par `extract_sae_traces.py` (le slug du modele y entre) : un repertoire
nomme par bras et par graine (`N_s0`, `Np_s7`) garde les traces distinctes
d'un run a l'autre.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

# Le package ``ict/`` reste numpy-only : l'importer ici n'introduit pas torch
# dans la bibliotheque (cf docstring de `extract_sae_traces.py`).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ict.sae_traces import assert_bf16_readout  # noqa: E402

CERTIFICAT = "merge_certificat.json"


def sha256_fichier(chemin: str | Path, bloc: int = 1 << 20) -> str:
    """Empreinte SHA-256 d'un fichier, lue par morceaux (pas de lecture
    entiere en memoire : un modele fusionne ne tient pas dans le tas)."""
    h = hashlib.sha256()
    with open(chemin, "rb") as f:
        while True:
            tranche = f.read(bloc)
            if not tranche:
                break
            h.update(tranche)
    return h.hexdigest()


def chemin_publie(chemin: str | Path, base: str | Path | None = None) -> str:
    """Chemin relatif a la base quand le fichier est sous la base de
    l'artefact, sinon le seul nom de fichier : un artefact commite ne
    porte jamais de chemin de machine."""
    p = Path(chemin)
    if base is not None:
        try:
            return p.resolve().relative_to(Path(base).resolve()).as_posix()
        except ValueError:
            pass
    return p.name


def poids_du_repertoire(dossier: str | Path) -> list[Path]:
    """Fichiers de poids d'un repertoire de modele HF (poids unique ou
    decoupe en pieces). Lève si le repertoire n'en porte aucun."""
    d = Path(dossier)
    if not d.is_dir():
        raise FileNotFoundError(f"repertoire de modele absent : {d}")
    uniques = sorted(d.glob("*.safetensors"))
    if uniques:
        return uniques
    index = d / "model.safetensors.index.json"
    if index.is_file():
        data = json.loads(index.read_text(encoding="utf-8"))
        noms = sorted(set(data.get("weight_map", {}).values()))
        fichiers = [d / n for n in noms]
        manquants = [f for f in fichiers if not f.is_file()]
        if manquants:
            raise FileNotFoundError(
                f"pieces de poids absentes : {[f.name for f in manquants]}")
        return fichiers
    raise FileNotFoundError(f"aucun poids dans {d} (ni *.safetensors ni index)")


def certificater(dossier: str | Path, base: str, adaptateur: str,
                 base_artefact: str | Path | None = None) -> dict:
    """Certifie un repertoire de modele fusionne : identite, dtype observe,
    empreintes des poids, garde bf16 appliquee.

    La garde est appliquee **ici**, sur la configuration reellement ecrite
    sur le disque : c'est elle qui decide si le readout est permis, pas
    l'intention du script qui l'a produit.
    """
    d = Path(dossier)
    config_path = d / "config.json"
    if not config_path.is_file():
        raise FileNotFoundError(f"config.json absent de {d}")
    config = json.loads(config_path.read_text(encoding="utf-8"))
    assert_bf16_readout(config.get("quantization_config"))

    poids = poids_du_repertoire(d)
    empreintes = {f.name: sha256_fichier(f) for f in poids}
    dossier_sha = hashlib.sha256(
        "".join(f"{n}:{h}" for n, h in sorted(empreintes.items())).encode("utf-8")
    ).hexdigest()

    return {
        "base": base,
        "adaptateur": adaptateur,
        "dtype_config": str(config.get("dtype") or config.get("torch_dtype")),
        "quantized_readout": False,
        "poids": {f.name: chemin_publie(f, base_artefact) for f in poids},
        "sha256_poids": empreintes,
        "sha256_dossier": dossier_sha,
    }


def fusionner(base: str, adaptateur: str, sortie: str | Path,
              base_artefact: str | Path | None = None) -> dict:
    """Fusionne l'adaptateur dans la base (bf16) et ecrit le repertoire de
    modele, puis renvoie son certificat.

    La base est chargee **sans** `quantization_config` : la garde
    `assert_bf16_readout` refuse ensuite toute sortie quantifiee.
    """
    import torch  # noqa: PLC0415  (import local : le module reste testable)
    from peft import PeftModel  # noqa: PLC0415
    from transformers import (  # noqa: PLC0415
        AutoModelForCausalLM,
        AutoTokenizer,
    )

    out = Path(sortie)
    out.mkdir(parents=True, exist_ok=True)

    tokenizer = AutoTokenizer.from_pretrained(base)
    modele = AutoModelForCausalLM.from_pretrained(base, dtype=torch.bfloat16)
    modele.config.quantization_config = None
    fusionne = PeftModel.from_pretrained(modele, adaptateur).merge_and_unload()
    fusionne.config.quantization_config = None
    fusionne.save_pretrained(str(out), safe_serialization=True)
    tokenizer.save_pretrained(str(out))

    dtype_observe = str(next(fusionne.parameters()).dtype)
    if dtype_observe != "torch.bfloat16":
        raise ValueError(
            f"fusion non bf16 : dtype observe {dtype_observe} — un readout "
            f"SAE sur un modele non pleine precision mesurerait l'arrondi de "
            f"la quantification, pas l'effet du post-training.")

    certificat = certificater(out, base, adaptateur, base_artefact)
    certificat["dtype_observe"] = dtype_observe
    (out / CERTIFICAT).write_text(
        json.dumps(certificat, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8")
    return certificat


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--base", required=True,
                   help="identifiant HF ou chemin du modele de base (bf16)")
    p.add_argument("--adapter", required=True,
                   help="repertoire de l'adaptateur PEFT")
    p.add_argument("--out", required=True,
                   help="repertoire de modele fusionne a ecrire")
    p.add_argument("--base-artefact", default=None,
                   help="racine a partir de laquelle publier les chemins")
    args = p.parse_args(argv)

    certificat = fusionner(args.base, args.adapter, args.out,
                            args.base_artefact)
    print(f"[merge] base={certificat['base']} "
          f"adaptateur={certificat['adaptateur']}")
    print(f"[merge] dtype={certificat['dtype_observe']} "
          f"sha256_dossier={certificat['sha256_dossier'][:12]}")
    for nom, sha in sorted(certificat["sha256_poids"].items()):
        print(f"[merge] poids {nom} sha256={sha[:12]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
