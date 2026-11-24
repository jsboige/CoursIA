"""Persistance des adaptateurs QLoRA de la campagne ICT-25a (#5105).

Le runner `ict25a_scaleup_grpo.py` entraine en QLoRA (`peft_config=lora`)
mais ne persistant **jamais** l'adaptateur : `save_strategy="no"` et aucun
`save_pretrained`. Mesure du 24/11 : aucun adaptateur de la campagne 2B du
20/11 n'existe sur le disque -- le bloc `trained` de la lecture SAE
(`extract_sae_traces.py --variant trained`) n'a donc **rien a recharger**, et
la moitie « panel persona » de la Gate 21 n'a pas d'instrument.

Ce module porte la persistance et sa **certification** : le SHA-256 de
l'adaptateur ecrit, et le chemin *publie* (relatif quand il est sous la base
de l'artefact) -- les poids ne sont jamais committes, mais l'artefact doit
dire **quels** poids ont produit la lecture.

Fonctions :
    `sha256_fichier` : empreinte d'un fichier, en morceaux (pas de lecture
                       entiere en memoire) ;
    `chemin_publie`  : chemin relatif a la base quand il est sous elle, sinon
                       le seul nom de fichier -- un artefact commite ne porte
                       jamais de chemin de machine ;
    `sauver_adaptateur` : ecrit l'adaptateur du modele PEFT et rend sa
                       certification.
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
from typing import Any


def sha256_fichier(chemin: os.PathLike[str] | str, bloc: int = 1 << 20) -> str:
    """Empreinte SHA-256 d'un fichier, lue par blocs.

    :param chemin: fichier a empreinter.
    :param bloc: taille de lecture, en octets.
    :return: l'empreinte hexadecimale.
    """
    h = hashlib.sha256()
    with open(chemin, "rb") as fh:
        while True:
            morceau = fh.read(bloc)
            if not morceau:
                break
            h.update(morceau)
    return h.hexdigest()


def chemin_publie(chemin: os.PathLike[str] | str,
                  base: os.PathLike[str] | str | None = None) -> str:
    """Chemin publiable dans un artefact commite.

    Un chemin relatif a `base` est rendu tel quel ; hors de `base`, seul le nom
    de fichier est conserve -- un artefact commite ne porte jamais de chemin de
    machine.

    :param chemin: chemin a publier.
    :param base: base de relativisation ; le repertoire courant par defaut.
    :return: le chemin publie.
    """
    p = Path(chemin)
    racine = Path(base) if base is not None else Path.cwd()
    try:
        return p.resolve().relative_to(racine.resolve()).as_posix()
    except ValueError:
        return p.name


def sauver_adaptateur(modele: Any, dest: os.PathLike[str] | str,
                       base: os.PathLike[str] | str | None = None) -> dict[str, str]:
    """Ecrit l'adaptateur PEFT du modele et rend sa certification.

    :param modele: modele PEFT (captation de `save_pretrained`).
    :param dest: repertoire de destination de l'adaptateur.
    :param base: base de relativisation du chemin publie.
    :return: la certification de l'adaptateur ecrit.
    """
    d = Path(dest)
    d.mkdir(parents=True, exist_ok=True)
    modele.save_pretrained(str(d), safe_serialization=True)
    poids = d / "adapter_model.safetensors"
    if not poids.is_file():
        raise FileNotFoundError(f"adaptateur non ecrit : {poids}")
    return {"fichier": chemin_publie(poids, base), "sha256": sha256_fichier(poids)}
