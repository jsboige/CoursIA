"""Batterie de sondes et echantillonnage d'activations -- run instrumente du panel persona.

Pourquoi ce module existe
-------------------------
Le panel persona (`docs/ict/ict25-panel-persona-pre-enregistrement.md`, issue
#26945 T1, suivi #5105 Gates 20-21) lit des **activations reelles**, pas un
`.npz` synthetique. Lire des activations suppose qu'elles aient ete
**echantillonnees pendant l'entrainement** : or les runs existants ne les
portent pas (`ict25a_scaleup_grpo.py` : `save_strategy="no"`, `output_dir`
ephemere horodate, artefacts sans tenseur). Le §6 du pre-enregistrement liste
ce que le run instrumente doit produire :

  1. des **checkpoints persistants**, hors `/tmp` ;
  2. un **echantillonnage d'activations a chaque checkpoint**, sur une
     batterie de sondes **fixe** (memes prompts a tous les checkpoints, meme
     graine de generation), avec la **couche** et la **position** declarees.

Ce module porte la partie **pure** de ce contrat : la batterie, son
empreinte, l'ecriture du `.npz` et du manifeste. Il ne depend que de `numpy`
et de la bibliotheque standard -- et il **n'importe ni torch ni transformers** :
il est donc testable sur CPU, et le test mesure le contrat lui-meme, pas une
imitation.

Le contrat, en sept points
--------------------------
  * la batterie est **fixe** : meme liste de prompts, meme graine de
    generation, quel que soit le checkpoint ;
  * chaque echantillon porte un **identifiant de prompt** (`p01`...), et le
    `.npz` porte la **couche** et la **position** declarees ;
  * le manifeste porte l'**empreinte SHA-256** de la batterie, du `.npz` et de
    **chaque vecteur** : une activation qui change change le manifeste, donc
    le manifeste **detecte** la derive au lieu de la cacher ;
  * le manifeste porte le **modele**, la **couche**, la **position**, le **pas**
    (etape du checkpoint), la **graine** et la **graine de generation** ;
  * les chemins sont **stables** et **hors repertoire temporaire** : un
    artefact ecrit dans un dossier ephemere ne survit pas au run -- c'est
    precisement ce qui rend le panel impossible aujourd'hui ;
  * `forward_transformers` est **duck-type** : il ne fait aucun `import
    torch` (le gradient est coupe par l'appelant), et un modele de test peut
    donc le piloter sans GPU ;
  * le module ne tient **aucun verdict** : il ecrit des faits, le lecteur
    tranche.

Usage :

    from ict25a_probe_battery import (BATTERIE, charger_batterie, chemin_artefact,
                                       echantillonner, ecrire_manifeste,
                                       ecrire_npz, forward_transformers)
"""
from __future__ import annotations

import hashlib
import json
import os
import tempfile
from collections.abc import Callable, Mapping, Sequence
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

#: Graine de generation **fixe** de la batterie. Elle est declaree dans le
#: `.npz` et dans le manifeste : deux checkpoints echantillonnes avec la meme
#: graine sont comparables, deux echantillons avec des graines differentes ne
#: le sont pas.
PROBE_SEED = 20261124

#: Positions de lecture supportees. `last` lit la derniere position de la
#: sequence ; `mean` moyenne toutes les positions.
POSITIONS = ("last", "mean")

#: La batterie de sondes -- FIXE, par construction. Les prompts sont ceux de la
#: famille du protocole ICT-25 (meme grammaire des paires arithmetiques) : le
#: panel mesure une persona **sur la distribution de la campagne**, pas sur une
#: distribution etrangere. Un ajout de prompt change l'empreinte de la
#: batterie -- c'est volontaire : une batterie modifiee invalide la comparaison
#: entre checkpoints.
BATTERIE: tuple[dict[str, str], ...] = (
    {"id": "p01", "prompt": "Combien font 3+4 ?"},
    {"id": "p02", "prompt": "Combien font 2+5 ?"},
    {"id": "p03", "prompt": "Combien font 6+1 ?"},
    {"id": "p04", "prompt": "Combien font 4+4 ?"},
    {"id": "p05", "prompt": "Combien font 5+5 ?"},
)


def ecrire_batterie(racine: os.PathLike | str,
                    batterie: Sequence[Mapping[str, str]] = BATTERIE,
                    graine: int = PROBE_SEED) -> Path:
    """Ecrit la batterie **sur disque** et la relit depuis le disque.

    Le run instrumente lit sa batterie depuis un fichier, jamais depuis une
    variable en memoire : le fichier dit quelle batterie a produit les
    activations, et deux runs qui lisent deux fichiers differents ne sont pas
    comparables.
    """
    base = Path(racine)
    base.mkdir(parents=True, exist_ok=True)
    chemin = base / "batterie.json"
    chemin.write_text(json.dumps(
        {"seed": int(graine),
         "prompts": [{"id": str(p["id"]), "prompt": str(p["prompt"])} for p in batterie]},
        indent=2, ensure_ascii=False), encoding="utf-8")
    return chemin


def plan_instrumentation(checkpoint_dir: os.PathLike | str | None = None,
                         probe_battery: os.PathLike | str | None = None,
                         *, save_steps: int | None = None,
                         couche: str = "last",
                         position: str = "last") -> dict[str, object]:
    """Construit le **plan** d'instrumentation d'un run (fonction pure).

    Sans `checkpoint_dir`, le plan est **vide** : le run n'est pas instrumente
    et son comportement est celui d'hier (c'est le mode par defaut, jamais un
    chemin degrade). Avec `checkpoint_dir`, le plan porte la racine **stable**,
    la batterie et son empreinte, la couche et la position declarees.

    `probe_battery` sans `checkpoint_dir` est **refuse** : des activations
    ecrites dans un repertoire temporaire ne survivraient pas au run.
    """
    if probe_battery and not checkpoint_dir:
        raise ValueError(
            "--probe-battery exige --checkpoint-dir : les activations echantillonnees "
            "doivent etre ecrites hors du repertoire temporaire")
    if not checkpoint_dir:
        return {}
    if position not in POSITIONS:
        raise ValueError(f"position inconnue : {position} (attendues : {POSITIONS})")
    racine = verifier_racine_stable(checkpoint_dir)
    if probe_battery:
        prompts, graine = charger_batterie(probe_battery)
    else:
        prompts, graine = BATTERIE, PROBE_SEED
    plan: dict[str, object] = {
        "checkpoint_dir": str(racine),
        "batterie": prompts,
        "graine_batterie": graine,
        "empreinte_batterie": empreinte_batterie(prompts, graine),
        "couche": str(couche),
        "position": str(position),
    }
    if save_steps:
        plan["save_steps"] = int(save_steps)
    return plan


def _sha256_octets(octets: bytes) -> str:
    return hashlib.sha256(octets).hexdigest()


def _sha256_fichier(chemin: Path) -> str:
    h = hashlib.sha256()
    with open(chemin, "rb") as f:
        for bloc in iter(lambda: f.read(1 << 20), b""):
            h.update(bloc)
    return h.hexdigest()


def _sha256_vecteur(vecteur: np.ndarray) -> str:
    """Empreinte d'un vecteur d'activation, en octets float64 contigus.

    Le vecteur est caste explicitement : le meme tenseur lu en float32 et en
    float64 ne doit pas produire deux empreintes differentes pour la meme
    valeur mesuree.
    """
    arr = np.ascontiguousarray(np.asarray(vecteur, dtype=np.float64))
    return _sha256_octets(arr.tobytes())


def empreinte_batterie(batterie: Sequence[Mapping[str, str]] = BATTERIE,
                        graine: int = PROBE_SEED) -> str:
    """SHA-256 de la batterie canonique (prompts + graine de generation)."""
    charge = {
        "graine": int(graine),
        "prompts": [{"id": str(p["id"]), "prompt": str(p["prompt"])} for p in batterie],
    }
    canonique = json.dumps(charge, sort_keys=True, ensure_ascii=False,
                           separators=(",", ":"))
    return _sha256_octets(canonique.encode("utf-8"))


def charger_batterie(chemin: os.PathLike | str) -> tuple[tuple[dict[str, str], ...], int]:
    """Lit une batterie depuis un JSON (`{"seed": ..., "prompts": [...]}`).

    Le fichier porte la **graine** : un run instrumente lit sa batterie depuis
    le disque, il ne la reconstruit pas -- deux checkpoints echantillonnes avec
    deux fichiers differents ne sont pas comparables, et le manifeste le dit.
    """
    data = json.loads(Path(chemin).read_text(encoding="utf-8"))
    prompts = tuple({"id": str(p["id"]), "prompt": str(p["prompt"])}
                     for p in data["prompts"])
    if not prompts:
        raise ValueError(f"batterie vide : {chemin}")
    return prompts, int(data.get("seed", PROBE_SEED))


def verifier_racine_stable(racine: os.PathLike | str) -> Path:
    """Renvoie la racine resolue, et **refuse** un dossier temporaire.

    Un artefact ecrit sous le repertoire temporaire du systeme ne survit pas au
    run : c'est la cause mesuree de l'impossibilite du panel (§5 du
    pre-enregistrement). Le refus est explicite plutot que silencieux.
    """
    resolu = Path(racine).expanduser().resolve()
    temporaire = Path(tempfile.gettempdir()).resolve()
    try:
        resolu.relative_to(temporaire)
    except ValueError:
        return resolu
    raise ValueError(
        f"racine d'artefacts temporaire refusee : {resolu} "
        f"(elle est sous {temporaire} ; un artefact ecrit la ne survit pas au run)")


def chemin_artefact(racine: os.PathLike | str, bras: str, graine: int, etape: int,
                     suffixe: str = ".npz") -> Path:
    """Chemin **stable** d'un artefact du run instrumente.

    Le nom porte le bras, la graine et le pas : deux checkpoints ecrits par le
    meme run ne s'ecrasent pas, et l'artefact d'un run se relit sans le log.
    """
    base = verifier_racine_stable(racine)
    return base / f"ict25a_{bras}_s{int(graine)}_step{int(etape)}{suffixe}"


def _vers_numpy(tenseur) -> np.ndarray:
    if isinstance(tenseur, np.ndarray):
        return tenseur
    detach = tenseur.detach()
    try:
        return np.asarray(detach.cpu().numpy(), dtype=np.float64)
    except TypeError:
        # **bfloat16 -> float32 avant numpy** (mesure du 2026-11-24 : numpy ne
        # sait pas lire le `ScalarType BFloat16` de torch -- `TypeError: Got
        # unsupported ScalarType BFloat16`). Le cast se fait par la methode
        # `.float()` du tenseur : aucun import torch, et un tenseur de test
        # dont la conversion reussit ne passe jamais par ce chemin.
        if not hasattr(detach, "float"):
            raise
        return np.asarray(detach.float().cpu().numpy(), dtype=np.float64)


def forward_transformers(model, tokenizer, prompt: str,
                          couche: int | None = None) -> np.ndarray:
    """`forward` duck-type pour un modele transformers -- **aucun import torch**.

    Le modele est appele avec `output_hidden_states=True` ; l'etat cache
    demande est lu. `couche` est l'index dans `hidden_states` (`0` = embeddings
    de sortie, `len-1` = derniere couche) ; `None` prend la derniere.

    **Convention d'indexation** : `hidden_states[0]` est la sortie d'embedding
    et `hidden_states[i + 1]` la sortie du bloc `i`. L'instrument de la meme
    serie `measure_truth_geometry_rung.py` lit `hidden_states[layer + 1]` :
    son `layer` (0-based sur les blocs) correspond donc a `couche = layer + 1`
    ici. Les deux lectures sont **comparables** a cette translation pres.

    L'appelant (le runner) coupe le gradient : ce module ne manipule aucun
    objet torch, et un modele de test peut donc le piloter sur CPU.

    **Les entrees du tokenizer sont deplacees sur le peripheral du modele**
    (mesure du 2026-11-24 : un `tokenizer(..., return_tensors="pt")` rend des
    tenseurs **CPU**, et un modele charge sur `cuda:0` refuse alors
    `Expected all tensors to be on the same device, but got index is on cpu`).
    Le deplacement passe par l'attribut `device` du modele -- pas d'import
    torch : un modele sans `device` (CPU, modele de test) est laisse intact.
    """
    entrees = tokenizer(prompt, return_tensors="pt")
    peripherique = getattr(model, "device", None)
    if peripherique is not None:
        if hasattr(entrees, "to"):
            entrees = entrees.to(peripherique)
        else:
            entrees = {cle: (valeur.to(peripherique)
                             if hasattr(valeur, "to") else valeur)
                       for cle, valeur in entrees.items()}
    sorties = model(**entrees, output_hidden_states=True)
    etats = getattr(sorties, "hidden_states", None)
    if not etats:
        raise RuntimeError("le modele n'a pas rendu `hidden_states`")
    index = len(etats) - 1 if couche is None else int(couche)
    if index < 0 or index >= len(etats):
        raise IndexError(f"couche {index} hors plage (0..{len(etats) - 1})")
    return _vers_numpy(etats[index][0])


def echantillonner(forward: Callable[[str], np.ndarray],
                   batterie: Sequence[Mapping[str, str]] = BATTERIE,
                   position: str = "last") -> dict[str, np.ndarray]:
    """Echantillonne la batterie : `{identifiant de prompt} -> vecteur`.

    `forward` renvoie le tenseur `[positions, dimension]` du prompt ; la
    position demandee (`last` ou `mean`) en extrait **un** vecteur par prompt.
    """
    if position not in POSITIONS:
        raise ValueError(f"position inconnue : {position} (attendues : {POSITIONS})")
    echantillons: dict[str, np.ndarray] = {}
    for item in batterie:
        tenseur = np.asarray(forward(str(item["prompt"])), dtype=np.float64)
        if tenseur.ndim != 2:
            raise ValueError(
                f"le forward doit renvoyer [positions, dimension], recu {tenseur.shape}")
        vecteur = tenseur[-1] if position == "last" else tenseur.mean(axis=0)
        echantillons[str(item["id"])] = np.ascontiguousarray(vecteur, dtype=np.float64)
    return echantillons


def ecrire_npz(chemin: os.PathLike | str,
                echantillons: Mapping[str, np.ndarray],
                *, couche: str, position: str,
                empreinte: str | None = None,
                graine: int = PROBE_SEED) -> Path:
    """Ecrit le `.npz` : les vecteurs, plus les **declarations** exigees.

    Le `.npz` porte la couche, la position, la graine de generation et
    l'empreinte de la batterie : le fichier se lit seul, sans son manifeste.
    """
    cible = Path(chemin)
    cible.parent.mkdir(parents=True, exist_ok=True)
    donnees = {str(k): np.asarray(v, dtype=np.float64) for k, v in echantillons.items()}
    donnees["__couche__"] = np.array(str(couche))
    donnees["__position__"] = np.array(str(position))
    donnees["__graine_generation__"] = np.array(int(graine))
    donnees["__batterie__"] = np.array(str(empreinte or empreinte_batterie()))
    np.savez_compressed(str(cible), **donnees)
    return cible


def ecrire_manifeste(chemin: os.PathLike | str,
                      echantillons: Mapping[str, np.ndarray],
                      npz_chemin: os.PathLike | str,
                      *, bras: str, graine: int, etape: int, modele: str,
                      couche: str, position: str,
                      empreinte: str | None = None,
                      graine_generation: int = PROBE_SEED) -> Path:
    """Ecrit le manifeste JSON du checkpoint : declarations + empreintes.

    Le manifeste est ce qui rend l'echantillon **falsifiable** : il porte le
    SHA-256 du `.npz` et de **chaque** vecteur, donc une activation qui derive
    d'un checkpoint a l'autre se voit dans le manifeste, sans reexecuter quoi
    que ce soit.
    """
    cible = Path(chemin)
    cible.parent.mkdir(parents=True, exist_ok=True)
    npz = Path(npz_chemin)
    charge = {
        "schema": 1,
        "cree_le_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "bras": str(bras),
        "graine": int(graine),
        "etape": int(etape),
        "modele": str(modele),
        "couche": str(couche),
        "position": str(position),
        "graine_generation": int(graine_generation),
        "empreinte_batterie": str(empreinte or empreinte_batterie()),
        "npz": {"chemin": npz.name, "sha256": _sha256_fichier(npz)},
        "prompts": {
            str(pid): {"sha256": _sha256_vecteur(v),
                       "norme": float(np.linalg.norm(np.asarray(v, dtype=np.float64)))}
            for pid, v in echantillons.items()
        },
    }
    cible.write_text(json.dumps(charge, indent=2, ensure_ascii=False), encoding="utf-8")
    return cible
