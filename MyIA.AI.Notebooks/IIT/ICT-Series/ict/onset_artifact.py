"""Schema de l'artefact du runner onset — module pur, sans dependance lourde.

Le runner :mod:`ict.onset_runner` importe torch / trl / peft au chargement : un test
qui voudrait verifier la forme de l'artefact devrait donc payer l'import du stack
d'entrainement, et ne pourrait pas tourner sur une machine sans lui. Le schema vit
donc ici, sans dependance, et le runner le consomme.

**Pourquoi le budget de completion est dans l'artefact (#21998).** Un artefact de
mesure qui ne dit pas sous quel regime de troncature il a ete produit n'est pas
relisible : `ict25_arms.py` a servi pendant des semaines des comparaisons entre un
bras a cap 1024 et un bras a cap 80 sans que rien, dans les fichiers, ne permette
de le voir. Le defaut a ete corrige la-bas le 2026-10-23 ; ce module porte la meme
exigence pour les runs onset — `max_completion_length` y est ecrit au niveau de
l'artefact **et** dans chaque resultat de graine.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

import numpy as np

# 1024 est le regime **mesure** des artefacts de reference de la serie : les
# artefacts `ict25_onset-W_120steps.json` / `_S_120steps.json` (modele 0.5B,
# 120 steps) portent `script = ict25_arms.py` et `git_commit = 602c2ca5975b` /
# `bef6527045b6`, et a ces commits l'ecrivain passait
# `max_completion_length=1024` a `GRPOConfig`. La constante homonyme de
# `scripts/ict25_records.py` — celle qu'`ict25_arms.py` importe — vaut 1024.
#
# 80 n'est PAS ce regime : c'est un regime heredier qui tronque systematique
# (mesure EOS de #13596 : min = max = 80 sur 40/40 steps, masque de troncature
# actif, perte et gradient nuls). Le garder par defaut mettrait un run neuf
# hors du regime des artefacts auxquels on le compare — et le ferait sans que
# personne l'ait decide. Le cap est un parametre de protocole, pas une
# propriete du modele : d'ou son enregistrement dans l'artefact (#21998).
DEFAULT_MAX_COMPLETION_LENGTH = 1024

SCRIPT_ID = "ict/onset_runner.py"


def artifact_payload(*, model: str, max_steps: int, lr: float, num_gen: int, seeds: list[int],
                     max_completion_length: int, results: dict[str, Any],
                     summary: dict[str, Any]) -> dict[str, Any]:
    """Assemble le JSON d'artefact d'un run onset. Fonction pure, sans effet de bord.

    Les cles ``script`` et ``max_completion_length`` ne sont pas decoratives : elles
    rendent l'artefact auto-suffisant pour un lecteur qui n'a pas le depot sous les
    yeux (regime de troncature et producteur).
    """
    return {
        "script": SCRIPT_ID,
        "model": model,
        "max_steps": max_steps,
        "lr": lr,
        "num_generations": num_gen,
        "max_completion_length": max_completion_length,
        "seeds": list(seeds),
        "results": results,
        "summary": summary,
    }


def seed_metrics(*, arm: str, seed: int, train_s: float, max_completion_length: int,
                  hack: Sequence[float], mc: Sequence[float], reward: Sequence[float],
                  steps: Sequence[int], max_steps: int) -> dict[str, Any]:
    """Assemble le resultat d'une graine — fonction pure, sans dependance lourde.

    Symmetrique exact de :func:`artifact_payload` : l'artefact dit sous quel
    regime de troncature il a ete produit, et chaque resultat de graine le
    repete. Le budget y est ecrit **tel quel** (la valeur effective du run,
    pas le defaut), parce que c'est ce champ qui survit a une comparaison
    graine a graine.

    Le calcul est celui du runner, a l'identique : memes moyennes (numpy),
    meme partage en deux moities (la premiere moitie contre la seconde), meme
    serie par etape. Extraire la fonction rend la promesse « et dans chaque
    resultat de graine » testable sans le stack d'entrainement — c'est
    exactement ce qui manquait.
    """
    hk = np.array(hack, float)
    mc_a = np.array(mc, float)
    rw = np.array(reward, float)
    step_idx = np.array(steps)
    h = len(hk) // 2 or 1
    per_step = [float(np.mean(hk[step_idx == s])) for s in range(max_steps)]
    return {
        "arm": arm, "seed": seed, "train_s": train_s,
        "max_completion_length": max_completion_length,
        "hack_early": float(np.mean(hk[:h])), "hack_late": float(np.mean(hk[h:])),
        "mc_early": float(np.mean(mc_a[:h])), "mc_late": float(np.mean(mc_a[h:])),
        "reward_early": float(np.mean(rw[:h])), "reward_late": float(np.mean(rw[h:])),
        "per_step": per_step,
    }
