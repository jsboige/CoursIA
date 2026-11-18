"""Mesures S-Lens sur capture dense des residus du banc 20 prompts (#17740).

Le pilote S-Lens (ICT, #15475/#15481) mesure la **self-location** sur des
bancs synthetiques munis d'oracles (copy_offset, variable_binding). Un banc
de textes naturels n'a pas d'oracle : ce module transpose la **methodologie
de mesure** — probe lineaire ridge en forme fermee, lecture held-out, controle
shuffle des etiquettes — sur la question decidable sur ce substrat : *la
position absolue du token dans son prompt est-elle lineairement decodable
du residu layer-16 ?* La reponse mesure la composante positionnelle de la
self-location sur le LLM reel ; elle ne pretend pas mesurer le suivi de
reference variable->valeur, qui exige un oracle.

Organe reutilise tel quel : :func:`ict.slens.ridge_probe` et
:func:`ict.slens.probe_metrics` (numpy-only) — pas de reimplementation
locale. Numpy-only, torch confine dans ``scripts/``.
"""

from __future__ import annotations

import numpy as np

from .slens import probe_metrics, ridge_probe

__all__ = ["measure_slens"]


def _position_metrics(resid: np.ndarray, positions: np.ndarray,
                      idx_train: np.ndarray, idx_test: np.ndarray,
                      alpha: float) -> dict:
    """Ridge -> lecture continue de la position, metriques held-out."""
    weights = ridge_probe(resid[idx_train], positions[idx_train], alpha=alpha)
    return probe_metrics(resid[idx_test], positions[idx_test], weights)


def measure_slens(dense: dict, *, alpha: float = 1e-2,
                  train_frac: float = 0.7, seed: int = 0) -> dict:
    """Probe de self-location positionnelle sur une capture dense alignee.

    Deux echelles rapportees separement :

    - **pooled** : tous les tokens du banc, cible = position absolue dans le
      prompt ; split aleatoire seede 70/30. Les positions se repetent a
      travers les prompts — la lecture y est evaluee sur des positions vues
      dans d'autres contextes.
    - **par prompt** : split contiguous 70/30 (convention slens), cible =
      position ; les positions held-out y sont NON vues a l'entrainement —
      lecture extrapolante, plus dure par construction.

    Le **controle shuffle** permute les etiquettes du train uniquement
    (appariement cible/representation detruit, held-out intact) : il fixe le
    plancher empirique du probe sur ce meme substrat. Un R2 pooled eleve avec
    un R2 par prompt plat est une reponse, pas un artefact : la position est
    decodable en interpolation cross-contexte mais pas extrapolable — les deux
    nombres sont rapportes, jamais fusionnes.
    """
    prompts = dense["prompts"]
    rng = np.random.default_rng(seed)

    acts, pos, prompt_of = [], [], []
    for rank, key in enumerate(sorted(prompts)):
        resid = prompts[key]["resid"]
        acts.append(resid)
        pos.append(np.arange(resid.shape[0], dtype=np.int64))
        prompt_of.append(np.full(resid.shape[0], rank, dtype=np.int64))
    x = np.concatenate(acts)
    y = np.concatenate(pos)
    n = y.shape[0]
    perm = rng.permutation(n)
    n_train = int(round(n * train_frac))
    tr, te = np.sort(perm[:n_train]), np.sort(perm[n_train:])
    pooled = _position_metrics(x, y, tr, te, alpha)
    shuffled_y = y[tr][rng.permutation(n_train)]
    w_shuf = ridge_probe(x[tr], shuffled_y, alpha=alpha)
    shuffle = probe_metrics(x[te], y[te], w_shuf)

    per_prompt = []
    for key in sorted(prompts):
        resid = prompts[key]["resid"]
        t = resid.shape[0]
        cut = int(round(t * train_frac))
        if cut < 2 or t - cut < 2:
            continue  # prompt trop court pour un split tenu
        metrics = _position_metrics(resid, np.arange(t, dtype=np.int64),
                                    np.arange(cut), np.arange(cut, t), alpha)
        per_prompt.append({"prompt": [key[0], key[1]], **metrics})

    return {
        "status": "measured",
        "alpha": float(alpha),
        "train_frac": float(train_frac),
        "pooled": pooled,
        "shuffle_control": shuffle,
        "per_prompt": per_prompt,
        "interpretation": (
            "R2/rmse de la lecture ridge de la position absolue. pooled : "
            "split aleatoire, positions repetees cross-contexte ; par "
            "prompt : split contiguous, positions held-out non vues "
            "(extrapolation). shuffle_control : etiquettes du train "
            "permutees, held-out intact — plancher empirique du probe. La "
            "self-location de reference (variable->valeur) exige l'oracle "
            "des bancs synthetiques : elle n'est pas mesuree ici."
        ),
    }
