"""Fenetres d'echantillon des artefacts ICT-25 (tete + queue).

Pourquoi ce module existe
-------------------------
L'artefact d'entrainement porte un echantillon des records (`records_sample`)
pour que les metriques publiees soient **recalculables** a partir de l'artefact
seul. L'echantillon initial ne portait que la **tete** de la liste
(`records[:64]`) : pour le bras N @120 steps (960 completions) il ne couvrait
que les **steps 0 a 7**, et les agregats de la fin du run n'etaient donc
corroborables par personne (revue du 2026-10-22 sur la PR #21973 ; issue de
suivi #22078).

Ce module expose une fonction pure, sans dependance lourde (ni torch, ni
transformers) : elle est donc testable partout, y compris en CI ou le GPU
n'existe pas. `ict25_arms.py` l'utilise ; `tests/test_ict25_records.py` la
teste.

Contrat
--------
- `records_sample` : la **tete** (les `max_records` premiers records). Le nom
  et le contenu ne changent pas -> les artefacts existants et leurs lecteurs
  restent valides.
- `records_sample_tail` : la **queue** (les `max_records` derniers records).
  Vide quand la tete couvre deja la totalite des records (run plus court que
  la fenetre) : la queue n'apporterait rien que la tete ne couvre pas.
- `records_total` : nombre total de records du seed -- permet de verifier
  d'un coup d'oeil la couverture de l'echantillon (avant : impossible, on ne
  pouvait pas savoir combien de records l'echantillon representait).
- `records_sample_window` : `"head"` pour le champ historique
  `records_sample` ; le champ tail est explicitement la fenetre tardive.

Les deux fenetres sont des **listes de records** (dictionnaires serialisables
en JSON) : un lecteur peut recalculer `mean_reward`, `mean_math_correct` et
`hack_rate` sur chacune d'elles separement, et comparer l'agregat publie a
l'agregat recalcule.
"""

from __future__ import annotations

__all__ = ["record_windows", "window_stats", "protocol_block"]

DEFAULT_MAX_RECORDS = 64
DEFAULT_MAX_COMPLETION_LENGTH = 1024


def record_windows(records, max_records: int = DEFAULT_MAX_RECORDS) -> dict:
    """Fenetres d'echantillon (tete + queue) d'une liste de records.

    Parameters
    ----------
    records : sequence
        Les records du seed, dans l'ordre de production.
    max_records : int
        Taille de chaque fenetre (tete et queue). Un entier positif.

    Returns
    -------
    dict
        Les cles ``records_sample`` (tete), ``records_sample_tail`` (queue),
        ``records_total`` et ``records_sample_window``.
    """
    if not isinstance(max_records, int) or isinstance(max_records, bool):
        raise TypeError(f"max_records doit etre un entier, recu {type(max_records).__name__}")
    if max_records <= 0:
        raise ValueError(f"max_records doit etre positif, recu {max_records}")

    records = list(records)
    total = len(records)
    return {
        "records_sample": records[:max_records],
        "records_sample_tail": records[-max_records:] if total > max_records else [],
        "records_total": total,
        "records_sample_window": "head",
    }


def window_stats(records) -> dict:
    """Agregats d'une fenetre de records (meme formule que l'artefact).

    Permet de recalculer les metriques publiees sur la tete **et** sur la
    queue, et de les comparer : c'est la contre-verification que l'echantillon
    head-only rendait impossible.
    """
    records = list(records)
    if not records:
        return {"n": 0, "mean_reward": None, "mean_math_correct": None, "hack_rate": None}
    return {
        "n": len(records),
        "mean_reward": round(sum(float(r.get("reward", 0.0)) for r in records) / len(records), 4),
        "mean_math_correct": round(sum(float(r.get("mc", 0.0)) for r in records) / len(records), 4),
        "hack_rate": round(sum(float(r.get("hack", 0)) for r in records) / len(records), 4),
    }


def protocol_block(*, max_completion_length: int, seeds, steps: int) -> dict:
    """Protocole d'un run, tel que l'artefact doit le porter (#21998).

    Pourquoi ce bloc existe : deux bras produits sous des budgets de
    completion differents (`cap 80` et `cap 1024`) ne sont pas au meme
    regime, et l'artefact ne permettait pas de les distinguer -- il ne
    portait pas le cap. Une comparaison entre bras de regimes differents se
    lisait donc comme une comparaison a protocole egal.

    Parameters
    ----------
    max_completion_length : int
        Budget de completion effectivement passe a `GRPOConfig`. Entier
        strictement positif.
    seeds : iterable d'entiers
        Les seeds du run, tels que la CLI les a resolus (pas le texte brut).
    steps : int
        Nombre de steps GRPO du run, entier strictement positif.

    Returns
    -------
    dict
        ``max_completion_length``, ``seeds`` et ``steps`` -- les trois
        champs sans lesquels la re-derivation du regime est impossible.
    """
    if not isinstance(max_completion_length, int) or isinstance(max_completion_length, bool):
        raise TypeError(
            "max_completion_length doit etre un entier, "
            f"recu {type(max_completion_length).__name__}"
        )
    if max_completion_length <= 0:
        raise ValueError(f"max_completion_length doit etre positif, recu {max_completion_length}")
    if not isinstance(steps, int) or isinstance(steps, bool):
        raise TypeError(f"steps doit etre un entier, recu {type(steps).__name__}")
    if steps <= 0:
        raise ValueError(f"steps doit etre positif, recu {steps}")

    seeds_list = list(seeds)
    if not seeds_list:
        raise ValueError("seeds ne doit pas etre vide : un run sans seed n'est pas re-derivable")
    for seed in seeds_list:
        if not isinstance(seed, int) or isinstance(seed, bool):
            raise TypeError(f"chaque seed doit etre un entier, recu {type(seed).__name__}")

    return {
        "max_completion_length": max_completion_length,
        "seeds": seeds_list,
        "steps": steps,
    }
