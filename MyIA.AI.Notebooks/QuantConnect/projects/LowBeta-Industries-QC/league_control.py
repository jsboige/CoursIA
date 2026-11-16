"""Le critere de comparaison du controle d'innocuite de la ligue (#25492).

Ce module ne contient que le **critere** : deux fonctions pures, sans acces
QC, sans dependance lourde, testables hors ligne.

La lecture des donnees (graphiques QC, trace journaliere) reste dans
`league_protocol.py` : elle depend de la plateforme. Ici, on ne compare que
des donnees deja normalisees.

**Ce que le critere distingue.** Une divergence de **mesure** et une
difference d'**exposition** ne se ressemblent pas :

  - divergence de mesure : les deux cotes exposent la serie et ses valeurs ne
    sont pas les memes -- c'est ce qui doit faire rouge ;
  - difference d'exposition : un des deux cotes n'expose pas la serie -- c'est
    **rapporte**, pas reproche.

Mesure du 2026-11-09 : le controle comparait la concatenation des series `ret`
et `spy` du graphique `Monthly`. La porte portait alors sur la **longueur** des
deux graphiques, pas sur leurs valeurs : deux executions identiques, dont
l'une exposait `spy` et pas l'autre, rendaient rouge. La correction compare
serie par serie, et la divergence de valeurs reste detectee.

Usage :

    from league_control import compare_series, compare_rows
"""
from __future__ import annotations


def compare_series(series_ref: dict[str, list[tuple[int, float]]],
                   series_ctl: dict[str, list[tuple[int, float]]]) -> dict:
    """Compare deux jeux de series, serie par serie.

    `series_ref` et `series_ctl` associent un nom de serie a ses points
    ranges par horodatage.

    La porte porte sur la divergence de **valeurs** des series presentes des
    deux cotes ; une serie exposee d'un seul cote est **rapportee**
    (`series_seulement_ref`, `series_seulement_ctl`), pas comptee comme
    divergence.
    """
    communes = sorted(set(series_ref) & set(series_ctl))
    return {
        "series_ref": sorted(series_ref),
        "series_ctl": sorted(series_ctl),
        "series_communes": communes,
        "series_seulement_ref": sorted(set(series_ref) - set(series_ctl)),
        "series_seulement_ctl": sorted(set(series_ctl) - set(series_ref)),
        "points_par_serie": {name: len(series_ref[name]) for name in communes},
        "divergence": [name for name in communes if series_ref[name] != series_ctl[name]],
    }


def compare_rows(rows_ref: list[tuple[str, float]],
                 rows_ctl: list[tuple[str, float]]) -> dict:
    """Compare deux traces journalieres : seances et valeurs, point par point.

    C'est la comparaison que le protocole consomme : la trace journaliere, pas
    la serie mensuelle. Une trace qui porte les memes seances avec des
    valeurs differentes diverge ; une trace qui porte d'autres seances
    diverge aussi -- le calendrier fait partie de la mesure.
    """
    dates_ref = [d for d, _ in rows_ref]
    dates_ctl = [d for d, _ in rows_ctl]
    values_ref = [v for _, v in rows_ref]
    values_ctl = [v for _, v in rows_ctl]
    max_diff = max((abs(a - b) for a, b in zip(values_ref, values_ctl)), default=0.0)
    same = dates_ref == dates_ctl and values_ref == values_ctl
    return {
        "points": len(rows_ref),
        "calendrier_identique": dates_ref == dates_ctl,
        "valeurs_identiques": values_ref == values_ctl,
        "ecart_max": max_diff,
        "divergence": [] if same else ["trace journaliere"],
    }
