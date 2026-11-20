# -*- coding: utf-8 -*-
"""Courbe de puissance du seuil ``|z| > 3`` de l'instrument humour (ICT-35).

Ce module complete la lecture « null global sur le maximum » (PR #27208) :
celle-ci dit *si* le seuil ``|z| > 3`` est une borne que l'instrument peut
atteindre sous le null ; celle-ci dit *quelle taille d'effet* il faudrait
pour que la regle de detection (``>= 3 features |z| > 3 du meme cote``)
s'ecole. Les deux lectures se lisent ensemble : sans la seconde, « zero
feature au-dela du seuil » se lit comme une absence de signal, alors que la
courbe dit quel seuil serait meme detectable.

La troisieme lecture (``power_vs_pairs``) responde a la question que les
deux premieres laissent ouverte : **combien de paires faut-il** ? L'effet de
``power_curve`` est exprime en unites de dispersion nulle de la
*statistique* -- une unite qui depend du nombre de paires, donc qui ne
permet pas de comparer deux ``n``. ``power_vs_pairs`` exprime l'effet en
**unites de bruit par paire** (independantes de ``n``) et fait varier ``n``
par reechantillonnage : le gain d'une paire y vaut ``sqrt(n)``, pas ``n``.

La quatrieme lecture (``power_by_trace``) etend la troisieme a **l'echelle
du protocole** : la puissance est-elle la meme sur toutes les jambes
(couches, bras) disponibles ? L'echelle par paire est une echelle
**relative a la jambe** (chaque feature est normalisee par son propre
bruit) : deux jambes dont les bruits different d'un facteur cinq sont
directement comparables dans l'unite ``d``, ce qui n'etait pas vrai dans
l'unite de la premiere lecture.

La cinquieme lecture (``power_vs_threshold``) mesure ce que la **convention
pre-enregistree** ``|z| > 3`` coute : le seuil est-il un detail de forme, ou
est-ce lui qui tient la specificite de l'instrument ? La reponse est la
seconde : sous null, la regle s'ecole dans 99,9 % des cas a un seuil de 2, et
dans 0,01 % des cas a un seuil de 3.

La sixieme lecture (``exact_null_rates``) est la **reference qui ne degrade
pas** : les lectures par `n` extrapolent en reechantillonnant les 30 paires
reelles, et ce substitut n'est valide qu'a ``n = 30`` -- au-dela, les
"paires ajoutees" sont des repetitions, et la queue nulle du substitut se
degrade (la regle s'ecole sous null dans 0,125 % des cas a 30 paires, contre
24,6 % a 240). `exact_null_rates` applique le null **exact** de
l'instrument (retournement de signe intra-paire, aucun re-tirage), qui est la
seule procedure dont la validite ne depend pas du nombre de paires.

**Les cinq questions de l'organ-first** (regle ``organ-first-implementation``) :

1. *Quelle serie possede la semantique ?* La serie ICT (carnets ICT-35b/35c/35d)
   via ``ict/humor_pairs.py`` : l'instrument (delta_pair, delta_ctrl, z par
   flip de signe intra-paire) et son seuil pre-enregistre ``|z| > 3``.
2. *Peut-on invoquer son module reel ?* Oui : ce module **reutilise** les
   primitives de zone de ``ict.humor_pairs`` (``_common_prefix_len``,
   ``_zone_vec``) et le chargeur ``ict.sae_traces.load_traces``. Aucune
   reimplementation de la construction de zone, aucune reimplementation du
   null : la seule quantite nouvelle est la **dispersion nulle exacte**,
   qui est une consequence algebrique du null de l'instrument (voir
   ``null_norms``).
3. *Que faut-il exporter dans la serie source ?* Rien pour l'instant : les
   deux primitives importees sont deja dans le module source. Si elles
   devenaient privees de fait, l'export a demander serait
   ``zone_diffs`` (les differences humour-unfun par paire) -- c'est la seule
   surface dont ce module a besoin.
4. *Quel temoin negatif l'organe natif fournit-il ?* Le null lui-meme :
   sous ``delta = 0``, la simulation doit reproduire la queue mesuree par
   l'organe natif (probabilite qu'une feature depasse le seuil sous null),
   et la regle de detection ne doit **pas** s'ecoler. C'est le test
   d'integrite de ``ict/tests/test_humor_power.py``.
5. *Quelle autre serie verifie independamment ?* ICT-35b (agregat),
   ICT-35c (profondeur) et ICT-35d (forme) rejouent le meme instrument sur
   les memes traces : une re-execution de 35d avec ce module doit retrouver
   la meme queue nulle que la « Lecture 5 bis ».

**Modele declare.** Sous H1, la statistique observee d'une feature est
``z = z_nul + delta`, ou ``z_nul`` est un tirage du null de l'instrument
(flip de signe intra-paire) et ``delta`` est le deplacement de la moyenne
par paire, exprime **en unites de dispersion nulle** (la meme unite que le
z). Le deplacement est suppose additif sur la moyenne par paire, donc
dispersion de la statistique inchangee : c'est ce qui rend le modele exact
plutot qu'approximatif.

Deux bornes structurent la lecture :

* ``|z| <= sqrt(n)`` -- le z d'une feature est un produit scalaire
  normalise, borne par Cauchy-Schwarz : avec 30 paires, aucune feature ne
  peut depasser ``sqrt(30) = 5.477``. Une courbe de puissance qui
  depasse cette borne decrit un effet inaccessible, pas un instrument
  faible.
* le seuil lui-meme est une **convention** de l'instrument, pas une
  propriete de la loi : la courbe se lit « si le seuil etait ``t``, quel
  effet faudrait-il ? », pas « quel est l'effet reel ? ».
"""
from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path
from typing import Any

import numpy as np

from .humor_pairs import _common_prefix_len, _zone_vec

__all__ = [
    "exact_null_rates",
    "n_for_power",
    "null_norms",
    "observed_z",
    "per_pair_rms",
    "power_by_trace",
    "power_curve",
    "power_vs_pairs",
    "power_vs_threshold",
    "z_ceiling",
    "zone_diffs",
]

# Seuil pre-enregistre de l'instrument (ICT-35b/35c/35d) : le module ne le
# change pas, il mesure la puissance qu'il porte.
DEFAULT_THRESHOLD = 3.0
# Regle de detection de l'instrument : au moins 3 features au-dela du seuil,
# du meme cote.
DEFAULT_MIN_SAME_SIDE = 3


def zone_diffs(
    traces_path: str | Path,
    pairs: list[dict[str, str]],
) -> np.ndarray:
    """Matrice des differences ``humour - unfun`` par paire, ``(n, d_sae)``.

    Meme construction de zone que ``ict.humor_pairs.measure_humor_differential``
    (prefixe commun token par token, moyenne dense des activations SAE
    top-50 de la zone d'edition) : les primitives sont **importees**, pas
    reecrites.
    """
    from .sae_traces import load_traces

    tr = load_traces(traces_path)
    d_sae = int(tr["meta"]["d_sae"])
    n = len(pairs)
    humour = []
    unfun = []
    for i in range(n):
        eh = tr["prompts"][("humour", i)]
        eu = tr["prompts"][("unfun", i)]
        k = _common_prefix_len(eh["tokens"], eu["tokens"])
        humour.append(_zone_vec(eh, k, d_sae))
        unfun.append(_zone_vec(eu, k, d_sae))
    return np.stack(humour) - np.stack(unfun)


def null_norms(diffs: np.ndarray) -> np.ndarray:
    """Dispersion nulle exacte par feature : ``||diffs_f||_2``.

    Le null de l'instrument est le **flip de signe intra-paire** : la
    moyenne d'une feature sous null vaut ``(1/n) * sum_i s_i diffs_if`` avec
    ``s_i`` independants a moyenne nulle et variance 1. Sa variance est donc
    ``(1/n^2) * sum_i diffs_if^2`` et son ecart-type vaut
    ``||diffs_f||_2 / n`` : c'est la formule **exacte** du null, sans aucun
    tirage. (L'instrument estimait cet ecart-type par ecart-type empirique
    sur 2048 tirages ; la formule exacte en est la limite, a moins de 2 %
    pres sur la dispersion.)
    """
    return np.linalg.norm(np.asarray(diffs, dtype=np.float64), axis=0)


def z_ceiling(n_pairs: int) -> float:
    """Borne superieure du |z| d'une feature : ``sqrt(n)``.

    Le z d'une feature vaut ``<a_f, 1> / ||a_f||`` : Cauchy-Schwarz donne
    ``|z| <= sqrt(n)``. Avec 30 paires, ``5.477`` -- un seuil a 3 n'est donc
    pas hors d'atteinte, mais il ne peut pas l'etre que de justesse.
    """
    return float(np.sqrt(float(n_pairs)))


def observed_z(diffs: np.ndarray) -> np.ndarray:
    """z observe par feature (moyenne par paire / dispersion nulle exacte).

    Les features sans variation (``||diffs_f|| = 0``) n'ont pas de z
    definie : elles sont rendues a 0 et exclues du choix des features
    plantees (elles ne peuvent pas porter un effet).
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    norms = null_norms(diffs)
    safe = np.where(norms > 0, norms, np.inf)
    return diffs.sum(axis=0) / safe


def power_curve(
    diffs: np.ndarray,
    deltas: Sequence[float],
    *,
    n_planted: int = DEFAULT_MIN_SAME_SIDE,
    n_replicates: int = 200,
    seed: int = 42,
    threshold: float = DEFAULT_THRESHOLD,
    min_same_side: int = DEFAULT_MIN_SAME_SIDE,
) -> dict[str, Any]:
    """Puissance de la regle de detection en fonction de l'effet plante.

    Sous H1, ``n_planted`` features sont affectees d'un deplacement
    ``delta`` (en unites de dispersion nulle) ; les autres restent a leur
    tirage nul. La regle de detection est celle de l'instrument : au moins
    ``min_same_side`` features au-dela de ``threshold`` **du meme cote**.

    Chaque replicat est une experience independante : un tirage de signes
    intra-paire (le null de l'instrument), puis l'effet plante. La
    realisation de l'effet est elle aussi aleatoire -- les features
    affectees sont tirees uniformement parmi les features actives -- parce
    que l'on ne sait pas *quelles* features porteraient un effet reel.

    Retourne, pour chaque ``delta`` : la probabilite que la regle
    s'ecole (``p_rule``), la probabilite qu'**au moins une** feature
    depasse le seuil (``p_any``) et le nombre moyen de features au-dela
    (``n_over_mean``). ``delta = 0`` est l'ancre nulle : c'est la queue que
    l'organe natif mesure deja.
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    n_pairs, n_features = diffs.shape
    norms = null_norms(diffs)
    eligible = np.flatnonzero(norms > 0)
    if eligible.size == 0:
        raise ValueError("aucune feature active : le null ne peut pas etre mesure")
    if n_planted > eligible.size:
        raise ValueError(
            f"n_planted={n_planted} > {eligible.size} features actives"
        )
    safe = np.where(norms > 0, norms, np.inf)

    rng = np.random.default_rng(seed)
    counters = {
        float(d): {"rule": 0, "any": 0, "n_over": 0, "max_absz": []}
        for d in deltas
    }
    for _ in range(n_replicates):
        signs = rng.choice(np.array([-1.0, 1.0]), size=n_pairs)
        z_null = (signs[:, None] * diffs).sum(axis=0) / safe
        planted = rng.choice(eligible, size=n_planted, replace=False)
        for delta in deltas:
            z = z_null.copy()
            z[planted] += float(delta)
            over = np.abs(z) > threshold
            n_over = int(over.sum())
            pos = int((z[over] > 0).sum())
            neg = n_over - pos
            counters[float(delta)]["rule"] += int(max(pos, neg) >= min_same_side)
            counters[float(delta)]["any"] += int(n_over >= 1)
            counters[float(delta)]["n_over"] += n_over
            counters[float(delta)]["max_absz"].append(float(np.abs(z).max()))

    rows = []
    for delta in deltas:
        c = counters[float(delta)]
        rows.append(
            {
                "delta": float(delta),
                "p_rule": c["rule"] / n_replicates,
                "p_any": c["any"] / n_replicates,
                "n_over_mean": c["n_over"] / n_replicates,
                "max_absz_median": float(np.median(c["max_absz"])),
            }
        )
    return {
        "rows": rows,
        "n_replicates": int(n_replicates),
        "n_pairs": int(n_pairs),
        "n_features": int(n_features),
        "n_eligible": int(eligible.size),
        "threshold": float(threshold),
        "min_same_side": int(min_same_side),
        "n_planted": int(n_planted),
        "seed": int(seed),
        "z_ceiling": z_ceiling(n_pairs),
    }


def per_pair_rms(diffs: np.ndarray) -> np.ndarray:
    """Ecart-type par paire estime par feature : ``||diffs_f||_2 / sqrt(n)``.

    C'est l'echelle de bruit **par paire** (RMS sur les paires) d'une feature.
    Elle sert a exprimer un effet dans une unite **independante du nombre de
    paires** : un effet de taille ``d`` signifie « chaque paire decale la
    feature de ``d`` fois son bruit par paire ».
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    n_pairs = diffs.shape[0]
    return null_norms(diffs) / np.sqrt(float(n_pairs))


def power_vs_pairs(
    diffs: np.ndarray,
    n_values: Sequence[int],
    effect_sizes: Sequence[float],
    *,
    n_planted: int = DEFAULT_MIN_SAME_SIDE,
    n_bootstraps: int = 20,
    n_replicates: int = 100,
    seed: int = 42,
    threshold: float = DEFAULT_THRESHOLD,
    min_same_side: int = DEFAULT_MIN_SAME_SIDE,
) -> dict[str, Any]:
    """Puissance de la regle en fonction du **nombre de paires**.

    Question posee par ``power_curve`` : l'effet etait exprime en unites de
    dispersion nulle de la *statistique*. Cette unite **depend du nombre de
    paires** (elle vaut ``||diffs_f||_2 / n``) : a effet identique, la
    puissance ne change donc pas quand on change ``n`` -- ce qui rend la
    question « combien de paires faut-il ? » sans reponse. Il faut une unite
    **independante de ``n``**.

    C'est la **taille d'effet par paire** ``d`` : chaque paire decale la
    feature de ``d`` fois son bruit par paire (``per_pair_rms``). Le z
    observe se deplace alors de ``d * sqrt(n)`` -- la loi classique de la
    puissance : le gain d'une paire vaut ``sqrt(n)``, pas ``n``.

    Les paires sont **tirees avec remise** (bootstrap) pour atteindre ``n`` :
    la zone d'edition d'une paire est calculee independamment des autres,
    donc reechantillonner les paires est legitime ; l'hypothese implicite
    est que les paires minimales sont des tirages approximativement
    exchangeables de la population des paires.

    Les tirages nuls sont calcules par produit matriciel (signes x diffs) :
    un replicat coute ``O(n * d_sae)`` mais le BLAS fait le travail, ce qui
    rend le balayage ``n x d`` praticable sans GPU.

    Retourne une ligne par couple ``(n, d)`` : ``p_rule`` (la regle
    s'ecole), ``p_any`` (au moins une feature au-dela du seuil) et
    ``n_over_mean``.
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    n_pairs = diffs.shape[0]
    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []

    for n in n_values:
        n = int(n)
        if n < 2:
            raise ValueError(f"n={n} : il faut au moins deux paires")
        counts: dict[float, dict[str, float]] = {
            float(d): {"rule": 0, "any": 0, "n_over": 0} for d in effect_sizes
        }
        n_draws = 0
        for _ in range(n_bootstraps):
            idx = rng.integers(0, n_pairs, size=n)
            sample = diffs[idx]
            norms = null_norms(sample)
            eligible = np.flatnonzero(norms > 0)
            if eligible.size < n_planted:
                continue
            safe = np.where(norms > 0, norms, np.inf)
            signs = rng.choice(
                np.array([-1.0, 1.0]), size=(n_replicates, n)
            )
            z_null = (signs @ sample) / safe          # (n_replicates, d_sae)
            for r in range(n_replicates):
                planted = rng.choice(eligible, size=n_planted, replace=False)
                for d in effect_sizes:
                    z = z_null[r].copy()
                    z[planted] += float(d) * np.sqrt(float(n))
                    over = np.abs(z) > threshold
                    n_over = int(over.sum())
                    pos = int((z[over] > 0).sum())
                    c = counts[float(d)]
                    c["rule"] += int(max(pos, n_over - pos) >= min_same_side)
                    c["any"] += int(n_over >= 1)
                    c["n_over"] += n_over
            n_draws += n_replicates
        for d in effect_sizes:
            c = counts[float(d)]
            denom = max(n_draws, 1)
            rows.append(
                {
                    "n_pairs": n,
                    "effect_size": float(d),
                    "p_rule": c["rule"] / denom,
                    "p_any": c["any"] / denom,
                    "n_over_mean": c["n_over"] / denom,
                    "z_shift": float(d) * np.sqrt(float(n)),
                }
            )
    return {
        "rows": rows,
        "n_bootstraps": int(n_bootstraps),
        "n_replicates": int(n_replicates),
        "n_planted": int(n_planted),
        "threshold": float(threshold),
        "min_same_side": int(min_same_side),
        "seed": int(seed),
        "source_pairs": int(n_pairs),
    }


def power_vs_threshold(
    diffs: np.ndarray,
    thresholds: Sequence[float],
    effect_sizes: Sequence[float],
    *,
    n_values: Sequence[int] = (30,),
    n_planted: int = DEFAULT_MIN_SAME_SIDE,
    n_bootstraps: int = 4,
    n_replicates: int = 100,
    seed: int = 42,
    min_same_side: int = DEFAULT_MIN_SAME_SIDE,
) -> dict[str, Any]:
    """Puissance et faux positifs **en fonction du seuil** de la regle.

    Le seuil ``|z| > 3`` est une **convention pre-enregistree** de
    l'instrument, pas une propriete de la loi. Les lectures precedentes
    mesurent la puissance a ce seuil-la ; celle-ci mesure ce que le
    seuil **coute**, et ce qu'un seuil different pourrait rapporter.

    Deux colonnes se lisent ensemble, pour chaque couple
    ``(seuil, taille d'effet)`` :

    * ``p_rule`` a ``effect_size = 0`` est le **taux de faux positifs**
      (la regle s'ecole sous null) ;
    * ``p_rule`` a ``effect_size > 0`` est la **puissance** (la regle
      s'ecole quand l'effet est present).

    Baisser le seuil augmente les deux : la question n'est donc pas « quel
    seuil est le mieux », mais « quel seuil achete combien de puissance
    pour combien de faux positifs ». Les deux quantites sont mesurees sur
    les **memes tirages nuls** (paired design) : la comparaison entre
    seuils ne repose pas sur deux lots de hasard independants.

    L'effet est exprime dans la meme unite que les lectures precedentes
    (bruit par paire), le deplacement du z valant ``d * sqrt(n)``.

    Retourne une ligne par triplet ``(n, seuil, taille d'effet)``.
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    n_source = diffs.shape[0]
    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []

    for n in n_values:
        n = int(n)
        if n < 2:
            raise ValueError(f"n={n} : il faut au moins deux paires")
        counts: dict[tuple[float, float], dict[str, float]] = {
            (float(t), float(d)): {"rule": 0, "any": 0, "n_over": 0}
            for t in thresholds
            for d in effect_sizes
        }
        n_draws = 0
        for _ in range(n_bootstraps):
            idx = rng.integers(0, n_source, size=n)
            sample = diffs[idx]
            norms = null_norms(sample)
            eligible = np.flatnonzero(norms > 0)
            if eligible.size < n_planted:
                continue
            safe = np.where(norms > 0, norms, np.inf)
            signs = rng.choice(np.array([-1.0, 1.0]), size=(n_replicates, n))
            z_null = (signs @ sample) / safe          # (n_replicates, d_sae)
            for r in range(n_replicates):
                planted = rng.choice(eligible, size=n_planted, replace=False)
                for d in effect_sizes:
                    z = z_null[r].copy()
                    if float(d) != 0.0:
                        z[planted] += float(d) * np.sqrt(float(n))
                    absz = np.abs(z)
                    for t in thresholds:
                        over = absz > float(t)
                        n_over = int(over.sum())
                        pos = int((z[over] > 0).sum())
                        c = counts[(float(t), float(d))]
                        c["rule"] += int(max(pos, n_over - pos) >= min_same_side)
                        c["any"] += int(n_over >= 1)
                        c["n_over"] += n_over
            n_draws += n_replicates
        denom = max(n_draws, 1)
        for t in thresholds:
            for d in effect_sizes:
                c = counts[(float(t), float(d))]
                rows.append(
                    {
                        "n_pairs": n,
                        "threshold": float(t),
                        "effect_size": float(d),
                        "p_rule": c["rule"] / denom,
                        "p_any": c["any"] / denom,
                        "n_over_mean": c["n_over"] / denom,
                        "z_shift": float(d) * np.sqrt(float(n)),
                    }
                )
    return {
        "rows": rows,
        "n_bootstraps": int(n_bootstraps),
        "n_replicates": int(n_replicates),
        "n_planted": int(n_planted),
        "min_same_side": int(min_same_side),
        "seed": int(seed),
        "source_pairs": int(n_source),
    }


def n_for_power(
    rows: Sequence[dict[str, Any]],
    effect_size: float,
    target: float = 0.8,
    threshold: float | None = None,
) -> int | None:
    """Plus petit nombre de paires pour lequel ``P(regle) >= target``.

    ``rows`` est la liste produite par :func:`power_vs_pairs`,
    :func:`power_by_trace` ou :func:`power_vs_threshold` (meme format). La
    reponse est ``None`` quand meme la plus grande valeur de ``n`` balayee
    n'atteint pas la cible : c'est une reponse, pas une absence de
    reponse -- elle dit que le budget de paires mesure ne suffit pas.

    ``threshold`` selectionne un seuil quand les lignes en portent
    plusieurs (cas de :func:`power_vs_threshold`) : sans lui, un lot
    melangeant plusieurs seuils serait ambigu et l'appel **echoue** plutot
    que de melanger silencieusement des seuils.
    """
    if threshold is None and any("threshold" in row for row in rows):
        thresholds = {float(row["threshold"]) for row in rows if "threshold" in row}
        if len(thresholds) > 1:
            raise ValueError(
                "les lignes portent plusieurs seuils : "
                f"precisez threshold= (seuils presents : {sorted(thresholds)})"
            )
    candidates = [
        int(row["n_pairs"])
        for row in rows
        if abs(float(row["effect_size"]) - float(effect_size)) <= 1e-12
        and (threshold is None or abs(float(row["threshold"]) - float(threshold)) <= 1e-12)
        and float(row["p_rule"]) >= float(target)
    ]
    return min(candidates) if candidates else None


def power_by_trace(
    trace_paths: Sequence[str | Path],
    pairs: list[dict[str, str]],
    n_values: Sequence[int],
    effect_sizes: Sequence[float],
    *,
    n_planted: int = DEFAULT_MIN_SAME_SIDE,
    n_bootstraps: int = 8,
    n_replicates: int = 100,
    seed: int = 42,
    threshold: float = DEFAULT_THRESHOLD,
    min_same_side: int = DEFAULT_MIN_SAME_SIDE,
) -> dict[str, Any]:
    """Puissance de la regle **jambe par jambe** (une trace = une jambe).

    La question que la troisieme lecture laisse ouverte : la puissance
    mesuree est-elle la meme sur toutes les jambes du protocole ? En
    effet, l'echelle par paire est une echelle **relative a la jambe**
    (chaque feature est normalisee par son propre bruit) : deux jambes
    dont les bruits different d'un facteur cinq sont directement
    comparables dans l'unite ``d``, ce qui n'etait pas vrai dans l'unite
    de la premiere lecture.

    Chaque jambe est decrite par :
    * le nombre de **features actives** (norme non nulle) ;
    * son **bruit par paire** median (l'echelle dans laquelle ``d`` est
      exprime) ;
    * le **plafond** ``sqrt(n)`` du z ;
    * les lignes de puissance (``n``, ``d``) produites par
      :func:`power_vs_pairs`.

    Le parametre ``d`` est le meme pour toutes les jambes : une jambe
    bruyante n'est donc pas handicapee, c'est la **regle de detection**
    qui est sous-equipee partout ou elle l'est sur une jambe.
    """
    legs: list[dict[str, Any]] = []
    for path in trace_paths:
        trace_path = Path(path)
        diffs = zone_diffs(trace_path, pairs)
        rms = per_pair_rms(diffs)
        active = rms[rms > 0]
        res = power_vs_pairs(
            diffs,
            n_values,
            effect_sizes,
            n_planted=n_planted,
            n_bootstraps=n_bootstraps,
            n_replicates=n_replicates,
            seed=seed,
            threshold=threshold,
            min_same_side=min_same_side,
        )
        legs.append(
            {
                "trace": trace_path.name,
                "n_source_pairs": int(diffs.shape[0]),
                "n_active_features": int(active.size),
                "per_pair_rms_median": float(np.median(active)) if active.size else 0.0,
                "per_pair_rms_p25": (
                    float(np.percentile(active, 25)) if active.size else 0.0
                ),
                "per_pair_rms_p75": (
                    float(np.percentile(active, 75)) if active.size else 0.0
                ),
                "per_pair_rms_max": float(active.max()) if active.size else 0.0,
                "z_ceiling": z_ceiling(int(diffs.shape[0])),
                "rows": res["rows"],
            }
        )
    return {
        "legs": legs,
        "n_bootstraps": int(n_bootstraps),
        "n_replicates": int(n_replicates),
        "n_planted": int(n_planted),
        "threshold": float(threshold),
        "min_same_side": int(min_same_side),
        "seed": int(seed),
        "source_pairs": len(pairs),
    }


def exact_null_rates(
    diffs: np.ndarray,
    thresholds: list[float],
    *,
    n_flips: int = 20000,
    seed: int = 42,
    min_same_side: int = DEFAULT_MIN_SAME_SIDE,
    chunk: int = 256,
) -> dict[str, Any]:
    """Queue nulle **exacte** du seuil, sans reechantillonnage des paires.

    Les lectures par ``power_vs_pairs`` / ``power_vs_threshold`` extrapollent
    a plus de 30 paires en **reechantillonnant les 30 paires reelles avec
    remise** (bootstrap). Ce substitut n'est valide qu'a ``n = 30`` : au-dela,
    les lignes ajoutees sont des **repetitions** du meme couple (paire,
    signe), et sa queue nulle se degrade (section 11 du ledger
    ``docs/ledgers/11690-ict-puissance-seuil-z.md``).

    Cette fonction donne la reference qui ne degrade pas : le null
    **exact** de l'instrument, obtenu en retournant le signe de chaque
    paire independamment (le flip intra-paire de ``ict/humor_pairs.py``),
    sans jamais remplacer une paire. Elle n'est definie que pour le
    ``n`` observe.

    Pour chaque seuil, elle rend :

    * ``p_any`` -- probabilite qu'**au moins une** feature depasse le seuil
      sous null (le « null global sur le maximum ») ;
    * ``p_rule`` -- probabilite que la **regle** de l'instrument
      (``>= min_same_side features du meme cote``) s'ecole sous null ;
    * ``n_over_mean`` -- nombre moyen de features au-dela du seuil par
      tirage.

    Les retournements sont traites par blocs (``chunk``) pour que la
    memoire reste bornee : une matrice de 20 000 x 32 768 tiendrait 5 Go.
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    if diffs.ndim != 2:
        raise ValueError("diffs doit etre une matrice (n_paires, n_features)")
    n_pairs = diffs.shape[0]
    if n_flips < 1:
        raise ValueError(f"n_flips={n_flips} : il faut au moins un retournement")
    norms = null_norms(diffs)
    safe = np.where(norms > 0, norms, np.inf)
    rng = np.random.default_rng(seed)
    thresholds = [float(t) for t in thresholds]
    counts: dict[float, dict[str, int]] = {
        t: {"any": 0, "rule": 0, "n_over": 0} for t in thresholds
    }
    done = 0
    while done < n_flips:
        m = min(int(chunk), n_flips - done)
        signs = rng.choice(np.array([-1.0, 1.0]), size=(m, n_pairs))
        z = (signs @ diffs) / safe
        absz = np.abs(z)
        for t in thresholds:
            over = absz > t
            n_over = over.sum(axis=1)
            pos = ((z > 0) & over).sum(axis=1)
            neg = ((z < 0) & over).sum(axis=1)
            c = counts[t]
            c["any"] += int((n_over >= 1).sum())
            c["rule"] += int((np.maximum(pos, neg) >= min_same_side).sum())
            c["n_over"] += int(n_over.sum())
        done += m
        del z, absz, over
    denom = max(done, 1)
    rows = [
        {
            "threshold": t,
            "p_any": counts[t]["any"] / denom,
            "p_rule": counts[t]["rule"] / denom,
            "n_over_mean": counts[t]["n_over"] / denom,
        }
        for t in thresholds
    ]
    return {
        "rows": rows,
        "n_flips": done,
        "n_pairs": int(n_pairs),
        "min_same_side": int(min_same_side),
        "seed": int(seed),
    }
