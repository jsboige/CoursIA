#!/usr/bin/env python
"""Mesure la saturation du budget de completion d'un bras DAPO/GRPO.

Un run GRPO/DAPO tronque chaque completion au budget `max_completion_length`.
Quand le modele veut ecrire plus long que ce budget, la completion est
tronquee : le masque `mask_truncated_completions` annule alors la perte de
ces steps. Le run continue, `rc=0`, le log est plein de metriques -- et
l'echantillon utile ne porte plus qu'une fraction des steps.

C'est ce qui a fait retirer le bras 14B de #15293 : sur ses steps,
`clipped_ratio` valait 1 et `mean_length` le plafond, donc `loss=0`,
`grad=0`, `frac_reward_zero_std=1`. Un run « reussi » qui n'a rien appris se
distingue d'un run qui a appris sur la seule fraction de steps vivantes.

Cet organe lit les ARTEFACTS JSON d'un run (donc des donnees commitees, pas
des logs de console) et rend, par graine :

- le budget et le nombre de steps ;
- la fraction de steps **satures** (`mean_length` au plafond, ou
  `clipped_ratio` a 1) ;
- la fraction de steps **sans gradient** (`grad_norm` nul) ;
- la fraction de steps **sans signal d'apprentissage** (`frac_reward_zero_std`
  a 1) ;
- la repartition des recompenses.

Les graines sont ensuite regroupees **par bras** (le champ `model_key` de
l'artefact) : les trois seuils nommes s'appliquent au bras, pas au lot de
fichiers passe en argument. Un fichier sans `log_history` (un `summary.json`,
un baseline) n'est pas une graine : il est signale hors bras et ne peut pas
contaminer le verdict d'un bras.

| verdict | condition | lecture |
|---|---|---|
| `SIGNAL_NUL` | `frac_satures >= 0.95` | le bras n'a produit aucun signal : a retirer |
| `SIGNAL_PARTIEL` | `frac_sans_gradient >= 0.5` | le signal existe, mais porte sur moins de la moitie des steps : toute comparaison se lit sur les steps vivantes |
| `SIGNAL_UTILE` | sinon | le budget n'est pas la contrainte dominante |

Les seuils sont **inclusifs** : une fraction de steps satures exactement egale
a `0.95` est un `SIGNAL_NUL`. Cette frontiere n'est pas un cas theorique --
c'est le cas **mesure** du bras `qwen35`, dont la graine 0 rend `0.95` pile --
et un test la pince des deux cotes.

Le verdict d'un bras suit la graine **mediane**. A effectif **pair**, la
convention est **optimiste** : le moins grave des deux verdicts centraux
(un bras dont une graine sur deux sature porte encore du signal). La
convention est ecrite dans le code et pincee par un test.

Le gain d'evaluation par step vivant (`gain_eval_par_step_avec_gradient`) est
la **mediane des ratios par graine**, chacun divise par le nombre de steps
qui ont porte un gradient **de cette graine**. Il ne se **rederive pas** depuis
`gain_eval_recompense / steps_avec_gradient` : le diviseur du bras est une
*mediane de comptes*, qui peut valoir moins de 1 (mediane de `{0, 1}`) et
amplifierait alors un gain reel d'un facteur 2. Quand le diviseur du bras est
< 1, la metrique vaut `None` et le champ `gain_eval_par_step_comparable` vaut
`false` : le gain par step n'est pas comparable entre bras sur ce bras-la.

Usage :

    python scripts/analyse_dapo_saturation.py scripts/results/m19_minicpm5_grpo/qwen3_8b_seed*.json
    python scripts/analyse_dapo_saturation.py --json scripts/results/m19_minicpm5_grpo/*.json

Code de sortie : 1 si TOUS les bras sont `SIGNAL_NUL` (le volume mesure est
inexploitable), 0 sinon.
"""

from __future__ import annotations

import argparse
import json
import statistics
from pathlib import Path
from typing import Any

# Seuils nommes -- un seuil non nomme dans le code est un seuil qu'on
# invente apres coup dans le rapport.
SEUIL_SATURATION_TOTALE = 0.95
SEUIL_SANS_GRADIENT_MAJORITAIRE = 0.5
# Tolerance de plafond : `mean_length` est une moyenne, elle peut choir sous le
# plafond sur une generation tronquee ; 0.5 unite evite de compter une
# generation terminee a 383,5 comme une generation saturee.
TOLERANCE_PLAFOND = 0.5

# Ordre de precedence des verdicts : du plus grave au plus benign.
RANG_VERDICT = {"SIGNAL_NUL": 0, "SIGNAL_PARTIEL": 1, "SIGNAL_UTILE": 2}


def _valeurs(log_history: list[dict[str, Any]], cle: str) -> list[float]:
    """Valeurs numeriques d'une metrique, cle absente -> ignoree."""
    out: list[float] = []
    for entree in log_history:
        valeur = entree.get(cle)
        if isinstance(valeur, bool):
            continue
        if isinstance(valeur, (int, float)):
            out.append(float(valeur))
    return out


def _part(fraction: float) -> float:
    return round(fraction, 4)


def mesurer(artefact: dict[str, Any]) -> dict[str, Any]:
    """Mesure une graine. Un artefact sans `log_history` exploitable est signale."""
    log_history = artefact.get("log_history")
    budget = artefact.get("max_completion_length")
    rapport: dict[str, Any] = {
        "modele": artefact.get("model"),
        "model_key": artefact.get("model_key"),
        "graine": artefact.get("seed"),
        "budget_completion": budget,
        "wallclock_s": artefact.get("wallclock_s"),
    }
    if not isinstance(log_history, list) or not log_history:
        rapport.update({"verdict": "ILLISIBLE", "raison": "aucune entree de log_history"})
        return rapport

    clipped = _valeurs(log_history, "completions/clipped_ratio")
    longueurs = _valeurs(log_history, "completions/mean_length")
    grad = _valeurs(log_history, "grad_norm")
    loss = _valeurs(log_history, "loss")
    zero_std = _valeurs(log_history, "frac_reward_zero_std")
    reward = _valeurs(log_history, "reward")

    steps = max(len(clipped), len(longueurs), len(grad), len(loss))
    rapport["steps"] = steps

    if not budget or not isinstance(budget, (int, float)) or budget <= 0:
        rapport.update({"verdict": "ILLISIBLE", "raison": "budget max_completion_length absent"})
        return rapport

    plafond = float(budget)
    satures = sum(1 for v in longueurs if v >= plafond - TOLERANCE_PLAFOND)
    tronques = sum(1 for v in clipped if v >= 1.0 - 1e-9)
    sans_gradient = sum(1 for v in grad if v == 0.0)
    sans_signal = sum(1 for v in zero_std if v >= 1.0 - 1e-9)
    recompense_nulle = sum(1 for v in reward if v == 0.0)

    base = len(longueurs) or steps
    steps_avec_gradient = (len(grad) - sans_gradient) if grad else None

    # Gain d'evaluation : ce que la session d'evaluation mesure, hors budget
    # de training. Il est divise par le nombre de steps qui ont porte un
    # gradient -- sans quoi un bras qui n'a appris que sur 2 steps parait
    # comparable a un bras qui a appris sur 24.
    gain_eval = None
    pre = artefact.get("pre_eval")
    post = artefact.get("post_eval")
    if isinstance(pre, dict) and isinstance(post, dict):
        avant, apres = pre.get("reward_mean"), post.get("reward_mean")
        if isinstance(avant, (int, float)) and isinstance(apres, (int, float)):
            gain_eval = round(float(apres) - float(avant), 6)

    rapport.update(
        {
            "frac_steps_satures": _part(satures / base),
            "frac_steps_tronquees": _part(tronques / base),
            "frac_steps_sans_gradient": _part(sans_gradient / len(grad)) if grad else None,
            "frac_steps_sans_signal": _part(sans_signal / len(zero_std)) if zero_std else None,
            "frac_steps_recompense_nulle": _part(recompense_nulle / len(reward)) if reward else None,
            "steps_avec_gradient": steps_avec_gradient,
            "gain_eval_recompense": gain_eval,
            "gain_eval_par_step_avec_gradient": (
                round(gain_eval / steps_avec_gradient, 6)
                if gain_eval is not None and steps_avec_gradient
                else None
            ),
            "mean_length_mediane": round(statistics.median(longueurs), 2) if longueurs else None,
            # Dispersion de la longueur PAR STEP. Un ecart type quasi nul
            # signifie que chaque generation finit exactement au plafond :
            # le modele ne termine jamais (contrat EOS rompu). Un ecart type
            # large signifie que le modele s'arrete parfois avant le budget :
            # la troncature est alors une pression de budget reelle.
            "mean_length_ecart_type": round(statistics.pstdev(longueurs), 3) if longueurs else None,
            "clipped_ratio_median": round(statistics.median(clipped), 4) if clipped else None,
            "grad_norm_max": round(max(grad), 6) if grad else None,
            "reward_max": round(max(reward), 6) if reward else None,
            "reward_median": round(statistics.median(reward), 6) if reward else None,
        }
    )

    frac_satures = rapport["frac_steps_satures"]
    frac_sans_gradient = rapport["frac_steps_sans_gradient"]
    if frac_satures >= SEUIL_SATURATION_TOTALE:
        rapport["verdict"] = "SIGNAL_NUL"
    elif frac_sans_gradient is not None and frac_sans_gradient >= SEUIL_SANS_GRADIENT_MAJORITAIRE:
        rapport["verdict"] = "SIGNAL_PARTIEL"
    else:
        rapport["verdict"] = "SIGNAL_UTILE"
    return rapport


def _verdict_median(verdicts: list[str]) -> str:
    """Verdict median d'une liste de verdicts, du plus grave au plus benin.

    Effectif impair : l'element central. Effectif **pair** : l'element central
    SUPERIEUR, c'est-a-dire le **moins grave** des deux centraux -- convention
    **optimiste**, explicite et assumee : un bras dont une graine sur deux
    sature porte encore du signal.

    Les verdicts inconnus ne votent pas (seuls ceux de `RANG_VERDICT` sont
    pris en compte) : un `ILLISIBLE` ne peut pas etre lu comme un `SIGNAL_*`.

    La convention est **pincee par un test**
    (`test_le_bras_a_effectif_pair_suit_la_convention_declaree`) : a deux
    graines de gravites differentes, c'est elle qui decide du verdict, et un
    lecteur qui la devinerait autrement lirait un verdict oppose au sien.
    """
    connus = sorted((v for v in verdicts if v in RANG_VERDICT), key=lambda v: RANG_VERDICT[v])
    if not connus:
        return "ILLISIBLE"
    return connus[len(connus) // 2]


def verdict_bras(graines: list[dict[str, Any]]) -> str:
    """Verdict d'un bras, a partir des verdicts de ses graines.

    Le bras suit la graine **mediane** : un bras dont une graine sur deux
    sature porte encore du signal. `SIGNAL_NUL` quand toutes les graines
    saturent.

    A effectif pair, la mediane suit la convention **optimiste** (le moins
    grave des deux verdicts centraux) -- voir `_verdict_median`.
    """
    verdicts = [g.get("verdict") for g in graines]
    if not verdicts:
        return "ILLISIBLE"
    if all(v == "SIGNAL_NUL" for v in verdicts):
        return "SIGNAL_NUL"
    return _verdict_median(verdicts)


def mesurer_fichiers(chemins: list[Path]) -> dict[str, Any]:
    """Mesure chaque artefact et regroupe les graines par bras."""
    rapports: list[dict[str, Any]] = []
    hors_bras: list[dict[str, Any]] = []
    for chemin in chemins:
        try:
            artefact = json.loads(chemin.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            hors_bras.append({"fichier": chemin.name, "raison": f"illisible : {exc}"})
            continue
        rapport = mesurer(artefact)
        rapport["fichier"] = chemin.name
        if rapport.get("verdict") == "ILLISIBLE" or not rapport.get("model_key"):
            # Un fichier qui n'est pas une graine (baseline, resume) ne peut
            # pas voter sur le verdict d'un bras.
            rapport["raison"] = rapport.get("raison", "model_key absent : hors bras")
            hors_bras.append(rapport)
            continue
        rapports.append(rapport)

    bras: dict[str, list[dict[str, Any]]] = {}
    for rapport in rapports:
        bras.setdefault(str(rapport["model_key"]), []).append(rapport)

    par_bras: dict[str, Any] = {}
    for cle, graines in sorted(bras.items()):
        graines = sorted(graines, key=lambda g: (g.get("graine") is None, g.get("graine")))
        steps_vivants = statistics.median(
            [g["steps_avec_gradient"] for g in graines if g.get("steps_avec_gradient") is not None]
        ) if any(g.get("steps_avec_gradient") is not None for g in graines) else None
        # Garde-fou du gain par step vivant (reserve de la revue structurelle
        # du 2026-10-26) : la metrique n'est COMPARABLE que si son diviseur --
        # la mediane des steps qui ont porte un gradient -- vaut au moins 1.
        # Divise par 0,5 (mediane de {0, 1}), elle DOUBLE un gain reel : une
        # amplification qui n'a aucun sens physique. Le gain par step n'est
        # donc pas publie quand le diviseur est < 1, et `comparable` le dit.
        comparable = steps_vivants is not None and steps_vivants >= 1
        gain_par_step = round(statistics.median(
            [g["gain_eval_par_step_avec_gradient"] for g in graines
             if g.get("gain_eval_par_step_avec_gradient") is not None]
        ), 6) if any(g.get("gain_eval_par_step_avec_gradient") is not None for g in graines) else None
        par_bras[cle] = {
            "verdict": verdict_bras(graines),
            "graines": [g.get("graine") for g in graines],
            "frac_steps_satures": _part(statistics.median(
                [g["frac_steps_satures"] for g in graines if g.get("frac_steps_satures") is not None]
            )) if any(g.get("frac_steps_satures") is not None for g in graines) else None,
            "frac_steps_sans_gradient": _part(statistics.median(
                [g["frac_steps_sans_gradient"] for g in graines if g.get("frac_steps_sans_gradient") is not None]
            )) if any(g.get("frac_steps_sans_gradient") is not None for g in graines) else None,
            "mean_length_ecart_type": round(statistics.median(
                [g["mean_length_ecart_type"] for g in graines if g.get("mean_length_ecart_type") is not None]
            ), 3) if any(g.get("mean_length_ecart_type") is not None for g in graines) else None,
            "steps_avec_gradient": steps_vivants,
            "gain_eval_recompense": round(statistics.median(
                [g["gain_eval_recompense"] for g in graines if g.get("gain_eval_recompense") is not None]
            ), 6) if any(g.get("gain_eval_recompense") is not None for g in graines) else None,
            "gain_eval_par_step_avec_gradient": gain_par_step if comparable else None,
            "gain_eval_par_step_comparable": comparable,
            "budget_completion": graines[0].get("budget_completion"),
        }

    verdicts = [b["verdict"] for b in par_bras.values()]
    if not verdicts:
        verdict_global = "ILLISIBLE"
    elif all(v == "SIGNAL_NUL" for v in verdicts):
        verdict_global = "SIGNAL_NUL"
    else:
        verdict_global = _verdict_median(verdicts)

    return {
        "graines": rapports,
        "bras": par_bras,
        "hors_bras": hors_bras,
        "verdict_global": verdict_global,
    }


def _afficher(rapport: dict[str, Any]) -> None:
    nom = rapport.get("fichier") or rapport.get("model_key") or "?"
    print(f"== {nom} (graine {rapport.get('graine')}, budget {rapport.get('budget_completion')})")
    if rapport.get("verdict") == "ILLISIBLE":
        print(f"   ILLISIBLE : {rapport.get('raison')}")
        return
    print(
        "   steps={steps} satures={frac_steps_satures} tronquees={frac_steps_tronquees} "
        "sans_gradient={frac_steps_sans_gradient} sans_signal={frac_steps_sans_signal} "
        "steps_avec_gradient={steps_avec_gradient}".format(**rapport)
    )
    print(
        "   gain_eval={gain_eval_recompense} gain_par_step_avec_gradient="
        "{gain_eval_par_step_avec_gradient}".format(**rapport)
    )
    print(
        "   mean_length_med={mean_length_mediane} mean_length_ecart_type={mean_length_ecart_type} "
        "clipped_ratio_med={clipped_ratio_median} "
        "grad_norm_max={grad_norm_max} reward_med={reward_median} reward_max={reward_max}".format(**rapport)
    )
    print(f"   VERDICT : {rapport['verdict']}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artefacts", nargs="+", type=Path, help="artefacts JSON de run")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    rapport = mesurer_fichiers(args.artefacts)

    if args.json:
        print(json.dumps(rapport, ensure_ascii=False, indent=1))
    else:
        for graine in rapport["graines"]:
            _afficher(graine)
        for hors in rapport["hors_bras"]:
            print(f"== {hors.get('fichier')} : hors bras ({hors.get('raison')})")
        print()
        print("VERDICT PAR BRAS :")
        for cle, bras in rapport["bras"].items():
            gain_par_step = bras["gain_eval_par_step_avec_gradient"]
            if not bras.get("gain_eval_par_step_comparable", True):
                gain_par_step = "non comparable (moins d'un step vivant)"
            print(
                f"   {cle:12s} {bras['verdict']:14s} graines={bras['graines']} "
                f"satures={bras['frac_steps_satures']} sans_gradient={bras['frac_steps_sans_gradient']} "
                f"ecart_type_longueur={bras['mean_length_ecart_type']} "
                f"steps_avec_gradient={bras['steps_avec_gradient']} "
                f"gain_eval={bras['gain_eval_recompense']} "
                f"gain_par_step={gain_par_step} "
                f"budget={bras['budget_completion']}"
            )
        print()
        print(f"VERDICT GLOBAL : {rapport['verdict_global']}")
        if rapport["verdict_global"] == "SIGNAL_NUL":
            print(
                "le budget de completion est la contrainte : tous les bras sont satures, "
                "aucune comparaison multi-graine n'a de sens sur ce volume"
            )
    return 1 if rapport["verdict_global"] == "SIGNAL_NUL" else 0


if __name__ == "__main__":
    raise SystemExit(main())
