"""Pli 5 Origami Wolfram (#23093) : sonde d'outil, controle de correction, mesure.

Trois blocs, dans l'ordre ou le pli les exige :

1. **verdict d'outil** (`engine_probe`, `capabilities`, `tool_verdict`) : il
   precede toute mesure et rend une des cinq valeurs de `sota-not-workaround.md` ;
2. **controle de correction** (`calibrate`) : le modele attendu est ecrit dans la
   constante `CALIBRATION` avant toute execution, jamais relu depuis la sortie ;
3. **mesure** (`growth`, `fit_power_law`, `fanout`, `measure`) : bandes de verdict
   declarees avant la mesure dans `EXPONENT_BANDS`, aucun seuil ajuste apres coup.

Le moteur est optionnel : absent, le module rend un verdict d'outil et refuse de
mesurer, il n'invente aucun chiffre.
"""

from __future__ import annotations

import json
import math
import shutil
import sys
from pathlib import Path

ISSUE = 23093
LANE = "myia-po-2023:CoursIA-2"

#: Les cinq valeurs admises par `.claude/rules/sota-not-workaround.md`.
VERDICTS = (
    "SOTA-OK",
    "RECOVERABLE-LOCAL",
    "RECOVERABLE-MACHINE",
    "RECOVERABLE-USER-HAND",
    "INTRINSIC",
)

#: Modele de correction ecrit a la main AVANT toute execution.
#: Regle {{x, y}} -> {{x, y}, {y, z}} sur l'etat initial {{1, 1}} : chaque evenement
#: consomme l'arete la plus ancienne (1 arete) et en produit deux, dont une vers un
#: atome frais. Donc arêtes = n + 1 et atomes = n + 1, calcules de tete.
CALIBRATION = {
    "rule": "{{x, y}} -> {{x, y}, {y, z}}",
    "initial": [[1, 1]],
    "expected": {1: {"edges": 2, "atoms": 2}, 2: {"edges": 3, "atoms": 3}, 3: {"edges": 4, "atoms": 4}},
}

#: Regles soumises a la mesure : une chaine (1 arete -> 2) et une branchante
#: (2 aretes -> 4). La seconde est celle dont un systeme multiway ferait exploser
#: le nombre de branches si l'enumeration existait.
RULES = {
    "chaine": {"rule": "{{x, y}} -> {{x, y}, {y, z}}", "initial": [[1, 1]]},
    "branchante": {
        "rule": "{{x, y}, {x, z}} -> {{x, y}, {x, w}, {y, w}, {z, w}}",
        "initial": [[1, 1], [1, 1]],
    },
}

#: Nombres d'evenements de la serie de mesure.
EVENTS_SERIES = (1, 2, 3, 5, 8, 13, 21)

#: Bandes de verdict sur l'exposant alpha de la loi de puissance, declarees avant.
EXPONENT_BANDS = (
    (0.0, 0.85, "sous-lineaire"),
    (0.85, 1.15, "lineaire"),
    (1.15, math.inf, "super-lineaire"),
)

#: Un chemin unique ne branche pas si aucun jeton n'est consomme par plus d'un
#: evenement ; declare avant la mesure, il sert de temoin negatif de branchement.
FANOUT_CAP = 1

#: Fragments de nom qui trahiraient une enumeration multiway dans l'API du moteur.
MULTIWAY_HINTS = ("multiway", "all_event", "all_state", "all_branch", "branchial")


def _import_engine():
    """Rend le module moteur, ou leve ImportError avec son motif."""
    import setreplace  # noqa: PLC0415 - import optionnel, motif rendu a l'appelant

    return setreplace


def engine_probe():
    """Sonde l'outil a la source : Wolfram local, puis l'alternative ouverte."""
    wolfram = {
        "wolframscript": shutil.which("wolframscript"),
        "wolfram_kernel": shutil.which("WolframKernel"),
        "install_dir_present": Path("C:/Program Files/Wolfram Research").exists(),
    }
    probe = {"wolfram": wolfram, "setreplace_available": False}
    try:
        module = _import_engine()
    except Exception as exc:  # noqa: BLE001 - le motif est la donnee mesuree
        probe["setreplace_error"] = f"{type(exc).__name__}: {exc}"
        return probe
    probe["setreplace_available"] = True
    probe["setreplace_version"] = getattr(module, "__version__", None)
    # Le chemin d'installation local n'est pas une donnee de la mesure : il n'entre
    # pas dans un artefact commite.
    return probe


def capabilities():
    """Enumere la surface de l'API et cherche une enumeration multiway."""
    module = _import_engine()
    names = sorted(n for n in dir(module) if not n.startswith("_"))
    hits = [n for n in names if any(h in n.lower() for h in MULTIWAY_HINTS)]
    return {
        "public_names": names,
        "multiway_surface": hits,
        "multiway_available": bool(hits),
    }


def tool_verdict(probe, caps):
    """Rend le verdict d'outil unique et son motif, sans arrondir la premisse."""
    if probe.get("setreplace_available"):
        motive = (
            "alternative ouverte installee et invoquee localement (paquet MIT, "
            "semantique SetReplace exacte, aucun moteur Wolfram requis)"
        )
        return {"verdict": "RECOVERABLE-LOCAL", "motive": motive}
    if probe["wolfram"]["wolframscript"] or probe["wolfram"]["wolfram_kernel"]:
        return {
            "verdict": "SOTA-OK",
            "motive": "moteur Wolfram local present, SetReplace invocable",
        }
    return {
        "verdict": "RECOVERABLE-USER-HAND",
        "motive": (
            "aucun moteur installe ; l'activation du Wolfram Engine passe par un "
            "compte, donc par une decision de mainteneur"
        ),
    }


def _system(rule_text, initial, seed=0):
    module = _import_engine()
    return module.HypergraphSystem([module.Rule.parse(rule_text)], initial, random_seed=seed)


def calibrate():
    """Rejoue le modele ecrit a la main et rend chaque point, passe ou echoue."""
    points = []
    for n, expected in sorted(CALIBRATION["expected"].items()):
        system = _system(CALIBRATION["rule"], CALIBRATION["initial"])
        system.evolve(max_events=n)
        got = {"edges": len(system.final_state), "atoms": system.final_atom_count}
        for key in ("edges", "atoms"):
            points.append(
                {
                    "events": n,
                    "quantity": key,
                    "expected": expected[key],
                    "got": got[key],
                    "ok": got[key] == expected[key],
                }
            )
    return {"rule": CALIBRATION["rule"], "points": points, "passed": all(p["ok"] for p in points)}


def growth(rule_text, initial, series=EVENTS_SERIES):
    """Etat final apres n evenements, pour chaque n de la serie."""
    rows = []
    for n in series:
        system = _system(rule_text, initial)
        applied = system.evolve(max_events=n)
        rows.append(
            {
                "events_requested": n,
                "events_applied": applied,
                "edges": len(system.final_state),
                "atoms": system.final_atom_count,
                "generations": system.generations_count,
                "termination": system.termination_reason,
            }
        )
    return rows


def fit_power_law(xs, ys):
    """Pente, ordonnee et R2 de log(y) = alpha * log(x) + c, moindres carres."""
    if len(xs) != len(ys) or len(xs) < 2:
        raise ValueError("il faut au moins deux points appariees")
    if any(x <= 0 for x in xs) or any(y <= 0 for y in ys):
        raise ValueError("la loi de puissance exige des valeurs strictement positives")
    lx = [math.log(x) for x in xs]
    ly = [math.log(y) for y in ys]
    n = len(lx)
    mx = sum(lx) / n
    my = sum(ly) / n
    sxx = sum((x - mx) ** 2 for x in lx)
    sxy = sum((x - mx) * (y - my) for x, y in zip(lx, ly))
    slope = sxy / sxx if sxx else float("nan")
    intercept = my - slope * mx
    ss_tot = sum((y - my) ** 2 for y in ly)
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(lx, ly))
    r2 = 1.0 - ss_res / ss_tot if ss_tot else 1.0
    return {"slope": slope, "intercept": intercept, "r2": r2, "n": n}


def classify_exponent(alpha):
    """Classe un exposant selon les bandes declarees avant la mesure."""
    for low, high, label in EXPONENT_BANDS:
        if low <= alpha < high:
            return label
    return "hors-bande"


def fit_affine(xs, ys):
    """Pente, ordonnee et R2 de y = a * x + b, moindres carres sur les valeurs brutes."""
    if len(xs) != len(ys) or len(xs) < 2:
        raise ValueError("il faut au moins deux points appariees")
    n = len(xs)
    mx = sum(xs) / n
    my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx if sxx else float("nan")
    intercept = my - slope * mx
    ss_tot = sum((y - my) ** 2 for y in ys)
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(xs, ys))
    r2 = 1.0 - ss_res / ss_tot if ss_tot else 1.0
    return {"slope": slope, "intercept": intercept, "r2": r2, "n": n}


def compare_models(xs, ys):
    """Retient le modele qui decrit la serie, entre affine et loi de puissance.

    Regle declaree avant la mesure : les deux modeles ont deux parametres, donc
    aucune correction de parcimonie n'est necessaire ; le R2 le plus haut gagne, et
    a egalite la loi de puissance l'emporte (elle est plus generale).

    Le piege que cette fonction existe pour attraper est mesure : une serie
    exactement affine `y = a * x + b` ajustee en loi de puissance rend un exposant
    nettement inferieur a 1 avec un R2 superieur a 0,99. Conclure « sous-lineaire »
    sur cet exposant serait faux.
    """
    affine = fit_affine(xs, ys)
    power = fit_power_law(xs, ys)
    chosen = "power-law" if power["r2"] > affine["r2"] else "affine"
    if chosen == "affine":
        classification = "affine (pente=%.3f, ordonnee=%.3f)" % (affine["slope"], affine["intercept"])
    else:
        classification = classify_exponent(power["slope"])
    return {"affine": affine, "power_law": power, "chosen": chosen, "classification": classification}


def fanout(rule_text, initial, n_events=13):
    """Nombre maximal d'evenements consommant un meme jeton (temoin de branchement)."""
    system = _system(rule_text, initial)
    system.evolve(max_events=n_events)
    consumers = {}
    for event_index, event in enumerate(system.events()):
        if event.rule is None:
            continue
        for token_id in event.inputs:
            consumers.setdefault(token_id, []).append(event_index)
    degrees = sorted((len(v) for v in consumers.values()), reverse=True)
    return {
        "events": n_events,
        "tokens_consumed": len(consumers),
        "max_consumers": degrees[0] if degrees else 0,
        "branches": degrees[0] > FANOUT_CAP if degrees else False,
    }


def measure():
    """Assemble le verdict, le controle et la mesure, sans horodatage (reproductible)."""
    probe = engine_probe()
    result = {"issue": ISSUE, "lane": LANE, "engine": probe}
    if not probe["setreplace_available"]:
        result["verdict"] = tool_verdict(probe, None)
        result["limits"] = ["moteur absent : aucune mesure produite"]
        return result
    caps = capabilities()
    result["verdict"] = tool_verdict(probe, caps)
    result["capabilities"] = caps
    calibration = calibrate()
    result["calibration"] = calibration
    if not calibration["passed"]:
        result["limits"] = ["controle de correction en echec : la mesure n'est pas produite"]
        return result
    fits = {}
    runs = {}
    for name, spec in RULES.items():
        rows = growth(spec["rule"], spec["initial"])
        runs[name] = rows
        events = [r["events_applied"] for r in rows]
        fits[name] = {quantity: compare_models(events, [r[quantity] for r in rows]) for quantity in ("edges", "atoms")}
    result["growth"] = runs
    result["fits"] = fits
    result["fanout"] = {name: fanout(spec["rule"], spec["initial"]) for name, spec in RULES.items()}
    result["limits"] = [
        "l'API du moteur retenu n'expose aucune enumeration multiway : la question "
        "de la reductibilite du nombre de branches n'est pas tranchee par cette mesure, "
        "qui ne porte que sur un chemin unique",
        "un seul ordre d'evenements est mesure (LeastRecentEdge par defaut) : les autres "
        "ordres ne sont pas explores",
        "sur un chemin unique la croissance est affine par construction (chaque evenement "
        "consomme k aretes et en produit m) ; un ajustement en loi de puissance y rend un "
        "exposant inferieur a 1 avec un R2 trompeur, ce que la selection de modele corrige",
    ]
    return result


def main(argv=None):
    """Ecrit le JSON de resultats et imprime un resume lisible."""
    argv = list(sys.argv[1:] if argv is None else argv)
    payload = measure()
    if "--write" in argv:
        target = Path(__file__).with_name("pli5_results.json")
        target.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"ecrit : {target}")
    print(f"verdict : {payload['verdict']['verdict']} -- {payload['verdict']['motive']}")
    if "calibration" in payload:
        print(f"controle de correction : {'PASS' if payload['calibration']['passed'] else 'ECHEC'}")
    for name, rows in payload.get("growth", {}).items():
        series = " ".join(f"{r['events_applied']}e/{r['edges']}a" for r in rows)
        print(f"  {name}: {series}")
        for quantity, fit in payload["fits"][name].items():
            power = fit["power_law"]
            print(
                f"    {quantity}: modele={fit['chosen']} -> {fit['classification']} "
                f"(alpha={power['slope']:.3f} R2_puissance={power['r2']:.4f} "
                f"R2_affine={fit['affine']['r2']:.4f})"
            )
    for name, fan in payload.get("fanout", {}).items():
        print(f"  fanout {name}: max={fan['max_consumers']} branche={fan['branches']}")
    return 0 if payload.get("calibration", {}).get("passed") else 1


if __name__ == "__main__":
    raise SystemExit(main())
