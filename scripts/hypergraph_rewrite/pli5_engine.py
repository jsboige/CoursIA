"""Pli 5 Origami Wolfram (#23093) : sonde d'outil, controle de coherence, mesure.

Trois blocs, dans l'ordre ou le pli les exige :

1. **verdict d'outil** (`engine_probe`, `capabilities`, `tool_verdict`) : il
   precede toute mesure et rend une des cinq valeurs de `sota-not-workaround.md` ;
2. **controle de coherence** (`calibrate`) : le modele attendu est ecrit dans la
   constante `CALIBRATION` avant toute execution, jamais relu depuis la sortie ;
   il valide la coherence interne du modele, pas son adequation au moteur ;
3. **mesure** (`growth`, `fit_power_law`, `occurrences`, `measure`) : bandes de
   verdict declarees avant la mesure dans `EXPONENT_BANDS`, aucun seuil ajuste
   apres coup.

Trois instruments ont ete corriges apres revue, parce qu'ils ne pouvaient pas
produire le resultat oppose a celui qu'ils annoncaient : la sonde de capacites ne
lisait que le module (jamais les 17 methodes de `HypergraphSystem`), le temoin de
fan-out valait 1 par construction sur toute regle, et la selection de modele
comparait un R2 de `log(y)` a un R2 de `y`.

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


def _public_names(obj):
    """Noms publics d'un objet (module ou classe), tries."""
    return sorted(n for n in dir(obj) if not n.startswith("_"))


def capabilities():
    """Enumere la surface de l'API -- module ET classes -- et cherche une enumeration multiway.

    Le module seul ne suffit pas : `dir(module)` rend 15 noms dont les classes, et
    toute la semantique de `setreplace` vit sur `HypergraphSystem` (17 methodes :
    `evolve`, `events`, `states_by_event`, `state_at_generation`, `replace_once`...).
    Une sonde qui ne lit que le module rend `False` sur un moteur qui exposerait
    l'enumeration sur sa classe -- elle ne mesure pas ce qu'elle annonce. Chaque
    surface est donc parcourue, et son denombrement est rendu pour que la lecture
    puisse verifier ce qui a ete regarde.
    """
    module = _import_engine()
    surfaces = {"module": _public_names(module)}
    for name in surfaces["module"]:
        obj = getattr(module, name, None)
        if isinstance(obj, type):
            surfaces[f"class:{name}"] = _public_names(obj)
    hits = {
        surface: [n for n in names if any(hint in n.lower() for hint in MULTIWAY_HINTS)]
        for surface, names in surfaces.items()
    }
    found = {surface: h for surface, h in hits.items() if h}
    return {
        "scanned": {surface: len(names) for surface, names in surfaces.items()},
        "multiway_surface": found,
        "multiway_available": bool(found),
        # Briques disponibles pour CONSTRUIRE l'enumeration hors du moteur : ce n'est
        # pas une enumeration multiway, et le dire ainsi evite de la confondre avec une.
        "occurrence_frontier_available": "set_replace_all" in surfaces["module"],
    }


def tool_verdict(probe, caps):
    """Rend le verdict d'outil unique et son motif, sans arrondir la premisse.

    L'ordre suit celui du corps du pli : la voie SOTA (moteur Wolfram) est epuisee
    en premier, l'alternative ouverte ensuite. Rendre `RECOVERABLE-LOCAL` alors que
    le moteur SOTA est present serait un verdict sous-optimal rendu en silence.
    """
    multiway = (caps or {}).get("multiway_available")
    suffix = "" if multiway is None else (" ; API sans enumeration multiway" if not multiway else " ; enumeration multiway presente")
    if probe["wolfram"]["wolframscript"] or probe["wolfram"]["wolfram_kernel"]:
        return {
            "verdict": "SOTA-OK",
            "motive": "moteur Wolfram local present, SetReplace invocable" + suffix,
        }
    if probe.get("setreplace_available"):
        motive = (
            "alternative ouverte installee et invoquee localement (paquet MIT, "
            "semantique SetReplace exacte, aucun moteur Wolfram requis)" + suffix
        )
        return {"verdict": "RECOVERABLE-LOCAL", "motive": motive}
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


def fit_power_law_raw(xs, ys, iterations=200):
    """Ajuste `y = A * x**alpha` en espace BRUT : SSE minimisee sur alpha.

    Necessaire pour comparer deux modeles sur la MEME variable reponse. Le R2 de
    `fit_power_law` porte sur `log(y)` ; celui de `fit_affine` porte sur `y`. Les
    comparer revient a comparer deux coefficients de determination qui n'ont pas la
    meme reponse, et le gagnant depend alors de l'echelle, pas de l'adequation.

    Pour un alpha donne, l'ordonnee qui minimise la SSE brute est celle des moindres
    carres lineaires `A = somme(y * x**alpha) / somme(x**(2*alpha))` ; alpha est
    cherche par section doree sur [0.01, 5.0]. Pas de dependance supplementaire.
    """
    if len(xs) != len(ys) or len(xs) < 2:
        raise ValueError("il faut au moins deux points appariees")
    if any(x <= 0 for x in xs) or any(y <= 0 for y in ys):
        raise ValueError("la loi de puissance exige des valeurs strictement positives")

    def sse(alpha):
        num = sum(y * (x**alpha) for x, y in zip(xs, ys))
        den = sum((x**alpha) ** 2 for x in xs)
        scale = num / den
        return sum((y - scale * (x**alpha)) ** 2 for x, y in zip(xs, ys)), scale

    lo, hi = 0.01, 5.0
    for _ in range(iterations):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if sse(m1)[0] < sse(m2)[0]:
            hi = m2
        else:
            lo = m1
    slope = (lo + hi) / 2
    ss_res, scale = sse(slope)
    mean = sum(ys) / len(ys)
    ss_tot = sum((y - mean) ** 2 for y in ys)
    r2 = 1.0 - ss_res / ss_tot if ss_tot else 1.0
    return {"slope": slope, "scale": scale, "r2": r2, "n": len(xs)}


def compare_models(xs, ys):
    """Retient le modele qui decrit la serie, entre affine et loi de puissance.

    Regle declaree avant la mesure : les deux modeles ont deux parametres, donc
    aucune correction de parcimonie n'est necessaire ; le R2 le plus haut gagne, et
    a egalite la loi de puissance l'emporte (elle est plus generale). Le tie-break
    est un `>=` : un `>` strict donnerait l'affine a egalite, l'inverse de la regle.

    **Le R2 compare est celui de l'espace brut pour les deux modeles** -- `fit_affine`
    ajuste `y`, `fit_power_law_raw` ajuste `y`. La version precedente comparait le R2
    de `log(y)` au R2 de `y` : sur une serie exactement affine a forte ordonnee
    (`y = 100 + x`), la loi de puissance y perdait pour la mauvaise raison. Les deux
    ajustements sont rendus cote a cote (`power_law` = log, `power_law_raw` = brut)
    pour que l'ecart d'espace reste lisible.

    Le piege que cette fonction existe pour attraper est mesure : une serie
    exactement affine `y = a * x + b` ajustee en loi de puissance *log-log* rend un
    exposant nettement inferieur a 1 avec un R2 superieur a 0,99. Conclure
    « sous-lineaire » sur cet exposant serait faux -- et c'est ce que le R2 brut
    départage, sans invoquer la sur-adequation.
    """
    affine = fit_affine(xs, ys)
    power = fit_power_law(xs, ys)
    power_raw = fit_power_law_raw(xs, ys)
    chosen = "power-law" if power_raw["r2"] >= affine["r2"] else "affine"
    if chosen == "affine":
        classification = "affine (pente=%.3f, ordonnee=%.3f)" % (affine["slope"], affine["intercept"])
    else:
        classification = classify_exponent(power_raw["slope"])
    return {
        "affine": affine,
        "power_law": power,
        "power_law_raw": power_raw,
        "chosen": chosen,
        "classification": classification,
    }


def occurrences(rule_text, initial, n_events=13):
    """Etats suivants DISTINCTS offerts a chaque generation (frontiere du multiway).

    Ce n'est **pas** un temoin negatif, et c'est precisement le point : un temoin
    « le chemin unique ne branche pas » ne peut pas rougir, puisque le moteur
    applique un evenement par generation par construction -- la mesure precedente
    (`max_consumers`) valait 1 sur cinq regles differentes, y compris la branchante.
    Ce n'etait pas un temoin, c'etait une identite.

    La grandeur rendue ici **varie** avec la regle et la generation : c'est le
    nombre d'etats suivants distincts que `set_replace_all` rend a partir de l'etat
    courant, donc le nombre d'occurrences distinctes disponibles. C'est l'entree de
    l'enumeration multiway qui manque au moteur -- une mesure, pas une preuve de
    non-branchement. Elle ne dit rien du nombre d'etats multiway.
    """
    module = _import_engine()
    rules = [module.Rule.parse(rule_text)]
    system = _system(rule_text, initial)
    system.evolve(max_events=n_events)
    rows = []
    for generation in range(system.generations_count + 1):
        state = system.state_at_generation(generation)
        row = {"generation": generation, "edges": len(state), "applied_here": 1}
        try:
            row["distinct_next_states"] = len(module.set_replace_all(state, rules, generations=1))
        except Exception as exc:  # noqa: BLE001 - le motif est la donnee mesuree
            row["distinct_next_states"] = None
            row["error"] = f"{type(exc).__name__}: {exc}"
        rows.append(row)
    counts = [r["distinct_next_states"] for r in rows if r["distinct_next_states"] is not None]
    return {
        "events": n_events,
        "generations": len(rows),
        "rows": rows,
        "max_distinct_next_states": max(counts) if counts else None,
        "note": (
            "un evenement applique par generation alors que la frontiere en offre "
            "davantage : propriete structurelle du chemin unique, pas un temoin "
            "negatif ; cette serie est l'entree du grain B (enumeration multiway)"
        ),
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
    result["occurrences"] = {name: occurrences(spec["rule"], spec["initial"]) for name, spec in RULES.items()}
    result["limits"] = [
        "l'API du moteur retenu n'expose aucune enumeration multiway (sonde elargie au "
        "module ET aux classes, cf `capabilities.scanned`) : la question de la "
        "reductibilite du nombre de branches n'est pas tranchee par cette mesure, qui "
        "ne porte que sur un chemin unique",
        "`set_replace_all` rend les etats suivants distincts d'un etat donne : c'est "
        "l'entree d'une enumeration multiway, pas l'enumeration elle-meme -- la "
        "frontiere mesuree (`occurrences`) n'est pas le nombre d'etats multiway",
        "un seul ordre d'evenements est mesure (LeastRecentEdge par defaut) : les autres "
        "ordres ne sont pas explores",
        "sur un chemin unique la croissance est affine par construction (chaque evenement "
        "consomme k aretes et en produit m) ; un ajustement en loi de puissance y rend un "
        "exposant inferieur a 1 avec un R2 trompeur, ce que la selection de modele corrige "
        "en comparant les deux modeles sur la meme variable reponse",
        "le controle de coherence compare un modele ecrit a la main a des constantes "
        "ecrites a la main : il valide la coherence interne, pas l'adequation de la regle "
        "au moteur, et il discrimine une VALEUR fausse, pas un MODELE faux",
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
            power_raw = fit["power_law_raw"]
            print(
                f"    {quantity}: modele={fit['chosen']} -> {fit['classification']} "
                f"(alpha_log={power['slope']:.3f} R2_puissance_log={power['r2']:.4f} "
                f"alpha_brut={power_raw['slope']:.3f} R2_puissance_brut={power_raw['r2']:.4f} "
                f"R2_affine={fit['affine']['r2']:.4f})"
            )
    for name, occ in payload.get("occurrences", {}).items():
        frontier = " ".join(
            f"g{r['generation']}={r['distinct_next_states']}" for r in occ["rows"]
        )
        print(f"  occurrences {name}: max={occ['max_distinct_next_states']} | {frontier}")
    return 0 if payload.get("calibration", {}).get("passed") else 1


if __name__ == "__main__":
    raise SystemExit(main())
