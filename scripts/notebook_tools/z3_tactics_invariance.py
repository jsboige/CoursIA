"""Sonde d'invariance des chaines de tactiques Z3 sur le corpus des series Z3.

Objet
-----
Le carnet `Z3-Linq2Z3/19_Solver_Choice_And_Tactics.ipynb` (et
`Z3-API/Z3-03-Tactics-Python.ipynb`) declarent des chaines de tactiques
(`Then(simplify, solve-eqs)`, `Then(simplify, propagate-values, ctx-solver-simplify)`)
et les opposent au solveur par defaut. Ces carnets mesurent le **cout** et le
**verdict** sur **une seule** instance (le Sudoku 9x9 a 30 indices), et concluent
que les quatre configurations rendent « la meme grille ».

Cette sonde etend la mesure a un **corpus** de la serie et separe trois
questions que les carnets confondent :

1. le **verdict** (sat / unsat / unknown) est-il invariant quand on change de
   chaine de tactiques ? -- c'est la propriete qui doit tenir ;
2. le **modele** rendu parle-t-il encore de l'enonce (toutes les variables
   definies) ? -- une chaine peut reecrire l'enonce au point que le modele ne
   parle plus des variables d'origine ;
3. quand le modele est lisible, est-ce **la meme** solution que celle des
   autres configurations ? -- sur une instance a solutions multiples, la reponse
   est non, alors que le carnet la conclut sur une instance a solution unique.

Falsifiabilite
--------------
Le verdict de la sonde est **binaire et reproductible** par instance :
`VERDICT_PRESERVE` si toutes les configurations rendent le meme verdict,
`DIVERGENCE` sinon. Les temps sont **mesures mais ne fondent aucun verdict** :
ils dependent de la machine et de la version de Z3. Un resultat qui depend du
chronometre n'est pas un resultat.

Provenance des instances
------------------------
Le corpus vient de la **serie Z3-API** elle-meme : le module
`MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/z3_instances.py` **exporte** les
encodages que les carnets portent dans leurs cellules (`Z3-11` pour le
graphe de Petersen, `Z3-10` pour le cryptarithme `SEND + MORE = MONEY`), et
la sonde l'**importe** au lieu de porter une copie.

C'est la reponse a la question 3 de la regle organ-first : l'organe natif
existe desormais sous forme importable, il est la **source unique**, et sa
fidelite aux carnets est **verifiee** par
`scripts/notebook_tools/tests/test_z3_instances_parity.py`, qui compare
l'export aux **sorties committes** des carnets.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import sys
import time
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from pathlib import Path

import z3

#: Racine du depot : le corpus est exporte par la serie Z3-API.
REPO_ROOT = Path(__file__).resolve().parents[2]

#: Dossier de la serie Z3-API, qui porte l'export du corpus.
SERIES_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "SMT" / "Z3-API"

if str(SERIES_DIR) not in sys.path:
    sys.path.insert(0, str(SERIES_DIR))

from z3_instances import petersen, send_more_money  # noqa: E402

# --- Instances ---------------------------------------------------------------

@dataclass(frozen=True)
class Instance:
    """Une instance du corpus : ses contraintes, ses variables, son empreinte."""

    name: str
    source: str
    build: Callable[[], tuple[list[z3.ExprRef], list[z3.ArithRef]]]
    fingerprint: Callable[[dict[str, int]], str]


def _defined_values(
    model: z3.ModelRef, variables: list[z3.ArithRef]
) -> dict[str, int]:
    """Valeurs definies par le modele, variable par variable.

    Une chaine de tactiques peut reecrire l'enonce au point que certaines
    variables n'apparaissent plus dans le modele : c'est une information, pas
    une erreur.
    """
    values: dict[str, int] = {}
    for variable in variables:
        value = model.eval(variable, model_completion=False)
        if z3.is_int_value(value):
            values[variable.decl().name()] = value.as_long()
    return values


def _fingerprint(values: dict[str, int]) -> str:
    """Empreinte stable d'une affectation (ordre des variables trie)."""
    payload = ",".join(f"{name}={values[name]}" for name in sorted(values))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def instances() -> list[Instance]:
    """Le corpus de la sonde : deux instances du carnet Z3-11, une de Z3-10.

    Les encodeurs viennent de l'export de la serie (`z3_instances`), pas d'une
    copie locale : la source unique est la serie.
    """
    return [
        Instance(
            name="petersen_k3",
            source="Z3-API/Z3-11-Graph-Coloring-Python.ipynb (coloration a 3 couleurs)",
            build=lambda: petersen(3),
            fingerprint=_fingerprint,
        ),
        Instance(
            name="petersen_k2",
            source="Z3-API/Z3-11-Graph-Coloring-Python.ipynb (coloration a 2 couleurs : chi(G) > 2)",
            build=lambda: petersen(2),
            fingerprint=_fingerprint,
        ),
        Instance(
            name="send_more_money",
            source="Z3-API/Z3-10-Cryptarithmetic-Python.ipynb (SEND + MORE = MONEY)",
            build=send_more_money,
            fingerprint=_fingerprint,
        ),
    ]


# --- Configurations ----------------------------------------------------------

#: Chaines comparees : le solveur par defaut, puis les chaines declarees par
#: les carnets `Z3-API/Z3-03-Tactics-*.ipynb` (memes noms de tactiques).
CONFIGS: dict[str, tuple[str, ...]] = {
    "solveur_par_defaut": (),
    "simplify": ("simplify",),
    "simplify+solve-eqs": ("simplify", "solve-eqs"),
    "simplify+propagate-values+ctx-solver-simplify": (
        "simplify",
        "propagate-values",
        "ctx-solver-simplify",
    ),
    "smt": ("smt",),
}


# --- Mesure ------------------------------------------------------------------

@dataclass
class Row:
    """Une mesure : une instance, une configuration, un verdict, des modeles, un temps."""

    instance: str
    config: str
    verdict: str
    source: str = ""
    fingerprints: list[str] = field(default_factory=list)
    readable_reps: int = 0
    partial_reps: int = 0
    blind_reps: int = 0
    total_reps: int = 0
    model_total: int = 0
    defined_counts: list[int] = field(default_factory=list)
    model_extends: str | None = None
    median_ms: float = 0.0
    samples_ms: list[float] = field(default_factory=list)


def _solver(constraints: Sequence[z3.ExprRef], chain: Sequence[str]) -> z3.Solver:
    """Construit un solveur, eventuellement preprocesse par une chaine de tactiques."""
    if not chain:
        solver = z3.Solver()
        solver.add(*constraints)
        return solver
    tactics = [z3.Tactic(name) for name in chain]
    # `z3.Then` exige au moins deux tactiques : une chaine de longueur 1
    # s'applique directement.
    goal = z3.Goal()
    goal.add(*constraints)
    goal = (tactics[0] if len(tactics) == 1 else z3.Then(*tactics))(goal)
    preprocessed = z3.Solver()
    for assertion in goal:
        preprocessed.add(assertion)
    return preprocessed


def _extends_solution(
    constraints: Sequence[z3.ExprRef],
    variables: list[z3.ArithRef],
    model: z3.ModelRef,
) -> str:
    """Le modele se prolonge-t-il en solution de l'enonce d'origine ?

    On rejoue l'enonce **d'origine** en y ajoutant les valeurs que le modele
    fixe : si la conjonction reste satisfiable, le modele n'introduit rien
    d'absurde. C'est le test de validite, independant du fait que le modele
    soit lisible ou non.
    """
    solver = z3.Solver()
    solver.add(*constraints)
    for variable in variables:
        value = model.eval(variable, model_completion=False)
        if z3.is_int_value(value):
            solver.add(variable == value.as_long())
    return str(solver.check())


def measure(
    instance: Instance,
    config: str,
    chain: Sequence[str],
    repetitions: int = 5,
) -> Row:
    """Mesure une instance sous une configuration : verdict, modeles, validite, temps."""
    samples: list[float] = []
    verdict = "unknown"
    fingerprints: list[str] = []
    readable_reps = 0
    partial_reps = 0
    blind_reps = 0
    defined_counts: list[int] = []
    model_total = 0
    extends: str | None = None

    # Echauffement hors mesure : la premiere resolution paie la compilation.
    warmup_constraints, _warmup_vars = instance.build()
    _solver(warmup_constraints, chain).check()

    for _ in range(repetitions):
        constraints, variables = instance.build()
        solver = _solver(constraints, chain)
        start = time.perf_counter()
        result = solver.check()
        elapsed_ms = (time.perf_counter() - start) * 1000.0
        samples.append(elapsed_ms)
        verdict = str(result)
        model_total = len(variables)
        if result == z3.sat:
            model = solver.model()
            values = _defined_values(model, variables)
            defined_counts.append(len(values))
            if len(values) == len(variables):
                readable_reps += 1
            elif values:
                partial_reps += 1
            else:
                blind_reps += 1
            fingerprint = instance.fingerprint(values)
            if fingerprint not in fingerprints:
                fingerprints.append(fingerprint)
            extends = _extends_solution(constraints, variables, model)
        else:
            extends = None

    return Row(
        instance=instance.name,
        config=config,
        verdict=verdict,
        source=instance.source,
        fingerprints=sorted(fingerprints),
        readable_reps=readable_reps,
        partial_reps=partial_reps,
        blind_reps=blind_reps,
        total_reps=repetitions,
        model_total=model_total,
        defined_counts=defined_counts,
        model_extends=extends,
        median_ms=statistics.median(samples),
        samples_ms=[round(sample, 3) for sample in samples],
    )


def measure_all(
    corpus: Sequence[Instance] | None = None,
    configs: dict[str, tuple[str, ...]] | None = None,
    repetitions: int = 5,
) -> list[Row]:
    """Mesure tout le corpus sous toutes les configurations."""
    corpus = list(corpus if corpus is not None else instances())
    configs = dict(configs if configs is not None else CONFIGS)
    rows: list[Row] = []
    for instance in corpus:
        for config, chain in configs.items():
            rows.append(measure(instance, config, chain, repetitions))
    return rows


# --- Verdict -----------------------------------------------------------------

@dataclass
class InstanceVerdict:
    """Le verdict d'une instance : invariance, lisibilite, accord, validite."""

    instance: str
    source: str = ""
    verdict: str = ""
    verdicts: dict[str, str] = field(default_factory=dict)
    fingerprints: dict[str, list[str]] = field(default_factory=dict)
    readable_reps: dict[str, int] = field(default_factory=dict)
    partial_reps: dict[str, int] = field(default_factory=dict)
    blind_reps: dict[str, int] = field(default_factory=dict)
    total_reps: dict[str, int] = field(default_factory=dict)
    defined_ranges: dict[str, list[int]] = field(default_factory=dict)
    median_ms: dict[str, float] = field(default_factory=dict)
    model_extends: dict[str, str | None] = field(default_factory=dict)
    model_total: int = 0
    distinct_verdicts: int = 0
    readable_configs: list[str] = field(default_factory=list)
    partial_configs: list[str] = field(default_factory=list)
    unreadable_configs: list[str] = field(default_factory=list)
    no_model_configs: list[str] = field(default_factory=list)
    distinct_readable_models: int = 0
    readable_models_agree: bool = True
    all_models_valid: bool = True
    status: str = ""

    def compute(self) -> InstanceVerdict:
        """Remplit les compteurs et le statut (`VERDICT_PRESERVE` / `DIVERGENCE`)."""
        self.distinct_verdicts = len(set(self.verdicts.values()))
        # La lisibilite du modele ne se discute que sur une instance SAT : sur
        # une instance UNSAT, il n'y a pas de modele du tout.
        self.no_model_configs = sorted(
            config for config, verdict in self.verdicts.items() if verdict != "sat"
        )
        sat_configs = [
            config for config, verdict in self.verdicts.items() if verdict == "sat"
        ]
        # Trois classes, et non deux : une chaine peut rendre le modele
        # parfaitement lisible, le rendre partiellement lisible (une variable
        # sur huit disparue) ou l'aveugler entierement. La classe « aveugle »
        # ne se discute que pour une instance SAT.
        self.readable_configs = sorted(
            config
            for config in sat_configs
            if self.readable_reps.get(config, 0) == self.total_reps.get(config, 0) > 0
        )
        self.partial_configs = sorted(
            config
            for config in sat_configs
            if config not in self.readable_configs
            and self.blind_reps.get(config, 0) < self.total_reps.get(config, 0)
        )
        self.unreadable_configs = sorted(
            config
            for config in sat_configs
            if self.blind_reps.get(config, 0) == self.total_reps.get(config, 0) > 0
        )
        readable_fingerprints = {
            fingerprint
            for config in self.readable_configs
            for fingerprint in self.fingerprints.get(config, [])
        }
        self.distinct_readable_models = len(readable_fingerprints)
        self.readable_models_agree = len(readable_fingerprints) <= 1
        self.all_models_valid = all(
            value == "sat" for value in self.model_extends.values() if value is not None
        )
        self.status = "VERDICT_PRESERVE" if self.distinct_verdicts == 1 else "DIVERGENCE"
        return self


def verdicts(rows: Sequence[Row]) -> list[InstanceVerdict]:
    """Agrege les mesures par instance et calcule les verdicts."""
    ordered: list[str] = []
    grouped: dict[str, InstanceVerdict] = {}
    for row in rows:
        if row.instance not in grouped:
            grouped[row.instance] = InstanceVerdict(
                instance=row.instance, source=row.source
            )
            ordered.append(row.instance)
        entry = grouped[row.instance]
        entry.verdicts[row.config] = row.verdict
        entry.fingerprints[row.config] = row.fingerprints
        entry.readable_reps[row.config] = row.readable_reps
        entry.partial_reps[row.config] = row.partial_reps
        entry.blind_reps[row.config] = row.blind_reps
        entry.total_reps[row.config] = row.total_reps
        entry.defined_ranges[row.config] = [
            min(row.defined_counts) if row.defined_counts else 0,
            max(row.defined_counts) if row.defined_counts else 0,
        ]
        entry.median_ms[row.config] = round(row.median_ms, 3)
        entry.model_extends[row.config] = row.model_extends
        entry.model_total = row.model_total
        entry.verdict = row.verdict
    return [grouped[name].compute() for name in ordered]


def report(rows: Sequence[Row]) -> dict[str, object]:
    """Rapport complet, serialisable en JSON."""
    per_instance = verdicts(rows)
    return {
        "rows": [
            {
                "instance": row.instance,
                "config": row.config,
                "verdict": row.verdict,
                "source": row.source,
                "fingerprints": row.fingerprints,
                "readable_reps": row.readable_reps,
                "partial_reps": row.partial_reps,
                "blind_reps": row.blind_reps,
                "total_reps": row.total_reps,
                "defined_counts": row.defined_counts,
                "model_total": row.model_total,
                "model_extends": row.model_extends,
                "median_ms": round(row.median_ms, 3),
            }
            for row in rows
        ],
        "verdicts": [
            {
                "instance": entry.instance,
                "source": entry.source,
                "status": entry.status,
                "distinct_verdicts": entry.distinct_verdicts,
                "readable_configs": entry.readable_configs,
                "partial_configs": entry.partial_configs,
                "unreadable_configs": entry.unreadable_configs,
                "defined_ranges": entry.defined_ranges,
                "no_model_configs": entry.no_model_configs,
                "distinct_readable_models": entry.distinct_readable_models,
                "readable_models_agree": entry.readable_models_agree,
                "all_models_valid": entry.all_models_valid,
                "verdicts": entry.verdicts,
                "fingerprints": entry.fingerprints,
                "median_ms": entry.median_ms,
                "model_extends": entry.model_extends,
            }
            for entry in per_instance
        ],
        "summary": {
            "instances": len(per_instance),
            "verdict_preserved": sum(1 for e in per_instance if e.status == "VERDICT_PRESERVE"),
            "verdict_diverged": sum(1 for e in per_instance if e.status == "DIVERGENCE"),
            "instances_with_disagreeing_models": sum(
                1 for e in per_instance if not e.readable_models_agree
            ),
            "instances_with_blind_configs": sum(
                1 for e in per_instance if e.unreadable_configs
            ),
            "models_all_valid": all(e.all_models_valid for e in per_instance),
        },
    }


def render(report_data: dict[str, object]) -> str:
    """Rendu texte du rapport (une ligne par instance, une ligne par configuration)."""
    lines: list[str] = []
    for entry in report_data["verdicts"]:  # type: ignore[index]
        lines.append(f"    source : {entry['source']}")
        lines.append(
            f"{entry['instance']} : {entry['status']} "
            f"(verdicts distincts : {entry['distinct_verdicts']}, "
            f"modeles lisibles distincts : {entry['distinct_readable_models']}, "
            f"accord : {entry['readable_models_agree']})"
        )
        for config, verdict in entry["verdicts"].items():
            median = entry["median_ms"].get(config)
            extends = entry["model_extends"].get(config)
            fingerprints = entry["fingerprints"].get(config, [])
            defined = entry["defined_ranges"].get(config, [0, 0])
            lines.append(
                f"    {config:<45s} {verdict:<12s} mediane {median} ms | "
                f"se prolonge : {extends} | modeles distincts : {len(fingerprints)} | "
                f"variables definies : {defined[0]}-{defined[1]}"
            )
        lines.append(
            f"    lisibles : {', '.join(entry['readable_configs']) or '(aucune)'} | "
            f"partielles : {', '.join(entry['partial_configs']) or '(aucune)'} | "
            f"aveugles : {', '.join(entry['unreadable_configs']) or '(aucune)'} | "
            f"sans modele : {', '.join(entry['no_model_configs']) or '(aucune)'}"
        )
    summary = report_data["summary"]  # type: ignore[index]
    lines.append(
        f"instances : {summary['instances']} | verdicts preserves : "
        f"{summary['verdict_preserved']} | divergences : {summary['verdict_diverged']} | "
        f"instances a modeles lisibles en desaccord : "
        f"{summary['instances_with_disagreeing_models']} | "
        f"instances a configuration aveugle : "
        f"{summary['instances_with_blind_configs']} | "
        f"tous les modeles valides : {summary['models_all_valid']}"
    )
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    """Point d'entree en ligne de commande."""
    parser = argparse.ArgumentParser(
        description="Sonde d'invariance des chaines de tactiques Z3 (verdict vs modele)."
    )
    parser.add_argument(
        "--reps", type=int, default=5, help="repetitions mesurees par configuration"
    )
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args(argv)

    rows = measure_all(repetitions=args.reps)
    report_data = report(rows)
    if args.json:
        print(json.dumps(report_data, indent=2, ensure_ascii=False))
    else:
        print(render(report_data))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
