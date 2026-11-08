"""Etude de variance du budget de tours par phase (#18776).

Mesure la stabilite de la forme du verdict de l'``AnalysisRunner`` sur des
executions REELLES (appels LLM effectifs, aucun mock) :

- configuration heritee : plafond partage ``max_turns // 2`` par phase
  (comportement par defaut, celui que decrit l'issue #18776) ;
- budget par phase : ``max_informal_turns`` / ``max_formal_turns``
  distincts (implementation #18785, deja sur ``main``).

Pour chaque execution on releve : le nombre d'arguments substantifs, le
nombre de sophismes substantifs, la forme du verdict (statut + raison
d'echec + score de confiance), et le cout (tours par phase, duree).

Les criteres de substance et le statut de validation sont portes
verbatim depuis la cellule 23 du carnet
``Argumentation-08b-Executor-Python.ipynb`` (validation de contenu,
issue #18395) : la mesure utilise exactement les memes seuils que la
demonstration.

Graines : les indices ``--seeds`` numerotent des executions independantes.
Le parametre ``seed`` de l'API OpenAI n'est PAS injecte : le phenomene
mesure est la variance naturelle run-to-run de l'echantillonnage LLM,
conformement au protocole de l'issue (mesure originelle : « 5 runs »).

Usage (depuis ``Argument_Analysis/``, cle dans ``.env``) ::

    python -m argumentation_lib.budget_variance_study \
        --seeds 0,1,7,42,99 --out etude_budget.json
"""

from __future__ import annotations

import argparse
import functools
import json
import os
import re
import statistics
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional


@functools.lru_cache(maxsize=1)
def _load_env() -> bool:
    """Charge ``Argument_Analysis/.env`` (cle LLM) une fois, avant toute lecture.

    Sans cet appel explicite, ``_resolve_chat_model_id()`` s'execute AVANT le
    ``load_dotenv`` de ``_build_runner`` : le premier run et l'en-tete du
    rapport enregistraient ``<unset>`` alors que les runs suivants portaient
    le vrai modele -- un champ de provenance faux au moment ou il est ecrit.
    """
    from dotenv import load_dotenv

    load_dotenv(Path(__file__).resolve().parent.parent / ".env", override=True)
    return True

# ---------------------------------------------------------------------------
# Texte d'analyse — extrait verbatim de la cellule 12 du carnet 08b
# (TEXTE_EXEMPLE_BATCH). La mesure doit porter sur le meme texte que la
# demonstration pour que les deux soient comparables.
# ---------------------------------------------------------------------------

_TEXTE_EXEMPLE_CELL_PATH = (
    Path(__file__).resolve().parent.parent / "Argumentation-08b-Executor-Python.ipynb"
)


def _load_batch_text() -> str:
    """Relit TEXTE_EXEMPLE_BATCH depuis le carnet (source unique)."""
    nb = json.loads(_TEXTE_EXEMPLE_CELL_PATH.read_text(encoding="utf-8"))
    for cell in nb["cells"]:
        src = "".join(cell.get("source", []))
        m = re.search(r'TEXTE_EXEMPLE_BATCH = """(.*?)"""', src, re.DOTALL)
        if m:
            return m.group(1)
    raise RuntimeError(
        "TEXTE_EXEMPLE_BATCH introuvable dans Argumentation-08b-Executor-Python.ipynb"
    )


# ---------------------------------------------------------------------------
# Validation de contenu — les seuils vivent dans _verdict.py (source unique,
# #18776 tranche reprise ciblee) : la mesure, la porte de reprise du runner
# et le carnet doivent appliquer les memes seuils. Re-exports pour les
# consommateurs historiques (tests, carnets) qui importent depuis ici.
# ---------------------------------------------------------------------------

from argumentation_lib._verdict import (  # noqa: F401
    MIN_ARGUMENT_TEXT_OVERLAP,
    MIN_ARGUMENT_WORDS,
    STATE_KEYS_BLACKLIST,
    argument_has_substance,
    compute_verdict_metrics,
    count_substantive_arguments,
    count_substantive_fallacies,
    fallacy_has_substance,
)

# Cibles = generation courante verifiee (docs/genai/model-mapping-openai.md) :
# famille mini/nano -> gpt-5.6-luna, principal -> gpt-5.6-sol. Les cibles
# d'origine (gpt-4o-mini, gpt-4o) sont elles-memes d'une generation
# remplacee -- substituer l'une par l'autre deplacait l'echec (#20135).
# Extension #22783 : la famille 4o entre dans la table (gpt-4o-mini ->
# gpt-5.6-luna, gpt-4o -> gpt-5.6-sol, memes cibles que le mapping) -- sans
# elle, un .env encore sur gpt-4o-mini passait le substitut a travers et la
# serie executait un modele obsolete en le nommant dans sa provenance.
# Port verbatim de la cellule de validation du carnet 08b : ne pas diverger.
OBSOLETE_MODEL_SUBSTITUTIONS = {
    "gpt-5-mini": "gpt-5.6-luna",
    "gpt-5": "gpt-5.6-sol",
    "gpt-5-nano": "gpt-5.6-luna",
    "gpt-4o-mini": "gpt-5.6-luna",
    "gpt-4o": "gpt-5.6-sol",
}


def _resolve_chat_model_id() -> str:
    _load_env()
    # Priorite a la cible REELLEMENT executee (#22783) : la cellule du kernel
    # pose ACTIVE_CHAT_MODEL_ID apres avoir configure le service (vLLM local
    # ou repli). Sans cette lecture, OPENAI_CHAT_MODEL_ID pourrait nommer un
    # modele que le run n'a pas utilise -- exactement la divergence que le
    # rapport de provenance existe pour empecher.
    active = os.getenv("ACTIVE_CHAT_MODEL_ID")
    if active:
        return active
    configured = os.getenv("OPENAI_CHAT_MODEL_ID")
    if not configured:
        raise RuntimeError(
            "OPENAI_CHAT_MODEL_ID absent : aucun modele n'est configure. "
            "Renseigner la variable (voir Argument_Analysis/.env.example) "
            "plutot que de laisser la serie appeler un identifiant par defaut."
        )
    return OBSOLETE_MODEL_SUBSTITUTIONS.get(configured.strip(), configured)


def _text_overlap(text: str, candidate: str) -> int:
    # Delegue a la source unique (_verdict) ; conserve pour les imports
    # historiques de ce module.
    from argumentation_lib._verdict import _text_overlap as _impl

    return _impl(text, candidate)


def _argument_has_substance(arg_desc: str, raw_text: str) -> bool:
    from argumentation_lib._verdict import argument_has_substance as _impl

    return _impl(arg_desc, raw_text)


def _fallacy_has_substance(f_data: Dict[str, Any]) -> bool:
    from argumentation_lib._verdict import fallacy_has_substance as _impl

    return _impl(f_data)


# ---------------------------------------------------------------------------
# Execution d'un run reel
# ---------------------------------------------------------------------------


def _build_runner(runner_kwargs: Dict[str, Any]):
    """Construit kernel + service + runner exactement comme le carnet 08b."""
    _load_env()

    from semantic_kernel import Kernel
    from semantic_kernel.connectors.ai.open_ai import (
        OpenAIChatCompletion,
        AzureChatCompletion,
    )

    from argumentation_lib import UnifiedAnalysisState, get_analysis_runner

    api_key = os.getenv("OPENAI_API_KEY")
    model_id = os.getenv("OPENAI_CHAT_MODEL_ID")
    endpoint = os.getenv("OPENAI_ENDPOINT")

    kernel = Kernel()
    if endpoint:
        kernel.add_service(AzureChatCompletion(
            service_id="global_llm_service",
            deployment_name=model_id,
            endpoint=endpoint,
            api_key=api_key,
        ))
    else:
        kernel.add_service(OpenAIChatCompletion(
            service_id="global_llm_service",
            ai_model_id=model_id,
            api_key=api_key,
            org_id=os.getenv("OPENAI_ORG_ID"),
        ))

    AnalysisRunner = get_analysis_runner()
    state = UnifiedAnalysisState(_load_batch_text())
    runner = AnalysisRunner(kernel, "global_llm_service", state, **runner_kwargs)
    return runner, state


def run_once(config_name: str, runner_kwargs: Dict[str, Any], seed: int) -> Dict[str, Any]:
    """Une execution complete du pipeline, mesuree."""
    record: Dict[str, Any] = {
        "config": config_name,
        "seed": seed,
        "runner_kwargs": runner_kwargs,
        "resolved_model_id": _resolve_chat_model_id(),
        "started_at": datetime.now().isoformat(),
    }
    try:
        runner, state = _build_runner(runner_kwargs)
        t0 = time.monotonic()
        result = runner.run_sync()
        duration = time.monotonic() - t0
        record["duration_s"] = round(duration, 1)
        record["phases"] = [
            {"name": p.get("name"), "turns": p.get("turns"), "status": p.get("status")}
            for p in result.get("phases", [])
        ]
        record["total_turns"] = sum(
            p.get("turns") or 0 for p in result.get("phases", [])
        )
        record.update(compute_verdict_metrics(state))
    except Exception as exc:  # reseau, quota, wiring : trace et continue
        record["error"] = f"{type(exc).__name__}: {exc}"
    return record


# ---------------------------------------------------------------------------
# Agrégation
# ---------------------------------------------------------------------------

METRIC_KEYS = [
    "substantive_arguments",
    "substantive_fallacies",
    "total_turns",
    "duration_s",
]


def summarize(runs: List[Dict[str, Any]]) -> Dict[str, Any]:
    ok = [r for r in runs if "error" not in r]
    summary: Dict[str, Any] = {
        "runs_total": len(runs),
        "runs_ok": len(ok),
        "runs_error": len(runs) - len(ok),
    }
    if not ok:
        return summary
    forms = [f"{r['validation_status']}" for r in ok]
    summary["verdict_forms_unique"] = sorted(set(forms))
    summary["verdict_forms_distribution"] = {
        f: forms.count(f) for f in sorted(set(forms))
    }
    failed = [r["failed_reason"] for r in ok if r["failed_reason"]]
    summary["failed_reasons_distribution"] = {
        f: failed.count(f) for f in sorted(set(failed))
    } if failed else {}
    for key in METRIC_KEYS:
        values = [r[key] for r in ok if key in r]
        if values:
            summary[key] = {
                "min": min(values),
                "max": max(values),
                "mean": round(statistics.mean(values), 2),
                "stdev": round(statistics.pstdev(values), 2) if len(values) > 1 else 0.0,
            }
    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

CONFIGS: Dict[str, Dict[str, Any]] = {
    # Comportement herite (= main) : chaque phase plafonnee a 5 tours par
    # DefaultTerminationStrategy (maximum_iterations=5, defaut SK). Jusqu'a
    # la tranche reprise ciblee de #18776 ce plafond etait IMPLICITE — les
    # budgets #18785 restaient inertes — et la baseline se declarait
    # ``max_turns // 2`` (10/10) alors qu'elle s'arretait a 5. Reproduire
    # main sur le runner a strategie explicite, c'est poser 5/5 : meme
    # mecanique, meme total (5+5+3 = 13 tours, mesure campagne3_baseline).
    "baseline": {"max_turns": 10, "max_informal_turns": 5, "max_formal_turns": 5},
    # Budget par phase (#18785) : phase informelle etendue a 15 tours,
    # phase formelle maintenue a 10. Depuis la tranche reprise ciblee,
    # ces budgets MORDENT (strategie de terminaison explicite).
    "proposal": {"max_turns": 20, "max_informal_turns": 15, "max_formal_turns": 10},
    # Reprise ciblee de la phase deficitaire (branche « ou » de l'issue) :
    # budgets 10/10 qui mordent, puis reprise focused arguments/sophismes
    # tant que l'un des deux livrables reste sous son seuil.
    "resumption": {
        "max_turns": 20,
        "max_informal_turns": 10,
        "max_formal_turns": 10,
        "targeted_resumption": True,
    },
}


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--configs",
        default="baseline,proposal",
        help="configurations separees par des virgules (cles de CONFIGS)",
    )
    parser.add_argument(
        "--seeds",
        default="0,1,7,42,99",
        help="indices d'execution separes par des virgules",
    )
    parser.add_argument(
        "--out",
        default="etude_budget_tours.json",
        help="chemin du rapport JSON (ecrit incrementalement)",
    )
    parser.add_argument(
        "--smoke",
        action="store_true",
        help="run minimal (max_turns=2) pour verifier le cablage LLM",
    )
    args = parser.parse_args(argv)

    if args.smoke:
        record = run_once("smoke", {"max_turns": 2}, 0)
        print(json.dumps(record, indent=2, ensure_ascii=False, default=str))
        return 0 if "error" not in record else 1

    config_names = [c.strip() for c in args.configs.split(",") if c.strip()]
    seeds = [int(s.strip()) for s in args.seeds.split(",") if s.strip()]
    out_path = Path(args.out)

    def _sk_version() -> str:
        try:
            import semantic_kernel

            return getattr(semantic_kernel, "__version__", "unknown")
        except Exception:
            return "absent"

    study: Dict[str, Any] = {
        "issue": 18776,
        "started_at": datetime.now().isoformat(),
        "model_id": _resolve_chat_model_id(),
        "semantic_kernel_version": _sk_version(),
        "configs": {},
    }

    for config_name in config_names:
        runner_kwargs = CONFIGS[config_name]
        runs: List[Dict[str, Any]] = []
        for seed in seeds:
            print(f"[{config_name}] seed={seed} en cours...", flush=True)
            record = run_once(config_name, runner_kwargs, seed)
            runs.append(record)
            status = record.get("validation_status", record.get("error", "?"))
            print(
                f"[{config_name}] seed={seed} -> {status} "
                f"(args_subst={record.get('substantive_arguments')}, "
                f"soph_subst={record.get('substantive_fallacies')}, "
                f"tours={record.get('total_turns')}, "
                f"{record.get('duration_s', '?')}s)",
                flush=True,
            )
            study["configs"][config_name] = {
                "runner_kwargs": runner_kwargs,
                "runs": runs,
                "summary": summarize(runs),
            }
            out_path.write_text(
                json.dumps(study, indent=2, ensure_ascii=False, default=str),
                encoding="utf-8",
            )

    study["finished_at"] = datetime.now().isoformat()
    out_path.write_text(
        json.dumps(study, indent=2, ensure_ascii=False, default=str),
        encoding="utf-8",
    )
    print(f"Rapport ecrit: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
