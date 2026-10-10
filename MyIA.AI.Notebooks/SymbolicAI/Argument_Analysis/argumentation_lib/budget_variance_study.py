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
from typing import Any, Dict, List, Optional, Set


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
# Validation de contenu — port verbatim de la cellule 23 du carnet 08b
# (issue #18395). Ne pas diverger : la demonstration et la mesure doivent
# appliquer les memes seuils.
# ---------------------------------------------------------------------------

STATE_KEYS_BLACKLIST: Set[str] = {
    "analysis_state", "arguments", "identified_arguments", "identified_fallacies",
    "belief_sets", "query_log", "answers", "raw_text", "final_conclusion",
    "shared_state", "task_context", "metadata", "state",
}

MIN_ARGUMENT_WORDS: int = 4
MIN_ARGUMENT_TEXT_OVERLAP: int = 12

OBSOLETE_MODEL_SUBSTITUTIONS = {
    "gpt-5-mini": "gpt-4o-mini",
    "gpt-5": "gpt-4o",
    "gpt-5-nano": "gpt-4o-mini",
}


def _resolve_chat_model_id() -> str:
    _load_env()
    configured = os.getenv("OPENAI_CHAT_MODEL_ID", "<unset>")
    return OBSOLETE_MODEL_SUBSTITUTIONS.get(configured, configured)


def _text_overlap(text: str, candidate: str) -> int:
    if not text or not candidate:
        return 0
    a = re.sub(r"\s+", " ", text.lower())
    b = re.sub(r"\s+", " ", candidate.lower())
    n = len(b)
    upper = min(n, 80)
    for size in range(upper, MIN_ARGUMENT_TEXT_OVERLAP - 1, -1):
        for i in range(0, n - size + 1):
            sub = b[i:i + size]
            if sub in a:
                return size
    return 0


def _argument_has_substance(arg_desc: str, raw_text: str) -> bool:
    desc = str(arg_desc).strip()
    if not desc:
        return False
    if desc.lower() in STATE_KEYS_BLACKLIST:
        return False
    if len(desc.split()) < MIN_ARGUMENT_WORDS:
        return False
    if _text_overlap(raw_text or "", desc) < MIN_ARGUMENT_TEXT_OVERLAP:
        return False
    return True


def _fallacy_has_substance(f_data: Dict[str, Any]) -> bool:
    if not isinstance(f_data, dict):
        return False
    ftype = str(f_data.get("type", "")).strip()
    if not ftype or ftype.lower() in ("unknown", "type inconnu", ""):
        return False
    justification = str(f_data.get("justification", "")).strip()
    if not justification or justification.lower() == "justification manquante":
        return False
    if len(justification) < 10:
        return False
    target = f_data.get("target_argument_id")
    if target is None or target == "":
        return False
    return True


def compute_verdict_metrics(state: Any) -> Dict[str, Any]:
    """Mesure la forme du verdict d'un etat issu d'un run agentique.

    Port de ``generate_validated_analysis_report`` (cellule 23 du carnet
    08b) limite aux champs utiles a l'etude : comptes substantifs, statut
    de validation, score, raison d'echec.
    """
    raw_text = getattr(state, "raw_text", None) or ""

    substantive_args = 0
    total_args = 0
    if hasattr(state, "identified_arguments"):
        for _arg_id, arg_desc in state.identified_arguments.items():
            total_args += 1
            if _argument_has_substance(arg_desc, raw_text):
                substantive_args += 1

    substantive_fallacies = 0
    total_fallacies = 0
    if hasattr(state, "identified_fallacies"):
        for _f_id, f_data in state.identified_fallacies.items():
            total_fallacies += 1
            if _fallacy_has_substance(f_data):
                substantive_fallacies += 1

    belief_sets = len(getattr(state, "belief_sets", {}) or {})

    meaningful_queries = 0
    total_queries = 0
    if hasattr(state, "query_log"):
        for qlog in state.query_log:
            total_queries += 1
            raw_result = qlog.get("raw_result", "") if isinstance(qlog, dict) else ""
            if "ACCEPTED" in str(raw_result) or "REJECTED" in str(raw_result):
                meaningful_queries += 1

    has_conclusion = bool(getattr(state, "final_conclusion", None))

    checks: List[str] = []
    failed_reasons: List[str] = []
    if substantive_args:
        checks.append("ARGUMENTS_IDENTIFIED")
    elif total_args > 0:
        failed_reasons.append("ARGUMENTS_FORM_ONLY")
    else:
        failed_reasons.append("ARGUMENTS_NONE")
    if substantive_fallacies:
        checks.append("FALLACIES_ANALYZED")
    elif total_fallacies > 0:
        failed_reasons.append("FALLACIES_FORM_ONLY")
    elif hasattr(state, "answers") and any(
        "sophisme" in str(v).lower() for v in state.answers.values()
    ):
        checks.append("FALLACY_ANALYSIS_ATTEMPTED")
    else:
        failed_reasons.append("FALLACIES_NONE")
    if belief_sets > 0:
        checks.append("BELIEF_SET_CREATED")
    else:
        failed_reasons.append("BELIEF_SET_NONE")
    if total_queries > 0:
        checks.append("QUERIES_SUBMITTED")
    else:
        failed_reasons.append("QUERIES_NONE")
    if meaningful_queries > 0:
        checks.append("QUERIES_MEANINGFUL")
    else:
        failed_reasons.append("QUERIES_NOT_MEANINGFUL")
    if has_conclusion:
        checks.append("CONCLUSION_GENERATED")
    else:
        failed_reasons.append("CONCLUSION_NONE")

    max_checks = 7
    confidence = round(len(checks) / max_checks, 2)

    if any(
        fr in ("ARGUMENTS_FORM_ONLY", "FALLACIES_FORM_ONLY") for fr in failed_reasons
    ):
        status = "INVALIDATED_FORM"
    elif confidence >= 0.8:
        status = "COMPLETE_VALIDATED"
    elif confidence >= 0.5:
        status = "PARTIAL_VALIDATED"
    elif confidence >= 0.3:
        status = "MINIMAL"
    else:
        status = "INCOMPLETE"

    return {
        "total_arguments": total_args,
        "substantive_arguments": substantive_args,
        "total_fallacies": total_fallacies,
        "substantive_fallacies": substantive_fallacies,
        "belief_sets": belief_sets,
        "total_queries": total_queries,
        "meaningful_queries": meaningful_queries,
        "has_conclusion": has_conclusion,
        "validation_status": status,
        "confidence_score": confidence,
        "failed_reason": failed_reasons[0] if failed_reasons else None,
    }


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
    # Comportement herite : plafond partage max_turns // 2 (10/10 sur 20).
    "baseline": {},
    # Budget par phase (#18785) : phase informelle etendue a 15 tours,
    # phase formelle maintenue a 10.
    "proposal": {"max_turns": 20, "max_informal_turns": 15, "max_formal_turns": 10},
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

    study: Dict[str, Any] = {
        "issue": 18776,
        "started_at": datetime.now().isoformat(),
        "model_id": _resolve_chat_model_id(),
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
