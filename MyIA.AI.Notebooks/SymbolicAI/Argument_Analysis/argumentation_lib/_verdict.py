"""Validation de contenu et metriques de verdict d'un etat d'analyse (#18776).

Source unique des seuils de substance, portes verbatim depuis la cellule de
validation du carnet ``Argumentation-08b-Executor-Python.ipynb`` (validation
de contenu, issue #18395) — version DURCIE de cette cellule : cle d'etat en
guise d'argument (check 1b), cible de sophisme fantome (check 2b),
normalisation canonique des identifiants (``argument_3`` / ``arg_3`` /
``arg_N3``) et statut ``FAILED_FORMAL`` quand la couche formelle ne produit
aucun verdict. La version anterieure, plus permissive, vivait dans
``budget_variance_study.py`` : elle laissait passer une cible non vide mais
inexistante, exactement le defaut que le durcissement de la cellule corrige.
Trois consommateurs, une definition :

- ``budget_variance_study`` : la mesure de variance de l'issue #18776 ;
- ``_runner`` : la porte de la reprise ciblee (compter les arguments et
  sophismes substantifs, detecter les entrees empoisonnees, reprendre la
  phase deficitaire) ;
- le carnet 08b : la demonstration.

Ne pas diverger : si un seuil change ici, la mesure et la demonstration
doivent le constater ensemble. Ce module ne lit ni env ni reseau (le
runner est zero-env par contrat, scelle par ``tests/test_runner.py``).
"""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Set

# ---------------------------------------------------------------------------
# Constantes de validation de contenu — port verbatim (cellule du carnet)
# ---------------------------------------------------------------------------

STATE_KEYS_BLACKLIST: Set[str] = {
    "analysis_state", "arguments", "identified_arguments", "identified_fallacies",
    "belief_sets", "query_log", "answers", "raw_text", "final_conclusion",
    "shared_state", "task_context", "metadata", "state",
}

MIN_ARGUMENT_WORDS: int = 4

# Longueur minimale de la sous-chaine commune (en caracteres) entre la
# description de l'argument et le texte source.
MIN_ARGUMENT_TEXT_OVERLAP: int = 12


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


def argument_has_substance(arg_desc: str, raw_text: str) -> bool:
    """Un argument substantif est une formulation reprise du texte source.

    Port verbatim de la cellule du carnet : ni cle d'etat, ni etiquette trop
    courte, ni texte sans recouvrement avec la source.
    """
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


def is_state_key_argument(arg_id: Any, arg_desc: Any) -> bool:
    """L'argument est-il en realite une cle de l'etat interne de l'agent ?

    Port verbatim (#18395, check 1b) : le check principal ne rougit que si
    AUCUN argument n'est substantiel, donc une cle d'etat glissee parmi des
    arguments reels passait inapercue. Une cle d'etat n'est jamais un
    argument, meme accompagnee de vrais.
    """
    for candidate in (arg_desc, arg_id):
        if str(candidate).strip().lower() in STATE_KEYS_BLACKLIST:
            return True
    return False


def normalize_argument_id(raw: Any) -> str:
    """Ramene les conventions d'identifiant d'argument a une forme unique.

    Port verbatim (#18395) : trois familles coexistent pour le meme objet —
    ``argument_3``, ``arg_3``, ``arg_N3``. Un sophisme qui cite l'une
    pendant que l'etat nomme l'autre est un lien perdu, pas un lien faux :
    on les compare sous une forme canonique (``arg_<n>``).
    """
    s = str(raw).strip().lower()
    m = re.fullmatch(r"arg(?:ument)?_n?(\d+)", s)
    return f"arg_{m.group(1)}" if m else s


def fallacy_has_substance(
    f_data: Dict[str, Any], known_arg_ids: Optional[Set[str]] = None
) -> bool:
    """Un sophisme substantif porte un type, une justification et une cible.

    Port verbatim de la cellule du carnet, version durcie : quand
    ``known_arg_ids`` est fourni, la cible doit designer un argument
    reellement present dans l'etat (comparaison directe puis canonique).
    ``known_arg_ids=None`` conserve le comportement historique (cible non
    vide) pour les appelants qui n'ont pas l'etat sous la main.
    """
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
    if known_arg_ids is not None:
        if (
            str(target).strip() not in known_arg_ids
            and normalize_argument_id(target) not in known_arg_ids
        ):
            return False
    return True


# ---------------------------------------------------------------------------
# Lectures d'etat — predicats uniques du runner et de la mesure
# ---------------------------------------------------------------------------

def _known_arg_ids(state: Any) -> Set[str]:
    """Identifiants d'arguments reellement presents, formes directe et canonique."""
    known: Set[str] = set()
    for arg_id in (getattr(state, "identified_arguments", None) or {}):
        known.add(str(arg_id).strip())
        known.add(normalize_argument_id(arg_id))
    return known


def count_substantive_arguments(state: Any) -> int:
    """Nombre d'arguments substantifs d'un etat."""
    raw_text = getattr(state, "raw_text", None) or ""
    return sum(
        1
        for _arg_id, arg_desc in (
            getattr(state, "identified_arguments", None) or {}
        ).items()
        if argument_has_substance(arg_desc, raw_text)
    )


def count_substantive_fallacies(state: Any) -> int:
    """Nombre de sophismes substantifs d'un etat (cible existante requise)."""
    known = _known_arg_ids(state)
    return sum(
        1
        for _f_id, f_data in (
            getattr(state, "identified_fallacies", None) or {}
        ).items()
        if fallacy_has_substance(f_data, known)
    )


def state_key_argument_ids(state: Any) -> List[str]:
    """Identifiants des arguments qui sont des cles de l'etat interne (#18395).

    Ce sont des entrees empoisonnees pour le verdict : le check 1b du carnet
    invalide la forme des qu'une seule existe, quelle que soit la qualite du
    reste. La reprise ciblee les retire avant de remplir.
    """
    return [
        arg_id
        for arg_id, arg_desc in (
            getattr(state, "identified_arguments", None) or {}
        ).items()
        if is_state_key_argument(arg_id, arg_desc)
    ]


def phantom_target_fallacy_ids(state: Any) -> List[str]:
    """Identifiants des sophismes dont la cible n'existe pas dans l'etat.

    Un sophisme dont la cible n'existe pas n'est pas un lien faible : c'est
    un lien absent (#18395, check 2b). La reprise ciblee les retire avant de
    remplir.
    """
    known = _known_arg_ids(state)
    return [
        f_id
        for f_id, f_data in (
            getattr(state, "identified_fallacies", None) or {}
        ).items()
        if isinstance(f_data, dict)
        and f_data.get("target_argument_id") not in (None, "")
        and str(f_data.get("target_argument_id")).strip() not in known
        and normalize_argument_id(f_data.get("target_argument_id")) not in known
    ]


def compute_verdict_metrics(state: Any) -> Dict[str, Any]:
    """Mesure la forme du verdict d'un etat issu d'un run agentique.

    Port de ``generate_validated_analysis_report`` (cellule de validation du
    carnet 08b, version durcie #18395) limite aux champs utiles a l'etude :
    comptes substantifs, statut de validation, score, raison d'echec.
    """
    raw_text = getattr(state, "raw_text", None) or ""
    known = _known_arg_ids(state)

    substantive_args = 0
    total_args = 0
    state_key_count = 0
    if hasattr(state, "identified_arguments"):
        for arg_id, arg_desc in state.identified_arguments.items():
            total_args += 1
            if argument_has_substance(arg_desc, raw_text):
                substantive_args += 1
            if is_state_key_argument(arg_id, arg_desc):
                state_key_count += 1

    substantive_fallacies = 0
    total_fallacies = 0
    phantom_target_count = 0
    if hasattr(state, "identified_fallacies"):
        for _f_id, f_data in state.identified_fallacies.items():
            total_fallacies += 1
            if fallacy_has_substance(f_data, known):
                substantive_fallacies += 1
            else:
                target = (
                    f_data.get("target_argument_id")
                    if isinstance(f_data, dict)
                    else None
                )
                if (
                    target not in (None, "")
                    and str(target).strip() not in known
                    and normalize_argument_id(target) not in known
                ):
                    phantom_target_count += 1

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

    # Check 1 : arguments REELS (defaut : "analysis_state" / "arguments")
    if substantive_args:
        checks.append("ARGUMENTS_IDENTIFIED")
    elif total_args > 0:
        failed_reasons.append("ARGUMENTS_FORM_ONLY")
    else:
        failed_reasons.append("ARGUMENTS_NONE")

    # Check 1b : aucune cle d'etat interne en guise d'argument (#18395).
    if state_key_count > 0:
        failed_reasons.append("ARGUMENTS_STATE_KEY")

    # Check 2 : sophismes REELS (defaut : "Type Inconnu" passait)
    fallacies_hors_cible_fantome = total_fallacies - phantom_target_count
    if substantive_fallacies:
        checks.append("FALLACIES_ANALYZED")
    elif fallacies_hors_cible_fantome > 0:
        failed_reasons.append("FALLACIES_FORM_ONLY")
    elif total_fallacies == 0:
        if hasattr(state, "answers") and any(
            "sophisme" in str(v).lower() for v in state.answers.values()
        ):
            checks.append("FALLACY_ANALYSIS_ATTEMPTED")
        else:
            failed_reasons.append("FALLACIES_NONE")

    # Check 2b : cible des sophismes (#18395, second symptome mesure).
    if phantom_target_count > 0:
        failed_reasons.append("FALLACY_TARGET_UNKNOWN")

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
        fr in (
            "ARGUMENTS_FORM_ONLY",
            "ARGUMENTS_STATE_KEY",
            "FALLACIES_FORM_ONLY",
            "FALLACY_TARGET_UNKNOWN",
        )
        for fr in failed_reasons
    ):
        status = "INVALIDATED_FORM"
    elif any(fr in ("QUERIES_NONE", "QUERIES_NOT_MEANINGFUL") for fr in failed_reasons):
        # La couche formelle n'a produit aucun verdict : le statut le dit
        # (port verbatim du carnet : avant ce correctif, ce cas traversait
        # les seuils de confiance et un run sans une seule reponse du moteur
        # sortait COMPLETE_VALIDATED).
        status = "FAILED_FORMAL"
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
        "state_key_arguments": state_key_count,
        "total_fallacies": total_fallacies,
        "substantive_fallacies": substantive_fallacies,
        "phantom_target_fallacies": phantom_target_count,
        "belief_sets": belief_sets,
        "total_queries": total_queries,
        "meaningful_queries": meaningful_queries,
        "has_conclusion": has_conclusion,
        "validation_status": status,
        "confidence_score": confidence,
        "failed_reason": failed_reasons[0] if failed_reasons else None,
    }
