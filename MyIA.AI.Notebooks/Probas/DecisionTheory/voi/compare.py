"""Comparateur cross-engine runtime — tranche 3/3 (issue #13569).

Execute les deux adaptateurs (PyMC + Infer.NET) sur le meme
``VoiContract`` et ecrit un tableau d'accord/desaccord. Toute divergence
entre les moteurs au-dela de la tolerance fixee est rapportee, jamais
lissée. La sortie est serialisable en JSON.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

from .contract import VoiContract, VoiResult, animat_decision_summary_contract
from . import adapter_pymc
from . import adapter_infernet


@dataclass(frozen=True)
class CompareReport:
    """Rapport de comparaison cross-engine.

    Attributes
    ----------
    contract : VoiContract
        Le contrat source.
    analytical : VoiResult
        Reference analytique NumPy.
    pymc : VoiResult or None
        Sortie PyMC ``None`` si l'adaptateur n'a pas pu tourner.
    infernet : VoiResult or None
        Sortie Infer.NET ``None`` si l'adaptateur n'a pas pu tourner.
    tolerance : float
        Tolerance absolue sur EVPI/EVSI/eu_no_info.
    diffs : list of dict
        Liste des divergences par grandeur, avec valeur analytique et
        difference observee.
    agreement : bool
        ``True`` si tous les moteurs disponibles sont en accord a tolerance
        pres sur toutes les grandeurs.

    Notes
    -----
    Une divergence n'est **PAS** lissee : on la rapporte avec les valeurs
    exactes de chaque moteur, jamais avec une moyenne cachee.
    """

    contract: VoiContract
    analytical: VoiResult
    pymc: Optional[VoiResult]
    infernet: Optional[VoiResult]
    tolerance: float
    diffs: List[Dict[str, Any]] = field(default_factory=list)
    agreement: bool = True

    def to_dict(self) -> Dict[str, Any]:
        return {
            "contract": self.contract.to_dict(),
            "analytical": self.analytical.to_dict(),
            "pymc": self.pymc.to_dict() if self.pymc else None,
            "infernet": self.infernet.to_dict() if self.infernet else None,
            "tolerance": self.tolerance,
            "diffs": self.diffs,
            "agreement": self.agreement,
        }


# Grandeurs howardiennes comparees entre moteurs.
_GRANDEURS = ("eu_no_info", "evpi", "evsi", "evsi_net")


def compare(
    contract: VoiContract,
    *,
    include_pymc: bool = True,
    include_infernet: bool = True,
    pymc_draws: int = 2000,
    pymc_tune: int = 1000,
    pymc_chains: int = 2,
    pymc_seed: int = 0,
    infernet_timeout_s: int = 120,
    infernet_bin: Optional[str] = None,
    tolerance: float = 1e-2,
) -> CompareReport:
    """Execute les moteurs selectionnes et rapporte les divergences.

    Parameters
    ----------
    contract : VoiContract
        Probleme de decision source.
    include_pymc : bool
        Tente d'executer l'adaptateur PyMC.
    include_infernet : bool
        Tente d'executer l'adaptateur Infer.NET.
    pymc_*, infernet_*
        Hyperparametres adaptateurs.
    tolerance : float
        Tolerance absolue sur les grandeurs howardiennes.

    Returns
    -------
    CompareReport
        Rapport complet avec reference analytique, sorties brutes par
        moteur, et liste des divergences.
    """
    analytical = animat_decision_summary_contract(contract)

    pymc_result: Optional[VoiResult] = None
    pymc_error: Optional[str] = None
    if include_pymc:
        try:
            pymc_result = adapter_pymc.run_pymc(
                contract,
                draws=pymc_draws,
                tune=pymc_tune,
                chains=pymc_chains,
                seed=pymc_seed,
            )
        except RuntimeError as e:
            pymc_error = str(e)

    infernet_result: Optional[VoiResult] = None
    infernet_error: Optional[str] = None
    if include_infernet:
        try:
            infernet_result = adapter_infernet.run_infernet(
                contract,
                timeout_s=infernet_timeout_s,
                dotnet_bin=infernet_bin,
            )
        except RuntimeError as e:
            infernet_error = str(e)

    diffs: List[Dict[str, Any]] = []
    agreement = True

    for grandeur in _GRANDEURS:
        ref = getattr(analytical, grandeur)
        for label, value in (
            ("pymc", getattr(pymc_result, grandeur, None) if pymc_result else None),
            ("infernet", getattr(infernet_result, grandeur, None) if infernet_result else None),
        ):
            if value is None:
                continue
            # Pour observe (bool) : on compare seulement la coherence de signe.
            if grandeur == "evsi_net":
                delta = value - ref
                if abs(delta) > tolerance:
                    diffs.append({
                        "engine": label,
                        "grandeur": grandeur,
                        "analytical": ref,
                        "engine_value": value,
                        "delta": delta,
                        "tolerance": tolerance,
                    })
                    agreement = False
            else:
                delta = value - ref
                if abs(delta) > tolerance:
                    diffs.append({
                        "engine": label,
                        "grandeur": grandeur,
                        "analytical": ref,
                        "engine_value": value,
                        "delta": delta,
                        "tolerance": tolerance,
                    })
                    agreement = False

    # Coherence de la decision observe / ne pas observer.
    decisions = {"analytical": analytical.observe}
    if pymc_result:
        decisions["pymc"] = pymc_result.observe
    if infernet_result:
        decisions["infernet"] = infernet_result.observe
    if len(set(decisions.values())) > 1:
        diffs.append({
            "type": "decision_disagreement",
            "decisions": decisions,
        })
        agreement = False

    if pymc_error:
        diffs.append({"type": "pymc_error", "message": pymc_error})
    if infernet_error:
        diffs.append({"type": "infernet_error", "message": infernet_error})

    return CompareReport(
        contract=contract,
        analytical=analytical,
        pymc=pymc_result,
        infernet=infernet_result,
        tolerance=tolerance,
        diffs=diffs,
        agreement=agreement,
    )


def write_report_json(report: CompareReport, path: str) -> None:
    """Serialize le rapport en JSON sur disque."""
    with open(path, "w", encoding="utf-8") as f:
        json.dump(report.to_dict(), f, indent=2, ensure_ascii=False)
