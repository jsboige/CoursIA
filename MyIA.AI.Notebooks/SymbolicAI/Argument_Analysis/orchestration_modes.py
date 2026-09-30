# -*- coding: utf-8 -*-
"""Comparaison des modes d'orchestration d'un debat — arbitrage par budget.

Distillation deterministe du sas EPITA ``docs/coursia_contrib/
orchestration_modes_compared.ipynb`` (instrument ``scripts/
compare_orchestration_modes.py``, issue EPITA #1735), mandat Triple
Distillation (EPIC CoursIA #4960, sous-grain ligne 11 du recensement sas du
2026-09-22T03:54Z).

Le carnet source n'enseigne pas un axe (une capacite) mais un instrument :
comment arbitrer entre des architectures qui font toutes « la meme chose ».
Sept modes d'orchestration tournent sur le meme texte ; l'instrument emet des
metriques d'arbitrage (termine / wall-time / decide / perimetre). Le piege
documente : au budget par defaut (180 s), 4 des 7 modes sont tues par le filet
de securite du harnais — et le « classement » qui emergait de ce run etait un
artefact du budget, pas un resultat d'architecture.

>>> len(RUNS["under_budget"]), len(RUNS["calibrated"])
(7, 7)
>>> verdict_text(RUNS["under_budget"][0])
'tue par le filet du harnais'
>>> len(depth_families(DEPTH_PARITY))
3

Divergences mesurees sur les sources (contrat de fidelite) :

1. **Les runs LLM ne sont pas portes.** L'instrument appelait un modele BYOK
   (cout reel mesure, 0,55 USD + 0,95 USD) pour produire ses metriques. Le
   port embarque les **mesures committes** (2 runs x 7 modes, 2026-09-15,
   corpus_A synthetique embarque dans le script source) comme donnees —
   aucune cle, aucun appel reseau, tout est rejouable a l'identique.
2. **``compute_depth_parity`` introspectait les builders vivants** (import de
   ``argumentation_analysis.orchestration.workflows``) : le port porte les
   constantes **mesurees** (light=3 / standard=15 / full=17 phases de DAG ;
   4 objectifs ; 3 macro-phases de dialogue) avec leur provenance, sans
   aucune import hors stdlib.
3. **La plage de delegation degeneree est conservee verbatim** : le palier
   LLM-derived de ``hierarchical_delegation`` a produit exactement 4
   objectifs sur 3 corpus (firsthand R711, po-2023 projet-is) — ecrit comme
   la plage « 4-4 », pas comme l'entier 4, pour que le lecteur voie une
   distribution mesuree (degeneree) et non une constante structurelle.
4. **Les emoji du tableau source ne sont pas portes** (regle E : pas d'emoji
   dans le code) : les verdicts sont du texte plein.
5. **Le pivot ``terminates`` / ``decides`` de la source est porte mais pas
   lu.** Dans le carnet source, la colonne « Terminates 7/7 » etait le
   pivot du piege (« un succes n'est pas un compte d'achevement »). Les deux
   champs restent sur ``ModeRun``, fideles au banc (vrais sur les 14
   records), mais le port change d'angle : il decompose la meme lecon en
   trois registres d'arret (filet du harnais / declaration du mode /
   phases reellement faites) plutot qu'en une colonne a relativiser.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Optional

__all__ = [
    "ModeRun",
    "RUNS",
    "PROVENANCE",
    "DepthParityRow",
    "DEPTH_PARITY",
    "verdict_text",
    "termination_registers",
    "depth_family",
    "depth_families",
    "depth_parity_verdict",
    "project_full_duration",
    "derive_calibrated_budget",
    "budget_dependence",
]

#: Provenance des mesures embarquees (fichier ``_examples.json`` du sas).
PROVENANCE = {
    "instrument": "scripts/compare_orchestration_modes.py (EPITA #1735)",
    "model": "gpt-5.6-luna (BYOK — cout reel mesure, pas estime)",
    "corpora": ["corpus_A"],
    "corpus_note": (
        "textes synthetiques embarques dans le script source "
        "(aucun corpus chiffre, aucun raw_text)"
    ),
    "measured_on": "2026-09-15",
    "runs": {
        "under_budget": {"max_wall_seconds": 180, "cost_usd": 0.5504},
        "calibrated": {"max_wall_seconds": 600, "cost_usd": 0.9485},
    },
}


@dataclass(frozen=True)
class ModeRun:
    """Une mesure committ d'un mode d'orchestration sur un run donne.

    Les trois registres d'arret, qui disent trois choses differentes :

    - ``terminated_by_budget`` — le **filet du harnais** a tue le mode. C'est
      le seul arret que le harnais decide.
    - ``success`` — ce que le **mode declare de lui-meme**. Un mode peut se
      declarer satisfait d'un travail partiel (son plafond interne n'est pas
      le filet du harnais).
    - ``phases_completed / phases_total`` — ce qui a **reellement** ete fait.
    """

    mode: str
    success: bool
    duration_seconds: float
    phases_completed: int
    phases_total: int
    terminated_by_budget: bool
    terminates: bool = True
    decides: bool = True
    perimeter_is_exhaustive: bool = False
    state_fill_rate: Optional[float] = None
    scope_of_work: str = ""

    @property
    def phases_ratio(self) -> float:
        """Fraction de phases completees (0.0 si aucune)."""
        if self.phases_total == 0:
            return 0.0
        return self.phases_completed / self.phases_total


def _mk(mode, success, duration, done, total, killed, fill, scope, **flags):
    return ModeRun(
        mode=mode,
        success=success,
        duration_seconds=duration,
        phases_completed=done,
        phases_total=total,
        terminated_by_budget=killed,
        state_fill_rate=fill,
        scope_of_work=scope,
        **flags,
    )


#: Les deux runs committes du sas — meme modele, meme corpus, meme modes ;
#: seul le budget change (180 s puis 600 s).
RUNS = {
    "under_budget": [
        _mk("pipeline_standard", False, 180.01, 6, 15, True, 0.196,
            "UnifiedPipeline DAG workflow"),
        _mk("pipeline_light", True, 148.76, 3, 3, False, 0.179,
            "UnifiedPipeline DAG workflow", perimeter_is_exhaustive=True),
        _mk("pipeline_full", False, 180.02, 7, 17, True, 0.196,
            "UnifiedPipeline DAG workflow"),
        _mk("conversational", True, 180.01, 1, 3, False, 0.096,
            "AgentGroupChat multi-agent (plafond interne 180 s)"),
        _mk("conversation_deterministic", True, 0.061, 3, 3, False, None,
            "ConversationOrchestrator(mode=demo, SimulatedAgent, no LLM)"),
        _mk("hierarchical_bridge", False, 180.01, 2, 4, True, 0.118,
            "Strategic planning -> objectives_to_workflow (4 axes)"),
        _mk("hierarchical_delegation", False, 180.02, 1, 5, True, None,
            "Strategic -> Tactical -> Operational (3-tier, 5 tasks)"),
    ],
    "calibrated": [
        _mk("pipeline_standard", True, 461.36, 15, 15, False, 0.462,
            "UnifiedPipeline DAG workflow", perimeter_is_exhaustive=True),
        _mk("pipeline_light", True, 178.80, 3, 3, False, 0.179,
            "UnifiedPipeline DAG workflow", perimeter_is_exhaustive=True),
        _mk("pipeline_full", True, 448.12, 17, 17, False, 0.487,
            "UnifiedPipeline DAG workflow", perimeter_is_exhaustive=True),
        _mk("conversational", True, 600.02, 2, 3, False, 0.308,
            "AgentGroupChat multi-agent (plafond interne 600 s)"),
        _mk("conversation_deterministic", True, 0.058, 3, 3, False, None,
            "ConversationOrchestrator(mode=demo, SimulatedAgent, no LLM)"),
        _mk("hierarchical_bridge", True, 236.38, 4, 4, False, None,
            "Strategic planning -> objectives_to_workflow (4 axes)"),
        _mk("hierarchical_delegation", True, 217.02, 3, 5, False, None,
            "Strategic -> Tactical -> Operational (3-tier, 5 tasks)"),
    ],
}


def verdict_text(run: ModeRun) -> str:
    """Verdict en texte plein, en gardant visibles les trois registres.

    L'ordre des tests est le sujet : un mode tue par le harnais est tue,
    meme s'il avait declare ``success`` au moment du filet.
    """
    if run.terminated_by_budget:
        return "tue par le filet du harnais"
    if run.success and run.phases_completed == run.phases_total:
        return "phases completes, mode satisfait"
    if run.success:
        return "mode satisfait d'un travail partiel"
    return "inacheve (auto-declaration d'echec)"


def termination_registers(run: ModeRun) -> dict:
    """Les trois registres d'arret, explicites, pour lecture en table."""
    return {
        "harnais (filet)": run.terminated_by_budget,
        "mode (declaration)": run.success,
        "realite (phases)": f"{run.phases_completed}/{run.phases_total}",
    }


# ── Depth-parity : les modes ne partagent pas le meme axe de profondeur ────
#
# Constantes mesurees sur l'instrument source (divergence 2) : les 7 modes
# sont comparables en INTERFACE (tous produisent un verdict sur le meme
# texte) mais pas en perimetre de travail. Aligner les axes serait un
# pendule (tronquer le catalogue du pipeline OU gonfler artificiellement
# les autres) — le port documente l'asymetrie, il ne la « repare » pas.


@dataclass(frozen=True)
class DepthParityRow:
    """Une ligne du tableau d'asymetrie structurelle par mode.

    ``depth_dimension`` nomme CE QUE compte ``depth_count`` (phases de DAG /
    objectifs / macro-phases de dialogue) : des etiquettes honnetes, pas une
    fausse echelle commune. ``nature`` porte la famille (au sens large,
    parenthese retiree par :func:`depth_family`).
    """

    mode: str
    depth_dimension: str
    depth_count: int
    nature: str
    measured_range: Optional[str] = None


#: 7 lignes, 3 familles. Palier LLM-derived : plage mesuree degeneree
#: (divergence 3), conservee comme distribution, pas comme constante.
DEPTH_PARITY: tuple = (
    DepthParityRow("pipeline_light", "workflow phases (DAG)", 3, "breadth"),
    DepthParityRow("pipeline_standard", "workflow phases (DAG)", 15, "breadth"),
    DepthParityRow("pipeline_full", "workflow phases (DAG)", 17, "breadth"),
    DepthParityRow(
        "hierarchical_bridge", "strategic objectives (default axes)", 4,
        "delegation"),
    DepthParityRow(
        "hierarchical_delegation",
        "strategic objectives (LLM-derived, measured)", 4,
        "delegation (3-tier depth)",
        measured_range=(
            "4-4 objectifs -> 5-5 taches (n=3, corpus_A/B/C, "
            "firsthand R711, po-2023 projet-is)")),
    DepthParityRow(
        "conversational", "dialogue macro-phases (multi-turn)", 3,
        "dialogue-depth"),
    DepthParityRow(
        "conversation_deterministic",
        "dialogue macro-phases (deterministic)", 3,
        "dialogue-depth (no LLM)"),
)


def depth_family(row: DepthParityRow) -> str:
    """La famille d'axe : ``"delegation (3-tier depth)"`` -> ``"delegation"``."""
    return row.nature.split(" (")[0].strip()


def depth_families(rows) -> set:
    """L'ensemble des familles d'axes de profondeur couvertes par ``rows``."""
    return {depth_family(r) for r in rows}


def depth_parity_verdict(rows=DEPTH_PARITY) -> str:
    """Verdict d'asymetrie dont les comptes sont DERIVES de ``rows``.

    L'instrument source derivait ses comptes de la structure qu'il decrit
    (anti-#1019 : un litteral durci roterait identiquement a l'ajout d'un
    mode). Le port garde la meme discipline.
    """
    n_modes = len(rows)
    n_families = len(depth_families(rows))
    return (
        f"Les {n_modes} modes sont comparables en interface (tous produisent "
        "un verdict sur le meme texte) mais pas en perimetre de travail : "
        f"ils occupent {n_families} axes de profondeur differents. Pipeline "
        "= largeur (catalogue large, peu profond par capacite), "
        "hierarchique = delegation (peu d'objectifs, plusieurs etages), "
        "conversationnel = profondeur de dialogue (peu de macro-phases, "
        "multi-tours). Cette asymetrie est un choix de conception documente, "
        "pas un defaut : aligner les axes fabriquerait une parite factice."
    )


# ── La regle de calibration : deriver le budget de la mesure ───────────────


def project_full_duration(run: ModeRun) -> Optional[float]:
    """Projection lineaire de la duree complete d'un mode tue en cours.

    ``duree * phases_total / phases_completed`` — une HEURISTIQUE, ni borne
    superieure ni borne inferieure : elle suppose que les phases restantes
    coutent comme celles deja faites. Sur le sas, elle surestime
    massivement les deux modes hierarchiques (x4,1 et x1,5 — compatible
    avec un cout fixe concentre en tete de run) et sous-estime d'environ
    2,5 % les deux pipelines, ecart plus petit que la variation d'un run a
    l'autre (``pipeline_light`` : 148,76 s puis 178,80 s). ``None`` si
    aucune phase n'est faite (rien a extrapoler).
    """
    if run.phases_completed <= 0:
        return None
    return run.duration_seconds * run.phases_total / run.phases_completed


def derive_calibrated_budget(records, margin: float = 0.2) -> Optional[int]:
    """Budget derive de la mesure : la projection la plus longue, majoree.

    Retourne ``ceil(max(projections des modes tues) * (1 + margin))``, ou
    ``None`` si aucun record tue ne porte de phase faite. Sur le run
    sous-budget du sas, la derivation naive rend **1081 s** alors que le run
    calibre reel a suffi a **600 s** : l'extrapolation lineaire surestime
    d'un facteur 1,8 les modes tues tot (leur premiere phase porte le cout
    fixe de mise en route). La fonction enseigne la regle ET sa limite.
    """
    projections = [
        p for p in (project_full_duration(r) for r in records
                    if r.terminated_by_budget)
        if p is not None
    ]
    if not projections:
        return None
    return math.ceil(max(projections) * (1 + margin))


def budget_dependence(under, calibrated) -> list:
    """Contraste mode par mode entre deux runs qui ne different que par le budget.

    Chaque element porte : le mode, le verdict aux deux budgets, la bascule
    du filet, et les durees. C'est la preuve que le « classement » du run
    sous-budget etait un artefact du budget.
    """
    by_mode_cal = {r.mode: r for r in calibrated}
    out = []
    for r in under:
        c = by_mode_cal[r.mode]
        out.append({
            "mode": r.mode,
            "verdict_sous_budget": verdict_text(r),
            "verdict_calibre": verdict_text(c),
            "filet_bascule": r.terminated_by_budget and not c.terminated_by_budget,
            "duree_sous_budget": r.duration_seconds,
            "duree_calibre": c.duration_seconds,
        })
    return out
