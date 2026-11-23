# -*- coding: utf-8 -*-
"""Schémas d'argumentation de Walton — table, classifieur déterministe et questions critiques.

Port de l'essence vivante du dépôt EPITA (mandat Triple Distillation, sous-grain
sas « argumentation_schemes », recensement #4960 du 2026-09-22T03:54Z). Source :
``argumentation_analysis/agents/core/debate/argumentation_schemes.py`` (tronc,
restauration G8 #1184) consommé par le carnet du sas
``docs/coursia_contrib/argumentation_schemes.ipynb`` et son banc
``argumentation_schemes_examples.json`` (#1961 Phase 5).

Fidélité du port (anti-pendule : restaurer, ne pas fabriquer) :

- Les **10 schémas** et leurs **forces a priori** sont ceux du moteur étudiant
  ``1_2_7_argumentation_dialogique/local_db_arg/src/core/argumentation_engine.py``
  repris verbatim par le tronc — y compris la lacune documentée : la table étudiante
  ne portait **aucune question critique**, le tronc a ajouté les questions
  canoniques de Walton (savoir canonique, non fabriqué).
- ``classify_scheme`` est un **matcher lexical déterministe** — aucun LLM, aucune
  JVM. Chaque schéma dispose d'ensembles de mots-clés alternatifs ; un ensemble
  ne « tire » que si **tous** ses mots apparaissent (AND intra-ensemble,
  précision privilégiée sur le rappel). L'**ordre canonique** départage les
  candidats : les schémas spécifiques d'abord, ``modus_ponens`` en **dernier**
  parce que « donc » est partout (le signal le plus faible ne doit tirer que
  quand rien de plus spécifique n'a tiré).
- **Échec bruyant** : ``None`` est un « aucun schéma détecté » honnête, jamais
  une étiquette fabriquée. Un corpus sans match est un résultat, pas une panne.

Divergences mesurées sur le source, documentées ici (classe des divergences de
gouvernance #17353) :

1. Le tronc importe ``logging`` et logge le schéma classifié en DEBUG — non
   porté : l'organe est stdlib pur silencieux, le notebook affiche lui-même.
2. ``schemes_as_prompt_context`` rend la table pour un prompt LLM (pont du débat
   EPITA) — portée telle quelle : côté CoursIA elle sert de rendu textuel de la
   table, aucun LLM ne la consomme.
3. ``_load_argumentation_schemes()`` reconstruit le dict à chaque appel côté
   tronc — porté à l'identique pour la fidélité (coût négligeable, 10 objets).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional


@dataclass(frozen=True)
class ArgumentationScheme:
    """Un schéma d'argumentation de type Walton.

    ``strength`` est la force a priori du moteur étudiant (un a priori sur la
    force du schéma, PAS un score mesuré sur le texte). ``critical_questions``
    sont les questions canoniques qu'un opposant pose pour tester le schéma —
    exposées pour qu'un échange puisse nommer le schéma ET le test qui le met
    en difficulté.
    """

    key: str
    label: str
    premises_pattern: List[str]
    conclusion_pattern: str
    strength: float
    critical_questions: List[str] = field(default_factory=list)


def _load_argumentation_schemes() -> Dict[str, ArgumentationScheme]:
    """Charge les 10 schémas d'argumentation (verbatim du moteur étudiant).

    Adaptation fidèle de ``argumentation_engine._load_argumentation_schemes`` :
    mêmes 10 clés, mêmes forces. Questions critiques ajoutées depuis le corpus
    canonique de Walton (le moteur étudiant n'en portait aucune).
    """
    return {
        "modus_ponens": ArgumentationScheme(
            key="modus_ponens",
            label="Déduction (modus ponens)",
            premises_pattern=["P", "P → Q"],
            conclusion_pattern="Q",
            strength=1.0,
            critical_questions=[
                "La prémisse P est-elle effectivement établie ?",
                "L'implication P → Q est-elle valide (pas un sophisme conditionnel) ?",
            ],
        ),
        "expert_opinion": ArgumentationScheme(
            key="expert_opinion",
            label="Argument d'autorité (advice of an expert)",
            premises_pattern=[
                "Expert E says P",
                "E is expert in domain D",
                "P is in domain D",
            ],
            conclusion_pattern="P",
            strength=0.8,
            critical_questions=[
                "E est-elle réellement une source experte sur ce domaine ?",
                "L'avis de E est-il cohérent avec le consensus des autres experts ?",
                "Y a-t-il une preuve directe (au-delà du seul témoignage) ?",
            ],
        ),
        "analogy": ArgumentationScheme(
            key="analogy",
            label="Argument par analogie",
            premises_pattern=[
                "Case A has property X",
                "Case B is similar to A",
                "X is relevant",
            ],
            conclusion_pattern="Case B has property X",
            strength=0.6,
            critical_questions=[
                "En quoi les cas A et B sont-ils réellement similaires sur la dimension pertinente ?",
                "Existe-t-il une différence pertinente qui brise l'analogie ?",
            ],
        ),
        "cause_effect": ArgumentationScheme(
            key="cause_effect",
            label="Argument de cause à effet",
            premises_pattern=["A causes B", "A occurred"],
            conclusion_pattern="B will occur",
            strength=0.7,
            critical_questions=[
                "La relation causale A → B est-elle établie (et non une simple corrélation) ?",
                "Y a-t-il d'autres causes possibles de B ?",
            ],
        ),
        "consensus": ArgumentationScheme(
            key="consensus",
            label="Argument d'ad hominem consensuel (appeal to consensus)",
            premises_pattern=[
                "Majority of experts agree on P",
                "Experts are qualified",
                "No systematic bias",
            ],
            conclusion_pattern="P is likely true",
            strength=0.85,
            critical_questions=[
                "Le consensus est-il largement partagé (et non une minorité bruyante) ?",
                "Les experts sont-ils exempts de biais systématiques ?",
            ],
        ),
        "empirical_evidence": ArgumentationScheme(
            key="empirical_evidence",
            label="Argument empirique (from evidence)",
            premises_pattern=[
                "Data shows P",
                "Data is reliable",
                "Sample is representative",
            ],
            conclusion_pattern="P is supported by evidence",
            strength=0.9,
            critical_questions=[
                "Les données sont-elles fiables (collecte, mesure) ?",
                "L'échantillon est-il représentatif de la population visée ?",
            ],
        ),
        "economic_argument": ArgumentationScheme(
            key="economic_argument",
            label="Argument économique (cost-benefit)",
            premises_pattern=["Action A costs X", "Action A benefits Y", "Y > X"],
            conclusion_pattern="Action A is economically justified",
            strength=0.75,
            critical_questions=[
                "Le calcul coût/bénéfice inclut-il tous les coûts externes ?",
                "Les bénéfices Y sont-ils réellement supérieurs aux coûts X une fois actualisés ?",
            ],
        ),
        "precautionary_principle": ArgumentationScheme(
            key="precautionary_principle",
            label="Principe de précaution",
            premises_pattern=[
                "Risk R is possible",
                "R has severe consequences",
                "Prevention is possible",
            ],
            conclusion_pattern="Prevention should be taken",
            strength=0.7,
            critical_questions=[
                "Le risque R est-il suffisamment plausible (et non spéculatif) ?",
                "Le coût de la prévention est-il proportionné à la gravité de R ?",
            ],
        ),
        "moral_argument": ArgumentationScheme(
            key="moral_argument",
            label="Argument moral (from rights)",
            premises_pattern=[
                "Action A affects group G",
                "G has rights",
                "A violates rights",
            ],
            conclusion_pattern="Action A is morally wrong",
            strength=0.8,
            critical_questions=[
                "L'action A viole-t-elle réellement un droit de G ?",
                "Existe-t-il un droit concurrent qui justifierait A ?",
            ],
        ),
        "historical_precedent": ArgumentationScheme(
            key="historical_precedent",
            label="Argument à partir d'un précédent historique",
            premises_pattern=[
                "Situation S occurred before",
                "S led to outcome O",
                "Current situation similar to S",
            ],
            conclusion_pattern="Outcome O is likely",
            strength=0.65,
            critical_questions=[
                "La situation actuelle est-elle réellement analogue à S ?",
                "Les conditions causales de O en S sont-elles réunies aujourd'hui ?",
            ],
        ),
    }


# Ensembles de mots-clés du classifieur déterministe. Chaque liste est la
# signature lexicale de son schéma (sous-chaînes en minuscules). Un schéma tire
# quand TOUS les mots d'un de ses ensembles apparaissent (AND dans le texte) —
# conservateur, la précision est privilégiée sur le rappel pour ne pas
# mal étiqueter. Vocabulaire exclusivement FRANÇAIS ACCENTUÉ : la docstring du
# source annonce « FR + EN » mais les 33 ensembles mesurés ne portent aucun
# mot anglais, et un texte désaccentué rend None (limite assumée, documentée
# au notebook). Deux écarts à la règle de la paire complète, mesurés sur le
# source et portés tels quels : « principe de précaution » est un singleton,
# et « donc » arme aussi cause_effect (["donc","parce que"]) AVANT
# modus_ponens dans l'ordre canonique.
_SCHEME_KEYWORDS: Dict[str, List[List[str]]] = {
    # Plusieurs ensembles alternatifs par schéma (un ensemble qui tire suffit).
    "expert_opinion": [
        ["expert", "domaine"],
        ["selon", "spécialiste"],
        ["autorité", "compétent"],
        ["source", "expert"],
    ],
    "analogy": [
        ["analogue", "similaire"],
        ["comme", "semblable"],
        ["à l'instar", "comparable"],
    ],
    "cause_effect": [
        ["cause", "effet"],
        ["entraîne", "conséquence"],
        ["provoque", "résultat"],
        ["donc", "parce que"],
    ],
    "consensus": [
        ["consensus", "experts"],
        ["majorité", "accord"],
        ["unanime", "scientifiques"],
    ],
    "empirical_evidence": [
        ["données", "représentatif"],
        ["étude", "mesure"],
        ["statistique", "échantillon"],
        ["résultat", "expérience"],
    ],
    "economic_argument": [
        ["coût", "bénéfice"],
        ["économique", "rentable"],
        ["investissement", "retour"],
    ],
    "precautionary_principle": [
        ["risque", "prévention"],
        ["principe de précaution"],
        ["danger", "éviter"],
    ],
    "moral_argument": [
        ["droit", "violation"],
        ["morale", "devoir"],
        ["éthique", "injuste"],
        ["droits", "atteinte"],
    ],
    "historical_precedent": [
        ["précédent", "historique"],
        ["déjà", "passé"],
        ["autrefois", "abouti"],
    ],
    "modus_ponens": [
        ["donc", "implique"],
        ["par conséquent", "si"],
    ],
}

# Ordre canonique de départage : les schémas spécifiques d'abord,
# modus_ponens en dernier — « donc » est partout, ce signal ne doit tirer
# que quand rien de plus spécifique n'a tiré.
_CANONICAL_ORDER: List[str] = [
    "expert_opinion",
    "empirical_evidence",
    "consensus",
    "analogy",
    "cause_effect",
    "economic_argument",
    "precautionary_principle",
    "moral_argument",
    "historical_precedent",
    "modus_ponens",
]


def classify_scheme(text: str) -> Optional[ArgumentationScheme]:
    """Classe un texte vers son schéma d'argumentation, de façon déterministe.

    Aucun LLM, aucune JVM — un matcher lexical sur ``_SCHEME_KEYWORDS``.
    Rend le ``ArgumentationScheme`` qui tire (le premier schéma dont un
    ensemble de mots-clés tire, dans l'ordre canonique de la table —
    modus_ponens en dernier comme signal le plus faible), ou ``None``
    quand rien ne tire.

    Échec bruyant : ``None`` est un « aucun schéma détecté » honnête, JAMAIS
    une étiquette fabriquée. Ce classifieur est volontairement conservateur :
    il préfère rendre None à mal étiqueter. Si un corpus ne rend aucun match,
    l'échange est rendu SANS étiquette de schéma plutôt qu'avec une invention.
    """
    if not text:
        return None
    lowered = text.lower()
    schemes = _load_argumentation_schemes()
    for key in _CANONICAL_ORDER:
        keyword_sets = _SCHEME_KEYWORDS.get(key, [])
        for kset in keyword_sets:
            if all(kw in lowered for kw in kset):
                scheme = schemes.get(key)
                if scheme is not None:
                    return scheme
    return None


def match_report(text: str) -> List[Dict[str, object]]:
    """Rapport d'introspection : chaque schéma qui tire sur le texte, dans l'ordre canonique.

    Expose le mécanisme interne du départage (même parcours que
    ``classify_scheme``) sans en changer la sémantique : chaque entrée rend la
    clé, l'ensemble de mots-clés qui a tiré et le rang dans l'ordre canonique.
    Le premier élément est donc toujours le schéma que ``classify_scheme``
    rendrait (quand la liste est non vide).
    """
    report: List[Dict[str, object]] = []
    if not text:
        return report
    lowered = text.lower()
    for rank, key in enumerate(_CANONICAL_ORDER, start=1):
        for kset in _SCHEME_KEYWORDS.get(key, []):
            if all(kw in lowered for kw in kset):
                report.append({"key": key, "matched_keywords": kset, "rank": rank})
                break
    return report


def schemes_as_prompt_context(limit: int = 10) -> str:
    """Rend la table des schémas comme bloc de connaissance textuel.

    Côté EPITA ce rendu alimente le prompt d'un débat LLM (chaque échange peut
    être ancré sur un schéma réel et son test). Côté CoursIA il sert de rendu
    lisible de la table — borné pour garder le budget raisonnable.
    """
    schemes = _load_argumentation_schemes()
    lines: List[str] = []
    for i, key in enumerate(list(schemes.keys())[:limit], start=1):
        s = schemes[key]
        qs = " ; ".join(s.critical_questions[:2])
        lines.append(
            f"  {i}. « {s.label} » (force a priori {s.strength:.2f}) — questions "
            f"critiques de test : {qs}"
        )
    return "\n".join(lines)
