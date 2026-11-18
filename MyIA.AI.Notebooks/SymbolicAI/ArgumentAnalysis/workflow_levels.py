# -*- coding: utf-8 -*-
"""Catalogue de niveaux d'analyse light / standard / full — etape 5 du volet B (EPIC #4960).

Port deterministe de la RECETTE pedagogique du catalogue EPITA
``argumentation_analysis/orchestration/workflows.py`` (lignes 152-610) :
quelles dimensions activer a quel niveau. La source orchestrait des agents
LLM (+ Tweety) en DAG de 3 / 15 / 17 phases ; ce port orchestre les
ORGANES DETERMINISTES de la serie (TweetyBridge, TaxonomySophismDetector)
en catalogues de 3 / 6 / 9 dimensions. La parite est STRUCTURELLE, pas
numerique : les niveaux s'emboitent strictement (light ⊂ standard ⊂ full),
comme les DAG de la source -- les constantes 3/15/17 sont mesurees et
portees par ``orchestration_modes.DEPTH_PARITY`` ; les compteurs 3/6/9 sont
DERIVES du present catalogue (anti-#1019 : aucun litteral durci).

>>> [len(dimensions_at(l)) for l in LEVELS]
[3, 6, 9]

Le banc de texte (``BENCH``) embarque un court debat ET ses annotations
formelles (traduction PL/FOL/modale declarees). Le gap NL->structure est
documente en source comme non bouché deterministement (translation-gap,
body #4960) : la traduction LLM vit dans ``_runner.py`` ; ici les formules
sont des artefacts du banc, declares comme tels -- jamais presentees comme
une traduction automatique.

Divergences mesurees sur la source (contrat de fidelite) :

1. **Les DAG LLM ne sont pas portes.** Le catalogue source activait des
   agents LLM par phase (cout reel mesure 0,55-0,95 USD par run, porte
   par ``orchestration_modes.PROVENANCE``). Ce port n'appelle AUCUN LLM :
   chaque dimension invoque un organe deterministe de la serie, rejouable
   a l'identique hors ligne.
2. **La restitution 3 actes est COMPACTE et DECLAREE.** Le renderer
   complet vit dans le carnet 08d (embarque, non extractible sans toucher
   au carnet) ; le niveau full produit la bande de verdict et la
   conclusion au FORMAT du contrat 3 actes, en citant 08d comme porteur
   du renderer integral. Copie pedagogique declaree (organ-first, Q3 :
   l'extraction du renderer de 08d vers la lib est le refactoring a
   demander a la serie source).
3. **JTMS n'est pas une dimension.** La brique JTMS vit dans le carnet 06
   (embarquee), pas dans ``argumentation_lib`` : l'invoquer exigerait le
   meme refactoring d'extraction que le renderer. Les dimensions full
   restent sur les organes reellement consommables (decision, synthese).
4. **ASPIC+/ABA/SETAF/weighted/bipolar ne sont pas des dimensions non plus**
   (interdit explicite du body #4960 : gap NL->structure non bouche --
   les porter serait consacrer un workaround #3801).
5. **FOL et modale sont des dimensions DECLAREES INDISPONIBLES dans cet
   arbre** — l'organe n'existe pas ici, preuve mesuree : le jar charge par
   la serie (``Tweety/libs/org.tweetyproject.tweety-7a-java8-shade.jar``)
   ne porte AUCUNE classe ``logics.fol`` ni ``logics.ml`` (inventaire
   zipfile : sous-packages ``logics/`` du jar = commons + pl seulement).
   Les handlers portes (``argumentation_lib._fol_handler``,
   ``_modal_handler``) le documentent eux-memes : dependances amont non
   vendues (prover9, TweetyInitializer C186f, normalizer modal) —
   import-module en echec, note G.9 du ``__init__``. L'EPITA executait
   FOL/modal sur SES jars 1.28 (dossier etudiant, interdit d'import).
   Ces dimensions restent au catalogue (le niveau full les annonce) mais
   ``run_level`` les rend ``unavailable`` avec cette preuve — jamais un
   faux resultat, jamais un silence.
6. **La detection de sophismes est symbolique, pas taxonomique.** La source
   pilotait la taxonomie 1552 par ``TaxonomySophismDetector`` ; ce module
   n'est pas standalone-importable dans cet arbre (notice DEPENDENCY du
   fichier : le plugin SK amont n'est pas vendu). L'organe reellement
   livre par la serie est ``fallacy_rules.py`` (#17348 : 13 motifs / 5
   cles, extraction de donnees declaree) — c'est lui qu'on invoque, avec
   sa limite mesuree : seules les formes canoniques matchent (4 formes
   sur le corpus de reference du carnet des regles symboliques).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple

__all__ = [
    "LEVELS",
    "Dimension",
    "BENCH",
    "dimensions_at",
    "run_level",
    "LevelRun",
    "OrganUnavailable",
    "fill_report",
    "fill_rate",
    "verdict_band",
    "PARITY_NOTE",
]

#: Les trois niveaux du catalogue source, dans l'ordre d'emboitement.
LEVELS: Tuple[str, ...] = ("light", "standard", "full")

#: Parite documentee avec les mesures du sas (orchestration_modes, divergence 2).
PARITY_NOTE = (
    "Catalogue deterministe : {n} dimensions par niveau ({detail}). "
    "DAG LLM de la source : 3/15/17 phases (constantes mesurees, "
    "orchestration_modes.DEPTH_PARITY). Emboitement strict light ⊂ "
    "standard ⊂ full dans les deux cas ; les echelles ne sont pas "
    "communes (asymetrie documentee, pas reparee)."
)


# ---------------------------------------------------------------------------
# Le banc : un court debat + ses annotations formelles declarees
# ---------------------------------------------------------------------------

#: Texte de reference — debat municipal dont les sophismes sont les FORMES
#: CANONIQUES mesurees sur l'organe fallacy_rules (corpus du carnet des
#: regles symboliques : 4 formes matchent sur 9 essayees — divergence 6).
BENCH: Dict[str, Any] = {
    "raw_text": (
        "Le conseil municipal doit interdire les echoppes du centre-ville, "
        "car elles detruisent le commerce de proximite. "
        "Si les echoppes detruisent le commerce, alors les boutiques "
        "centrales fermeront. "
        "On ne peut pas faire confiance à ce conseiller qui defend les "
        "echoppes. "
        "Selon une etude de boutique, la mesure est efficace. "
        "On a toujours fait comme ça, pourquoi changer la position de la "
        "ville ? "
        "Le premier pas vers le declin du centre-ville. "
        "Toute regulation qui protege le commerce de proximite merite "
        "d'etre essayee, et la fermeture des echoppes protege le "
        "commerce de proximite. "
        "Donc la fermeture des echoppes merite d'etre essayee."
    ),
    # Annotations formelles DECLAREES (artefacts du banc — pas une traduction
    # automatique ; le gap NL->structure est documente en entete de module).
    "pl_belief_set": (
        "detruit_proximite\n"
        "detruit_proximite => fermeture_boutiques\n"
        "fermeture_echoppes => protege_proximite"
    ),
    "pl_queries": ["fermeture_boutiques"],
    "fol_belief_set": (
        "forall X: (echoppe(X) => nuisance(X))\n"
        "forall X: (nuisance(X) => fermeture_boutiques(X))"
    ),
    # AF Dung declaree : les arguments du debat + leurs attaques.
    "dung_arguments": ["A1_interdire", "A2_evidence", "A3_fermeture", "A4_ad_hominem", "A5_regulation"],
    "dung_attacks": [
        ["A4_ad_hominem", "A1_interdire"],   # l'attaque ad hominem vise A1
        ["A2_evidence", "A4_ad_hominem"],    # l'appel a l'evidence ne prouve rien -> contre-attaque
        ["A5_regulation", "A3_fermeture"],   # la regulation soutient, l'attaque vient du sens
    ],
    # KB modale declaree : croyance du conseil sur la fermeture.
    "modal_belief_set": "[] detruit_proximite\n[] (detruit_proximite => fermeture_boutiques)",
    "modal_query": "[] fermeture_boutiques",
    # Decision : la consequence que le conseil veut etablir (requete PL).
    "decision_formula": "fermeture_boutiques",
}


# ---------------------------------------------------------------------------
# Le catalogue : dimension = niveau minimal + runner + champs peuples
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Dimension:
    """Une dimension d'analyse du catalogue.

    ``level_min`` — le plus petit niveau qui active cette dimension
    (emboitement strict : une dimension ``standard`` tourne aussi en
    ``full``). ``fills`` nomme les champs de ``RhetoricalAnalysisState``
    que la dimension peuple — c'est la matiere du fill-rate. ``organ``
    cite l'organe invoque (provenance, jamais cachee).
    """

    name: str
    level_min: str
    fills: Tuple[str, ...]
    organ: str
    runner: Callable[[Dict[str, Any], Any], str]


def _dimension_extract(bench: Dict[str, Any], state: Any) -> str:
    """Decoupage declaratif du texte en segments d'argument.

    Regles simples et audibles : un segment est une phrase portant un
    marqueur d'argumentation (connecteur conclusif ou causal). Ce n'est
    PAS l'extraction LLM du catalogue source — c'est un releve
    deterministe declare.
    """
    import re

    markers = re.compile(
        r"\b(car|donc|alors|si\b|toute|tout le monde|merite)", re.IGNORECASE
    )
    segments = [
        s.strip()
        for s in re.split(r"(?<=[.!?])\s+", bench["raw_text"])
        if markers.search(s)
    ]
    state.identified_arguments = [
        {"arg_id": f"A{i+1}", "description": seg} for i, seg in enumerate(segments)
    ]
    return f"{len(segments)} segments releves (marqueurs deterministes)"


def _dimension_pl(bench: Dict[str, Any], state: Any) -> str:
    """PL : KB declaree passee au vrai SimplePlReasoner (pattern 00-Setup)."""
    import jpype

    JClass = jpype.JClass
    PlParser = JClass("org.tweetyproject.logics.pl.parser.PlParser")
    SimplePlReasoner = JClass("org.tweetyproject.logics.pl.reasoner.SimplePlReasoner")
    PlBeliefSet = JClass("org.tweetyproject.logics.pl.syntax.PlBeliefSet")

    parser, reasoner = PlParser(), SimplePlReasoner()
    bs = PlBeliefSet()
    for line in bench["pl_belief_set"].splitlines():
        bs.add(parser.parseFormula(line))
    answers = []
    for q in bench["pl_queries"]:
        answers.append((q, bool(reasoner.query(bs, parser.parseFormula(q)))))
    state.belief_sets["pl"] = bench["pl_belief_set"]
    state.query_log.extend(
        {"dimension": "pl", "query": q, "answer": str(a)} for q, a in answers
    )
    for q, a in answers:
        state.answers[q] = str(a)
    # Consistance lue sur la requete duale : la KB est incoherente si elle
    # implique une contradiction (pattern SimplePlReasoner, source 00-Setup).
    contradiction = bool(reasoner.query(bs, parser.parseFormula("a && !a")))
    return (
        f"KB PL {'incoherente' if contradiction else 'coherente'} ; "
        f"{len(answers)} requete(s) Tweety ({', '.join(q for q, _ in answers)})"
    )


#: Pipeline spaCy partage (chargement paresseux unique — le modele
#: fr_core_news_sm coute ~2 s a charger, inutile de le refaire par requete).
_NLP_CACHE: List[Any] = []


def _dimension_informal(bench: Dict[str, Any], state: Any) -> str:
    """Sophismes : l'organe symbolique de la serie (fallacy_rules, #17348).

    Divergence 6 : la taxonomie 1552 de la source n'est pas
    standalone-importable (plugin SK amont non vendu, notice DEPENDENCY
    du fichier) ; fallacy_rules est l'organe reellement livre. Ses motifs
    spaCy attrapent les formes canoniques — le banc n'en embarque que
    ces formes (mesure sur le corpus de reference : 4/9).
    """
    import spacy

    from fallacy_rules import detect_fallacies

    if not _NLP_CACHE:
        _NLP_CACHE.append(spacy.load("fr_core_news_sm"))
    hits = detect_fallacies(bench["raw_text"], nlp=_NLP_CACHE[0])
    state.identified_fallacies = [
        {
            "key": h["key"],
            "label": h["label"],
            "excerpt": h["excerpt"],
            "source": "fallacy_rules#17348",
        }
        for h in hits
    ]
    familles = sorted({h["key"] for h in hits})
    return (
        f"{len(hits)} sophisme(s) releve(s) par motifs symboliques "
        f"({', '.join(familles) if familles else 'aucun motif canonique'})"
    )


def _dimension_dung(bench: Dict[str, Any], state: Any) -> str:
    """AF de Dung : extensions par semantique — classes Tweety reelles.

    Pattern canonique de la serie Tweety voisine (Tweety-05, cellule 8) :
    ``jpype.imports`` + ``Simple*Reasoner`` — l'inventaire du jar charge
    par la serie (7a-java8-shade) ne porte QUE les reasoners prefixes
    ``Simple*`` (mesure zipfile : pas de classe ``GroundedReasoner``).
    ``SimpleGroundedReasoner.getModel`` rend UNE extension ;
    ``getModels`` rend une collection.
    """
    from org.tweetyproject.arg.dung.syntax import DungTheory, Argument, Attack
    from org.tweetyproject.arg.dung.reasoner import (
        SimpleGroundedReasoner,
        SimplePreferredReasoner,
        SimpleStableReasoner,
    )

    theory = DungTheory()
    args = {name: Argument(name) for name in bench["dung_arguments"]}
    for name, arg in args.items():
        theory.add(arg)
    for attacker, attacked in bench["dung_attacks"]:
        theory.add(Attack(args[attacker], args[attacked]))

    result: Dict[str, List[List[str]]] = {}
    grounded = SimpleGroundedReasoner().getModel(theory)
    result["grounded"] = [sorted(str(a.getName()) for a in grounded)]
    for label, reasoner_cls in (
        ("preferred", SimplePreferredReasoner),
        ("stable", SimpleStableReasoner),
    ):
        exts = list(reasoner_cls().getModels(theory))
        result[label] = sorted(
            sorted(str(a.getName()) for a in ext) for ext in exts
        )
    state.belief_sets["dung_extensions"] = repr(result)[:300]
    state.query_log.append(
        {"dimension": "dung", "query": "extensions", "answer": str(result)[:400]}
    )
    n_ext = {k: len(v) for k, v in result.items()}
    return f"AF sous 3 semantiques : {n_ext}"


class OrganUnavailable(RuntimeError):
    """Dimension declaree indisponible : l'organe n'existe pas dans cet arbre.

    Portee par une PREUVE mesuree (divergence 5 du contrat de fidelite) —
    a distinguer d'un echec d'execution, qui lui reste fail-loud.
    """


def _dimension_fol(bench: Dict[str, Any], state: Any) -> str:
    """FOL : DECLARE INDISPONIBLE dans cet arbre (divergence 5).

    Le jar de la serie (7a-java8-shade) ne porte aucune classe
    ``logics.fol`` ; le handler porte (``_fol_handler``) documente ses
    dependances amont non vendues (note G.9 du ``__init__``). La KB FOL
    du banc reste AFFICHEE par le carnet comme annotation declaree.
    """
    raise OrganUnavailable(
        "organe FOL absent : 0 classe logics.fol dans le jar 7a-java8-shade "
        "(inventaire zipfile) ; handler porte en dependances non vendues "
        "(prover9, TweetyInitializer C186f) — note G.9 de argumentation_lib"
    )


def _dimension_modal(bench: Dict[str, Any], state: Any) -> str:
    """Modale : DECLAREE INDISPONIBLE dans cet arbre (divergence 5).

    Idem FOL : 0 classe ``logics.ml`` dans le jar ; ``_modal_handler``
    leve ModuleNotFoundError a l'import (sibling non vendu, note G.9).
    """
    raise OrganUnavailable(
        "organe modal absent : 0 classe logics.ml dans le jar 7a-java8-shade "
        "(inventaire zipfile) ; handler porte en siblings non vendus "
        "(normalizer, TweetyInitializer C186f) — note G.9 de argumentation_lib"
    )


def _dimension_sat(bench: Dict[str, Any], state: Any) -> str:
    """Decision : la formule d'engagement passee au SimplePlReasoner.

    Divergence declaree : le catalogue source resolvait la decision par un
    solveur SAT ; ce port interroge le moteur de requete PL (organe
    reellement consomme par la serie, pattern 00-Setup) sur la formule de
    decision. Aucun solveur natif n'est pretendu.
    """
    import jpype

    JClass = jpype.JClass
    PlParser = JClass("org.tweetyproject.logics.pl.parser.PlParser")
    SimplePlReasoner = JClass("org.tweetyproject.logics.pl.reasoner.SimplePlReasoner")
    PlBeliefSet = JClass("org.tweetyproject.logics.pl.syntax.PlBeliefSet")

    parser, reasoner = PlParser(), SimplePlReasoner()
    bs = PlBeliefSet()
    # KB COMPLETE : la decision se derive par la chaine (fait + regle x2),
    # pas sur le seul fait initial — charger les trois formules.
    for line in bench["pl_belief_set"].splitlines():
        bs.add(parser.parseFormula(line))
    answer = bool(reasoner.query(bs, parser.parseFormula(bench["decision_formula"])))
    state.query_log.append(
        {"dimension": "decision", "query": bench["decision_formula"], "answer": str(answer)}
    )
    return f"Formule de decision : {bench['decision_formula']} => {answer}"


def _dimension_synthesis(bench: Dict[str, Any], state: Any) -> str:
    """Synthese au FORMAT du contrat 3 actes (copie pedagogique declaree).

    Acte I ce qui est pose ; Acte II ce qui est attaque ; Acte III ce qui
    tient. Le renderer integral vit dans le carnet 08d.
    """
    n_args = len(state.identified_arguments or [])
    n_fallacies = len(state.identified_fallacies or [])
    n_queries = len(state.query_log or [])
    kb_posees = ", ".join(sorted(state.belief_sets or {})) or "aucune"
    act1 = f"{n_args} arguments releves, KB posees : {kb_posees}"
    act2 = f"{n_fallacies} sophisme(s) releve(s), AF attaquee"
    act3 = f"{n_queries} requetes formelles executees, verdict par semantique Dung"
    state.final_conclusion = (
        f"Acte I — {act1}. Acte II — {act2}. Acte III — {act3}. "
        "(format compact du contrat 3 actes ; renderer integral : carnet 08d)"
    )
    return "conclusion 3 actes ecrite dans l'etat"


#: Le catalogue — l'ORDRE est le fil conducteur, l'emboitement est structurel.
#: Les dimensions fol/modal restent annoncees au catalogue (le niveau full
#: les nome) mais leurs runners rendent OrganUnavailable (divergence 5).
DIMENSIONS: Tuple[Dimension, ...] = (
    Dimension("extract_arguments", "light", ("identified_arguments",),
              "releve deterministe (marqueurs)", _dimension_extract),
    Dimension("pl_belief_set", "light", ("belief_sets", "query_log"),
              "Tweety PlParser + SimplePlReasoner (pattern 00-Setup)", _dimension_pl),
    Dimension("pl_queries", "light", ("query_log", "answers"),
              "Tweety SimplePlReasoner (requetes)", _dimension_pl),
    Dimension("informal_fallacies", "standard", ("identified_fallacies",),
              "fallacy_rules.py — organe symbolique #17348", _dimension_informal),
    Dimension("dung_semantics", "standard", ("query_log",),
              "Tweety Simple{Grounded,Preferred,Stable}Reasoner (Tweety-05)", _dimension_dung),
    Dimension("fol_consistency", "standard", ("belief_sets", "query_log"),
              "DECLARE INDISPONIBLE (divergence 5 : jar sans logics.fol)", _dimension_fol),
    Dimension("modal_queries", "full", ("belief_sets", "query_log"),
              "DECLAREE INDISPONIBLE (divergence 5 : jar sans logics.ml)", _dimension_modal),
    Dimension("sat_decision", "full", ("query_log",),
              "Tweety SimplePlReasoner sur la formule de decision", _dimension_sat),
    Dimension("synthesis_3_actes", "full", ("final_conclusion",),
              "format du contrat 3 actes (carnet 08d)", _dimension_synthesis),
)

_LEVEL_ORDER = {name: i for i, name in enumerate(LEVELS)}


def dimensions_at(level: str) -> List[Dimension]:
    """Les dimensions actives a un niveau, dans l'ordre du catalogue.

    >>> dimensions_at("light")[0].name
    'extract_arguments'
    >>> len(dimensions_at("full"))
    9
    """
    if level not in _LEVEL_ORDER:
        raise ValueError(f"niveau inconnu : {level!r} (attendus : {LEVELS})")
    return [d for d in DIMENSIONS if _LEVEL_ORDER[d.level_min] <= _LEVEL_ORDER[level]]


# ---------------------------------------------------------------------------
# Execution d'un niveau + fill-rate
# ---------------------------------------------------------------------------

#: Champs de RhetoricalAnalysisState comptes dans le fill-rate (7 utiles).
STATE_FIELDS: Tuple[str, ...] = (
    "raw_text", "identified_arguments", "identified_fallacies",
    "belief_sets", "query_log", "answers", "final_conclusion",
)


def _fresh_state(bench: Dict[str, Any]):
    """Un etat partage neuf, raw_text deja pose (comme la source)."""
    from argumentation_lib._shared_state import RhetoricalAnalysisState

    return RhetoricalAnalysisState(bench["raw_text"])


def fill_report(state: Any) -> Dict[str, bool]:
    """Champ par champ : peuplee ou non (le fill-rate de la source, en deterministe)."""
    report: Dict[str, bool] = {}
    for f in STATE_FIELDS:
        value = getattr(state, f, None)
        if isinstance(value, (list, dict, str)):
            report[f] = len(value) > 0
        else:
            report[f] = value is not None
    return report


def fill_rate(state: Any) -> float:
    """Fraction des champs utiles peuples — comparable au state_fill_rate du sas."""
    report = fill_report(state)
    return sum(report.values()) / len(report) if report else 0.0


@dataclass
class LevelRun:
    """Le resultat d'un niveau sur le banc : dimensions, fill, verdicts.

    ``unavailable`` porte les dimensions DECLAREES indisponibles (divergence
    5) avec leur preuve — elles ne comptent ni comme executees ni comme
    echecs : le niveau full annonce 9 dimensions dont 2 rendues avec preuve.
    """

    level: str
    dimensions: List[str] = field(default_factory=list)
    unavailable: Dict[str, str] = field(default_factory=dict)
    notes: List[str] = field(default_factory=list)
    fill_rate: float = 0.0
    fill_report: Dict[str, bool] = field(default_factory=dict)

    def verdict_band(self) -> str:
        """La bande de verdict : niveau, dimensions, fill — comptes DERIVES."""
        return (
            f"[{self.level}] {len(self.dimensions)} dimensions executees"
            + (f", {len(self.unavailable)} declarees indisponibles" if self.unavailable else "")
            + f", fill {self.fill_rate:.2f} ({sum(self.fill_report.values())}/"
            f"{len(self.fill_report)} champs peuples)"
        )


def run_level(bench: Dict[str, Any], level: str, state: Optional[Any] = None) -> Tuple[Any, LevelRun]:
    """Execute les dimensions actives d'un niveau sur le banc.

    Retourne (etat, LevelRun). Fail-loud pour toute erreur d'execution
    (la serie refuse le mode degrade, 00-Setup) — SAUF OrganUnavailable,
    qui est une absence declaree avec preuve, rendue a part.
    """
    active = dimensions_at(level)
    if state is None:
        state = _fresh_state(bench)
    run = LevelRun(level=level)
    for dim in active:
        try:
            note = dim.runner(bench, state)
        except OrganUnavailable as unavailable:
            run.unavailable[dim.name] = str(unavailable)
            run.notes.append(f"{dim.name}: INDISPONIBLE — {unavailable}")
            continue
        run.dimensions.append(dim.name)
        run.notes.append(f"{dim.name}: {note}")
    run.fill_report = fill_report(state)
    run.fill_rate = fill_rate(state)
    return state, run
