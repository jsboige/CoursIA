# _pl_reasoner.py — expose le VRAI solveur propositionnel aux agents (#22981)
#
# Constat (#22981) : aucun outil expose aux agents ne produisait de verdict.
# Les seules sources de verdict `ACCEPTED`/`REJECTED` du depot sont
# `PLHandler.pl_query` (`_pl_handler.py`) et son enveloppe
# `TweetyBridge.execute_pl_query` (`_tweety_bridge.py`) — deux modules
# NON importables dans ce checkout (ils exigent le paquet upstream
# `argumentation_analysis`, absent ; verifie : `ModuleNotFoundError` a
# l'import). L'agent pouvait donc seulement consigner une question en
# langage naturel, ce que le carnet `Argumentation-08b-Executor-Python.ipynb`
# rejette ensuite (`QUERIES_NOT_MEANINGFUL`).
#
# Ce module branche l'organe REEL de la serie : le solveur propositionnel
# Tweety via la JVM JPype (deja utilise par
# `Argumentation-05-Formal-Verification-Python.ipynb`). Le LLM designe ce
# qui merite d'etre verifie ; le solveur decide. Aucune simulation : si la
# JVM ou les jars manquent, l'appel echoue bruyamment (mode degrade interdit
# dans cette serie, mandat EPITA #2137).
#
# Incident #23671 (mesure du 2026-11-06, run OpenAI gpt-5.6-luna) : sur un
# belief set reel de 15 formules (traduction d'un debat par le LLM), le
# raisonner initial `SimplePlReasoner` meurt en
# `java.lang.OutOfMemoryError: Java heap space` : il ENUMERE les mondes
# (2^n interpretations materialisees en memoire) avant de decider. L'agent
# appelait bien `pl_query` ; le plugin retournait
# `FUNC_ERROR: echec du moteur PL`, donc jamais `ACCEPTED`/`REJECTED` --
# la phase formelle paraissait muette (QUERIES_NONE / QUERIES_NOT_MEANINGFUL
# selon la cible LLM). L'engine passe au `SatReasoner` de Tweety
# (Tseitin->CNF->SAT4j embarque dans `libs/org.ow2.sat4j.core-2.3.5.jar`,
# espace polynomial) -- deja l'organe documente de cette serie par
# `_pl_handler.py` (Sat4jRunner : "linear -- distinct from
# SimplePlReasoner (model enumeration, 2^n, OOM-prone)"). Mesure comparative
# graduee des deux raisonners dans le body de la PR.
#
# Incident #23120 (mesures 28/10 et 06/11) : deux defauts de CONTENU
# subsistaient, independants du raisonner. (a) `PlParser` ACCEPTe une
# phrase en langage naturel (chaque mot devient un atome, conjonction
# implicite) : le solveur rendait alors un verdict sur des atomes-mots
# sans sens -- et avec l'ancien raisonner, la conversion CNF explosait en
# OOM (les runs 1-2 du 28/10 : belief sets en phrases). La courbe du
# 06/11 (chaines de biconditionnels propres) montre en outre que la
# validation de contenu seule n'aurait pas sauve la phase : le raisonner
# ET le contenu devaient etre repares tous les deux. (b) l'agent ecrit
# spontanement l'implication `R1 -> R2` ; `PlParser` REFUSE `->`
# ("General parsing error"), la consignation etait refusee par le garde.
# Remedes ici : reecriture `->` en `=>` AVANT l'appel au solveur et
# avant la cle du registre (la formule consignee est celle interrogee),
# et garde de contenu propositionnel AVANT l'appel -- une ligne prose
# rend une erreur de contenu diagnostiquable (CONTENT_ERROR), pas un
# OOM qui emporte la phase.

from __future__ import annotations

import logging
import os
import re
from typing import Any, List, Optional, Sequence

from semantic_kernel.functions import kernel_function

from argumentation_lib._pl_verdict import VerdictRegistry, format_verdict, registry_for

logger = logging.getLogger("Orchestration.PLReasoner")

#: Syntaxe propositionnelle acceptee par le parseur Tweety (`PlParser`).
#: Mesure sur `PlParser.parseFormula` (28/10) : `!`, `&&`, `||`, `=>`, `<=>`
#: sont acceptes ; `->` est REFUSE ("General parsing error"). Le prompt de
#: la phase formelle doit donc prescrire `=>` et non `->`.
PL_SYNTAX_HINT = (
    "syntaxe PL : atomes = identifiants (lettres, chiffres, `_`) ; "
    "connecteurs `!` (non), `&&` (et), `||` (ou), `=>` (implique), "
    "`<=>` (equivalent) ; parentheses pour la priorite"
)


class EngineUnavailableError(RuntimeError):
    """Le solveur propositionnel n'est pas joignable (JVM, jars, JDK)."""


class FormulaSyntaxError(ValueError):
    """Une formule n'est pas acceptee par le VRAI parseur du moteur."""

    def __init__(self, formula: str, detail: str):
        super().__init__(f"formule invalide {formula!r} : {detail}")
        self.formula = formula
        self.detail = detail


def split_formulas(content: str) -> List[str]:
    """Decoupe le contenu d'un belief set en formules propositionnelles.

    Format attendu : une formule par ligne, ou des formules separees par
    `;`. Les lignes vides sont ignorees ; tout le reste est renvoye tel quel
    — la SYNTAXE est validee par le VRAI parseur du moteur (PlParser refuse
    `->`, les connecteurs inconnus) ; la garde anti-prose de ce module
    (`non_propositional_line`) intercepte en amont ce que le parseur
    accepte a tort (les phrases en langage naturel, mesure #23120).
    """
    if not content:
        return []
    candidates: List[str] = []
    for raw_line in str(content).replace(";", "\n").splitlines():
        line = raw_line.strip()
        if line:
            candidates.append(line)
    return candidates


#: Connecteurs et parentheses de la syntaxe PL acceptee par PlParser.
_PL_CONNECTIVES = {"!", "&&", "||", "=>", "<=>", "(", ")"}

#: Un atome propositionnel : identifiant lettres/chiffres/`_`, sans espaces
#: ni ponctuation (PL_SYNTAX_HINT).
_ATOM_PATTERN = re.compile(r"[A-Za-z0-9_]+")


def _bare_atom(token: str) -> str:
    """Noyau d'un token : negations et parentheses collees retirees."""
    core = token
    while core.startswith(("(", "!")):
        core = core[1:]
    while core.endswith(")"):
        core = core[:-1]
    return core


def normalize_implication(formula: str) -> str:
    """Reecrit l'implication ASCII `->` en `=>`, attendu par `PlParser`.

    Mesure #23120 (28/10) : l'agent ecrit spontanement `R1 -> R2` ; le
    parseur Tweety REFUSE `->` ("General parsing error") alors que la
    semantique est evidente. La reecriture se fait AVANT l'appel au
    solveur ET avant la cle du registre, pour que la formule consignee
    soit exactement celle qui a ete interrogee.
    """
    return str(formula).replace("->", "=>")


def non_propositional_line(lines: Sequence[str]) -> Optional[str]:
    """Premiere ligne qui n'est pas une formule propositionnelle, sinon None.

    Mesure #23120 (28/10) : `PlParser` ACCEPTe une phrase en langage
    naturel — chaque mot devient un atome, conjonction implicite — et le
    solveur rend alors un verdict sur des atomes-mots sans sens. Un belief
    set propositionnel = des atomes sans espaces ni ponctuation relies par
    des connecteurs EXPLICITES. Deux motifs sont refuses :
    - deux atomes adjacents separes par un espace sans connecteur (prose) ;
    - un token qui n'est pas un identifiant (ponctuation, accents, etc.).
    """
    for line in lines:
        prev_was_atom = False
        for token in str(line).split():
            if token in _PL_CONNECTIVES:
                prev_was_atom = False
                continue
            core = _bare_atom(token)
            if not core or not _ATOM_PATTERN.fullmatch(core):
                return line
            if prev_was_atom:
                return line
            prev_was_atom = True
    return None


class TweetyPLEngine:
    """Moteur propositionnel reel : `SatReasoner` de Tweety (JVM, SAT4j).

    L'engine est volontairement separe du plugin : le plugin porte le
    contrat (resolution du belief set, format du verdict, enregistrement
    dans le registre), l'engine porte l'appel au solveur.

    Choix du raisonner (#23671) : `SatReasoner` decide par SAT
    (Tseitin->CNF->SAT4j, espace polynomial) ; `SimplePlReasoner` enumere
    les mondes (2^n interpretations en memoire) et meurt en OOM JVM sur
    les belief sets reels de la serie (~2 douzaines d'atomes). Les deux
    rendent le meme verdict sur les petits ensembles ; seul le premier
    survit aux gros.
    """

    name = "tweety-sat4j-pl-reasoner"

    def __init__(self) -> None:
        self._parser = None
        self._belief_set_class = None
        self._reasoner = None
        self._ready = False

    # -- initialisation -----------------------------------------------------
    def _ensure_ready(self) -> None:
        """Demarre la JVM si necessaire (idempotent) et charge les classes.

        `initialize_jvm()` deplacement le repertoire courant dans le dossier
        Tweety (les jars et le JDK y sont localises relativement au cwd) ;
        on restaure le cwd d'origine : un appel d'outil ne doit pas
        deporter le repertoire de travail du carnet.
        """
        if self._ready:
            return
        from argumentation_lib._jvm_compat import initialize_jvm

        cwd = os.getcwd()
        try:
            ok = initialize_jvm()
        finally:
            try:
                os.chdir(cwd)
            except OSError:  # pragma: no cover - cwd rendu inaccessible
                pass
        if not ok:
            raise EngineUnavailableError(
                "JVM/Tweety indisponible : verifiez `jdk-17-portable/` et "
                "`libs/*.jar` sous MyIA.AI.Notebooks/SymbolicAI/Tweety/. "
                "Mode degrade (verdict simule) INTERDIT."
            )
        try:
            import jpype

            jclass = jpype.JClass
            self._parser = jclass(
                "org.tweetyproject.logics.pl.parser.PlParser"
            )()
            self._belief_set_class = jclass(
                "org.tweetyproject.logics.pl.syntax.PlBeliefSet"
            )
            self._reasoner = jclass(
                "org.tweetyproject.logics.pl.reasoner.SatReasoner"
            )()
        except Exception as exc:  # pragma: no cover - classpath incomplet
            raise EngineUnavailableError(
                f"classes Tweety introuvables sur le classpath : {exc}"
            ) from exc
        self._ready = True

    # -- requete ------------------------------------------------------------
    def entails(self, formulas: Sequence[str], query: str) -> bool:
        """Vrai si le belief set entail la requete (decide par le solveur)."""
        self._ensure_ready()
        parsed = []
        for formula in formulas:
            parsed.append(self._parse(formula))
        parsed_query = self._parse(query)
        belief_set = self._belief_set_class()
        for formula in parsed:
            belief_set.add(formula)
        return bool(self._reasoner.query(belief_set, parsed_query))

    def _parse(self, formula: str):
        # La traduction texte->PL utilise ce point d'entree directement,
        # sans passer par entails() : initialiser ici aussi le parseur.
        self._ensure_ready()
        try:
            return self._parser.parseFormula(formula)
        except Exception as exc:  # jpype leve des exceptions Java
            raise FormulaSyntaxError(formula, str(exc).strip()[:200]) from exc


class PLReasonerPlugin:
    """Plugin Semantic Kernel exposant le solveur propositionnel aux agents.

    Le kernel function `pl_query` est le SEUL chemin d'obtention d'un
    verdict : il renvoie une chaine `ACCEPTED: ...` ou `REJECTED: ...`,
    qu'il enregistre dans le registre des verdicts. La garde de
    `StateManager-log_query_result` n'accepte ensuite que cette chaine.
    """

    def __init__(
        self,
        state,
        registry: Optional[VerdictRegistry] = None,
        engine: Any = None,
    ) -> None:
        self._state = state
        self._registry = registry if registry is not None else registry_for(state)
        self._engine = engine
        self._logger = logger

    # -- helpers ------------------------------------------------------------
    def _get_engine(self) -> Any:
        """Moteur effectif : cree a la demande (la JVM n'est demarree qu'au
        premier usage reel)."""
        if self._engine is None:
            self._engine = TweetyPLEngine()
        return self._engine

    def _belief_set_content(self, belief_set_id: str) -> Optional[str]:
        entry = getattr(self._state, "belief_sets", {}).get(belief_set_id)
        if entry is None:
            return None
        return entry.get("content", "")

    # -- kernel function ----------------------------------------------------
    @kernel_function(
        description=(
            "Interroge le VRAI solveur propositionnel (Tweety SatReasoner, SAT4j) "
            "sur un belief set et une formule. Parametres: belief_set_id "
            "(identifiant renvoye par add_belief_set), query (formule "
            "propositionnelle). Renvoie un verdict `ACCEPTED: ...` (la "
            "conclusion decoule du belief set) ou `REJECTED: ...` (elle ne "
            "decoule pas). Ce verdict doit ensuite etre consigne tel quel via "
            "log_query_result. " + PL_SYNTAX_HINT
        ),
        name="pl_query",
    )
    def pl_query(self, belief_set_id: str, query: str) -> str:
        """Verdict du solveur sur (belief_set, query)."""
        # #23120 : la reecriture precede TOUT — l'appel au solveur, la
        # chaine de verdict ET la cle du registre voient la meme formule.
        query = normalize_implication(query)
        content = self._belief_set_content(belief_set_id)
        if content is None:
            known = list(getattr(self._state, "belief_sets", {}).keys())
            return (
                f"FUNC_ERROR: belief set inconnu '{belief_set_id}' "
                f"(disponibles : {known})"
            )
        formulas = [normalize_implication(f) for f in split_formulas(content)]
        if not formulas:
            return (
                f"FUNC_ERROR: le belief set '{belief_set_id}' est vide ; "
                "appelez d'abord add_belief_set avec une formule par ligne."
            )
        # #23120 : garde de contenu AVANT l'appel — une phrase en langage
        # naturel rend une erreur diagnostiquable, pas un verdict sans sens
        # (ou, sous l'ancien raisonner, un OOM qui emportait la phase).
        bad_line = non_propositional_line(formulas)
        if bad_line is not None:
            return (
                f"CONTENT_ERROR: le belief set '{belief_set_id}' contient "
                f"une ligne qui n'est pas une formule propositionnelle "
                f"({bad_line[:80]!r}) ; une phrase n'est pas une formule. "
                "Ecrivez des atomes sans espaces ni ponctuation, relies "
                f"par des connecteurs explicites. {PL_SYNTAX_HINT}"
            )
        bad_query = non_propositional_line([query])
        if bad_query is not None:
            return (
                f"CONTENT_ERROR: la requete {query[:80]!r} n'est pas une "
                "formule propositionnelle ; une phrase n'est pas une "
                f"formule. {PL_SYNTAX_HINT}"
            )
        try:
            engine = self._get_engine()
            entailed = engine.entails(formulas, query)
        except FormulaSyntaxError as exc:
            return (
                f"FUNC_ERROR: {exc} ; {PL_SYNTAX_HINT}"
            )
        except EngineUnavailableError as exc:
            return f"FUNC_ERROR: moteur PL indisponible : {exc}"
        except Exception as exc:  # pragma: no cover - incident moteur
            self._logger.error(
                "Echec du solveur propositionnel sur %s / %s",
                belief_set_id,
                query,
                exc_info=True,
            )
            return f"FUNC_ERROR: echec du moteur PL : {exc}"
        verdict = format_verdict(
            belief_set_id, query, entailed, getattr(engine, "name", "moteur-pl")
        )
        self._registry.record(belief_set_id, query, verdict)
        self._logger.info("Verdict PL : %s", verdict)
        return verdict
