# =============================================================================
# ADAPTATION LOCALE (CoursIA, 2026-10-29) — ce fichier n'est PLUS verbatim.
# -----------------------------------------------------------------------------
# Point de depart : copie verbatim du depot EPITA-IS (voir le bloc d'origine
# conserve ci-dessous), portee par le Volet B etape 4 sous-tranche C186c.
#
# Pourquoi l'adaptation : l'organe ADF n'etait exerce par AUCUN carnet de la
# serie (organe orphelin), et il etait casse contre le jar reellement vende
# `MyIA.AI.Notebooks/SymbolicAI/Tweety/libs/adf-1.30.jar`. Quatre derives
# d'API ont ete mesurees firsthand (JVM amorcee par
# `argumentation_lib.initialize_jvm()`, conda `epita_symbolic_ai`) :
#
#  1. `builder.add(arg)` : surcharge ABSENTE en 1.30 (le builder n'expose que
#     `add(Argument, AcceptanceCondition)` et `add(Link)`). Symptome mesure :
#     `TypeError: No matching overloads found for ...AbstractBuilder.add(...)`.
#     Correction : le statement est ajoute une seule fois, avec sa condition.
#  2. `TautologyAcceptanceCondition` et `ContradictionAcceptanceCondition`
#     sont des ENUMERATIONS en 1.30 (constantes `T` et `F`) : `self.TautologyAcc()`
#     leve `TypeError: Java class has no constructors`. Correction : lecture de
#     la constante d'enumeration, avec repli sur l'instanciation pour les
#     versions anterieures.
#  3. Le graphe ADF exige ses liens : en mode `eager` (defaut), toute condition
#     d'acceptation qui cite un argument impose un lien. Symptome mesure :
#     `IllegalStateException: Could not build ADF because of missing links!`.
#     Correction : construction en mode `provided()` + liens explicites, un par
#     argument cite (lien `SUPPORTING` du parent vers l'argument conditionne).
#  4. Les reasoners ADF sont SAT-based : seule la surcharge
#     `Reasoner(IncrementalSatSolver)` existe (`GroundReasoner()` leve
#     `TypeError: No matching overloads found`). Correction : solveur natif
#     `NativeMinisatSolver` (le jar ADF embarque `minisat.dll`, `picosat.dll`
#     et `lingeling.dll`), cree paresseusement et partage par les reasoners.
#
# Capacite ajoutee (declaree) : le vocabulaire des conditions d'acceptation
# accepte des composites `or:<c1>,<c2>` et `and:<c1>,<c2>` (disjonction et
# conjonction de conditions), ce qui rend l'exemple canonique des ADF
# (`a <-> b`, `c` accepte si `¬a` ou `¬b`) exprimable par l'API.
#
# Perimetre NON cable (gate-out explicite, pas de contournement) : la lecture
# d'un fichier KPPADF. Mesure : `KppADFFormatParser(LinkStrategy, boolean)`
# n'a plus de constructeur sans argument, et la lecture du fichier
# `adf_example.txt` livre par le jar echoue alors sur
# `java.util.EmptyStackException`. Voir `parse_adf_file`.
#
# Preuve de non-regression : l'intepretation des resultats est inchangee
# (memes cles de retour, memes semantiques) ; seule la construction du cadre
# est corrigee, et les resultats sont DESORMAIS structurees
# (`interpretations_detailed` : accepted / rejected / undecided).
#
# Le bloc d'origine (verbatim EPITA-IS) est conserve ci-dessous pour la
# traçabilite de la copie ; la table `NOTICE-EPITA` porte la mention
# NOT-VERBATIM correspondante.
# =============================================================================
# =============================================================================
# Verbatim copy from EPITA-IS (2025-Epita-Intelligence-Symbolique)
# Source file : argumentation_analysis/agents/core/logic/adf_handler.py
# Source SHA1 : 3ac651e01cdfde50641710c5ef3ebddb8154761d (161L @ a8025f60)
# Source LICENSE: MIT (Copyright (c) 2025 jsboigeEpita)
# CoursIA copy: MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/_adf_handler.py
# Copy LICENSE : MIT (inherited from upstream)
# Volet B etape 4 sub-tranche C186c — See EPIC #4960
#
# DEPENDENCY NOTICE (G.9 honest caveat):
# This verbatim port has NO upstream `argumentation_analysis.*` imports at
# top-level — only stdlib (`jpype`, `logging`, `typing`). The class symbol
# is therefore import-safe today; ONLY JPype-Tweety singletons are referenced
# (jpype.JClass, jpype.JException). Instantiation WILL FAIL at runtime until
# the JPype bridge singleton from C184 (`argumentation_lib.initialize_jvm`)
# is initialized and the target classes
# (`org.tweetyproject.arg.adf.syntax.adf.GraphAbstractDialecticalFramework`
# and 6 others, see REASONERS dict) are exposed by the JVM.
#
# Until the JPype-Tweety bridge is properly initialized (sub-tranche C186g
# runtime bridge shim), the lazy accessor
# `argumentation_lib.get_adf_handler_symbol()` returns the ADFHandler class
# symbol without triggering instantiation. Top-level
# `from argumentation_lib._adf_handler import ADFHandler` WILL succeed (no
# upstream sibling imports); failing import would mean the verbatim block
# was modified.
#
# Chain anchor: a8025f60 (consistent with C186a #5237, C186b #5234 MERGED).
# No upstream commits on adf_handler.py between a8025f60 and HEAD (verified
# via `git log a8025f60..HEAD -- adf_handler.py` = 0 commits).
# =============================================================================
"""Handler for Abstract Dialectical Frameworks (ADF) via TweetyProject.

ADFs generalize Dung's abstract argumentation by replacing attack/no-attack
with acceptance conditions — Boolean functions determining when a statement
is accepted based on its parents.

Supports:
- Grounded, Complete, Preferred, Admissible, Model, Stable semantics
- KppADF file format parsing (NOT wired against the vendored 1.30 jar — see
  the adaptation block at the top of the file and `parse_adf_file`)

ADAPTATION LOCALE (CoursIA, 2026-10-29) : this module no longer matches the
upstream copy byte for byte. The adaptation block at the top of the file lists
the four measured API drifts (Tweety 1.30) and the fix applied to each one.
"""

import jpype
import logging
from typing import List, Dict, Any, Optional, Set, Tuple

logger = logging.getLogger(__name__)


class ADFHandler:
    """Abstract Dialectical Framework analysis using Tweety."""

    REASONERS = {
        "grounded": "org.tweetyproject.arg.adf.reasoner.GroundReasoner",
        "complete": "org.tweetyproject.arg.adf.reasoner.CompleteReasoner",
        "preferred": "org.tweetyproject.arg.adf.reasoner.PreferredReasoner",
        "admissible": "org.tweetyproject.arg.adf.reasoner.AdmissibleReasoner",
        "model": "org.tweetyproject.arg.adf.reasoner.ModelReasoner",
        "naive": "org.tweetyproject.arg.adf.reasoner.NaiveReasoner",
        "conflict_free": "org.tweetyproject.arg.adf.reasoner.ConflictFreeReasoner",
    }

    def __init__(self, initializer_instance=None):
        if initializer_instance and not initializer_instance.is_jvm_ready():
            raise RuntimeError("ADFHandler instantiated before JVM is ready.")
        self.ADF = jpype.JClass(
            "org.tweetyproject.arg.adf.syntax.adf.GraphAbstractDialecticalFramework"
        )
        self.ADFArgument = jpype.JClass("org.tweetyproject.arg.adf.syntax.Argument")
        self.TautologyAcc = jpype.JClass(
            "org.tweetyproject.arg.adf.syntax.acc.TautologyAcceptanceCondition"
        )
        self.ContradictionAcc = jpype.JClass(
            "org.tweetyproject.arg.adf.syntax.acc.ContradictionAcceptanceCondition"
        )
        self.NegationAcc = jpype.JClass(
            "org.tweetyproject.arg.adf.syntax.acc.NegationAcceptanceCondition"
        )
        # Adaptation locale : conditions composites (disjonction / conjonction).
        self.DisjunctionAcc = jpype.JClass(
            "org.tweetyproject.arg.adf.syntax.acc.DisjunctionAcceptanceCondition"
        )
        self.ConjunctionAcc = jpype.JClass(
            "org.tweetyproject.arg.adf.syntax.acc.ConjunctionAcceptanceCondition"
        )
        self.KppParser = jpype.JClass("org.tweetyproject.arg.adf.io.KppADFFormatParser")
        # Adaptation locale : liens du graphe + solveur SAT des reasoners.
        self._Link = jpype.JClass("org.tweetyproject.arg.adf.semantics.link.Link")
        self._LinkType = jpype.JClass(
            "org.tweetyproject.arg.adf.semantics.link.LinkType"
        )
        self._SatSolver = jpype.JClass(
            "org.tweetyproject.arg.adf.sat.solver.NativeMinisatSolver"
        )
        self._reasoner_cache = {}
        self._solver = None

    # ------------------------------------------------------------------
    # Adaptations locales (Tweety 1.30)
    # ------------------------------------------------------------------

    @staticmethod
    def _acceptance_constant(cls):
        """Constante d'enumeration d'une condition de base.

        En 1.30, `TautologyAcceptanceCondition` et
        `ContradictionAcceptanceCondition` sont des enumerations (constantes
        `T` et `F`) : leur constructeur est prive, l'instanciation directe
        echoue. Les versions anterieures exposaient des classes
        instanciables : on garde les deux formes, sans exception silencieuse.
        """
        values = getattr(cls, "values", None)
        if callable(values):
            constants = values()
            if len(constants) > 0:
                return constants[0]
        return cls()

    def _sat_solver(self):
        """Solveur SAT incremental partage par les reasoners ADF.

        Mesure (2026-10-29) : les reasoners ADF de 1.30 n'existent qu'avec un
        `IncrementalSatSolver` ; `NativeMinisatSolver` est l'implementation
        native livree dans le jar ADF (`minisat.dll` sous Windows).
        """
        if self._solver is None:
            self._solver = self._SatSolver()
        return self._solver

    def _parse_condition(
        self, spec: str, arg_map: Dict[str, Any]
    ) -> Tuple[Any, Set[str]]:
        """Traduit une specification de condition en condition Java.

        Vocabulaire accepte :
          "tautology"        l'argument est toujours acceptable
          "contradiction"    l'argument n'est jamais acceptable
          "negation:<stmt>"  l'argument est acceptable ssi <stmt> ne l'est pas
          "or:<c1>,<c2>"     disjonction de deux conditions
          "and:<c1>,<c2>"    conjonction de deux conditions

        Retourne (condition Java, ensemble des arguments dont la condition
        d'acceptation depend — ces arguments sont les « parents » dans le
        graphe ADF).
        """
        spec = spec.strip()
        if spec == "tautology":
            return self._acceptance_constant(self.TautologyAcc), set()
        if spec == "contradiction":
            return self._acceptance_constant(self.ContradictionAcc), set()
        if spec.startswith("negation:"):
            other = spec.split(":", 1)[1].strip()
            if other not in arg_map:
                raise ValueError(
                    f"Condition 'negation:{other}' : l'argument '{other}' ne fait "
                    f"pas partie des statements {sorted(arg_map)}."
                )
            return self.NegationAcc(arg_map[other]), {other}
        for prefix, builder_name in (("or:", "DisjunctionAcc"), ("and:", "ConjunctionAcc")):
            if spec.startswith(prefix):
                parts = [p.strip() for p in spec[len(prefix):].split(",")]
                if len(parts) != 2:
                    raise ValueError(
                        f"Condition '{spec}' : '{prefix}' attend exactement deux "
                        f"conditions, {len(parts)} fournie(s)."
                    )
                left, left_deps = self._parse_condition(parts[0], arg_map)
                right, right_deps = self._parse_condition(parts[1], arg_map)
                builder = getattr(self, builder_name)
                return builder(left, right), left_deps | right_deps
        raise ValueError(
            f"Condition d'acceptation inconnue : '{spec}'. Vocabulaire accepte : "
            "tautology, contradiction, negation:<stmt>, or:<c1>,<c2>, and:<c1>,<c2>."
        )

    def _get_reasoner(self, semantics: str):
        if semantics not in self._reasoner_cache:
            if semantics not in self.REASONERS:
                raise ValueError(
                    f"Unknown ADF semantics: {semantics}. Available: {list(self.REASONERS.keys())}"
                )
            cls = jpype.JClass(self.REASONERS[semantics])
            # Adaptation locale : les reasoners ADF de 1.30 exigent un solveur.
            self._reasoner_cache[semantics] = cls(self._sat_solver())
        return self._reasoner_cache[semantics]

    # ------------------------------------------------------------------
    # Analyse
    # ------------------------------------------------------------------

    def analyze_adf(
        self,
        statements: List[str],
        acceptance_conditions: Dict[str, str],
        semantics: str = "grounded",
    ) -> Dict[str, Any]:
        """Analyze an ADF programmatically.

        Args:
            statements: List of statement names.
            acceptance_conditions: Dict mapping statement -> acceptance type
                ("tautology", "contradiction", "negation:other_stmt",
                "or:<c1>,<c2>", "and:<c1>,<c2>"). A statement absent from the
                mapping gets a tautological condition (always acceptable).
            semantics: Semantics to use.

        Returns:
            Dict with interpretations and statistics.
        """
        try:
            arg_map = {stmt: self.ADFArgument(stmt) for stmt in statements}

            # Mode `provided()` : les liens du graphe sont fournis explicitement
            # (mesure 2026-10-29 : en mode `eager`, le builder exige un lien
            # par argument cite, ou une LinkStrategy SAT).
            builder = self.ADF.builder().provided()

            parents = {}
            for stmt in statements:
                spec = acceptance_conditions.get(stmt, "tautology")
                condition, dependencies = self._parse_condition(spec, arg_map)
                builder.add(arg_map[stmt], condition)
                parents[stmt] = dependencies

            # Un argument cite par une condition d'acceptation est un parent
            # de l'argument conditionne : c'est ce lien qui porte la structure
            # du graphe ADF.
            for stmt, dependencies in parents.items():
                for dependency in sorted(dependencies):
                    builder.add(
                        self._Link.of(
                            arg_map[dependency],
                            arg_map[stmt],
                            self._LinkType.SUPPORTING,
                        )
                    )

            adf = builder.build()

            reasoner = self._get_reasoner(semantics)
            interpretations = reasoner.getModels(adf)

            interp_list = []
            detailed = []
            for interp in interpretations:
                interp_list.append(str(interp))
                detailed.append(
                    {
                        "text": str(interp),
                        "accepted": sorted(str(x) for x in interp.satisfied()),
                        "rejected": sorted(str(x) for x in interp.unsatisfied()),
                        "undecided": sorted(str(x) for x in interp.undecided()),
                    }
                )

            return {
                "semantics": semantics,
                "statements": sorted(statements),
                "interpretations": interp_list,
                "interpretations_detailed": detailed,
                "statistics": {
                    "statements_count": len(statements),
                    "conditions_count": len(acceptance_conditions),
                    "interpretations_count": len(interp_list),
                },
            }
        except jpype.JException as e:
            logger.error(f"Java exception in ADF analysis: {e}")
            raise RuntimeError(f"ADF analysis failed: {e}") from e

    def parse_adf_file(
        self, file_path: str, semantics: str = "grounded"
    ) -> Dict[str, Any]:
        """Parse an ADF from a KppADF format file and analyze it.

        NOT WIRED against the vendored Tweety 1.30 jar — honest gate-out, no
        workaround. Measured 2026-10-29:
        - the KPP reader constructor is `KppADFFormatParser(LinkStrategy,
          boolean)`; the upstream `KppParser()` call raises `TypeError: No
          matching overloads found`;
        - with the available `SatLinkStrategy`, reading the `adf_example.txt`
          shipped in the jar raises `java.util.EmptyStackException`.

        The programmatic path (`analyze_adf`) covers the same semantics and is
        the supported entry point.

        Args:
            file_path: Path to ADF file.
            semantics: Semantics to use.

        Returns:
            Dict with analysis results.
        """
        raise RuntimeError(
            "parse_adf_file n'est pas cable contre le jar Tweety 1.30 vende "
            "(KppADFFormatParser exige une LinkStrategy et un booleen ; la "
            "lecture du fichier d'exemple du jar echoue sur "
            "java.util.EmptyStackException). Utilisez analyze_adf, qui couvre "
            "les memes semantiques sur un cadre construit en Python."
        )
