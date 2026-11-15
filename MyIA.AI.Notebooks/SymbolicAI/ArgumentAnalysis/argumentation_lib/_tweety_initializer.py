# Copyright (c) 2025 jsboigeEpita
# SPDX-License-Identifier: MIT
#
# VERBATIM PORT -- EPITA-IS upstream a8025f60 (CONV-C PM eclaire PR #1345).
# Source : https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique
#          argumentation_analysis/agents/core/logic/tweety_initializer.py
# License: MIT (Copyright (c) 2025 jsboigeEpita)
#          See https://opensource.org/licenses/MIT
#
# Verbatim integrity: full file SHA1 below must equal upstream RAW bytes SHA1.
#
# DEPENDENCY NOTICE (G.9 honest caveat -- verbatim upstream imports):
#   This file ships 3 EPITA-IS-internal sibling imports that are NOT vendored
#   in argumentation_lib/:
#     L11: from argumentation_analysis.core.utils.logging_utils import setup_logging
#     L14-17: from argumentation_analysis.core.jvm_setup import (
#                initialize_jvm as initialize_jvm_robustly,
#              )
#             from argumentation_analysis.core.jvm_setup import shutdown_jvm, is_jvm_started
#   Therefore this module is NOT standalone-importable today. Even the
#   module-level `import argumentation_lib._tweety_initializer` will fail with
#   `ModuleNotFoundError: No module named 'argumentation_analysis'` until the
#   upstream logging_utils.py + jvm_setup.py modules are vendored in a
#   later tranche of the EPIC #4960 chain.
#
#   This is the G.9 honest fingerprint of a verbatim upstream port: the upstream
#   code imports upstream siblings, and the CoursIA vendoring does not yet
#   match. The lazy accessor `get_tweety_initializer_symbol()` in __init__.py
#   preserves the class symbol path without triggering the module-level
#   import-time failure.
#
#   Anti-pendule / anti-regression: 0 `pass`, 0 `return None`, 0 stub bodies,
#   0 NotImplementedError introduced. The verbatim block is byte-for-byte
#   identical to upstream a8025f60. Only an MIT attribution header (the block
#   above) was prepended.

# argumentation_analysis/agents/core/logic/tweety_initializer.py
"""
Gestionnaire d'initialisation pour les composants Tweety.
Ce module suppose que la JVM a déjà été démarrée et configurée par un
gestionnaire externe (ex: une fixture pytest de session).
"""

import jpype
import logging
import os
from argumentation_analysis.core.utils.logging_utils import setup_logging

# On importe directement la fonction d'initialisation robuste
from argumentation_analysis.core.jvm_setup import (
    initialize_jvm as initialize_jvm_robustly,
)
from argumentation_analysis.core.jvm_setup import shutdown_jvm, is_jvm_started

logger = logging.getLogger(__name__)


class TweetyInitializer:
    """
    Handles the initialization of JVM and components for TweetyProject.
    The JVM lifecycle is now managed by the central jvm_setup.py module.
    This class acts as a central point for initialization logic and component access.
    """

    _classes_loaded = False
    _pl_parser = None
    _fol_parser = None
    _modal_parser = None
    _modal_reasoner = None
    _af_parser = None  # Ajout pour le parser d'argumentation
    _initialized_components = False
    _jvm_started = False

    # FOL classes (will be populated by _import_java_classes)
    FolBeliefSet = None
    FolSignature = None
    Sort = None
    Constant = None
    Predicate = None
    FolFormula = None
    FolAtom = None
    ForallQuantifiedFormula = None
    ExistsQuantifiedFormula = None
    Variable = None
    Implication = None
    Conjunction = None
    Negation = None

    def __init__(self, tweety_bridge_instance=None):
        if tweety_bridge_instance:
            self._tweety_bridge = tweety_bridge_instance

    def ensure_jvm_and_components_are_ready(self):
        """
        Garantit que la JVM est démarrée ET que les classes Java de Tweety sont chargées.
        Cette méthode gère le cas spécial où les tests sont exécutés via pytest.
        """
        if self.__class__._initialized_components:
            logger.debug("Les composants JVM et Tweety sont déjà prêts.")
            return

        if os.environ.get("DISABLE_JAVA_LOGIC") == "1":
            logger.info(
                "Java logic is disabled. Skipping all JVM and component initialization."
            )
            return

        # Étape 1: Démarrer la JVM si nécessaire
        if not is_jvm_started():
            is_pytest_running = os.environ.get("PYTEST_RUNNING") == "1"
            if is_pytest_running:
                # Dans un contexte de test, une fixture est responsable du démarrage de la JVM.
                # Si elle n'est pas démarrée à ce stade, c'est une erreur de configuration du test.
                msg = "Pytest is running, but the JVM is not started. A fixture like 'jvm_fixture' must be used."
                logger.error(msg)
                raise RuntimeError(msg)
            else:
                # Contexte normal (hors test), on démarre la JVM nous-mêmes.
                logger.info("JVM not started. Calling the robust initializer.")
                if not self.initialize_jvm():
                    raise RuntimeError(
                        "Échec du démarrage de la JVM par l'initialiseur robuste."
                    )

        self.__class__._jvm_started = True

        # Étape 2: Charger les classes et initialiser les composants
        # Cette étape doit se produire dans tous les cas si elle n'a pas été faite.
        if not self.__class__._initialized_components:
            logger.info(
                "JVM is running. Initializing Java class imports and components for the first time."
            )
            self._import_java_classes()
            self.initialize_pl_components()
            self.initialize_fol_components()
            self.initialize_modal_components()
            self.initialize_af_components()
            self.__class__._initialized_components = True
            logger.info("Java components initialized successfully.")
        else:
            logger.debug("Java components were already initialized.")

    @staticmethod
    def initialize_jvm():
        """
        Delegates JVM initialization to the robust, centralized jvm_setup.py script.
        This script handles JDK provisioning (download, unzip) and proper JVM startup.
        """
        logger.info("Delegating JVM initialization to core.jvm_setup.initialize_jvm...")
        try:
            # On appelle la fonction renommée pour plus de clarté
            if initialize_jvm_robustly():
                logger.info("Robust JVM initialization successful.")
                TweetyInitializer._jvm_started = True
                return True
            else:
                logger.error("Robust JVM initialization failed.")
                return False
        except Exception as e:
            logger.critical(
                f"An unhandled exception occurred during robust JVM initialization: {e}",
                exc_info=True,
            )
            return False

    def load_classes(self):
        """
        Public method to explicitly trigger the import of Java classes.
        """
        if not self.__class__._classes_loaded:
            logger.info("Explicitly loading Java classes...")
            self._import_java_classes()
        else:
            logger.debug("Java classes already loaded.")

    def initialize_components(self):
        """
        Public method to explicitly initialize parsers and other components.
        """
        if not self.__class__._initialized_components:
            logger.info("Explicitly initializing Java components (parsers, etc.)...")
            self.initialize_pl_components()
            self.initialize_fol_components()
            self.initialize_modal_components()
            self.initialize_af_components()
            self.__class__._initialized_components = True
        else:
            logger.debug("Java components already initialized.")

    def _import_java_classes(self):
        """
        Imports and caches required Java classes.
        Raises RuntimeError if a class is not found, indicating a classpath issue.
        """
        logger.info("Importation des classes Java de TweetyProject...")
        try:
            # PL Classes
            jpype.JClass("org.tweetyproject.logics.pl.syntax.PlSignature")
            jpype.JClass("org.tweetyproject.logics.pl.syntax.Proposition")
            jpype.JClass("org.tweetyproject.logics.pl.syntax.PlBeliefSet")
            jpype.JClass("org.tweetyproject.logics.pl.reasoner.SatReasoner")
            jpype.JClass("org.tweetyproject.logics.pl.sat.Sat4jSolver")

            # FOL Classes
            TweetyInitializer.FolBeliefSet = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.FolBeliefSet"
            )
            TweetyInitializer.FolSignature = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.FolSignature"
            )
            TweetyInitializer.FolFormula = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.FolFormula"
            )
            TweetyInitializer.FolAtom = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.FolAtom"
            )
            TweetyInitializer.ForallQuantifiedFormula = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.ForallQuantifiedFormula"
            )
            TweetyInitializer.ExistsQuantifiedFormula = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.ExistsQuantifiedFormula"
            )
            TweetyInitializer.Variable = jpype.JClass(
                "org.tweetyproject.logics.commons.syntax.Variable"
            )
            TweetyInitializer.Predicate = jpype.JClass(
                "org.tweetyproject.logics.commons.syntax.Predicate"
            )

            # Common Classes
            TweetyInitializer.Sort = jpype.JClass(
                "org.tweetyproject.logics.commons.syntax.Sort"
            )
            TweetyInitializer.Constant = jpype.JClass(
                "org.tweetyproject.logics.commons.syntax.Constant"
            )
            TweetyInitializer.Implication = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.Implication"
            )
            TweetyInitializer.Conjunction = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.Conjunction"
            )
            TweetyInitializer.Negation = jpype.JClass(
                "org.tweetyproject.logics.fol.syntax.Negation"
            )
            jpype.JClass("org.tweetyproject.commons.ParserException")

            # Modal classes
            _ = jpype.JClass("org.tweetyproject.logics.ml.syntax.MlFormula")
            _ = jpype.JClass("org.tweetyproject.logics.ml.syntax.MlBeliefSet")
            _ = jpype.JClass("org.tweetyproject.logics.ml.reasoner.SimpleMlReasoner")
            _ = jpype.JClass("org.tweetyproject.logics.ml.parser.MlParser")
            _ = jpype.JClass("org.tweetyproject.commons.Signature")

            # Argumentation Framework Classes
            jpype.JClass("org.tweetyproject.arg.dung.syntax.DungTheory")
            jpype.JClass("org.tweetyproject.arg.dung.syntax.Argument")
            jpype.JClass("org.tweetyproject.arg.dung.syntax.Attack")
            jpype.JClass(
                "org.tweetyproject.arg.dung.reasoner.AbstractExtensionReasoner"
            )
            jpype.JClass("org.tweetyproject.arg.dung.reasoner.SimplePreferredReasoner")
            jpype.JClass("org.tweetyproject.arg.dung.semantics.Extension")
            jpype.JClass("org.tweetyproject.arg.dung.parser.FileFormat")

            # Reasoner (using EProver, not Prover9)
            jpype.JClass("org.tweetyproject.logics.fol.reasoner.SimpleFolReasoner")

            logger.info("Successfully imported and cached TweetyProject Java classes.")
            TweetyInitializer._classes_loaded = True

        except jpype.JException as e:
            logger.error(
                f"A Java exception occurred during class import: {e.stacktrace()}",
                exc_info=True,
            )
            java_system = jpype.JClass("java.lang.System")
            actual_classpath = java_system.getProperty("java.class.path")
            logger.error(f"Classpath at time of error: {actual_classpath}")
            raise RuntimeError(f"Java class import failed: {e}") from e
        except Exception as e:
            logger.error(
                f"A Python exception occurred during class import: {e}", exc_info=True
            )
            raise RuntimeError(
                f"A non-Java exception occurred during class import: {e}"
            ) from e

    def initialize_pl_components(self):
        if self.__class__._pl_parser:
            return
        try:
            logger.debug("Initializing PL components...")
            self.__class__._pl_parser = jpype.JClass(
                "org.tweetyproject.logics.pl.parser.PlParser"
            )()
            logger.info("PL parser initialized.")
        except Exception as e:
            logger.error(f"Error initializing PL components: {e}", exc_info=True)
            raise

    def initialize_fol_components(self):
        if self.__class__._fol_parser:
            return
        try:
            logger.debug("Initializing FOL components...")
            self.__class__._fol_parser = jpype.JClass(
                "org.tweetyproject.logics.fol.parser.FolParser"
            )()
            logger.info("FOL parser initialized.")
        except Exception as e:
            logger.error(f"Error initializing FOL components: {e}", exc_info=True)
            raise

    def initialize_modal_components(self):
        if self.__class__._modal_parser:
            return
        try:
            logger.debug("Initializing Modal Logic components...")
            self.__class__._modal_parser = jpype.JClass(
                "org.tweetyproject.logics.ml.parser.MlParser"
            )()
            self.__class__._modal_reasoner = jpype.JClass(
                "org.tweetyproject.logics.ml.reasoner.SimpleMlReasoner"
            )()
            logger.info("Modal Logic parser and reasoner initialized.")
        except Exception as e:
            logger.error(
                f"Error initializing Modal Logic components: {e}", exc_info=True
            )
            raise

    def initialize_af_components(self):
        if self.__class__._af_parser:
            return
        try:
            logger.debug("Initializing AF components...")
            # Tweety ne semble pas avoir de parser simple pour les AFs comme pour PL/FOL.
            # La construction se fait souvent manuellement. On met un placeholder.
            self.__class__._af_parser = True
            logger.info("AF components initialized (placeholder).")
        except Exception as e:
            logger.error(f"Error initializing AF components: {e}", exc_info=True)
            raise

    @staticmethod
    def get_pl_parser():
        if not TweetyInitializer._pl_parser:
            raise RuntimeError("PL Parser not initialized.")
        return TweetyInitializer._pl_parser

    @staticmethod
    def get_fol_parser():
        if not TweetyInitializer._fol_parser:
            raise RuntimeError("FOL Parser not initialized.")
        return TweetyInitializer._fol_parser

    @staticmethod
    def get_modal_parser():
        if not TweetyInitializer._modal_parser:
            raise RuntimeError("Modal Parser not initialized.")
        return TweetyInitializer._modal_parser

    @staticmethod
    def get_modal_reasoner():
        if not TweetyInitializer._modal_reasoner:
            raise RuntimeError("Modal Reasoner not initialized.")
        return TweetyInitializer._modal_reasoner

    @staticmethod
    def get_reasoner(reasoner_name: str):
        """
        Returns a Tweety reasoner instance by name.

        Supported names: SimpleFolReasoner, SimplePlReasoner
        """
        if not TweetyInitializer._classes_loaded:
            raise RuntimeError("Tweety classes not loaded. Ensure JVM is initialized.")
        try:
            if reasoner_name == "SimpleFolReasoner":
                ReasonerClass = jpype.JClass(
                    "org.tweetyproject.logics.fol.reasoner.SimpleFolReasoner"
                )
            elif reasoner_name == "SimplePlReasoner":
                ReasonerClass = jpype.JClass(
                    "org.tweetyproject.logics.pl.reasoner.SimplePlReasoner"
                )
            else:
                raise ValueError(f"Unknown reasoner: {reasoner_name}")
            return ReasonerClass()
        except Exception as e:
            logger.error(f"Failed to create reasoner '{reasoner_name}': {e}")
            raise

    @staticmethod
    def is_jvm_ready() -> bool:
        """Checks if the JVM is started and classes are loaded."""
        return is_jvm_started() and TweetyInitializer._classes_loaded

    def is_jvm_started(self) -> bool:
        return self.__class__._jvm_started
