#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/agents/core/logic/tweety_bridge.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: a8025f60 (2026-07-02).
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content below this header is byte-for-byte identical
# to the upstream source at the cited commit. No CoursIA modification.
#
# DEPENDENCY NOTICE : This module imports `jpype`, `jpype.imports`, and at
# module-level imports 12 logic handlers + `TweetyInitializer` from
# `argumentation_analysis.agents.core.logic.*` via lines 29-41 :
#
#     from .pl_handler import PLHandler as PropositionalLogicHandler
#     from .fol_handler import FOLHandler as FirstOrderLogicHandler
#     from .modal_handler import ModalHandler
#     from .af_handler import AFHandler as ArgumentationFrameworkHandler
#     from .ranking_handler import RankingHandler
#     from .bipolar_handler import BipolarHandler
#     from .aba_handler import ABAHandler
#     from .adf_handler import ADFHandler
#     from .aspic_handler import ASPICHandler
#     from .belief_revision_handler import BeliefRevisionHandler
#     from .probabilistic_handler import ProbabilisticHandler
#     from .dialogue_handler import DialogueHandler
#     from .tweety_initializer import TweetyInitializer
#
# None of these 13 sibling modules are vendored in `argumentation_lib/`
# today. Therefore this file is **NOT standalone-importable today** :
# even `from argumentation_lib._tweety_bridge import TweetyBridge` raises
# `ImportError` because the top-level `from .pl_handler import ...` cannot
# resolve `argumentation_analysis.agents.core.logic.pl_handler`.
#
# The class symbol import is safe (analysis-only). Runtime instantiation
# triggers the JPype dependency chain and will fail until Volet B etape 4
# sub-tranches C186b+ (12 handlers + tweety_initializer) land. The lazy
# accessor `argumentation_lib.get_tweety_bridge_symbol()` is preserved for
# API symmetry with C184 (`get_taxonomy_sophism_detector`) and C185
# (`get_informal_definitions_symbols`), and surfaces the current
# ImportError transparently.
#
# FORCE_RELOAD
# argumentation_analysis/agents/core/logic/tweety_bridge.py
"""
Ce module implémente le pont avec la bibliothèque Java TweetyProject en utilisant JPype.

Il est conçu comme un singleton pour garantir qu'une seule instance de la JVM est
démarrée et gérée tout au long de la vie de l'application. Le pont charge les
JARs nécessaires, configure la JVM et expose des handlers pour différentes
logiques (comme la logique propositionnelle ou la logique du premier ordre).

L'initialisation se fait via la méthode `initialize_jvm`.
"""

import jpype
from jpype import java
import jpype.imports
import logging
import os
import glob
import threading
import asyncio
from typing import Optional, Dict, List, Tuple, Any

# Importer les handlers de logique spécifiques
# Pour éviter les dépendances circulaires, on les importe et on les type-hint comme ça
from .pl_handler import PLHandler as PropositionalLogicHandler
from .fol_handler import FOLHandler as FirstOrderLogicHandler
from .modal_handler import ModalHandler
from .af_handler import AFHandler as ArgumentationFrameworkHandler
from .ranking_handler import RankingHandler
from .bipolar_handler import BipolarHandler
from .aba_handler import ABAHandler
from .adf_handler import ADFHandler
from .aspic_handler import ASPICHandler
from .belief_revision_handler import BeliefRevisionHandler
from .probabilistic_handler import ProbabilisticHandler
from .dialogue_handler import DialogueHandler
from .tweety_initializer import TweetyInitializer

logger = logging.getLogger(__name__)


class TweetyBridge:
    """
    Un pont singleton pour interagir avec la bibliothèque Java TweetyProject.
    Gère le cycle de vie de la JVM et fournit un accès aux fonctionnalités logiques.
    """

    _instance = None
    _lock = threading.Lock()  # Thread-safe lock for singleton creation (__new__)
    _async_lock: Optional["asyncio.Lock"] = None  # Async lock for JVM operations
    _jvm_started = False
    _jvm_path: Optional[str] = None

    # Handlers pour les différentes logiques. Initialisés avec la logique du pont.
    _pl_handler: Optional[PropositionalLogicHandler] = None
    _af_handler: Optional[ArgumentationFrameworkHandler] = None
    _fol_handler: Optional[FirstOrderLogicHandler] = None
    _modal_handler: Optional[ModalHandler] = None
    # Track A handlers (lazy-loaded)
    _ranking_handler: Optional[RankingHandler] = None
    _bipolar_handler: Optional[BipolarHandler] = None
    _aba_handler: Optional[ABAHandler] = None
    _adf_handler: Optional[ADFHandler] = None
    _aspic_handler: Optional[ASPICHandler] = None
    _belief_revision_handler: Optional[BeliefRevisionHandler] = None
    _probabilistic_handler: Optional[ProbabilisticHandler] = None
    _dialogue_handler: Optional[DialogueHandler] = None
    _qbf_handler: Optional[Any] = None  # QBFHandler (lazy-loaded)

    # Nouvel attribut pour l'initialiseur
    _initializer: Optional[TweetyInitializer] = None

    def __new__(cls, *args, **kwargs):
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super(TweetyBridge, cls).__new__(cls)
        return cls._instance

    def __init__(self, jar_directory: Optional[str] = None):
        """
        Initialise le pont. La JVM n'est pas démarrée ici, mais dans `initialize_jvm`.
        Les handlers sont chargés paresseusement (lazy-loaded) lors du premier accès.
        """
        if not hasattr(self, "_initialized"):
            self.jar_directory = jar_directory or self._find_default_jar_dir()
            self._initializer = TweetyInitializer(self)
            # L'initialisation de la JVM et des composants est maintenant gérée par une méthode unifiée
            self._initializer.ensure_jvm_and_components_are_ready()
            # Les handlers ne sont plus initialisés ici pour éviter les erreurs de JVM
            self._initialized = True

    def _find_default_jar_dir(self) -> str:
        """
        Trouve le répertoire des JARs par défaut, en supposant une structure de projet standard.
        Le répertoire 'libs/tweety/native' est recherché depuis le répertoire de ce script.
        """
        script_dir = os.path.dirname(__file__)
        # Le chemin relatif vers le répertoire des JARs natifs
        # argumentation_analysis/agents/core/logic/ -> argumentation_analysis/libs/tweety/native
        relative_jar_path = os.path.join(script_dir, "../../../..", "libs", "tweety")
        return os.path.normpath(relative_jar_path)

    @classmethod
    def get_instance(cls, jar_directory: Optional[str] = None) -> "TweetyBridge":
        """
        Méthode d'accès au singleton, avec initialisation si nécessaire.
        """
        if cls._instance is None:
            cls._instance = TweetyBridge(jar_directory)
        return cls._instance

    @property
    def pl_handler(self) -> PropositionalLogicHandler:
        """Retourne le handler pour la logique propositionnelle, en l'initialisant si nécessaire."""
        if not self.initializer.is_jvm_ready():
            raise RuntimeError(
                "La JVM n'est pas démarrée. Appelez initialize_jvm() en premier."
            )
        if self._pl_handler is None:
            logger.debug("Chargement paresseux (lazy-loading) du PLHandler.")
            self._pl_handler = PropositionalLogicHandler(self._initializer)
        return self._pl_handler

    @property
    def af_handler(self) -> ArgumentationFrameworkHandler:
        """Retourne le handler pour les frameworks d'argumentation, en l'initialisant si nécessaire."""
        if not self.initializer.is_jvm_ready():
            raise RuntimeError(
                "La JVM n'est pas démarrée. Appelez initialize_jvm() en premier."
            )
        if self._af_handler is None:
            logger.debug("Chargement paresseux (lazy-loading) du AFHandler.")
            self._af_handler = ArgumentationFrameworkHandler(self._initializer)
        return self._af_handler

    @property
    def modal_handler(self) -> ModalHandler:
        """Retourne le handler pour la logique modale, en l'initialisant si nécessaire."""
        if not self.initializer.is_jvm_ready():
            raise RuntimeError(
                "La JVM n'est pas démarrée. Appelez initialize_jvm() en premier."
            )
        if self._modal_handler is None:
            logger.debug("Chargement paresseux (lazy-loading) du ModalHandler.")
            self._modal_handler = ModalHandler(self._initializer)
        return self._modal_handler

    @property
    def initializer(self) -> TweetyInitializer:
        """Retourne l'initialiseur Tweety, qui gère le chargement des classes Java."""
        return self._initializer

    @property
    def fol_handler(self) -> FirstOrderLogicHandler:
        """Retourne le handler pour la logique du premier ordre, en l'initialisant si nécessaire."""
        if not self.initializer.is_jvm_ready():
            raise RuntimeError(
                "La JVM n'est pas démarrée. Appelez initialize_jvm() en premier."
            )
        if self._fol_handler is None:
            logger.debug("Chargement paresseux (lazy-loading) du FOLHandler.")
            self._fol_handler = FirstOrderLogicHandler(self._initializer)
        return self._fol_handler

    # ============================================================================
    # Track A handlers — lazy-loaded properties
    # ============================================================================

    @property
    def ranking_handler(self) -> RankingHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._ranking_handler is None:
            self._ranking_handler = RankingHandler(self._initializer)
        return self._ranking_handler

    @property
    def bipolar_handler(self) -> BipolarHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._bipolar_handler is None:
            self._bipolar_handler = BipolarHandler(self._initializer)
        return self._bipolar_handler

    @property
    def aba_handler(self) -> ABAHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._aba_handler is None:
            self._aba_handler = ABAHandler(self._initializer)
        return self._aba_handler

    @property
    def adf_handler(self) -> ADFHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._adf_handler is None:
            self._adf_handler = ADFHandler(self._initializer)
        return self._adf_handler

    @property
    def aspic_handler(self) -> ASPICHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._aspic_handler is None:
            self._aspic_handler = ASPICHandler(self._initializer)
        return self._aspic_handler

    @property
    def belief_revision_handler(self) -> BeliefRevisionHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._belief_revision_handler is None:
            self._belief_revision_handler = BeliefRevisionHandler(self._initializer)
        return self._belief_revision_handler

    @property
    def probabilistic_handler(self) -> ProbabilisticHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._probabilistic_handler is None:
            self._probabilistic_handler = ProbabilisticHandler(self._initializer)
        return self._probabilistic_handler

    @property
    def dialogue_handler(self) -> DialogueHandler:
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._dialogue_handler is None:
            self._dialogue_handler = DialogueHandler(self._initializer)
        return self._dialogue_handler

    @property
    def qbf_handler(self):
        """QBF (Quantified Boolean Formulas) handler — lazy-loaded."""
        if not self.initializer.is_jvm_ready():
            raise RuntimeError("JVM not started.")
        if self._qbf_handler is None:
            from .qbf_handler import QBFHandler

            self._qbf_handler = QBFHandler(self._initializer)
        return self._qbf_handler

    # ============================================================================
    # Compatibility wrappers for backward compatibility with agents
    # Added to fix regression from commit f2754578
    # These methods delegate to the specialized handlers while maintaining
    # the original API that agents depend on
    # ============================================================================

    def execute_pl_query(self, belief_set: str, query: str) -> Tuple[bool, str]:
        """Backward compatibility wrapper for execute_pl_query."""
        return self.pl_handler.execute_pl_query(belief_set, query)

    def execute_fol_query(self, belief_set: str, query: str) -> Tuple[bool, str]:
        """Backward compatibility wrapper for execute_fol_query."""
        return self.fol_handler.execute_fol_query(belief_set, query)

    def execute_modal_query(
        self, belief_set: str, query: str, logic_type: str = "K"
    ) -> Tuple[bool, str]:
        """Backward compatibility wrapper for execute_modal_query.

        #1192: the underlying ``ModalHandler.execute_modal_query`` takes only
        ``(belief_set, query)`` (the reasoner is selected globally via
        ``settings.modal_solver``, not per-call). The previous call passed
        ``logic_type`` as a third positional arg → ``TypeError`` on every
        modal query. Drop it here rather than adding an unused parameter to
        the handler (anti-pendule: subtract the mismatch).
        """
        _ = logic_type  # accepted for API compatibility; handler is reasoner-global
        result_str = self.modal_handler.execute_modal_query(belief_set, query)
        # Handler returns a descriptive string; parse ACCEPTED/REJECTED/FUNC_ERROR.
        if isinstance(result_str, str):
            if "ACCEPTED" in result_str:
                return True, result_str
            if "REJECTED" in result_str:
                return False, result_str
            return False, result_str  # FUNC_ERROR or unexpected
        return bool(result_str), str(result_str)

    def check_consistency(
        self, belief_set: str, logic_type: str = "propositional"
    ) -> Tuple[bool, str]:
        """Backward compatibility wrapper for check_consistency.

        #1192: ``ModalHandler`` exposes ``is_modal_kb_consistent`` (not
        ``check_consistency``); the previous dispatch raised
        ``AttributeError`` for K/T/S4/S5. Route modal consistency to the
        existing method.
        """
        if logic_type == "propositional":
            return self.pl_handler.check_consistency(belief_set)
        elif logic_type == "first_order":
            return self.fol_handler.check_consistency(belief_set)
        elif logic_type in ["K", "T", "S4", "S5"]:
            return self.modal_handler.is_modal_kb_consistent(belief_set)
        else:
            return False, f"Unknown logic type: {logic_type}"

    def check_consistency_detailed(
        self, belief_set: str, logic_type: str = "propositional"
    ) -> Tuple[bool, Optional[dict], str]:
        """Consistency verdict that also returns the real solver witness.

        #1208 (FP-10): the plain ``check_consistency`` returns only ``(bool,
        str)`` and the message string is where the SAT model was buried (and
        then dropped by the caller). This returns the structured named model
        so the PL invoke-callable persists the genuine PySAT assignment
        instead of fabricating ``{p1: True, p2: True}`` (silent loss of a
        real decision, #1019). Currently supported for propositional logic;
        other logic types fall back to ``(bool, None, msg)``.
        """
        if logic_type == "propositional":
            return self.pl_handler.check_consistency_detailed(belief_set)
        is_consistent, msg = self.check_consistency(belief_set, logic_type)
        return is_consistent, None, msg

    async def compare_fol_backends(self, belief_set: str) -> dict:
        """Run every available FOL backend on the same KB and compare verdicts.

        FP-19 #1243 thin wrapper over ``FOLHandler.compare_fol_backends`` so the
        orchestration layer can request a multi-prover cross-validation without
        reaching into the handler. DISAGREEMENT is surfaced, never reconciled.
        """
        return await self.fol_handler.compare_fol_backends(belief_set)

    async def compare_pl_backends(self, belief_set: str) -> dict:
        """Run every available PL/SAT backend on the same KB and compare verdicts.

        FP-20 #1244 thin wrapper over ``PLHandler.compare_pl_backends`` so the
        orchestration layer can request a multi-prover cross-validation without
        reaching into the handler. DISAGREEMENT is surfaced, never reconciled.
        """
        return await self.pl_handler.compare_pl_backends(belief_set)

    async def wait_for_jvm(self, timeout: int = 30) -> None:
        """Attend de manière asynchrone que la JVM soit prête."""
        if TweetyInitializer.is_jvm_ready():
            return

        waited_time = 0
        while not TweetyInitializer.is_jvm_ready() and waited_time < timeout:
            await asyncio.sleep(0.5)
            waited_time += 0.5

        if not TweetyInitializer.is_jvm_ready():
            raise TimeoutError(
                f"La JVM n'a pas démarré dans le temps imparti de {timeout} secondes."
            )

    @classmethod
    def _get_async_lock(cls) -> "asyncio.Lock":
        """
        Get or create the asyncio.Lock for async JVM operations.
        Must be called from an async context (requires running event loop).
        """
        if cls._async_lock is None:
            cls._async_lock = asyncio.Lock()
        return cls._async_lock

    async def async_initialize_jvm(self, jvm_path: Optional[str] = None) -> None:
        """
        Async version of initialize_jvm using asyncio.Lock.
        Prevents concurrent JVM startup in async contexts without blocking the event loop.
        """
        async with self._get_async_lock():
            # Delegate to sync method (which has its own threading.Lock for actual JVM start)
            self.initialize_jvm(jvm_path)

    async def async_shutdown_jvm(self) -> None:
        """
        Async version of shutdown_jvm using asyncio.Lock.
        Prevents concurrent JVM shutdown in async contexts.
        """
        async with self._get_async_lock():
            self.shutdown_jvm()

    def set_jvm_path(self, jvm_path: str):
        """Définit manuellement le chemin vers la bibliothèque de la JVM (dll, so, etc.)."""
        self._jvm_path = jvm_path
        logger.info(f"Chemin de la JVM défini manuellement sur : {jvm_path}")

    def initialize_jvm(self, jvm_path: Optional[str] = None) -> None:
        """
        Démarre la JVM avec les JARs du répertoire spécifié.
        Cette méthode est bloquante et peut prendre du temps.
        """
        with self._lock:  # Utilise un verrou pour éviter le démarrage concurrent de la JVM
            if TweetyInitializer.is_jvm_ready():
                logger.warning(
                    "La JVM est déjà démarrée. L'appel d'initialisation est ignoré."
                )
                return

            effective_jvm_path = jvm_path or self._jvm_path or jpype.getDefaultJVMPath()
            logger.info(
                f"Tentative de démarrage de la JVM avec le chemin : {effective_jvm_path}"
            )

            try:
                jar_paths = glob.glob(os.path.join(self.jar_directory, "*.jar"))
                if not jar_paths:
                    raise IOError(
                        f"Aucun fichier .jar trouvé dans le répertoire : {self.jar_directory}"
                    )

                classpath = os.pathsep.join(jar_paths)
                logger.info(f"Classpath configuré avec {len(jar_paths)} JARs.")

                jpype.startJVM(
                    effective_jvm_path,
                    "-ea",  # Enable assertions
                    f"-Djava.class.path={classpath}",
                    convertStrings=False,
                )
                TweetyBridge._jvm_started = True
                logger.info("La JVM a démarré avec succès.")

                # Une fois la JVM démarrée, on peut charger les classes
                self._initializer.import_java_classes()

            except (Exception, jpype.JException) as e:
                logger.error(
                    f"Échec du démarrage de la JVM avec le chemin '{effective_jvm_path}'. Erreur : {e}",
                    exc_info=True,
                )
                TweetyBridge._jvm_started = False
                # Propage l'exception pour que les appelants sachent que l'initialisation a échoué.
                raise RuntimeError("Échec de l'initialisation de la JVM.") from e

    def shutdown_jvm(self):
        """Arrête la JVM si elle est en cours d'exécution."""
        with self._lock:
            if TweetyInitializer.is_jvm_ready():
                # shutdown_jvm est maintenant géré de manière centralisée
                from argumentation_analysis.core.jvm_setup import shutdown_jvm

                shutdown_jvm()
                self._jvm_started = False
                logger.info("La JVM a été arrêtée via le gestionnaire centralisé.")

    def validate_pl_formula(self, formula: str) -> bool:
        """Valide la syntaxe d'une formule de logique propositionnelle en tentant de la parser."""
        try:
            # La validation se fait en tentant un parsing. Si ça ne lève pas d'erreur, c'est valide.
            self.pl_handler.parse_pl_formula(formula)
            return True
        except ValueError:
            return False

    def pl_query(self, knowledge_base: str, query: str) -> Optional[bool]:
        """
        Exécute une requête en logique propositionnelle.
        Retourne True si la KB entraîne la requête, False sinon, ou None en cas d'erreur.
        """
        return self.pl_handler.pl_query(knowledge_base, query)

    def create_pl_belief_base_from_string(
        self, formula_string: str
    ) -> Optional["java.lang.Object"]:
        """Crée un objet PlBeliefSet Java à partir d'une chaîne."""
        return self.pl_handler.create_belief_base_from_string(formula_string)

    @staticmethod
    def get_tweety_project_version() -> str:
        """
        Récupère la version de TweetyProject à partir du nom d'un des fichiers JAR.
        Suppose un format de nommage comme 'tweetyproject-1.2.3.jar'.
        """
        bridge = TweetyBridge.get_instance()
        try:
            jar_paths = glob.glob(
                os.path.join(bridge.jar_directory, "tweetyproject-*.jar")
            )
            if jar_paths:
                filename = os.path.basename(jar_paths[0])
                # Extrait la version, par ex. de 'tweetyproject-2.0.jar'
                version = filename.replace("tweetyproject-", "").replace(".jar", "")
                return version
        except Exception as e:
            logger.warning(f"Impossible d'extraire la version de TweetyProject : {e}")
        return "Version inconnue"
