# -*- coding: utf-8 -*-
"""
Tests for Lean Game Theory Definitions
======================================

Tests the Lean code in lean_game_defs/ using lean_runner.py
when available, or just validates file structure otherwise.
"""

import os
import sys
import unittest
from pathlib import Path

# Add parent directory for imports
GAMETHEORY_DIR = Path(__file__).parent.parent
sys.path.insert(0, str(GAMETHEORY_DIR))

# Try to import lean_runner from Lean series
LEAN_DIR = GAMETHEORY_DIR.parent / "SymbolicAI" / "Lean"
sys.path.insert(0, str(LEAN_DIR))

try:
    from lean_runner import LeanRunner
    HAS_LEAN_RUNNER = True
except ImportError:
    HAS_LEAN_RUNNER = False

# Lean files to test
LEAN_FILES = [
    "lean_game_defs/Basic.lean",
    "lean_game_defs/Nash.lean",
    "lean_game_defs/Combinatorial.lean",
    "lean_game_defs/SocialChoice.lean",
]


class TestLeanFilesExist(unittest.TestCase):
    """Test that all Lean files exist."""

    def test_lean_files_exist(self):
        """Check that all Lean definition files are present."""
        for lean_file in LEAN_FILES:
            path = GAMETHEORY_DIR / lean_file
            self.assertTrue(
                path.exists(),
                f"Missing Lean file: {lean_file}"
            )

    def test_lean_files_not_empty(self):
        """Check that Lean files have content."""
        for lean_file in LEAN_FILES:
            path = GAMETHEORY_DIR / lean_file
            if path.exists():
                content = path.read_text(encoding='utf-8')
                self.assertGreater(
                    len(content), 100,
                    f"Lean file appears empty: {lean_file}"
                )


class TestLeanBasicContent(unittest.TestCase):
    """Test that Lean files contain expected definitions."""

    def test_basic_lean_has_game_structure(self):
        """Check Basic.lean defines Game structures."""
        path = GAMETHEORY_DIR / "lean_game_defs" / "Basic.lean"
        content = path.read_text(encoding='utf-8')

        self.assertIn("NormalFormGame", content)
        self.assertIn("FiniteGame", content)
        self.assertIn("Game2x2", content)
        self.assertIn("payoff", content)

    def test_nash_lean_has_equilibrium(self):
        """Check Nash.lean defines Nash equilibrium."""
        path = GAMETHEORY_DIR / "lean_game_defs" / "Nash.lean"
        content = path.read_text(encoding='utf-8')

        self.assertIn("isNashEquilibrium", content)
        self.assertIn("isPureNashEquilibrium", content)
        self.assertIn("isBestResponse", content)
        self.assertIn("prisonersDilemma", content)

    def test_combinatorial_lean_has_pgame_concepts(self):
        """Check Combinatorial.lean has game tree concepts."""
        path = GAMETHEORY_DIR / "lean_game_defs" / "Combinatorial.lean"
        content = path.read_text(encoding='utf-8')

        self.assertIn("GameTree", content)
        self.assertIn("NimPosition", content)
        self.assertIn("grundy", content.lower())

    def test_social_choice_lean_has_arrow(self):
        """Check SocialChoice.lean has Arrow's theorem concepts."""
        path = GAMETHEORY_DIR / "lean_game_defs" / "SocialChoice.lean"
        content = path.read_text(encoding='utf-8')

        self.assertIn("Preference", content)
        self.assertIn("SocialWelfareFunction", content)
        self.assertIn("Pareto", content)
        self.assertIn("IIA", content)
        self.assertIn("arrow", content.lower())


@unittest.skipIf(not HAS_LEAN_RUNNER, "lean_runner.py not available")
class TestLeanExecution(unittest.TestCase):
    """Test Lean code execution using lean_runner.py."""

    @classmethod
    def setUpClass(cls):
        """Initialize Lean runner."""
        cls.runner = LeanRunner(backend='auto')

    @classmethod
    def tearDownClass(cls):
        """Cleanup runner."""
        if hasattr(cls, 'runner'):
            cls.runner.cleanup()

    def test_basic_lean_compiles(self):
        """Test that basic Lean definitions compile."""
        code = '''
        -- Test basic game structure
        structure TestGame where
          players : Nat
          payoff : Fin players → Int

        #check TestGame

        def simpleGame : TestGame := {
          players := 2
          payoff := fun i => if i.val == 0 then 1 else -1
        }

        #eval simpleGame.players
        '''
        result = self.runner.run(code)
        self.assertTrue(
            result.success,
            f"Basic Lean code failed: {result.errors}"
        )

    def test_nash_definition_compiles(self):
        """Test Nash equilibrium definition compiles."""
        # Note: avoid apostrophes in variable names (a1' -> a1alt) for WSL shell compatibility
        # Use And instead of /\ which is interpreted as division
        code = '''
        -- Simplified Nash equilibrium check
        structure Game2x2 where
          payoff1 : Fin 2 -> Fin 2 -> Int
          payoff2 : Fin 2 -> Fin 2 -> Int

        def isPureNash (g : Game2x2) (a1 a2 : Fin 2) : Prop :=
          And (forall a1alt : Fin 2, g.payoff1 a1 a2 >= g.payoff1 a1alt a2)
              (forall a2alt : Fin 2, g.payoff2 a1 a2 >= g.payoff2 a1 a2alt)

        #check @isPureNash
        '''
        result = self.runner.run(code)
        self.assertTrue(
            result.success,
            f"Nash definition failed: {result.errors}"
        )


class TestExamplesExist(unittest.TestCase):
    """Test that example files exist."""

    EXAMPLES = [
        "examples/prisoners_dilemma.py",
        "examples/topology_2x2_periodic_table.py",
        "examples/centipede_game.py",
        "examples/stag_hunt_forward_induction.py",
        "examples/kuhn_poker_cfr.py",
        "examples/stackelberg_leader_follower.py",
        "examples/vcg_auction.py",
        "examples/arrow_simple.lean",
    ]

    def test_examples_exist(self):
        """Check all example files are present."""
        for example in self.EXAMPLES:
            path = GAMETHEORY_DIR / example
            self.assertTrue(
                path.exists(),
                f"Missing example: {example}"
            )


if __name__ == "__main__":
    unittest.main(verbosity=2)
