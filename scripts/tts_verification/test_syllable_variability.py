#!/usr/bin/env python3
"""Test de non-régression — variabilité du compte de syllabes (#11682).

Le fondateur body de #11682 documente que 5 fichiers de durées différentes
rendaient tous exactement 120 syllabes au run du 2026-08-16, ce qui a fait
écrire à ai-01 « une constante là où on attend une variable ». Sur signaux
synthétiques propres, l'instrument VARIÉ correctement (15 syll / 45 syll
mesurés sur 5s / 15s). Ce test ferme la classe d'incidents :

* 2 fichiers synthétiques varied de 5s et 15s doivent rendre des comptes
  de syllabes significativement différents. Si un module en service rend
  le même compte sur deux entrées de tailles 3× différentes, c'est un
  retour de la classe « l'instrument plafonne / reboucle / mesure le
  mauvais buffer ».

Le test est **rouge avant le fix** : un module qui rend 120 pour les
deux échoue ; un module qui varie passe.

Dépendances : librosa + soundfile (miniconda base). Le test ajoute le
``prosody_lab`` au sys.path comme ``verify_prosody._default_lab_dir``
le fait déjà.
"""
from __future__ import annotations

import os
import sys
import tempfile
import unittest
from pathlib import Path

import numpy as np
import soundfile as sf

REPO_ROOT = Path(__file__).resolve().parents[2]
LAB = REPO_ROOT / "MyIA.AI.Notebooks" / "GenAI" / "Audio" / "04-Applications" / "v4" / "prosody_lab"
sys.path.insert(0, str(LAB))

import syllable_pitch as sp  # noqa: E402


def _synth_varied(duration_s: float, syll_per_s: float = 3.0, seed: int = 42) -> tuple:
    """Build a varied (expressivity) synthetic signal of the given duration.

    Uses a deterministic cycle over the [-8, +12] semitone range around A2
    so the pitch contour has structure (not noise). The point is to have
    a signal whose syllable count is set by ``syll_per_s * duration_s``,
    not by some accidental ceiling.
    """
    import random
    n_syll = max(int(duration_s * syll_per_s), 2)
    rng = random.Random(seed)
    seq = [45 + rng.randrange(-8, 13) for _ in range(n_syll)]
    return sp._synth(seq, syll_per_s=syll_per_s)


class TestSyllableVariability(unittest.TestCase):
    """Two clips of different durations must render different n_syllables."""

    def test_short_and_long_varied_render_different_counts(self):
        with tempfile.TemporaryDirectory(prefix="sylltest_variability_") as tmp:
            # 5s varied — expected ~15 syll
            y_short, sr = _synth_varied(5.0)
            wav_short = os.path.join(tmp, "short_varied.wav")
            sf.write(wav_short, y_short, sr)

            # 15s varied — expected ~45 syll (3x longer)
            y_long, sr = _synth_varied(15.0)
            wav_long = os.path.join(tmp, "long_varied.wav")
            sf.write(wav_long, y_long, sr)

            a_short = sp.analyze_syllables(wav_short)
            a_long = sp.analyze_syllables(wav_long)

            # The acceptance check: a 3x duration ratio MUST produce a
            # noticeably different syllable count. We allow a +-20% slop
            # because nucleus detection is heuristic, but the ratio
            # between the two counts must be at least 2.0 (15 / 5 = 3,
            # and we'd flag a module that halves or holds the count).
            n_short = a_short["n_syllables"]
            n_long = a_long["n_syllables"]
            self.assertGreater(n_short, 0,
                f"short clip rendered 0 syllables ({a_short})")
            self.assertGreater(n_long, 0,
                f"long clip rendered 0 syllables ({a_long})")
            ratio = n_long / n_short
            self.assertGreater(
                ratio, 2.0,
                f"variability regressed: short={n_short} syll, long={n_long} syll "
                f"(ratio={ratio:.2f}, expected >=2.0 for 3x duration). "
                f"This is the exact bug class #11682: a constant value where "
                f"the audio varies.",
            )

            # Bonus check: module_sha is present in the result so a
            # stale or pinned version cannot masquerade as a fresh run.
            self.assertTrue(a_short.get("module_sha"),
                "analyze_syllables must surface module_sha so the consumer "
                "can tell which version rendered the reading")
            self.assertEqual(a_short["module_sha"], a_long["module_sha"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
