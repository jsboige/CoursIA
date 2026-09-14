"""CharacterProfile.relationships coercion (Issue #15002 P0) — offline tests.

The 2026-09-12 gpt-5.2 P0 run returned ``relationships`` as a list of
"Name : description" strings for all 11 characters (strict mode is off for
NarrativeContext), which pydantic rejected. These tests pin the before-
validator that absorbs the observed form. Run from the v4 directory:

    python -m pytest tests/test_p0_relationships_coercion.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))

from v4.schemas import CharacterProfile  # noqa: E402


def _profile(relationships) -> CharacterProfile:
    return CharacterProfile(
        name="Loiseau",
        aliases=["M. Loiseau"],
        traits=["roublard"],
        voice_register="baryton nasillard",
        emotional_arc={"act1": "enjoué"},
        prosody_defaults=["chuckling"],
        relationships=relationships,
    )


class TestRelationshipsCoercion:
    def test_dict_form_is_untouched(self):
        """The schema-conformant dict stays byte-identical."""
        p = _profile({"Elizabeth Rousset": "protecteur intéressé"})
        assert p.relationships == {"Elizabeth Rousset": "protecteur intéressé"}

    def test_observed_list_form_is_coerced(self):
        """The measured gpt-5.2 shape: a list of "Name : description"."""
        p = _profile([
            "Elizabeth Rousset : protège, puis rejoint le mépris",
            "Mme Loiseau : complicité marchande",
        ])
        assert p.relationships == {
            "Elizabeth Rousset": "protège, puis rejoint le mépris",
            "Mme Loiseau": "complicité marchande",
        }

    def test_separator_inside_description_survives(self):
        """Split on the FIRST separator only."""
        p = _profile(["Cornudet : camarade : puis distance politique"])
        assert p.relationships == {
            "Cornudet": "camarade : puis distance politique",
        }

    def test_string_without_separator_keeps_empty_description(self):
        p = _profile(["Comtesse"])
        assert p.relationships == {"Comtesse": ""}

    def test_non_string_items_are_dropped(self):
        p = _profile(["Loiseau : complice", 42, None])
        assert p.relationships == {"Loiseau": "complice"}

    def test_empty_list_is_allowed(self):
        assert _profile([]).relationships == {}
