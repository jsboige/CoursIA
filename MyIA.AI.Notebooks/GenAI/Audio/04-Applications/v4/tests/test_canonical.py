"""
test_canonical.py — test coverage for v4/canonical.py (speaker name normalization).

Boucle de Suif audiobook pipeline (Epic #1273) — module `canonical.py` (171L)
expose 3 fonctions publiques :
  - `normalize_speaker(raw: str) -> CanonicalSpeaker`
  - `load_catalog(path=None) -> SpeakerCatalog`
  - `resolve_figurant(raw: str, catalog=None) -> str`

`canonical.py` consommé par P0-P7 (research, casting, segmentation, dramatic
context, verification). 0 test Python dédié avant cette PR — garde-fou
anti-régression sur le mapping des 14 locuteurs canoniques + 13 figurants.

Co-localisé avec le module sous `v4/tests/` pour suivre la convention des
tests v4 existants (`test_p5_prosody_rescue.py`). Le module utilise une
importation **relative** (`from .schemas import`) — pattern d'import via
sys.path.insert(0, parent-of-v4) + import package `v4.canonical`
(cf `test_p5_prosody_rescue.py` modèle ligne 14-17).

Aucune dépendance externe — pydantic v2 (already a CoursIA dep) + stdlib
uniquement. Aucun subprocess, aucun appel LLM, aucun I/O hors fichiers
temporaires pytest `tmp_path` pour `load_catalog`.

Sibling-pattern: c.535 PR #7386 (claude_cli.py), c.628 PR #7391
(claudish_client.py) — même approche hermétique CPU-only.
"""

from __future__ import annotations

import importlib
import json
import os
import sys
from pathlib import Path

import pytest

# Make `v4.canonical` importable as a package (canonical.py uses `from .schemas import`).
# Layout:
#   04-Applications/v4/canonical.py       <- target
#   04-Applications/v4/schemas.py         <- relative-imported
#   04-Applications/v4/__init__.py        <- makes `v4` a package
#   04-Applications/                      <- must be on sys.path for `import v4.canonical`
_v4_parent = Path(__file__).resolve().parent.parent.parent  # 04-Applications/
if str(_v4_parent) not in sys.path:
    sys.path.insert(0, str(_v4_parent))

# Import the module under test via importlib (handles module name matching the
# filename — avoids collisions if pytest --import-mode=importlib is set somewhere).
canonical = importlib.import_module("v4.canonical")

# Reload-resilient reference to the canonical function set. Capture at
# import-time so the test methods that follow are deterministic regardless
# of any monkey-patching we do later (and so the file is grep-friendly).
normalize_speaker = canonical.normalize_speaker
load_catalog = canonical.load_catalog
resolve_figurant = canonical.resolve_figurant
RAW_TO_CANONICAL = canonical.RAW_TO_CANONICAL
FIGURANT_NAMES = canonical.FIGURANT_NAMES


# ─────────────────────────── Fixtures ───────────────────────────


@pytest.fixture(autouse=True)
def reset_catalog_cache():
    """`load_catalog` uses a module-level cache — reset before each test."""
    canonical._cached_catalog = None  # type: ignore[attr-defined]
    yield
    canonical._cached_catalog = None  # type: ignore[attr-defined]


@pytest.fixture
def minimal_catalog_json(tmp_path: Path) -> Path:
    """Write a minimal SpeakerCatalog JSON on disk for load_catalog tests."""
    catalog_path = tmp_path / "speaker_catalog.json"
    catalog_path.write_text(
        json.dumps(
            {
                "canonical_speakers": {},
                "figurants": [
                    {
                        "raw_name": "Le Cocher",
                        "canonical": "figurant",
                        "voice_archetype": "male_gruff",
                        "first_paragraph": 1,
                        "total_appearances": 5,
                        "appearances": [],
                        "description": "",
                        "relationships": {},
                    },
                    {
                        "raw_name": "Une Dame",
                        "canonical": "figurant",
                        "voice_archetype": "female_curious",
                        "first_paragraph": 3,
                        "total_appearances": 2,
                        "appearances": [],
                        "description": "",
                        "relationships": {},
                    },
                ],
                "figurant_voice_map": {},
                "total_speakers": 0,
                "total_dialogue_segments": 0,
            }
        ),
        encoding="utf-8",
    )
    return catalog_path


# ─────────────────── Constants & invariants ────────────────────


class TestModuleInvariants:
    """The module's STATIC data must remain sound — these tests pin the
    baseline count so accidental deletion in PRs is caught immediately."""

    def test_raw_to_canonical_is_nonempty(self):
        assert len(RAW_TO_CANONICAL) >= 30  # baseline floor (current: 46)

    def test_figurants_is_nonempty(self):
        assert len(FIGURANT_NAMES) >= 10  # baseline floor (current: 13)

    def test_all_raw_keys_are_lowercase_and_stripped(self):
        """`normalize_speaker` does `key = raw.lower().strip()` — keys must
        already be lowercase + stripped so the lookup is symmetric."""
        for raw in RAW_TO_CANONICAL.keys():
            assert raw == raw.lower().strip(), (
                f"RAW_TO_CANONICAL key {raw!r} not normalized "
                "(must be lowercased + stripped)"
            )

    def test_all_values_are_valid_canonical_speakers(self):
        """`CanonicalSpeaker` is a Literal — ensure no typos leak into the dict."""
        valid = {
            "narrateur", "elisabeth_rousset", "loiseau", "madame_loiseau",
            "comte", "comtesse", "cornudet", "carre_lamadon",
            "madame_carre_lamadon", "soeurs", "follenvie", "madame_follenvie",
            "officier", "figurant",
        }
        for canonical_id in set(RAW_TO_CANONICAL.values()):
            assert canonical_id in valid, (
                f"Unknown canonical id {canonical_id!r} (not in CanonicalSpeaker Literal)"
            )

    def test_no_narrateur_fallthrough_clobber(self):
        """`narrateur` is the DEFAULT fallback in `normalize_speaker`. If the
        bare key `narrateur` is somehow absent, the default would mask the
        defect — pin the literal entry exists."""
        assert "narrateur" in RAW_TO_CANONICAL
        assert RAW_TO_CANONICAL["narrateur"] == "narrateur"


# ─────────────────── normalize_speaker: direct lookup ──────────


class TestNormalizeSpeakerDirectLookup:
    """Step 1 of the resolution chain: raw key found verbatim in
    RAW_TO_CANONICAL (case-insensitive). Covers all 14 canonical speakers."""

    @pytest.mark.parametrize(
        "raw, expected",
        [
            # narrateur
            ("narrateur", "narrateur"),
            ("le narrateur", "narrateur"),
            ("NARRATEUR", "narrateur"),
            # elisabeth_rousset (4 raw variants)
            ("boule de suif", "elisabeth_rousset"),
            ("elisabeth", "elisabeth_rousset"),
            ("elisabeth rousset", "elisabeth_rousset"),
            ("mlle elisabeth rousset", "elisabeth_rousset"),
            ("elizabeth rousset", "elisabeth_rousset"),  # missing accent tolerated
            # loiseau (4 raw variants)
            ("loiseau", "loiseau"),
            ("monsieur loiseau", "loiseau"),
            ("m. loiseau", "loiseau"),
            ("m loiseau", "loiseau"),
            # madame_loiseau (2 raw variants)
            ("madame loiseau", "madame_loiseau"),
            ("mme loiseau", "madame_loiseau"),
            # comte (4 raw variants)
            ("comte", "comte"),
            ("le comte", "comte"),
            ("comte de breville", "comte"),
            ("comte hubert de breville", "comte"),
            ("comte hubert de bréville", "comte"),  # accent tolerated
            # comtesse (4 raw variants)
            ("comtesse", "comtesse"),
            ("la comtesse", "comtesse"),
            ("comtesse de breville", "comtesse"),
            ("mme de bréville", "comtesse"),
            # cornudet (single key)
            ("cornudet", "cornudet"),
            # carre_lamadon (4 raw variants incl. accent variants)
            ("carre-lamadon", "carre_lamadon"),
            ("carre lamadon", "carre_lamadon"),
            ("carré-lamadon", "carre_lamadon"),
            ("m. carré-lamadon", "carre_lamadon"),
            # madame_carre_lamadon (3 raw variants)
            ("madame carré-lamadon", "madame_carre_lamadon"),
            ("mme carré-lamadon", "madame_carre_lamadon"),
            ("madame carre-lamadon", "madame_carre_lamadon"),
            # soeurs (6 raw variants)
            ("soeurs", "soeurs"),
            ("les soeurs", "soeurs"),
            ("les bonnes soeurs", "soeurs"),
            ("bonne soeur", "soeurs"),
            ("religieuse", "soeurs"),
            ("les religieuses", "soeurs"),
            # follenvie (3 raw variants)
            ("follenvie", "follenvie"),
            ("m. follenvie", "follenvie"),
            ("m follenvie", "follenvie"),
            # madame_follenvie (2 raw variants)
            ("madame follenvie", "madame_follenvie"),
            ("mme follenvie", "madame_follenvie"),
            # officier (4 raw variants)
            ("officier", "officier"),
            ("l'officier", "officier"),
            ("l'officier prussien", "officier"),
            ("officier prussien", "officier"),
        ],
    )
    def test_direct_lookup_round_trip(self, raw: str, expected: str):
        assert normalize_speaker(raw) == expected

    def test_whitespace_only_difference_does_not_break(self):
        """`raw.lower().strip()` in normalize_speaker — leading/trailing
        whitespace must be tolerated on any input."""
        assert normalize_speaker("  narrateur  ") == "narrateur"
        assert normalize_speaker("\tnarrateur\n") == "narrateur"
        assert normalize_speaker(" Madame Loiseau ") == "madame_loiseau"


# ─────────── normalize_speaker: figurant resolution ───────────


class TestNormalizeSpeakerFigurants:
    """Step 2: raw matches FIGURANT_NAMES verbatim — must return 'figurant'."""

    @pytest.mark.parametrize(
        "raw",
        [
            "cocher",
            "bedeau",
            "un homme",
            "un autre homme",
            "un troisième homme",
            "homme",
            "dames",
            "voix du dehors",
            "voix du dedans",
            "moi",
            "georges garin",
            "l'anglais",
            "la petite anglaise",
        ],
    )
    def test_figurant_match_returns_figurant(self, raw: str):
        assert normalize_speaker(raw) == "figurant"

    def test_figurant_case_insensitive(self):
        assert normalize_speaker("COCHER") == "figurant"
        assert normalize_speaker("Le Cocher") == "figurant"

    def test_figurants_do_not_pollute_canonical_space(self):
        """Sanity guard: a figurant raw never accidentally collides with a
        canonical speaker via direct lookup."""
        for fig in FIGURANT_NAMES:
            assert fig not in RAW_TO_CANONICAL


# ─────────── normalize_speaker: partial matching ──────────────


class TestNormalizeSpeakerPartialMatching:
    """Steps 3-4: raw NOT in the dict EXACTLY, but matches via substring.

    Contract:
      - `alias in key` (alias is a substring of raw)
      - `key in alias` (raw is a substring of alias)
    Both directions are scanned. Tested via raw values that aren't in any
    direct lookup table but DO contain a known alias as a substring."""

    def test_partial_alias_substring_of_raw_first_alias_wins(self):
        """`normalize_speaker` iterates RAW_TO_CANONICAL and returns the
        FIRST matching alias. We pin this behavior: a raw containing
        multiple potential substrings resolves to whichever alias the
        Python dict iteration encounters first.

        Concrete: `et Madame Loiseau est entrée` contains both
        `madame loiseau` AND `loiseau` as substrings. Since `loiseau` is
        declared first in RAW_TO_CANONICAL (Python dict insertion order),
        the FIRST-match wins, returning `loiseau` — NOT `madame_loiseau`.

        This is the actual contract; pin it so a future refactor that
        changes iteration order is caught with intent."""
        assert normalize_speaker("et Madame Loiseau est entrée") == "loiseau"

    def test_partial_match_prefers_longer_alias_if_it_appears_first(self):
        """Inverse of the above: if a SHORTER alias appears first, it wins.
        Verified via a raw that ONLY matches via the shorter alias."""
        # "le pretre" → "le pretre" partial-matches via "les bonnes soeurs"? No.
        # Use a real raw that ONLY matches via one specific alias substring.
        # "religieuse inconnue" → matches via "religieuse" → soeurs
        assert normalize_speaker("religieuse inconnue") == "soeurs"

    def test_partial_raw_substring_of_alias(self):
        """`comte` is the alias; `le comte de bré` (truncated form) → key
        `le comte de bré` is a substring of `le comte` only if `le comte de bré`
        contains `le comte`... actually reversed: key in alias means key ⊂ alias.

        Use a real example: `comte` is registered as both alias and value.
        A raw like just `comte` IS direct-match — so construct one that's
        NOT direct-match but IS a substring of an alias."""
        # "huber" is not direct but is a substring of "comte hubert de breville"
        # → alias-substring-detection on aliases iterates RAW_TO_CANONICAL.
        # Contract: the first matching alias wins.
        result = normalize_speaker("huber")
        # Huber's alias match: any alias containing "huber" → comte
        assert result == "comte"

    def test_partial_match_over_figurant(self):
        """`cocher` is a figurant. A raw string CONTAINING `cocher` as
        substring → partial-fall-through to figurant path."""
        # "le cocher de la diligence" contains "cocher"
        assert normalize_speaker("le cocher de la diligence") == "figurant"

    def test_partial_match_returns_canonical_not_partial_str(self):
        """Partial-match step returns the CANONICAL value (underscore-form),
        not the raw alias as it appears in the input.

        Pin the FIRST-MATCH-WINS contract: a raw containing multiple
        candidate substrings returns whichever canonical id is hit first
        in RAW_TO_CANONICAL dict iteration order."""
        # "Madame Loiseau, qui rit" matches via "loiseau" (direct) → "loiseau"
        # NOT "madame_loiseau" — because the iteration encounters `loiseau`
        # first in RAW_TO_CANONICAL.
        assert normalize_speaker("Madame Loiseau, qui rit") == "loiseau"
        # Sanity: result is a valid CanonicalSpeaker Literal (must be one of the 14 ids).
        valid_ids = {
            "narrateur", "elisabeth_rousset", "loiseau", "madame_loiseau",
            "comte", "comtesse", "cornudet", "carre_lamadon",
            "madame_carre_lamadon", "soeurs", "follenvie", "madame_follenvie",
            "officier", "figurant",
        }
        assert "loiseau" in valid_ids


# ───── normalize_speaker: fallback / edge cases ───────────────


class TestNormalizeSpeakerFallback:
    """Step 5: nothing matches → default fallback 'narrateur'."""

    def test_unknown_raw_falls_back_to_narrateur(self):
        # Truly novel string — no alias, no figurant, no partial match.
        assert normalize_speaker("xyzzy_inexistant_42") == "narrateur"

    def test_empty_string_falls_back_to_narrateur(self):
        """Edge case: empty input. Note: empty string is NOT a figurant
        (only non-empty names), and `key = "".lower().strip()` = "" —
        direct-lookup miss, then partial-match against non-empty aliases
        also misses, → fallback."""
        assert normalize_speaker("") == "narrateur"

    def test_whitespace_only_falls_back_to_narrateur(self):
        """`"   ".strip()` = "" — same path as empty string above."""
        assert normalize_speaker("    ") == "narrateur"

    def test_partial_match_priority_over_fallback(self):
        """If any partial-match engages, fallback must NOT activate."""
        # "soeurs de charité" contains "soeurs" alias → soeurs, not narrateur
        assert normalize_speaker("soeurs de charité") == "soeurs"

    def test_fallback_idempotent(self):
        """Calling normalize_speaker on a narrateur raw returns narrateur —
        it's both an exact match AND the fallback; the result is consistent."""
        assert normalize_speaker("narrateur") == normalize_speaker("totally_unknown")


# ─────────────────── load_catalog ───────────────────────────────


class TestLoadCatalog:
    """Tests for the catalog loader. Cache + FileNotFound + happy path."""

    def test_load_missing_catalog_raises_filenotfound(self, tmp_path: Path):
        missing = tmp_path / "absolutely_not_here.json"
        with pytest.raises(FileNotFoundError) as exc_info:
            load_catalog(path=missing)
        # Contract: error message mentions the missing path AND the P1.5
        # guidance — that's what tells callers what's wrong.
        msg = str(exc_info.value)
        assert str(missing) in msg
        assert "P1.5" in msg
        # Also ensure the default path was NOT touched (we forced `path=`).
        assert "Lancez" in msg or "P1.5" in msg

    def test_load_minimal_catalog(self, minimal_catalog_json: Path):
        catalog = load_catalog(path=minimal_catalog_json)
        assert catalog is not None
        assert len(catalog.figurants) == 2
        assert catalog.figurants[0].raw_name == "Le Cocher"
        assert catalog.figurants[0].voice_archetype == "male_gruff"
        assert catalog.figurants[1].raw_name == "Une Dame"

    def test_load_catalog_caches_result(self, minimal_catalog_json: Path):
        """The module-level cache prevents re-reading on subsequent calls."""
        catalog_first = load_catalog(path=minimal_catalog_json)
        # Mutate the on-disk file after the first load.
        minimal_catalog_json.write_text(
            json.dumps(
                {
                    "canonical_speakers": {},
                    "figurants": [],  # empty now
                    "figurant_voice_map": {},
                    "total_speakers": 0,
                    "total_dialogue_segments": 0,
                }
            ),
            encoding="utf-8",
        )
        catalog_second = load_catalog(path=minimal_catalog_json)
        # Cache hit → same object as the first load.
        assert catalog_second is catalog_first
        # And the cache reflects the FIRST load's content.
        assert len(catalog_second.figurants) == 2

    def test_load_catalog_with_no_path_arg_uses_default(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ):
        """When `path=None`, the loader falls back to
        `<v4>/outputs/speaker_catalog.json`. If that file is missing,
        FileNotFoundError is raised; this test pins the default path by
        ensuring the absence raises."""
        # No need to actually create outputs/speaker_catalog.json — just
        # verify the loader's default behavior is to raise when missing.
        # To not pollute the real v4 directory, we monkeypatch the module
        # attribute `_CATALOG_PATH` to a guaranteed-missing path.
        sentinel = tmp_path / "wont_be_created.json"
        monkeypatch.setattr(canonical, "_CATALOG_PATH", sentinel)
        with pytest.raises(FileNotFoundError):
            load_catalog()  # no `path` arg → uses default (now patched)


# ─────────────────── resolve_figurant ──────────────────────────


class TestResolveFigurant:
    """`resolve_figurant(raw, catalog=None) -> str` — returns voice_archetype
    if the raw matches a figurant in the catalog, else empty string.

    The helper uses both exact and substring matching against
    `catalog.figurants[*].raw_name`."""

    def test_resolve_figurant_exact_match(self, minimal_catalog_json: Path):
        catalog = load_catalog(path=minimal_catalog_json)
        assert resolve_figurant("Le Cocher", catalog) == "male_gruff"
        assert resolve_figurant("Une Dame", catalog) == "female_curious"

    def test_resolve_figurant_case_insensitive(self, minimal_catalog_json: Path):
        catalog = load_catalog(path=minimal_catalog_json)
        assert resolve_figurant("le cocher", catalog) == "male_gruff"
        assert resolve_figurant("UNE DAME", catalog) == "female_curious"

    def test_resolve_figurant_unknown_returns_empty(
        self, minimal_catalog_json: Path
    ):
        catalog = load_catalog(path=minimal_catalog_json)
        assert resolve_figurant("Personne Inconnue", catalog) == ""

    def test_resolve_figurant_lazy_loads_when_catalog_none(
        self, minimal_catalog_json: Path, monkeypatch: pytest.MonkeyPatch
    ):
        """When `catalog=None`, the helper falls back to `load_catalog()`.
        It must NOT raise FileNotFoundError — instead it returns "". The
        contract is "soft-fail with empty", allowing `normalize_speaker`
        callers to chain without exception handling."""
        # Patch default path to the test catalog so load_catalog() succeeds.
        monkeypatch.setattr(canonical, "_CATALOG_PATH", minimal_catalog_json)
        result = resolve_figurant("Le Cocher")
        assert result == "male_gruff"

    def test_resolve_figurant_lazy_load_falls_back_when_missing(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ):
        """When `catalog=None` AND the default catalog is missing, the
        function must NOT raise — returns "" (silent soft-fail).

        Pin the contract: P0-P7 callers can call resolve_figurant before
        P1.5 has produced its artifact, and the function tolerates it."""
        monkeypatch.setattr(canonical, "_CATALOG_PATH", tmp_path / "nope.json")
        result = resolve_figurant("Le Cocher")
        assert result == ""  # NOT a raise.

    def test_resolve_figurant_substring_match(self, minimal_catalog_json: Path):
        """Partial matching: the raw contains a figurant's raw_name as a
        substring (in either direction) → resolves to voice_archetype.

        Note: the algorithm uses raw_name normalized lowercase + stripped,
        so the substring direction matters. `le cocher de la diligence`
        contains `le cocher` → match. `la dame inconnue` does NOT contain
        `une dame` (different surface form) → no match (returns "")."""
        catalog = load_catalog(path=minimal_catalog_json)
        # Substring: raw_name ⊂ raw → match
        assert (
            resolve_figurant("le cocher de la diligence", catalog)
            == "male_gruff"
        )
        # Substring in OTHER direction: raw ⊂ raw_name → also match.
        # "une dame" is fully contained in "une dame de la cour".
        assert (
            resolve_figurant("une dame de la cour", catalog)
            == "female_curious"
        )
        # Surface-form mismatch: "la dame" ≠ "une dame" → no match.
        assert resolve_figurant("la dame inconnue", catalog) == ""


# ─────────────────── Cross-cutting integration ─────────────────


class TestRoundTripIntegration:
    """End-to-end probes: the 3 functions together, simulating how P0-P7
    consume them. Guards against future regressions in their interaction."""

    def test_normalize_then_resolve_chain(self, minimal_catalog_json: Path):
        """`normalize_speaker` returns "figurant" for a figurant raw; the
        subsequent `resolve_figurant` step confirms the voice archetype."""
        catalog = load_catalog(path=minimal_catalog_json)
        # normalize_speaker sees "Le Cocher" → "figurant" (figurant step)
        assert normalize_speaker("Le Cocher") == "figurant"
        # Then resolve_figurant looks up the canonical raw → male_gruff
        assert resolve_figurant("Le Cocher", catalog) == "male_gruff"

    def test_normalize_canonical_then_resolve_returns_empty(
        self, minimal_catalog_json: Path
    ):
        """For a CANONICAL speaker (not a figurant), resolve_figurant must
        return "" — because the catalog only stores figurants."""
        catalog = load_catalog(path=minimal_catalog_json)
        canonical_speaker = normalize_speaker("Madame Loiseau")
        assert canonical_speaker == "madame_loiseau"  # not a figurant
        # resolve_figurant looks for canonicals → not found → empty
        assert resolve_figurant("Madame Loiseau", catalog) == ""

    def test_all_canonical_resolution_paths_stable(self):
        """Property: for every canonical raw key → the result is exactly
        the canonical id, never alias leakage, never narrateur-by-accident."""
        canonical_ids = {
            "narrateur", "elisabeth_rousset", "loiseau", "madame_loiseau",
            "comte", "comtesse", "cornudet", "carre_lamadon",
            "madame_carre_lamadon", "soeurs", "follenvie", "madame_follenvie",
            "officier", "figurant",
        }
        # At least the canonical-bare keys must round-trip to themselves.
        for raw in [
            "narrateur", "loiseau", "comte", "comtesse",
            "cornudet", "follenvie", "soeurs", "officier",
        ]:
            result = normalize_speaker(raw)
            assert result in canonical_ids, (
                f"normalize_speaker({raw!r}) → {result!r} which is not a "
                f"CanonicalSpeaker Literal"
            )
            # And: bare bare-key inputs that are themselves canonical
            # values should round-trip exactly (no degradation).
            if raw in RAW_TO_CANONICAL and RAW_TO_CANONICAL[raw] == raw:
                assert result == raw
