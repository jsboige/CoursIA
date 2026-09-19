#!/usr/bin/env python3
"""test_evict_orphan_caches.py -- tests unitaires pour evict_orphan_caches.py (#16088).

Le script principal est un orchestrateur REST ; ces tests portent sur
les fonctions deterministes pures (regex, classification) qui sont
l'identite du predicat d'eviction. Les appels API REST sont hors scope
(necessiteraient un mock ou un replay ; cf. test_pr_gh_apis pour le
precedent).

Les tests n'ont PAS besoin de GH_TOKEN : ils sont purement CPU.
"""
from __future__ import annotations

import datetime as _dt
import os
import sys
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_REPO, "scripts", "ci"))

import evict_orphan_caches as eoc  # noqa: E402


def _iso(dt: _dt.datetime) -> str:
    return dt.isoformat().replace("+00:00", "Z")


class TestCodeQLRegex(unittest.TestCase):
    """Le regex CodeQL overlay capture les 6 champs mesures."""

    def test_real_python_key(self):
        k = (
            "codeql-overlay-base-database-1-d953d79b74456ce0-python-2.27.0-"
            "1ebc412b8f69cf1e0623da3accfdba852e35aaa5-34799381268-1"
        )
        m = eoc.CODEQL_OVERLAY_RE.match(k)
        self.assertIsNotNone(m)
        self.assertEqual(m.group("random8"), "d953d79b74456ce0")
        self.assertEqual(m.group("lang"), "python")
        self.assertEqual(m.group("toolchain"), "2.27.0")
        self.assertEqual(m.group("sha40"), "1ebc412b8f69cf1e0623da3accfdba852e35aaa5")
        self.assertEqual(m.group("runid"), "34799381268")
        self.assertEqual(m.group("version"), "1")

    def test_real_csharp_key(self):
        k = (
            "codeql-overlay-base-database-1-5eeba31e73e2d4ed-csharp-2.27.0-"
            "d46cbf302eeabbbe63c039e223e3f6d83c8fef09-34799019470-1"
        )
        m = eoc.CODEQL_OVERLAY_RE.match(k)
        self.assertIsNotNone(m)
        self.assertEqual(m.group("lang"), "csharp")
        self.assertEqual(m.group("sha40"), "d46cbf302eeabbbe63c039e223e3f6d83c8fef09")

    def test_real_javascript_key(self):
        k = (
            "codeql-overlay-base-database-1-c801913f1ee29663-javascript-2.27.0-"
            "1ebc412b8f69cf1e0623da3accfdba852e35aaa5-34799381268-1"
        )
        m = eoc.CODEQL_OVERLAY_RE.match(k)
        self.assertIsNotNone(m)
        self.assertEqual(m.group("lang"), "javascript")

    def test_non_codeql_key_does_not_match(self):
        # lake-...-axiom-Linux-... : pas codeql-overlay
        k = "lake-knot_lean-axiom-Linux-821f5e3b8a379423434e088dca75a9c1787ac38c8aa6b74bc3f12"
        self.assertIsNone(eoc.CODEQL_OVERLAY_RE.match(k))
        # setup-python-... : pas codeql-overlay
        k = (
            "setup-python-Linux-x64-24.04-Ubuntu-python-3.12.14-pip-"
            "26eefd1d8ac010ffd38b5847e1c6bf7defa3b2fb67215469b040c348f6a44444"
        )
        self.assertIsNone(eoc.CODEQL_OVERLAY_RE.match(k))

    def test_short_sha_does_not_match(self):
        # SHA tronque a 32 hex (les premiers) -- ne doit PAS matcher.
        k = (
            "codeql-overlay-base-database-1-d953d79b74456ce0-python-2.27.0-"
            "1ebc412b8f69cf1e0623da3accfdba852-34799381268-1"
        )
        self.assertIsNone(eoc.CODEQL_OVERLAY_RE.match(k))

    def test_uppercase_sha_does_not_match(self):
        # Le SHA de GitHub est toujours lower-case.
        k = (
            "codeql-overlay-base-database-1-d953d79b74456ce0-python-2.27.0-"
            "1EBC412B8F69CF1E0623DA3ACCFDBA852E35AAA5-34799381268-1"
        )
        self.assertIsNone(eoc.CODEQL_OVERLAY_RE.match(k))


class TestClassifyCache(unittest.TestCase):
    """Le predicat d'eviction est deterministe et readonly (n'appelle pas l'API)."""

    def _cache(self, key, last_accessed_at, created_at):
        return {
            "id": 1,
            "key": key,
            "size_in_bytes": 200_000_000,
            "created_at": created_at,
            "last_accessed_at": last_accessed_at,
        }

    KEY_ORPHAN = (
        "codeql-overlay-base-database-1-d953d79b74456ce0-python-2.27.0-"
        "0000000000000000000000000000000000000001-34799381268-1"
    )
    KEY_ANCESTOR = (
        "codeql-overlay-base-database-1-d953d79b74456ce0-python-2.27.0-"
        "d46cbf302eeabbbe63c039e223e3f6d83c8fef09-34799381268-1"
    )
    KEY_NON_CODEQL = (
        "lake-knot_lean-axiom-Linux-821f5e3b8a379423434e088dca75a9c1787ac38c"
    )

    def test_non_codeql_cache_is_refused(self):
        # Meme si le SHA n'est pas ancetre, on ne touche PAS aux caches
        # non-codeql-overlay : ils sont reutilises (lean, setup-python, etc.).
        cache = self._cache(self.KEY_NON_CODEQL, _iso(_dt.datetime.now(_dt.timezone.utc)), _iso(_dt.datetime.now(_dt.timezone.utc)))
        rec = eoc._classify_cache(
            cache, max_age_hours=24, remote="origin", main_branch="main"
        )
        self.assertEqual(rec["verdict"], "REFUSE")
        self.assertEqual(rec["reason"], "not_codeql_overlay")

    def test_orphan_sha_is_evicted_even_if_recent(self):
        now = _dt.datetime.now(_dt.timezone.utc)
        cache = self._cache(self.KEY_ORPHAN, _iso(now), _iso(now))
        # KEY_ORPHAN = "...0000...0001" n'existe PAS comme commit : un
        # appel reel a git merge-base retournerait rc=128 (None) -- ce qui
        # est maintenant REFUSE (fail-CLOSED, c.1149 NanoClaw CONCERNS
        # PR #16099 nit 1). Pour tester le verdict "pas ancetre = EVICT",
        # on patche _is_ancestor pour qu'il rende False explicitement
        # (la distinction "pas ancetre" vs "impossible de determiner" est
        # testee separement dans test_ancestor_check_unknown_refuses).
        original = eoc._is_ancestor
        eoc._is_ancestor = lambda sha, remote, branch: False  # noqa: E731
        try:
            rec = eoc._classify_cache(
                cache, max_age_hours=24, remote="origin", main_branch="main"
            )
        finally:
            eoc._is_ancestor = original
        self.assertEqual(rec["verdict"], "EVICT")
        self.assertIn("sha_not_ancestor_of_main", rec["reason"])

    def test_old_accessed_evicts_even_if_ancestor(self):
        # Cache cree il y a 25h, non accede depuis. Doit etre EVICT.
        old = _dt.datetime.now(_dt.timezone.utc) - _dt.timedelta(hours=25)
        cache = self._cache(self.KEY_ANCESTOR, _iso(old), _iso(old))
        rec = eoc._classify_cache(
            cache, max_age_hours=24, remote="origin", main_branch="main"
        )
        self.assertEqual(rec["verdict"], "EVICT")
        self.assertIn("last_accessed_older_than_24h", rec["reason"])

    def test_ancestor_and_recent_is_kept(self):
        # Cache ancetre ET accede recemment (< 24h). Doit etre KEEP.
        now = _dt.datetime.now(_dt.timezone.utc)
        cache = self._cache(self.KEY_ANCESTOR, _iso(now), _iso(now))
        rec = eoc._classify_cache(
            cache, max_age_hours=24, remote="origin", main_branch="main"
        )
        self.assertEqual(rec["verdict"], "KEEP")
        self.assertEqual(rec["reason"], "recent_and_ancestor")

    def test_both_reasons_can_combine(self):
        # Cache non-ancetre ET ancien : les deux raisons apparaissent.
        # KEY_ORPHAN n'existe pas comme commit -- on patche _is_ancestor
        # pour rendre False (cf. test_orphan_sha_is_evicted_even_if_recent
        # pour la justification complete du pattern de mock).
        old = _dt.datetime.now(_dt.timezone.utc) - _dt.timedelta(hours=48)
        cache = self._cache(self.KEY_ORPHAN, _iso(old), _iso(old))
        original = eoc._is_ancestor
        eoc._is_ancestor = lambda sha, remote, branch: False  # noqa: E731
        try:
            rec = eoc._classify_cache(
                cache, max_age_hours=24, remote="origin", main_branch="main"
            )
        finally:
            eoc._is_ancestor = original
        self.assertEqual(rec["verdict"], "EVICT")
        self.assertIn("sha_not_ancestor_of_main", rec["reason"])
        self.assertIn("last_accessed_older_than_24h", rec["reason"])

    def test_ancestor_check_unknown_refuses(self):
        # REPAIR 2026-09-14 c.1149 NanoClaw CONCERNS PR #16099 nit 1 :
        # _is_ancestor peut renvoyer None (git absent, rc>=2, ref
        # missing) -- un check indecidable doit REFUSE (fail-CLOSED),
        # pas EVICT. La direction d'echec d'un outil dont le metier
        # est de supprimer ne peut pas etre fail-OPEN.
        cache = self._cache(self.KEY_ANCESTOR, _iso(_dt.datetime.now(_dt.timezone.utc)), _iso(_dt.datetime.now(_dt.timezone.utc)))
        # Patch _is_ancestor to simulate an undecidable check (e.g.
        # git missing on PATH, or ref absent on remote).
        original = eoc._is_ancestor
        eoc._is_ancestor = lambda sha, remote, branch: None  # noqa: E731
        try:
            rec = eoc._classify_cache(
                cache, max_age_hours=24, remote="origin", main_branch="main"
            )
        finally:
            eoc._is_ancestor = original
        self.assertEqual(rec["verdict"], "REFUSE")
        self.assertEqual(rec["reason"], "ancestor_check_failed")


class TestParseIso(unittest.TestCase):
    """Compat GitHub '...Z' suffix."""

    def test_z_suffix(self):
        dt = eoc._parse_iso("2026-09-14T02:34:37.140539Z")
        self.assertEqual(dt.year, 2026)
        self.assertEqual(dt.month, 9)
        self.assertEqual(dt.day, 14)
        self.assertEqual(dt.utcoffset(), _dt.timedelta(0))

    def test_plus_zero_offset(self):
        dt = eoc._parse_iso("2026-09-14T02:34:37.140539+00:00")
        self.assertEqual(dt.utcoffset(), _dt.timedelta(0))


class TestScopeConstants(unittest.TestCase):
    """Le regex et la version API sont pins contre la derive."""

    def test_api_version_pinned(self):
        # 2022-11-28 documente sur
        # https://docs.github.com/en/rest/actions/cache -- ne pas deriver
        # silencieusement vers une date plus recente.
        self.assertEqual(eoc.GITHUB_API_VERSION, "2022-11-28")

    def test_regex_anchored(self):
        # Le regex doit etre ancre sinon il matcherait du substring.
        # Tester sur un prefixe legitime mais sans suffixe : doit echouer.
        k = "codeql-overlay-base-database-1-foo-python-2.27.0-suffixe-invalide"
        self.assertIsNone(eoc.CODEQL_OVERLAY_RE.match(k))


if __name__ == "__main__":
    # PYTHONIOENCODING utf-8 (Tell c.1067 strict)
    os.environ.setdefault("PYTHONIOENCODING", "utf-8")
    unittest.main(verbosity=2)
