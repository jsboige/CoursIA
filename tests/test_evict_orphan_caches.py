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
        #
        # #22486 : le nom du test dit "even if ancestor" -- on l'etablit par
        # le patch plutot qu'en laissant le vrai git decider de l'ancetre.
        # Sans ce patch, le test passe quand meme (assertIn), mais la branche
        # d'anciennete interrogeait le clone ambiant : un origin/main perime
        # y ajoutait "sha_not_ancestor_of_main" sans que rien ne le signale.
        original = eoc._is_ancestor
        eoc._is_ancestor = lambda sha, remote, branch: True  # noqa: E731
        try:
            old = _dt.datetime.now(_dt.timezone.utc) - _dt.timedelta(hours=25)
            cache = self._cache(self.KEY_ANCESTOR, _iso(old), _iso(old))
            rec = eoc._classify_cache(
                cache, max_age_hours=24, remote="origin", main_branch="main"
            )
        finally:
            eoc._is_ancestor = original
        self.assertEqual(rec["verdict"], "EVICT")
        self.assertIn("last_accessed_older_than_24h", rec["reason"])

    def test_ancestor_and_recent_is_kept(self):
        # Cache ancetre ET accede recemment (< 24h). Doit etre KEEP.
        #
        # REPAIR 2026-10-25 (#22486) : ce test etait le seul du fichier a
        # laisser _is_ancestor interroger le vrai git du clone appelant. Il
        # ne mesurait donc pas la classification mais l'etat du clone : sur
        # un origin/main plus vieux que le commit d46cbf302e (2026-09-14),
        # `git merge-base --is-ancestor` rend rc=1, _is_ancestor rend False,
        # et le verdict devient EVICT "sha_not_ancestor_of_main" -- le test
        # rougit sur main sans qu'aucune ligne de code n'ait change. Les
        # trois autres tests qui atteignent cette branche patchent deja
        # _is_ancestor (False pour l'orphelin et le cas combine, None pour
        # "unknown") ; celui-ci suit le meme patron.
        original = eoc._is_ancestor
        eoc._is_ancestor = lambda sha, remote, branch: True  # noqa: E731
        try:
            now = _dt.datetime.now(_dt.timezone.utc)
            cache = self._cache(self.KEY_ANCESTOR, _iso(now), _iso(now))
            rec = eoc._classify_cache(
                cache, max_age_hours=24, remote="origin", main_branch="main"
            )
        finally:
            eoc._is_ancestor = original
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


class TestMarkSuperseded(unittest.TestCase):
    """Reouverture #16088 (2026-09-28) : garder les N overlays les plus
    recents par famille, evincer les autres, meme ancetres de main."""

    def _rec(self, family, hours_ago, verdict="KEEP", reason="recent_and_ancestor"):
        created = _dt.datetime(2026, 9, 28, 4, 0, tzinfo=_dt.timezone.utc) - _dt.timedelta(hours=hours_ago)
        return {
            "key": f"{family}-{hours_ago}",
            "family": family,
            "created_at": _iso(created),
            "verdict": verdict,
            "reason": reason,
        }

    def test_keeps_latest_n_per_family(self):
        recs = [self._rec("py", h) for h in (5, 1, 3, 0, 4)]
        eoc._mark_superseded(recs, 3)
        kept = sorted(r["key"] for r in recs if r["verdict"] == "KEEP")
        self.assertEqual(kept, ["py-0", "py-1", "py-3"])
        evicted = [r for r in recs if r["verdict"] == "EVICT"]
        self.assertEqual(len(evicted), 2)
        self.assertTrue(all(r["reason"] == "superseded_beyond_latest_3" for r in evicted))

    def test_families_are_independent(self):
        recs = [self._rec("py", h) for h in (0, 1)] + [self._rec("cs", h) for h in (0, 1, 2)]
        eoc._mark_superseded(recs, 2)
        evicted = [r["key"] for r in recs if r["verdict"] == "EVICT"]
        self.assertEqual(evicted, ["cs-2"])

    def test_already_evicted_does_not_take_a_slot(self):
        # Un overlay deja evince (SHA orphelin) ne compte pas parmi les N gardes.
        recs = [
            self._rec("py", 0, verdict="EVICT", reason="sha_not_ancestor_of_main"),
            self._rec("py", 1),
            self._rec("py", 2),
        ]
        eoc._mark_superseded(recs, 2)
        self.assertEqual([r["verdict"] for r in recs], ["EVICT", "KEEP", "KEEP"])
        self.assertEqual(recs[0]["reason"], "sha_not_ancestor_of_main")

    def test_refuse_is_never_turned_into_eviction(self):
        recs = [self._rec("py", h) for h in (0, 1)]
        recs.append(self._rec("py", 2, verdict="REFUSE", reason="ancestor_check_failed"))
        eoc._mark_superseded(recs, 1)
        self.assertEqual(recs[2]["verdict"], "REFUSE")
        self.assertEqual([r["verdict"] for r in recs[:2]], ["KEEP", "EVICT"])

    def test_zero_disables(self):
        recs = [self._rec("py", h) for h in range(6)]
        eoc._mark_superseded(recs, 0)
        self.assertTrue(all(r["verdict"] == "KEEP" for r in recs))

    def test_records_without_family_are_untouched(self):
        rec = {"key": "lake-x", "created_at": "2026-09-28T00:00:00Z",
               "verdict": "REFUSE", "reason": "not_codeql_overlay"}
        eoc._mark_superseded([rec], 1)
        self.assertEqual(rec["verdict"], "REFUSE")

    def test_classify_sets_family(self):
        now = _dt.datetime.now(_dt.timezone.utc)
        cache = {
            "id": 1,
            "key": TestClassifyCache.KEY_ORPHAN,
            "size_in_bytes": 1,
            "created_at": _iso(now),
            "last_accessed_at": _iso(now),
        }
        # #22486 : la famille derive de la cle, pas de l'histoire git du
        # clone appelant -- on coupe l'appel a git pour que ce test mesure
        # la seule chose qu'il annonce.
        original = eoc._is_ancestor
        eoc._is_ancestor = lambda sha, remote, branch: True  # noqa: E731
        try:
            rec = eoc._classify_cache(cache, max_age_hours=24, remote="origin", main_branch="main")
        finally:
            eoc._is_ancestor = original
        self.assertEqual(rec["family"], "d953d79b74456ce0-python-2.27.0")


class TestMarkDuplicateKeys(unittest.TestCase):
    """#19658 : une cle content-addressee dupliquee entre scopes de branche
    n'est servie qu'une fois ; les copies sont de la redondance pure.

    Mesure du 2026-10-25 qui fonde la regle : 72 entrees `setup-python-*`
    pour 5 cles distinctes -- 50 copies de la cle 3.12.14 et 22 de la
    3.12.15, ~293 Mo chacune, 4,85 Go d'un quota de 10 Go.
    """

    KEY_312 = ("setup-python-Linux-x64-24.04-Ubuntu-python-3.12.14-"
               "pip-df2f915356ec2e5d50e2dfa2b")

    def _rec(self, key, hours_ago, ref="refs/heads/main", verdict="KEEP"):
        created = (_dt.datetime(2026, 10, 25, 12, 0, tzinfo=_dt.timezone.utc)
                   - _dt.timedelta(hours=hours_ago))
        rec = {
            "key": key,
            "ref": ref,
            "created_at": _iso(created),
            "verdict": verdict,
            "reason": "dedupe_candidate" if verdict == "KEEP" else "not_codeql_overlay",
        }
        if verdict == "KEEP":
            rec["dedupe_key"] = key
        return rec

    def test_classify_marks_setup_python_as_dedupe_candidate(self):
        now = _dt.datetime.now(_dt.timezone.utc)
        cache = {
            "id": 1,
            "key": self.KEY_312,
            "ref": "refs/heads/feature/x",
            "size_in_bytes": 293_300_000,
            "created_at": _iso(now),
            "last_accessed_at": _iso(now),
        }
        rec = eoc._classify_cache(cache, max_age_hours=24,
                                  remote="origin", main_branch="main")
        self.assertEqual(rec["verdict"], "KEEP")
        self.assertEqual(rec["dedupe_key"], self.KEY_312)

    def test_classify_still_refuses_other_families(self):
        # La famille ouverte est une exception nommee : `lake-*` reste REFUSE,
        # sinon la regle de surete « on ne touche pas au quota reutilisable »
        # n'existerait plus.
        now = _dt.datetime.now(_dt.timezone.utc)
        rec = eoc._classify_cache(
            {"id": 2, "key": "lake-knot_lean-axiom-Linux-821f5e3b-1",
             "size_in_bytes": 1, "created_at": _iso(now),
             "last_accessed_at": _iso(now)},
            max_age_hours=24, remote="origin", main_branch="main")
        self.assertEqual(rec["verdict"], "REFUSE")
        self.assertEqual(rec["reason"], "not_codeql_overlay")
        self.assertNotIn("dedupe_key", rec)

    def test_duplicate_key_keeps_only_the_newest(self):
        recs = [self._rec(self.KEY_312, h, ref=f"refs/heads/f{h}")
                for h in (5, 1, 3, 0, 4)]
        eoc._mark_duplicate_keys(recs, "main")
        kept = [r for r in recs if r["verdict"] == "KEEP"]
        self.assertEqual(len(kept), 1)
        self.assertEqual(kept[0]["created_at"], _iso(
            _dt.datetime(2026, 10, 25, 12, 0, tzinfo=_dt.timezone.utc)))
        evicted = [r for r in recs if r["verdict"] == "EVICT"]
        self.assertEqual(len(evicted), 4)
        self.assertTrue(all(r["reason"] == "duplicate_key_superseded"
                            for r in evicted))

    def test_default_branch_copy_survives_even_when_older(self):
        # `refs/heads/main` est le repli de toute branche sans copie propre :
        # l'evincer ferait perdre le hit a toutes ces branches a la fois.
        recs = [
            self._rec(self.KEY_312, 0, ref="refs/heads/feature/recent"),
            self._rec(self.KEY_312, 9, ref="refs/heads/main"),
            self._rec(self.KEY_312, 4, ref="refs/heads/feature/old"),
        ]
        eoc._mark_duplicate_keys(recs, "main")
        main_rec = [r for r in recs if r["ref"] == "refs/heads/main"][0]
        self.assertEqual(main_rec["verdict"], "KEEP")
        self.assertEqual(main_rec["dedupe_kept"], "default_branch")
        newest = [r for r in recs if r["ref"] == "refs/heads/feature/recent"][0]
        self.assertEqual(newest["verdict"], "KEEP")
        old = [r for r in recs if r["ref"] == "refs/heads/feature/old"][0]
        self.assertEqual(old["verdict"], "EVICT")

    def test_live_branch_outranks_a_newer_pr_merge_ref(self):
        # Mesure du 2026-10-25 : 73 copies d'une meme cle, TOUTES sur
        # `refs/pull/<n>/merge` et aucune sur `main`. Une ref de PR n'est lue
        # que par les runs de cette PR-la : quand une branche vivante porte la
        # cle, c'est sa copie qui doit survivre, meme plus ancienne.
        #
        # La PR 22027 est CLOSED ici (ensemble ouvert vide) : c'est la seule
        # situation ou sa copie est evincable depuis la review ai-01 du
        # 2026-10-25 -- sur une PR ouverte elle est lue par ses propres runs.
        recs = [
            self._rec(self.KEY_312, 0, ref="refs/pull/22027/merge"),
            self._rec(self.KEY_312, 30, ref="refs/heads/main"),
        ]
        eoc._mark_duplicate_keys(recs, "main", open_prs=set())
        pr_rec = [r for r in recs if r["ref"].startswith("refs/pull/")][0]
        main_rec = [r for r in recs if r["ref"] == "refs/heads/main"][0]
        self.assertEqual(main_rec["verdict"], "KEEP")
        self.assertEqual(pr_rec["verdict"], "EVICT")

    # --- review ai-01 du 2026-10-25 (tete 647f417530) : une copie de PR
    # OUVERTE sert encore ses runs. L'evincer rend du quota a `lake-*` et
    # fait repayer un `pip install` a froid a chaque run de cette PR, puis un
    # re-save de ~293 Mo -- au moment ou c'est le calcul qui manque (#22461).

    def test_open_pr_copy_is_kept(self):
        """Controle negatif exige par la review : copie d'une PR ouverte = KEEP,
        meme quand elle est la plus ancienne et qu'une autre copie existe."""
        recs = [
            self._rec(self.KEY_312, 0, ref="refs/heads/feature/x"),
            self._rec(self.KEY_312, 40, ref="refs/pull/20123/merge"),
        ]
        eoc._mark_duplicate_keys(recs, "main", open_prs={20123})
        pr_rec = [r for r in recs if r["ref"].startswith("refs/pull/")][0]
        self.assertEqual(pr_rec["verdict"], "KEEP")
        self.assertEqual(pr_rec["dedupe_kept"], "pr_open")

    def test_closed_pr_copy_is_evicted(self):
        """Le pendant : la meme copie, la PR etant fermee, est bien evincee."""
        recs = [
            self._rec(self.KEY_312, 0, ref="refs/heads/feature/x"),
            self._rec(self.KEY_312, 40, ref="refs/pull/20123/merge"),
        ]
        eoc._mark_duplicate_keys(recs, "main", open_prs={999, 1000})
        pr_rec = [r for r in recs if r["ref"].startswith("refs/pull/")][0]
        self.assertEqual(pr_rec["verdict"], "EVICT")
        self.assertEqual(pr_rec["reason"], "duplicate_key_superseded")

    def test_open_prs_unknown_keeps_every_pr_copy(self):
        """`open_prs=None` = « je ne sais pas », pas « aucune PR ouverte ».
        Fail-CLOSED : aucune copie de PR n'est evincee, et le dry-run le dit."""
        recs = [
            self._rec(self.KEY_312, 0, ref="refs/heads/feature/x"),
            self._rec(self.KEY_312, 40, ref="refs/pull/20123/merge"),
            self._rec(self.KEY_312, 50, ref="refs/pull/20124/merge"),
        ]
        eoc._mark_duplicate_keys(recs, "main", open_prs=None)
        pr_recs = [r for r in recs if r["ref"].startswith("refs/pull/")]
        self.assertEqual(len(pr_recs), 2)
        for r in pr_recs:
            self.assertEqual(r["verdict"], "KEEP")
            self.assertEqual(r["dedupe_kept"], "open_prs_unknown")

    def test_pr_number_from_ref(self):
        self.assertEqual(eoc._pr_number_from_ref("refs/pull/20123/merge"), 20123)
        self.assertEqual(eoc._pr_number_from_ref("refs/pull/7/head"), 7)
        self.assertIsNone(eoc._pr_number_from_ref("refs/heads/main"))
        self.assertIsNone(eoc._pr_number_from_ref("refs/heads/feature/12"))
        self.assertIsNone(eoc._pr_number_from_ref(""))

    def test_distinct_keys_are_untouched(self):
        other = self.KEY_312.replace("3.12.14", "3.12.15")
        recs = [self._rec(self.KEY_312, 0), self._rec(other, 1)]
        eoc._mark_duplicate_keys(recs, "main")
        self.assertTrue(all(r["verdict"] == "KEEP" for r in recs))

    def test_refuse_without_dedupe_key_is_never_evicted(self):
        recs = [
            self._rec(self.KEY_312, 0, ref="refs/heads/main"),
            {"key": "lake-x", "ref": "refs/heads/main",
             "created_at": "2026-10-25T00:00:00Z",
             "verdict": "REFUSE", "reason": "not_codeql_overlay"},
        ]
        eoc._mark_duplicate_keys(recs, "main")
        self.assertEqual(recs[1]["verdict"], "REFUSE")

    def test_no_dedupe_flag_is_declared(self):
        argv = sys.argv
        try:
            sys.argv = ["evict_orphan_caches.py", "--no-dedupe"]
            self.assertTrue(eoc._parse_args().no_dedupe)
            sys.argv = ["evict_orphan_caches.py"]
            self.assertFalse(eoc._parse_args().no_dedupe)
        finally:
            sys.argv = argv


_DEMAND_312 = [
    {"pm": "pip", "version": "3.9"},
    {"pm": "pip", "version": "3.11"},
    {"pm": "pip", "version": "3.12"},
]


class TestMarkUnrequestedKeys(unittest.TestCase):
    """Le critere « plus aucun workflow de main ne demande cette cle » (#19658).

    Decision A du coordinateur (2026-10-26) : une cle `setup-python` dont le
    couple (cache, version) n'est plus declare par les workflows de `main` est
    prouvee orpheline, et evincee **meme sur une PR ouverte**. La regle
    fail-closed « copie de PR ouverte » reste intacte pour les cles encore
    demandees.
    """

    KEY_312 = (
        "setup-python-Linux-x64-24.04-Ubuntu-python-3.12.14-pip-"
        "df2f915356ec2e5d50e2dfa2bb34caf601c5c89eaf81ae09d9834972f0296fde"
    )
    KEY_311 = (
        "setup-python-Linux-x64-24.04-Ubuntu-python-3.11.17-pip-"
        "b15947e0b9e073efda57fecf1a11f71ea4ac176abfe8d847f391a618432fe02d"
    )
    KEY_ORPHAN = (
        "setup-python-Linux-x64-24.04-Ubuntu-python-3.7.9-pip-"
        "aa2f915356ec2e5d50e2dfa2bb34caf601c5c89eaf81ae09d9834972f0296fde"
    )

    def _rec(self, key, ref="refs/pull/12345/merge", verdict="KEEP"):
        return {
            "key": key,
            "ref": ref,
            "created_at": "2026-10-26T00:00:00Z",
            "last_accessed_at": "2026-10-26T00:00:00Z",
            "size_bytes": 68_000_000,
            "verdict": verdict,
            "reason": "dedupe_candidate",
        }

    def test_unrequested_key_is_evicted_even_on_an_open_pr(self):
        recs = [self._rec(self.KEY_ORPHAN)]
        eoc._mark_unrequested_keys(recs, _DEMAND_312)
        self.assertEqual(recs[0]["verdict"], "EVICT")
        self.assertEqual(recs[0]["reason"], "unrequested_by_main_workflows")

    def test_requested_key_is_kept(self):
        # Temoin NEGATIF : une cle encore demandee par main ne bouge pas.
        recs = [self._rec(self.KEY_312), self._rec(self.KEY_311)]
        eoc._mark_unrequested_keys(recs, _DEMAND_312)
        for r in recs:
            self.assertEqual(r["verdict"], "KEEP")
            self.assertEqual(r["reason"], "requested_by_main")
        self.assertEqual(recs[0]["declared_by"], "3.12")

    def test_unknown_demand_keeps_everything(self):
        # Fail-CLOSED : workflows illisibles -> demande inconnue -> rien n'est
        # affirme, la raison le dit.
        recs = [self._rec(self.KEY_ORPHAN)]
        eoc._mark_unrequested_keys(recs, None)
        self.assertEqual(recs[0]["verdict"], "KEEP")
        self.assertEqual(recs[0]["reason"], "unrequested_check_failed")

    def test_unresolved_spec_covers_every_version(self):
        # Une spec qu'on ne sait pas lire (expression de matrice) ne peut pas
        # etre niee : elle couvre tout.
        demand = [{"pm": "pip", "version": "${{ matrix.python-version }}"}]
        recs = [self._rec(self.KEY_ORPHAN)]
        eoc._mark_unrequested_keys(recs, demand)
        self.assertEqual(recs[0]["verdict"], "KEEP")

    def test_other_package_manager_is_not_covered(self):
        demand = [{"pm": "npm", "version": "3.12"}]
        recs = [self._rec(self.KEY_312)]
        eoc._mark_unrequested_keys(recs, demand)
        self.assertEqual(recs[0]["verdict"], "EVICT")

    def test_non_setup_python_record_is_untouched(self):
        recs = [{"key": "lake-x", "verdict": "KEEP", "reason": "recent_and_ancestor"}]
        eoc._mark_unrequested_keys(recs, _DEMAND_312)
        self.assertEqual(recs[0]["reason"], "recent_and_ancestor")

    def test_refused_record_is_never_evicted(self):
        recs = [self._rec(self.KEY_ORPHAN, verdict="REFUSE")]
        eoc._mark_unrequested_keys(recs, _DEMAND_312)
        self.assertEqual(recs[0]["verdict"], "REFUSE")

    def test_spec_coverage_rules(self):
        self.assertTrue(eoc._spec_covers("3.12", "3.12.14"))
        self.assertTrue(eoc._spec_covers("3.12", "3.12.15"))
        self.assertTrue(eoc._spec_covers("3.x", "3.12.14"))
        self.assertTrue(eoc._spec_covers("3.12.14", "3.12.14"))
        self.assertFalse(eoc._spec_covers("3.12", "3.11.17"))
        self.assertFalse(eoc._spec_covers("3.12.14", "3.12.15"))
        self.assertTrue(eoc._spec_covers("", "3.12.14"))
        self.assertTrue(eoc._spec_covers("${{ matrix.python-version }}", "3.12.14"))

    def test_setup_python_regex_reads_the_real_key(self):
        m = eoc.SETUP_PYTHON_RE.match(self.KEY_312)
        self.assertIsNotNone(m)
        self.assertEqual(m.group("version"), "3.12.14")
        self.assertEqual(m.group("pm"), "pip")
        self.assertEqual(
            m.group("filehash"),
            "df2f915356ec2e5d50e2dfa2bb34caf601c5c89eaf81ae09d9834972f0296fde",
        )

    def test_setup_python_regex_ignores_other_families(self):
        self.assertIsNone(
            eoc.SETUP_PYTHON_RE.match(
                "codeql-overlay-base-database-1-a-python-2.27.0-" + "0" * 40 + "-1-1"
            )
        )


class TestDeclaredDemand(unittest.TestCase):
    """La demande est DERIVEE des workflows, jamais figee dans le script."""

    def _write(self, name, body):
        d = os.path.join(self._tmp, name)
        with open(d, "w", encoding="utf-8") as fh:
            fh.write(body)
        return d

    def setUp(self):
        import tempfile

        self._tmp = tempfile.mkdtemp(prefix="eoc-workflows-")

    def test_demand_is_read_from_the_workflows(self):
        self._write(
            "demo.yml",
            "name: demo\n"
            "on: [push]\n"
            "jobs:\n"
            "  build:\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - uses: actions/setup-python@v5\n"
            "        with:\n"
            "          python-version: '3.10'\n"
            "          cache: 'pip'\n"
            "          cache-dependency-path: requirements.txt\n"
            "      - run: echo hello\n",
        )
        demand = eoc._declared_demand(self._tmp)
        self.assertIsNotNone(demand)
        self.assertIn({"pm": "pip", "version": "3.10"}, demand)

    def test_step_without_cache_does_not_count(self):
        self._write(
            "nocache.yml",
            "jobs:\n"
            "  build:\n"
            "    steps:\n"
            "      - uses: actions/setup-python@v5\n"
            "        with:\n"
            "          python-version: '3.10'\n",
        )
        demand = eoc._declared_demand(self._tmp)
        self.assertEqual(demand, [])

    def test_matrix_spec_is_kept_unresolved(self):
        self._write(
            "matrix.yml",
            "jobs:\n"
            "  build:\n"
            "    strategy:\n"
            "      matrix:\n"
            "        py: ['3.10', '3.11']\n"
            "    steps:\n"
            "      - uses: actions/setup-python@v5\n"
            "        with:\n"
            "          python-version: ${{ matrix.py }}\n"
            "          cache: 'pip'\n",
        )
        demand = eoc._declared_demand(self._tmp)
        self.assertEqual(
            demand, [{"pm": "pip", "version": "${{ matrix.py }}"}]
        )

    def test_missing_directory_is_unknown(self):
        self.assertIsNone(
            eoc._declared_demand(os.path.join(self._tmp, "does-not-exist"))
        )

    def test_empty_directory_is_unknown(self):
        # Aucun workflow lu n'est pas « aucune demande » : c'est « je ne sais
        # pas » -> fail-CLOSED.
        self.assertIsNone(eoc._declared_demand(self._tmp))

    def test_the_real_repository_yields_a_demand(self):
        # Fumigation : la derivation reste applicable sur les workflows reels.
        demand = eoc._declared_demand(os.path.join(_REPO, ".github", "workflows"))
        self.assertIsNotNone(demand)
        self.assertTrue(demand)
        for d in demand:
            self.assertTrue(d.get("pm"))

    def test_no_unrequested_flag_is_declared(self):
        argv = sys.argv
        try:
            sys.argv = ["evict_orphan_caches.py", "--no-unrequested"]
            self.assertTrue(eoc._parse_args().no_unrequested)
            sys.argv = ["evict_orphan_caches.py"]
            self.assertFalse(eoc._parse_args().no_unrequested)
        finally:
            sys.argv = argv


class TestCodeQLTrapRegex(unittest.TestCase):
    """#22937 : le regex TRAP capture les 4 champs mesures."""

    def test_real_measured_key(self):
        k = ("codeql-trap-1-2.27.3-javascript-"
             "62e906dcf63d8c36dce530ba7b84568ea7cb7005")
        m = eoc.CODEQL_TRAP_RE.match(k)
        self.assertIsNotNone(m)
        self.assertEqual(m.group("cachever"), "1")
        self.assertEqual(m.group("toolchain"), "2.27.3")
        self.assertEqual(m.group("lang"), "javascript")
        self.assertEqual(m.group("sha40"),
                         "62e906dcf63d8c36dce530ba7b84568ea7cb7005")

    def test_short_sha_does_not_match(self):
        k = ("codeql-trap-1-2.27.3-javascript-"
             "62e906dcf63d8c36dce530ba7b84568")
        self.assertIsNone(eoc.CODEQL_TRAP_RE.match(k))

    def test_uppercase_sha_does_not_match(self):
        k = "codeql-trap-1-2.27.3-javascript-" + "A" * 40
        self.assertIsNone(eoc.CODEQL_TRAP_RE.match(k))

    def test_overlay_key_does_not_match_trap_re(self):
        k = (
            "codeql-overlay-base-database-1-d953d79b74456ce0-python-2.27.0-"
            "1ebc412b8f69cf1e0623da3accfdba852e35aaa5-34799381268-1"
        )
        self.assertIsNone(eoc.CODEQL_TRAP_RE.match(k))

    def test_trap_key_does_not_match_overlay_re(self):
        k = ("codeql-trap-1-2.27.3-javascript-"
             "62e906dcf63d8c36dce530ba7b84568ea7cb7005")
        self.assertIsNone(eoc.CODEQL_OVERLAY_RE.match(k))


class TestClassifyTrap(unittest.TestCase):
    """La classification TRAP ne consulte ni git ni l'horloge : l'adressage
    d'un cache TRAP ne depend ni du SHA de sa cle (la cle exacte demandee
    par les analyses est `...-<lang>-unknown`) ni de son age (la
    restore-key rend la plus recente de la famille). Cf. section « Format
    de cle TRAP CodeQL » du module pour les journaux qui fondent ce
    lecteur unique et partiel."""

    KEY = ("codeql-trap-1-2.27.3-javascript-"
           "62e906dcf63d8c36dce530ba7b84568ea7cb7005")

    def _cache(self, last_accessed_at, created_at):
        return {"id": 1, "key": self.KEY, "size_in_bytes": 1,
                "created_at": created_at, "last_accessed_at": last_accessed_at}

    def test_trap_is_candidate_with_family(self):
        now = _iso(_dt.datetime.now(_dt.timezone.utc))
        rec = eoc._classify_cache(self._cache(now, now), max_age_hours=24,
                                  remote="origin", main_branch="main")
        self.assertEqual(rec["verdict"], "KEEP")
        self.assertEqual(rec["reason"], "trap_candidate")
        self.assertEqual(rec["trap_family"], "1-2.27.3-javascript")

    def test_trap_classification_never_calls_git(self):
        # La branche TRAP ne doit jamais atteindre _is_ancestor : un
        # callable qui fait echouer le test le prouve (le test reste purement
        # CPU, comme l'en-tete du fichier l'exige).
        def _boom(sha, remote, branch):
            raise AssertionError("trap classification must not consult git")
        now = _iso(_dt.datetime.now(_dt.timezone.utc))
        original = eoc._is_ancestor
        eoc._is_ancestor = _boom
        try:
            rec = eoc._classify_cache(self._cache(now, now), max_age_hours=24,
                                      remote="origin", main_branch="main")
        finally:
            eoc._is_ancestor = original
        self.assertEqual(rec["verdict"], "KEEP")

    def test_old_never_hit_trap_is_still_candidate(self):
        # Contrairement aux overlays, un trap jamais lu depuis 30 h n'est
        # pas evince par l'age : seule la passe _mark_superseded_traps
        # tranche, sur le rang par famille -- pas l'anciennete d'acces.
        old = _iso(_dt.datetime.now(_dt.timezone.utc) - _dt.timedelta(hours=30))
        rec = eoc._classify_cache(self._cache(old, old), max_age_hours=24,
                                  remote="origin", main_branch="main")
        self.assertEqual(rec["verdict"], "KEEP")
        self.assertEqual(rec["reason"], "trap_candidate")


class TestMarkSupersededTraps(unittest.TestCase):
    """#22937 : garder les N traps les plus recents par famille sur la
    branche par defaut, evincer les autres, ne jamais toucher un trap
    scelle sur une ref de PR."""

    BASE = _dt.datetime(2026, 10, 27, 14, 0, tzinfo=_dt.timezone.utc)

    def _trap(self, sha, minutes_ago, ref="refs/heads/main",
              family="1-2.27.3-javascript"):
        return {
            "key": f"codeql-trap-{family}-{sha}",
            "ref": ref,
            "created_at": _iso(self.BASE - _dt.timedelta(minutes=minutes_ago)),
            "size_bytes": 28_921_148,
            "verdict": "KEEP",
            "reason": "trap_candidate",
            "trap_family": family,
        }

    def test_keeps_only_newest_per_family(self):
        recs = [self._trap("a" * 40, 0), self._trap("b" * 40, 10),
                self._trap("c" * 40, 20)]
        eoc._mark_superseded_traps(recs, "main", 1)
        self.assertEqual(recs[0]["verdict"], "KEEP")
        self.assertTrue(all(r["verdict"] == "EVICT" for r in recs[1:]))
        self.assertTrue(all(r["reason"] == "trap_superseded_by_newer"
                            for r in recs[1:]))

    def test_keep_2_keeps_two_newest(self):
        recs = [self._trap("a" * 40, 0), self._trap("b" * 40, 10),
                self._trap("c" * 40, 20)]
        eoc._mark_superseded_traps(recs, "main", 2)
        self.assertEqual([r["verdict"] for r in recs],
                         ["KEEP", "KEEP", "EVICT"])

    def test_families_are_independent(self):
        # Deux toolchains = deux familles restore-key distinctes : chacune
        # garde sa plus recente.
        recs = [self._trap("a" * 40, 0, family="1-2.27.3-javascript"),
                self._trap("b" * 40, 30, family="1-2.27.3-javascript"),
                self._trap("d" * 40, 40, family="1-2.28.0-javascript")]
        eoc._mark_superseded_traps(recs, "main", 1)
        kept = [r["key"] for r in recs if r["verdict"] == "KEEP"]
        self.assertEqual(len(kept), 2)

    def test_pr_ref_entry_is_not_touched(self):
        # Un trap scelle sur refs/pull/<n>/merge reste visible des runs de
        # sa PR (scope GitHub) : jamais evince, affiche not_default_branch.
        recs = [self._trap("a" * 40, 0),
                self._trap("e" * 40, 90, ref="refs/pull/22937/merge")]
        eoc._mark_superseded_traps(recs, "main", 1)
        pr_rec = recs[1]
        self.assertEqual(pr_rec["verdict"], "KEEP")
        self.assertEqual(pr_rec["trap_kept"], "not_default_branch")

    def test_zero_disables(self):
        recs = [self._trap("a" * 40, 0), self._trap("b" * 40, 10)]
        eoc._mark_superseded_traps(recs, "main", 0)
        self.assertTrue(all(r["verdict"] == "KEEP" for r in recs))

    def test_refuse_without_trap_family_is_untouched(self):
        recs = [self._trap("a" * 40, 0),
                {"key": "lake-x", "ref": "refs/heads/main",
                 "created_at": "2026-10-27T00:00:00Z",
                 "verdict": "REFUSE", "reason": "not_codeql_overlay"}]
        eoc._mark_superseded_traps(recs, "main", 1)
        self.assertEqual(recs[1]["verdict"], "REFUSE")


class TestTrapAcceptanceMeasured(unittest.TestCase):
    """Acceptance #22937 : le jeu MESURE du 2026-10-27 (~15:50Z).

    77 entrees `codeql-trap-1-2.27.3-javascript-<sha>` relevees par l'API
    actions/caches, toutes sur refs/heads/main, 2 221 605 488 octets au
    total, 77 SHA distincts. La passe doit garder exactement la plus
    recente (celle du run main 40512896186, SHA 62e906dcf63d...) et
    evincer les 76 autres, soit 2 192 684 340 octets liberes.
    """

    MEASURED = [
        # (key, created_at, size_in_bytes) -- releves le 2026-10-27.
        ('codeql-trap-1-2.27.3-javascript-e8890842efec2f139d6d65a8ffaf5ff275216d2f',
         '2026-10-26T02:10:06.927439Z', 28800321),
        ('codeql-trap-1-2.27.3-javascript-d350f7f9d327826025d34227c7a1a3507df55d7b',
         '2026-10-26T03:42:15.471708Z', 28800497),
        ('codeql-trap-1-2.27.3-javascript-80dad04da3a46564faa5c772a9bb014fa52b151e',
         '2026-10-26T03:44:06.639033Z', 28799926),
        ('codeql-trap-1-2.27.3-javascript-f6725a39088767f19ab44dca5e5e473a867dd15d',
         '2026-10-26T04:11:58.661392Z', 28789887),
        ('codeql-trap-1-2.27.3-javascript-5d99cf1777214a98fb23fa7013b65f0c0964aaf4',
         '2026-10-26T04:20:03.205913Z', 28824087),
        ('codeql-trap-1-2.27.3-javascript-ee5e7b58b1bf1f9493b3f2290816f6fc1988d16d',
         '2026-10-26T04:24:04.775105Z', 28803896),
        ('codeql-trap-1-2.27.3-javascript-0bc024064e44c3cf3ca085515cd23cd3f691a3c2',
         '2026-10-26T04:28:55.179315Z', 28822466),
        ('codeql-trap-1-2.27.3-javascript-502cd963957957fc9ef57f44ff93ebee995af44e',
         '2026-10-26T04:30:55.638190Z', 28829645),
        ('codeql-trap-1-2.27.3-javascript-2d1ca6d07b896e7cf0242959c104f00a1a2c7787',
         '2026-10-26T04:30:59.413957Z', 28819765),
        ('codeql-trap-1-2.27.3-javascript-723dad4893061e4ff9d387db6fa9547f6420c57b',
         '2026-10-26T04:32:37.665392Z', 28824779),
        ('codeql-trap-1-2.27.3-javascript-9e0fc3de3fc1a09fbd85a05216d12b3ee955759d',
         '2026-10-26T04:34:06.171531Z', 28829028),
        ('codeql-trap-1-2.27.3-javascript-54f9b9eec1d5e096890026adb2d55c307c437188',
         '2026-10-26T05:17:58.489882Z', 28822963),
        ('codeql-trap-1-2.27.3-javascript-89dd95acdfdbb079c04bf48092a5b6d80d462f3a',
         '2026-10-26T06:13:51.531023Z', 28834700),
        ('codeql-trap-1-2.27.3-javascript-7eff951f33b2d3f314f359dd7bf9a8450b81749a',
         '2026-10-26T06:25:35.974439Z', 28833331),
        ('codeql-trap-1-2.27.3-javascript-87a880b7f29db28b12f164006f64b5711c4f7f64',
         '2026-10-26T06:54:02.572500Z', 28823411),
        ('codeql-trap-1-2.27.3-javascript-0db8a455c45463ff9f9b666f23c354aaf5dbe6e3',
         '2026-10-26T06:54:52.610955Z', 28830035),
        ('codeql-trap-1-2.27.3-javascript-131958b1250b829a977e1074b565a5967b835ceb',
         '2026-10-26T06:55:09.310995Z', 28827092),
        ('codeql-trap-1-2.27.3-javascript-0bbbbf40a78cdea479084dfe23c00663ac31adaf',
         '2026-10-26T08:04:11.015874Z', 28826184),
        ('codeql-trap-1-2.27.3-javascript-dc16971719d9373af3f6cb23c6eee951b943ccbe',
         '2026-10-26T08:31:45.995740Z', 28815478),
        ('codeql-trap-1-2.27.3-javascript-aac0688aa20542ac2026efda345a0e897f394e85',
         '2026-10-26T08:32:27.495421Z', 28821743),
        ('codeql-trap-1-2.27.3-javascript-89c1f807f3be334e58fc2f79368f7f0c626b6b0b',
         '2026-10-26T08:32:58.396256Z', 28819288),
        ('codeql-trap-1-2.27.3-javascript-dbc9c855134ee316fe106b57e06fd0a4ae9ee47a',
         '2026-10-26T08:37:18.135149Z', 28828743),
        ('codeql-trap-1-2.27.3-javascript-bbac3bb54340b63e66ac3d10fa3518df42444d80',
         '2026-10-26T08:39:36.294084Z', 28837482),
        ('codeql-trap-1-2.27.3-javascript-0c33c520bf668061fd5c321da7852c3ba1f4a94a',
         '2026-10-26T08:41:17.370990Z', 28823802),
        ('codeql-trap-1-2.27.3-javascript-9ab5eed36a4b98ae6f5869faf35668eb57bd10a1',
         '2026-10-26T08:44:47.560498Z', 28835516),
        ('codeql-trap-1-2.27.3-javascript-bf1f9c20b6b8105794ae7f3113f07d7ccedf9188',
         '2026-10-26T08:47:29.058599Z', 28839966),
        ('codeql-trap-1-2.27.3-javascript-082e67eb40ec2ad50b2d7ff76a6f19c6131fdd01',
         '2026-10-26T10:29:41.622228Z', 28847218),
        ('codeql-trap-1-2.27.3-javascript-9327c3ae1d41679be300787abbeeba8690887cfb',
         '2026-10-26T10:39:55.886474Z', 28836475),
        ('codeql-trap-1-2.27.3-javascript-8f90d5920ca4b5f907d91b4aaa4f9c243352cc24',
         '2026-10-26T10:41:44.408707Z', 28845220),
        ('codeql-trap-1-2.27.3-javascript-0df66d391b748c0bdf0e4ab292e49328fe8eaeb7',
         '2026-10-26T11:57:49.290729Z', 28838236),
        ('codeql-trap-1-2.27.3-javascript-f68b470520bba109d3892f359c6e4fb2ae8b95d5',
         '2026-10-26T12:41:20.971361Z', 28835336),
        ('codeql-trap-1-2.27.3-javascript-a70f64eb04e1f0c78c6fb741bb80fc630dff0feb',
         '2026-10-26T13:06:49.752220Z', 28838887),
        ('codeql-trap-1-2.27.3-javascript-e1c457d598b7b105967d8d30c929c7933dc7e23f',
         '2026-10-26T13:12:28.225944Z', 28840779),
        ('codeql-trap-1-2.27.3-javascript-69a4161378cff5eec3d61fdb9876879f34f2cf88',
         '2026-10-26T13:14:53.125262Z', 28835810),
        ('codeql-trap-1-2.27.3-javascript-82ea7b1edf8e22c14d6412e0eac984994b9b7810',
         '2026-10-26T13:15:16.842527Z', 28846762),
        ('codeql-trap-1-2.27.3-javascript-702b36f1d2b9713c567bdd45dac593e514f9b199',
         '2026-10-26T13:19:46.218118Z', 28837740),
        ('codeql-trap-1-2.27.3-javascript-675894c31b9a0b6fdc510d2b3106e581713d2d3a',
         '2026-10-26T13:20:33.236071Z', 28834901),
        ('codeql-trap-1-2.27.3-javascript-863502c5344b5c08b8590a184968c1c297ab66cd',
         '2026-10-26T13:22:46.411995Z', 28829274),
        ('codeql-trap-1-2.27.3-javascript-ffdd381a59a78c25f03b50a9ee22c9bdca29527f',
         '2026-10-26T13:24:24.466860Z', 28842185),
        ('codeql-trap-1-2.27.3-javascript-cf11416e3b561a4105db0e6693edc567b02489fb',
         '2026-10-26T16:11:27.792255Z', 28838101),
        ('codeql-trap-1-2.27.3-javascript-cb6796263007ffa9cf5bc4a9d65703151ef7a944',
         '2026-10-26T16:12:14.574130Z', 28843511),
        ('codeql-trap-1-2.27.3-javascript-674dbca251c5786560513ffe45f55e70d734286e',
         '2026-10-26T16:29:03.529869Z', 28842819),
        ('codeql-trap-1-2.27.3-javascript-b07ed07bad33ca1a3102d9bc6c14f456e87ae573',
         '2026-10-26T16:38:20.746837Z', 28848552),
        ('codeql-trap-1-2.27.3-javascript-d372ef1ebef8df2517383b80e628f5ecc3709695',
         '2026-10-26T16:40:58.433796Z', 28845839),
        ('codeql-trap-1-2.27.3-javascript-1d3379fc7c3a5a9e95b73dcf07030eece302f4d2',
         '2026-10-26T16:42:27.129911Z', 28839915),
        ('codeql-trap-1-2.27.3-javascript-65af2ad35038d1c4105d3f392514a456e120963c',
         '2026-10-26T16:55:14.173865Z', 28839587),
        ('codeql-trap-1-2.27.3-javascript-f1ec5f2a46107c175186322d41e63a72d8dd1b2f',
         '2026-10-26T17:16:35.101285Z', 28848320),
        ('codeql-trap-1-2.27.3-javascript-96dcb80e4132d3be35cedd2d8532d8f6b5436082',
         '2026-10-26T17:32:12.660452Z', 28844971),
        ('codeql-trap-1-2.27.3-javascript-be9979b424134139f80f2dd4f046e5aedd028373',
         '2026-10-26T18:17:33.908476Z', 28846133),
        ('codeql-trap-1-2.27.3-javascript-d80ea3588e009ffb2a9960d96cbdf3af680001a1',
         '2026-10-26T20:30:49.034516Z', 28837902),
        ('codeql-trap-1-2.27.3-javascript-7a647f04a94be2dafd38add04edb4d7038cb0d8a',
         '2026-10-26T20:33:35.409055Z', 28857244),
        ('codeql-trap-1-2.27.3-javascript-46e5a48cda9f03aff3f3ef0aeabeaa2cee57796d',
         '2026-10-26T20:33:39.621356Z', 28884638),
        ('codeql-trap-1-2.27.3-javascript-198cc084c14b53b024a9fcc17c6b48921aed584b',
         '2026-10-26T21:14:05.834585Z', 28887618),
        ('codeql-trap-1-2.27.3-javascript-7d83cceded2280318b2a1034ed69c95122f06d2f',
         '2026-10-26T21:25:23.002587Z', 28896220),
        ('codeql-trap-1-2.27.3-javascript-a9bfa41b15e14b33e1048359e2afd75d0d9baaf5',
         '2026-10-26T22:48:27.741947Z', 28884881),
        ('codeql-trap-1-2.27.3-javascript-f3836c3d7e6f4d9c21ba21c111c8af786317f803',
         '2026-10-26T22:58:18.899398Z', 28883331),
        ('codeql-trap-1-2.27.3-javascript-daa7efa04d824875ee3533ab993953d8716f8742',
         '2026-10-26T23:05:22.247891Z', 28876077),
        ('codeql-trap-1-2.27.3-javascript-1a2cf9d908303bf932edf67faea21db2d6dc6ca8',
         '2026-10-26T23:15:25.698847Z', 28888376),
        ('codeql-trap-1-2.27.3-javascript-c8a5ff4611576b8ca5a27914c1641ef463b57b7e',
         '2026-10-27T00:33:11.599059Z', 28885971),
        ('codeql-trap-1-2.27.3-javascript-8591831e938f7a3d4bb5fac1618bb95b788197b9',
         '2026-10-27T00:50:39.383726Z', 28881063),
        ('codeql-trap-1-2.27.3-javascript-6734de57a7954490f1751f46c048be3a3b996fc7',
         '2026-10-27T01:05:08.808546Z', 28881350),
        ('codeql-trap-1-2.27.3-javascript-5eb2b91f426dc5402ed9333df4bd4e53f11b7515',
         '2026-10-27T01:39:35.327068Z', 28881468),
        ('codeql-trap-1-2.27.3-javascript-24e7bed4d3d8d07a4b1145e195b67f9b985c5fcc',
         '2026-10-27T01:53:10.997665Z', 28884834),
        ('codeql-trap-1-2.27.3-javascript-550c0a140c9bb6678b6b1934753f8979780489c2',
         '2026-10-27T01:54:50.957959Z', 28868899),
        ('codeql-trap-1-2.27.3-javascript-6a6e4cd0288c5dbf367af4e7ba595934da45573b',
         '2026-10-27T02:25:50.497123Z', 28878342),
        ('codeql-trap-1-2.27.3-javascript-4b2fc535bd0bef5cefe77b78b6350dc05c5d54ac',
         '2026-10-27T04:00:40.179982Z', 28886703),
        ('codeql-trap-1-2.27.3-javascript-284e5192be25d7a84b221ffee0ce6b37abaa3e89',
         '2026-10-27T04:40:27.083790Z', 28900830),
        ('codeql-trap-1-2.27.3-javascript-3028c6c063141a256ae1ad02fc31440492eb08bc',
         '2026-10-27T04:44:25.562983Z', 28892288),
        ('codeql-trap-1-2.27.3-javascript-955cd1e61e7094582140c7683e244de89811ea6a',
         '2026-10-27T05:27:56.388443Z', 28887288),
        ('codeql-trap-1-2.27.3-javascript-11487ceb3d4049a6a375ee54afcc80cbc2611db5',
         '2026-10-27T06:04:20.618182Z', 28896836),
        ('codeql-trap-1-2.27.3-javascript-06b1bfd6ef08170483efec27baa4a18804e2d265',
         '2026-10-27T06:58:13.115291Z', 28905486),
        ('codeql-trap-1-2.27.3-javascript-21ad9a48ccb89fe8c54fc0da18f94da0a6b51db8',
         '2026-10-27T08:38:02.472917Z', 28900422),
        ('codeql-trap-1-2.27.3-javascript-ac04df7cb1c73df85136061c9c38106ee7468e41',
         '2026-10-27T11:51:53.250636Z', 28900602),
        ('codeql-trap-1-2.27.3-javascript-7a5a9f48a9a5574c5e346eb0791a7a9d00f21c54',
         '2026-10-27T12:01:37.881952Z', 28893551),
        ('codeql-trap-1-2.27.3-javascript-d6892b210966749b1a511151a076d9476c91b7cc',
         '2026-10-27T12:15:15.761830Z', 28902312),
        ('codeql-trap-1-2.27.3-javascript-1c35c93525fca40efa19865707c3f2082064c41f',
         '2026-10-27T14:26:32.341737Z', 28949206),
        ('codeql-trap-1-2.27.3-javascript-62e906dcf63d8c36dce530ba7b84568ea7cb7005',
         '2026-10-27T14:52:58.588016Z', 28921148),
    ]

    def test_77_measured_entries_yield_76_evictions(self):
        self.assertEqual(len(self.MEASURED), 77)
        records = [
            eoc._classify_cache(
                {"id": i, "key": key, "ref": "refs/heads/main",
                 "size_in_bytes": size, "created_at": created,
                 "last_accessed_at": created},
                max_age_hours=24, remote="origin", main_branch="main")
            for i, (key, created, size) in enumerate(self.MEASURED)
        ]
        self.assertTrue(all(r["verdict"] == "KEEP" for r in records))
        eoc._mark_superseded_traps(records, "main", 1)
        evicted = [r for r in records if r["verdict"] == "EVICT"]
        kept = [r for r in records if r["verdict"] == "KEEP"]
        self.assertEqual(len(evicted), 76)
        self.assertEqual(len(kept), 1)
        self.assertEqual(
            kept[0]["key"],
            "codeql-trap-1-2.27.3-javascript-"
            "62e906dcf63d8c36dce530ba7b84568ea7cb7005")
        self.assertTrue(all(r["reason"] == "trap_superseded_by_newer"
                            for r in evicted))
        freed = sum(r["size_bytes"] for r in evicted)
        self.assertEqual(freed, 2_221_605_488 - 28_921_148)
        self.assertEqual(round(freed / 1e6, 1), 2192.7)

    def test_default_keep_is_one(self):
        argv = sys.argv
        try:
            sys.argv = ["evict_orphan_caches.py"]
            self.assertEqual(eoc._parse_args().keep_latest_traps, 1)
            sys.argv = ["evict_orphan_caches.py", "--keep-latest-traps", "3"]
            self.assertEqual(eoc._parse_args().keep_latest_traps, 3)
        finally:
            sys.argv = argv


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
    # PYTHONIOENCODING utf-8
    os.environ.setdefault("PYTHONIOENCODING", "utf-8")
    unittest.main(verbosity=2)
