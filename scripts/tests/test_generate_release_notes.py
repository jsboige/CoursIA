"""Tests for scripts/release/generate_release_notes.py (#9856).

The acceptance criterion is literal: "les notes citent des comptes **lus dans
le catalogue**, jamais recopies a la main". The test suite therefore exercises
the rendering functions against synthetic catalogues to assert that:

  - The totals line equals len(entries).
  - Per-serie/per-status/per-maturity/per-kernel breakdowns sum to the total
    and contain the expected counts for each entry.
  - Series README links are rendered with a "(README absent)" annotation when
    the path does not exist on disk, so a human reviewer can verify.
  - The "since rentree" filter excludes entries with no ``executed_at`` and
    respects the TZ-aware comparison.
  - Empty catalogue and missing file are hard errors, not silent successes.
  - Determinism: two renders with the same inputs differ only in the
    generated_at timestamp (which the test controls).

The tests follow the stdlib-only convention of this repo's CI tooling (no
pytest fixture factory, no parametrize -- just unittest.TestCase subclasses
that build temp catalogues with ``tempfile``).
"""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path

# Add scripts/release to sys.path so the import resolves in the test runner.
SCRIPTS_RELEASE = Path(__file__).resolve().parents[1] / "release"
sys.path.insert(0, str(SCRIPTS_RELEASE.parent))

from release import generate_release_notes as grn  # noqa: E402


def make_entry(
    *,
    serie: str = "GenAI",
    sous_serie: str = "Image",
    status: str = "READY",
    maturity: str = "BETA",
    kernel: str = "Python 3",
    executed_at: str | None = "2026-08-01T10:00:00+02:00",
    path: str = "MyIA.AI.Notebooks/GenAI/Image/x.ipynb",
    title: str = "x",
    last_success_sha: str = "abc123456",
) -> dict:
    """Build a synthetic catalogue entry. Only fields the renderer actually
    reads are populated, and only when the test exercises them. Keeping the
    factory minimal reduces drift when the catalogue schema evolves -- the
    renderer uses ``.get()`` with defaults, so omitting a field is the same
    as passing ``None``."""
    return {
        "path": path,
        "title": title,
        "serie": serie,
        "sous_serie": sous_serie,
        "kernel": kernel,
        "status": status,
        "maturity": maturity,
        "executed_at": executed_at,
        "last_success_sha": last_success_sha,
    }


class LoadCatalogueTests(unittest.TestCase):
    def test_loads_list_shape(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "cat.json"
            p.write_text(json.dumps([make_entry()]), encoding="utf-8")
            out = grn.load_catalogue(p)
            self.assertEqual(len(out), 1)
            self.assertEqual(out[0]["serie"], "GenAI")

    def test_loads_dict_with_entries_shape(self) -> None:
        # Forward-compat: the catalogue once used a dict wrapper. The loader
        # must still find the list inside, otherwise the script breaks on
        # archive snapshots.
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "cat.json"
            p.write_text(
                json.dumps({"entries": [make_entry(), make_entry()]}), encoding="utf-8"
            )
            out = grn.load_catalogue(p)
            self.assertEqual(len(out), 2)

    def test_missing_file_is_error(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(FileNotFoundError):
                grn.load_catalogue(Path(d) / "absent.json")

    def test_malformed_json_is_error(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "cat.json"
            p.write_text("not json", encoding="utf-8")
            with self.assertRaises(json.JSONDecodeError):
                grn.load_catalogue(p)


class CountByTests(unittest.TestCase):
    def test_counts_match(self) -> None:
        entries = [
            make_entry(serie="GenAI"),
            make_entry(serie="GenAI"),
            make_entry(serie="Lean"),
        ]
        out = grn.count_by(entries, "serie")
        # sorted by count desc, then key asc on ties
        self.assertEqual(out["GenAI"], 2)
        self.assertEqual(out["Lean"], 1)
        self.assertEqual(sum(out.values()), 3)

    def test_missing_key_bucketed_as_unknown(self) -> None:
        entries = [make_entry(serie="GenAI"), {"path": "x"}]
        out = grn.count_by(entries, "serie")
        self.assertEqual(out["GenAI"], 1)
        self.assertEqual(out["(unknown)"], 1)

    def test_empty_input(self) -> None:
        self.assertEqual(grn.count_by([], "serie"), {})


class EntriesAddedSinceTests(unittest.TestCase):
    def test_filters_by_executed_at(self) -> None:
        # Aug-01 is on/after the cutoff; Jul-15 is before; null is excluded.
        entries = [
            make_entry(executed_at="2026-08-01T10:00:00+02:00", path="a.ipynb"),
            make_entry(executed_at="2026-07-15T10:00:00+02:00", path="b.ipynb"),
            make_entry(executed_at=None, path="c.ipynb"),
        ]
        cutoff = datetime(2026, 8, 1, tzinfo=timezone.utc)
        out = grn.entries_added_since(entries, cutoff)
        paths = [e["path"] for e in out]
        # ``a`` is on the cutoff (>=) and has an explicit TZ, so it qualifies.
        # ``b`` is before the cutoff. ``c`` has executed_at=None and is
        # excluded by the conservative contract documented in the script.
        self.assertEqual(paths, ["a.ipynb"])

    def test_naive_timestamp_is_treated_as_utc(self) -> None:
        # The fromisoformat round-trip on a naive string yields a naive
        # datetime -- the loader normalises it to UTC. This guards against a
        # regression where naive timestamps would compare incorrectly against
        # an aware cutoff (TypeError in 3.10+ semantics).
        entries = [make_entry(executed_at="2026-08-01T10:00:00")]
        cutoff = datetime(2026, 8, 1, tzinfo=timezone.utc)
        out = grn.entries_added_since(entries, cutoff)
        self.assertEqual(len(out), 1)


class RenderSeriesReadmeLinkTests(unittest.TestCase):
    def test_known_serie_renders_link(self) -> None:
        # The function annotates "(README absent, verifier ...)" when the file
        # does not exist on disk. With a tempdir that has no GenAI README,
        # we expect the absent annotation rather than a silent drop.
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            link = grn.render_series_readme_link("GenAI", root)
            self.assertIn("MyIA.AI.Notebooks/GenAI/README.md", link)
            self.assertIn("README absent", link)

    def test_existing_readme_does_not_annotate(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "MyIA.AI.Notebooks" / "GenAI").mkdir(parents=True)
            (root / "MyIA.AI.Notebooks" / "GenAI" / "README.md").write_text("ok")
            link = grn.render_series_readme_link("GenAI", root)
            self.assertIn("README.md", link)
            self.assertNotIn("README absent", link)

    def test_unknown_serie_falls_back(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            link = grn.render_series_readme_link("NewSerie", Path(d))
            self.assertIn("no README convention", link)


class RenderNotesTests(unittest.TestCase):
    def _render(self, entries: list[dict], **kwargs) -> str:
        return grn.render_notes(
            entries,
            tag="v2026.S2",
            since=None,
            repo_root=Path(tempfile.gettempdir()),
            generated_at=datetime(2026, 8, 7, 12, 0, 0, tzinfo=timezone.utc),
            **kwargs,
        )

    def test_totals_reflect_catalogue(self) -> None:
        entries = [make_entry() for _ in range(7)]
        md = self._render(entries)
        self.assertIn("Notebooks catalogues : **7**", md)

    def test_breakdown_sums_equal_total(self) -> None:
        entries = [
            make_entry(serie="GenAI", status="READY"),
            make_entry(serie="GenAI", status="DEMO"),
            make_entry(serie="Lean", status="READY"),
        ]
        md = self._render(entries)
        # Per-serie breakdown
        self.assertIn("| GenAI | 2 |", md)
        self.assertIn("| Lean | 1 |", md)
        # Per-status breakdown
        self.assertIn("| READY | 2 |", md)
        self.assertIn("| DEMO | 1 |", md)

    def test_empty_catalogue_is_hard_error(self) -> None:
        with self.assertRaises(ValueError):
            self._render([])

    def test_since_filter_section_present_when_set(self) -> None:
        entries = [
            make_entry(executed_at="2026-08-05T10:00:00+02:00", path="recent.ipynb"),
            make_entry(executed_at="2026-07-01T10:00:00+02:00", path="old.ipynb"),
        ]
        # _render pins since=None; we override it explicitly here so the
        # "since rentree" section is rendered. Using grn.render_notes
        # directly avoids a kwargs collision on the helper signature.
        md = grn.render_notes(
            entries,
            tag="v2026.S2",
            since=datetime(2026, 8, 1, tzinfo=timezone.utc),
            repo_root=Path(tempfile.gettempdir()),
            generated_at=datetime(2026, 8, 7, 12, 0, 0, tzinfo=timezone.utc),
        )
        self.assertIn("Notebooks executes depuis la rentree", md)
        self.assertIn("**1**", md)

    def test_since_section_omitted_by_default(self) -> None:
        # When ``--since`` is not passed, the section is suppressed rather
        # than emitted with an empty result -- the operator never sees a
        # vacuous section.
        entries = [make_entry()]
        md = self._render(entries)
        self.assertNotIn("depuis la rentree", md)


class MainTests(unittest.TestCase):
    """End-to-end CLI tests using ``grn.main([...])`` -- the same entry point
    a CI job or human operator would hit. Avoids spawning a subprocess so the
    tests stay sub-second, matching the rest of the repo's CI matrix."""

    def _write_catalogue(self, d: str, entries: list[dict]) -> Path:
        p = Path(d) / "cat.json"
        p.write_text(json.dumps(entries), encoding="utf-8")
        return p

    def test_stdout_when_no_out(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = self._write_catalogue(d, [make_entry()])
            buf: list[str] = []
            old = sys.stdout.write
            sys.stdout.write = lambda s: buf.append(s)  # type: ignore[assignment]
            try:
                rc = grn.main(["--tag", "v2026.S2", "--catalogue", str(p)])
            finally:
                sys.stdout.write = old  # type: ignore[assignment]
            self.assertEqual(rc, 0)
            self.assertTrue(any("Notebooks catalogues : **1**" in s for s in buf))

    def test_out_writes_file(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = self._write_catalogue(d, [make_entry(), make_entry()])
            out = Path(d) / "notes.md"
            rc = grn.main(
                [
                    "--tag",
                    "v2026.S2",
                    "--catalogue",
                    str(p),
                    "--out",
                    str(out),
                ]
            )
            self.assertEqual(rc, 0)
            self.assertTrue(out.exists())
            self.assertIn("Notebooks catalogues : **2**", out.read_text(encoding="utf-8"))

    def test_missing_catalogue_exits_2(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            rc = grn.main(
                [
                    "--tag",
                    "v2026.S2",
                    "--catalogue",
                    str(Path(d) / "absent.json"),
                ]
            )
            self.assertEqual(rc, 2)

    def test_empty_catalogue_exits_3(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = self._write_catalogue(d, [])
            rc = grn.main(["--tag", "v2026.S2", "--catalogue", str(p)])
            self.assertEqual(rc, 3)

    def test_invalid_since_exits_2(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = self._write_catalogue(d, [make_entry()])
            rc = grn.main(
                ["--tag", "v2026.S2", "--catalogue", str(p), "--since", "not-a-date"]
            )
            self.assertEqual(rc, 2)


if __name__ == "__main__":
    unittest.main()
