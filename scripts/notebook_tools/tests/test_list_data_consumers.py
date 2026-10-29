"""Tests for scripts/notebook_tools/list_data_consumers.py.

The organ answers one question: when a vendored taxonomy file changes, which
notebooks read it, and which of those are absent from the same change set?
Tests cover the predicate, the exclusion of translation/archive consumers,
deduplication, and the two controls (a real data file finds consumers; a
non-vendored file finds none).
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import list_data_consumers as organ

REPO_ROOT = Path(__file__).resolve().parents[3]

OWL = "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ontologies/argumentum_fallacies.owl"
CSV = "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_fallacies_taxonomy.csv"
CARDS = "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-02b-Argumentum-Cards-Python.ipynb"


class TestVendoredDataPredicate:
    def test_owl_is_vendored(self):
        assert organ.is_vendored_data(OWL)

    def test_taxonomy_csv_is_vendored(self):
        assert organ.is_vendored_data(CSV)

    def test_other_csv_is_not_vendored(self):
        assert not organ.is_vendored_data(
            "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/other.csv"
        )

    def test_docs_are_not_vendored(self):
        assert not organ.is_vendored_data("docs/reference/common-commands.md")


class TestConsumerExclusions:
    def test_archive_consumer_is_excluded(self):
        assert organ.EXCLUDED_CONSUMER.search(
            "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/_archive/Old.ipynb"
        )

    def test_translation_consumer_is_excluded(self):
        assert organ.EXCLUDED_CONSUMER.search(
            "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-02b-EN.ipynb"
        )

    def test_source_consumer_is_kept(self):
        assert not organ.EXCLUDED_CONSUMER.search(CARDS)


@pytest.mark.skipif(not REPO_ROOT.joinpath(".git").exists(), reason="needs the git index")
class TestPositiveControl:
    def test_owl_finds_consumers(self):
        cons = organ.consumers_of(Path(OWL).name, cwd=REPO_ROOT)
        assert cons, "aucun carnet ne lit l'OWL des sophismes"
        assert any("Argumentation-" in c for c in cons)

    def test_changed_consumer_is_not_reported_missing(self):
        report = organ.analyse([CSV, CARDS], cwd=REPO_ROOT)
        assert CARDS not in report["missing"]

    def test_unchanged_consumer_is_reported_missing(self):
        report = organ.analyse([OWL], cwd=REPO_ROOT)
        assert report["missing"], "un changement de donnee seule devrait signaler des carnets"

    def test_render_mentions_the_action(self):
        text = organ.render(organ.analyse([OWL], cwd=REPO_ROOT))
        assert "A RE-EXECUTER" in text


@pytest.mark.skipif(not REPO_ROOT.joinpath(".git").exists(), reason="needs the git index")
class TestNegativeControl:
    def test_non_vendored_file_is_silent(self):
        report = organ.analyse(["docs/reference/common-commands.md"], cwd=REPO_ROOT)
        assert report["data_files"] == []
        assert report["missing"] == []
        assert organ.render(report) == ""


@pytest.mark.skipif(not REPO_ROOT.joinpath(".git").exists(), reason="needs the git index")
class TestDeduplication:
    def test_notebook_citing_two_data_files_appears_once(self):
        report = organ.analyse([OWL, CSV], cwd=REPO_ROOT)
        assert len(report["missing"]) == len(set(report["missing"]))


class TestExitCodes:
    @pytest.mark.skipif(not REPO_ROOT.joinpath(".git").exists(), reason="needs the git index")
    def test_advisory_never_fails(self, monkeypatch):
        monkeypatch.setattr(
            organ, "changed_files", lambda base, cwd=None: [OWL]
        )
        assert organ.main(["--advisory", "--repo", str(REPO_ROOT)]) == 0

    @pytest.mark.skipif(not REPO_ROOT.joinpath(".git").exists(), reason="needs the git index")
    def test_strict_mode_fails_on_missing_consumer(self, monkeypatch):
        monkeypatch.setattr(
            organ, "changed_files", lambda base, cwd=None: [OWL]
        )
        assert organ.main(["--repo", str(REPO_ROOT)]) == 1

    def test_self_test_passes(self):
        assert organ.self_test(cwd=REPO_ROOT) == 0
