"""Tests for scripts/notebook_tools/phase0_sample_stratify.py.

Couvre les 4 points P0 du preflight po-2025 (cf. commentaire PR #13713
5471093380) :

  1. ``revision_band`` couvre les SIX bandes EPIC #9768 (1, 2-4, 5-9,
     10-19, 20-39, 40+).
  2. ``band_priority`` est deterministe et privilegie les bandes hautes.
  3. ``run_scanner`` est fail-loud sur les 5 cas degeneres du scanner.
  4. ``select_top_per_family`` >= 4 familles distinctes en sortie (critere
     Phase 0 EPIC #9768).

Note : le module n'a pas de loop au top-level (juste un guard
``if __name__ == "__main__"``), donc l'import est direct sous pytest.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import phase0_sample_stratify as p0

import pytest


# -------- SIX bandes EPIC #9768 --------

class TestRevisionBand:
    """Les SIX bandes doivent etre couvertes par ``revision_band``."""

    @pytest.mark.parametrize(
        "revs,expected",
        [
            (0, None),       # 0 = jamais touche par main, exclu
            (1, "1"),        # limite basse bande 1
            (2, "2-4"),
            (4, "2-4"),      # limite haute bande 2-4
            (5, "5-9"),
            (9, "5-9"),      # limite haute bande 5-9
            (10, "10-19"),
            (19, "10-19"),   # limite haute bande 10-19
            (20, "20-39"),
            (39, "20-39"),   # limite haute bande 20-39
            (40, "40+"),
            (100, "40+"),
            (10**9, "40+"),
        ],
    )
    def test_six_bandes(self, revs, expected):
        assert p0.revision_band(revs) == expected

    def test_six_labels_distincts(self):
        """Les SIX bandes doivent produire SIX labels distincts."""
        labels = {p0.revision_band(n) for n in (1, 3, 7, 15, 30, 100)}
        assert len(labels) == 6, f"attendu 6 labels, obtenu {labels}"
        assert labels == {"1", "2-4", "5-9", "10-19", "20-39", "40+"}

    def test_REVISION_BANDS_a_six_entrees(self):
        """Le tableau ``REVISION_BANDS`` doit contenir exactement 6 entrees."""
        assert len(p0.REVISION_BANDS) == 6


# -------- Tri deterministe par bande prioritaire --------

class TestBandPriority:
    """``band_priority`` : 40+ > 20-39 > 10-19 > 5-9 > 2-4 > 1 > None."""

    @pytest.mark.parametrize(
        "label_a,label_b",
        [
            ("40+", "20-39"),
            ("20-39", "10-19"),
            ("10-19", "5-9"),
            ("5-9", "2-4"),
            ("2-4", "1"),
        ],
    )
    def test_bandes_havent_priorite_sur_basses(self, label_a, label_b):
        """bandes hautes < bandes basses numeriquement (cle de tri croissante)."""
        assert p0.band_priority(label_a) < p0.band_priority(label_b)

    def test_none_exclu(self):
        assert p0.band_priority(None) == 0


# -------- Fail-loud scanner --------

class TestRunScannerFailLoud:
    """``run_scanner`` doit marquer INDETERMINE + scanner_error sur 5 cas."""

    def _make_selection(self):
        return [{"family": "Test", "path": "fake.ipynb", "total_revisions": 10}]

    def test_payload_liste_vide(self, monkeypatch):
        """Cas 5 : liste vide -> scanner_error + INDETERMINE."""
        import subprocess

        class _FakeCompleted:
            returncode = 0
            stdout = "[]"
            stderr = ""

        monkeypatch.setattr(
            subprocess, "run",
            lambda *a, **kw: _FakeCompleted(),
        )
        out = p0.run_scanner(self._make_selection())
        assert out[0]["verdict"] == "INDETERMINE"
        assert "liste vide" in out[0]["scanner_error"]

    def test_stdout_vide(self, monkeypatch):
        """Cas 2 : stdout vide -> scanner_error + INDETERMINE."""
        import subprocess

        class _FakeCompleted:
            returncode = 0
            stdout = "   \n  "
            stderr = ""

        monkeypatch.setattr(
            subprocess, "run",
            lambda *a, **kw: _FakeCompleted(),
        )
        out = p0.run_scanner(self._make_selection())
        assert out[0]["verdict"] == "INDETERMINE"
        assert "stdout vide" in out[0]["scanner_error"]

    def test_stdout_non_json(self, monkeypatch):
        """Cas 3 : stdout non-JSON -> scanner_error + INDETERMINE."""
        import subprocess

        class _FakeCompleted:
            returncode = 0
            stdout = "ceci n'est pas du JSON"
            stderr = ""

        monkeypatch.setattr(
            subprocess, "run",
            lambda *a, **kw: _FakeCompleted(),
        )
        out = p0.run_scanner(self._make_selection())
        assert out[0]["verdict"] == "INDETERMINE"
        assert "non-JSON" in out[0]["scanner_error"]

    def test_payload_non_liste(self, monkeypatch):
        """Cas 4 : payload non-liste (dict, str, ...) -> scanner_error."""
        import subprocess

        class _FakeCompleted:
            returncode = 0
            stdout = '{"unexpected": "dict"}'
            stderr = ""

        monkeypatch.setattr(
            subprocess, "run",
            lambda *a, **kw: _FakeCompleted(),
        )
        out = p0.run_scanner(self._make_selection())
        assert out[0]["verdict"] == "INDETERMINE"
        assert "non-liste" in out[0]["scanner_error"]

    def test_subprocess_rc_nonzero(self, monkeypatch):
        """Cas 1 : returncode != 0 -> scanner_error + INDETERMINE."""
        import subprocess

        class _FakeCompleted:
            returncode = 1
            stdout = ""
            stderr = "boom"

        monkeypatch.setattr(
            subprocess, "run",
            lambda *a, **kw: _FakeCompleted(),
        )
        out = p0.run_scanner(self._make_selection())
        assert out[0]["verdict"] == "INDETERMINE"
        assert "rc=1" in out[0]["scanner_error"]

    def test_entree_sans_verdict(self, monkeypatch):
        """Cas 6 : entree payload valide mais sans champ verdict."""
        import subprocess

        class _FakeCompleted:
            returncode = 0
            stdout = '[{"path": "x.ipynb", "findings": []}]'
            stderr = ""

        monkeypatch.setattr(
            subprocess, "run",
            lambda *a, **kw: _FakeCompleted(),
        )
        out = p0.run_scanner(self._make_selection())
        assert out[0]["verdict"] == "INDETERMINE"
        assert "sans verdict" in out[0]["scanner_error"]

    def test_scanner_introuvable(self, monkeypatch):
        """Cas 0 : le scanner n'existe pas sur disque."""
        from pathlib import Path
        monkeypatch.setattr(
            Path, "exists", lambda self: False,
        )
        out = p0.run_scanner(self._make_selection())
        assert all(s["verdict"] == "INDETERMINE" for s in out)
        assert all("introuvable" in s.get("scanner_error", "") for s in out)

    def test_cas_nominal_passe(self, monkeypatch):
        """Cas nominal : payload liste non vide avec verdict -> pas d'erreur."""
        import subprocess

        class _FakeCompleted:
            returncode = 0
            stdout = '[{"path": "x.ipynb", "verdict": "SAIN", "findings": [], "notes": "ok"}]'
            stderr = ""

        monkeypatch.setattr(
            subprocess, "run",
            lambda *a, **kw: _FakeCompleted(),
        )
        out = p0.run_scanner(self._make_selection())
        assert out[0]["verdict"] == "SAIN"
        assert "scanner_error" not in out[0]


# -------- ``generated_at_utc`` dans la sortie --------

class TestOutputSchema:
    """La sortie JSON doit inclure ``generated_at_utc`` (coherence docstring)."""

    def test_generated_at_utc_present(self, monkeypatch, tmp_path, capsys):
        """Le main() doit emettre un champ ``generated_at_utc`` ISO-8601."""
        import subprocess

        # Eviter que le scanner externe soit appele.
        class _FakeCompleted:
            returncode = 0
            stdout = '[{"path": "x.ipynb", "verdict": "SAIN", "findings": [], "notes": ""}]'
            stderr = ""

        monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeCompleted())

        # Stub argparse : on court-circuite parse_args et on fixe --select-only off.
        class _Args:
            families = ["GenAI"]
            per_family = 1
            min_revisions = 1
            output_json = tmp_path / "out.json"
            select_only = False

        monkeypatch.setattr(p0, "parse_args", lambda: _Args())
        monkeypatch.setattr(p0, "build_revision_counts", lambda: {})
        # Stub select pour eviter le scan du disque.
        monkeypatch.setattr(
            p0, "select_top_per_family",
            lambda **kw: [
                {"family": "GenAI", "path": "x.ipynb",
                 "total_revisions": 5, "revision_band": "2-4"}
            ],
        )

        rc = p0.main()
        assert rc == 0
        import json as _json
        payload = _json.loads(_Args.output_json.read_text(encoding="utf-8"))
        assert "generated_at_utc" in payload
        # Format ISO-8601 UTC.
        assert payload["generated_at_utc"].endswith("+00:00") or \
               payload["generated_at_utc"].endswith("Z")


# -------- Cliquet rename-aware pour count_revisions_follow (#13776) --------

class TestCountRevisionsFollow:
    """Cliquet de non-regression pour ``count_revisions_follow`` (#13776).

    Ce compteur est le compte AUTHENTIQUE de revisions du selecteur Phase 0
    (l.204 de scripts/notebook_tools/phase0_sample_stratify.py) : il fixe la
    bande d'un notebook, donc sa presence dans l'echantillon d'audit #9768.
    Il n'avait aucun test. Un futur refactor qui retirerait ``--follow`` de la
    liste d'arguments passerait toute la suite au vert (les 11 tests existants
    portent sur les bandes/priorites/fail-loud, aucun ne traverse cette
    fonction). Les deux tests ci-dessous echouent si ``--follow`` disparait.
    """

    def _make_fixture(self, tmp_path, monkeypatch):
        """Repaire git auto-contenu : commit c1, ``git mv``, commit c2.

        Le module derive ``REPO_ROOT`` de son propre emplacement et exige que
        le notebook soit dessous ; on pointe donc le module sur le repaire via
        ``monkeypatch`` (aucune dependance au corpus reel du depot).
        """
        import subprocess

        repo = tmp_path / "repo"
        repo.mkdir()

        def git(*args):
            subprocess.run(["git", "-C", str(repo), *args], check=True)

        git("init", "-q")
        nb = repo / "notebook.ipynb"
        nb.write_text("{}", encoding="utf-8")
        git("add", ".")
        git("-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "c1")
        renamed = repo / "renamed.ipynb"
        git("mv", "notebook.ipynb", "renamed.ipynb")
        git("-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "c2")

        monkeypatch.setattr(p0, "REPO_ROOT", repo)
        return repo, renamed

    def test_follow_compte_a_travers_le_rename(self, tmp_path, monkeypatch):
        """Sans ``--follow``, ``git log`` sur le chemin renomme voit 1 commit ;
        avec ``--follow`` il voit les 2. Le cliquet exige >= 2."""
        _repo, renamed = self._make_fixture(tmp_path, monkeypatch)
        assert p0.count_revisions_follow(renamed) >= 2

    def test_sans_follow_le_compte_nu_est_1_controle_positif(self, tmp_path, monkeypatch):
        """Preuve que le cliquet n'est pas une assertion morte (cf. #13667) :
        le compte NU sur le chemin renomme vaut exactement 1, donc un compte
        traversant le rename (>= 2) ne peut venir que de ``--follow``. Retirer
        cet argument fait echouer le test precedent."""
        import subprocess

        repo, _renamed = self._make_fixture(tmp_path, monkeypatch)
        bare = subprocess.run(
            ["git", "-C", str(repo), "log", "HEAD", "--format=oneline", "--", "renamed.ipynb"],
            capture_output=True, text=True, encoding="utf-8", check=True,
        )
        assert sum(1 for l in bare.stdout.splitlines() if l.strip()) == 1