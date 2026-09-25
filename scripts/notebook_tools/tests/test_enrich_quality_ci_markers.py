"""Tests du marqueur body ``enrich-quality: reecriture assumee`` (#17744).

Symetrique des marqueurs des gardes jumeaux (#13491 md-content-loss,
#14532 plan-loss) : une reecriture ANNONCEE (Epic #14442 D3) ne doit pas
bloquer sur la signature MD_REWRITE, mais un marqueur ne peut jamais masquer
une categorie de defaut absolue (anchors, hrefs, diacritics).

Couverture exigee par l'issue :
  1. marqueur present + finding base-vs-head (MD_REWRITE) -> pass ;
  2. marqueur present + finding absolu (MD_ANCHOR) -> toujours fail ;
  3. marqueur malforme / mauvais notebook -> inert.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import enrich_quality_ci  # noqa: E402


NB_NAME = "rl_15_grpo_group_relative_policy.ipynb"
MARKER = (
    f"enrich-quality: reecriture assumee -- MyIA.AI.Notebooks/RL/{NB_NAME} : "
    "retrait de la chronologie Git (Epic #14442 D3), substance relue base et tete"
)
MD_REWRITE = (
    "MD_REWRITE",
    "only 13/83 substantive markdown lines of the base survive verbatim (16%)"
    " -- announced extension is a rewrite",
)
MD_ANCHOR = ("MD_ANCHOR", "markdown cites output of code[2] but that cell has no output")


# ---------------------------------------------------------------------------
# 1. Parseur
# ---------------------------------------------------------------------------

class TestParsePrBodyMarkers:
    def _parse(self, body: str) -> bool:
        return enrich_quality_ci._parse_pr_body_markers(
            body, Path(f"MyIA.AI.Notebooks/RL/{NB_NAME}")
        )

    def test_valid_marker_full_path(self):
        assert self._parse(f"Intro\n\n{MARKER}\n") is True

    def test_valid_marker_basename(self):
        body = f"enrich-quality: reecriture assumee -- {NB_NAME} : raison"
        assert self._parse(body) is True

    def test_em_dash_tolerated(self):
        body = f"enrich-quality: reecriture assumee — {NB_NAME} : raison"
        assert self._parse(body) is True

    def test_accented_variants_tolerated(self):
        # Formes couvertes par la classe `re[eé]` des jumeaux (#13491) :
        # "reecriture" et "reécriture" (2e lettre e/é). Ni « recriture »
        # (e simple) ni « réécriture » (2e lettre é) n'en font partie.
        for token in ("reecriture assumee", "reécriture assumee", "reécriture assumée"):
            assert self._parse(f"enrich-quality: {token} -- {NB_NAME} : raison") is True

    def test_wrong_notebook_inert(self):
        body = "enrich-quality: reecriture assumee -- MyIA.AI.Notebooks/RL/rl_6c_ppo_from_scratch.ipynb : autre notebook"
        assert self._parse(body) is False

    def test_missing_reason_inert(self):
        # Pas de `` : <raison>`` final : le marqueur reste incomplet.
        assert self._parse(f"enrich-quality: reecriture assumee -- {NB_NAME}") is False

    def test_empty_body_inert(self):
        assert self._parse("") is False


# ---------------------------------------------------------------------------
# 2-3. Verdict : le marqueur ne couvre QUE les categories base-vs-head
# ---------------------------------------------------------------------------

@pytest.fixture
def run_gate(monkeypatch, tmp_path):
    """Retourne une fonction run(findings, body_text) -> (rc, stdout)."""
    head = tmp_path / NB_NAME
    head.write_text("{}", encoding="utf-8")
    base = tmp_path / "base.ipynb"
    base.write_text("{}", encoding="utf-8")
    body_path = tmp_path / "body.md"
    monkeypatch.setattr(enrich_quality_ci, "resolve_base", lambda *a, **k: str(base))

    def run(findings: list[tuple[str, str]], body_text: str = "") -> int:
        monkeypatch.setattr(enrich_quality_ci, "regressions", lambda *a, **k: list(findings))
        body_path.write_text(body_text, encoding="utf-8")
        return enrich_quality_ci.main([
            "--base", "resolved-by-monkeypatch", "--head", str(head),
            "--pr-body-file", str(body_path),
        ])

    return run, head, tmp_path


def test_md_rewrite_without_marker_fails(run_gate, capsys):
    run, *_ = run_gate
    assert run([MD_REWRITE]) == 1
    assert "REGRESSION" in capsys.readouterr().out


def test_md_rewrite_with_marker_passes_with_trace(run_gate, capsys):
    run, *_ = run_gate
    assert run([MD_REWRITE], MARKER) == 0
    out = capsys.readouterr().out
    assert "JUSTIFIED_BY_BODY" in out
    assert "MD_REWRITE" in out  # trace preserved, not silently dropped


def test_absolute_finding_still_fails_with_marker(run_gate, capsys):
    run, *_ = run_gate
    assert run([MD_ANCHOR], MARKER) == 1
    out = capsys.readouterr().out
    assert "MD_ANCHOR" in out and "REGRESSION" in out


def test_mixed_findings_marker_covers_only_rewrite(run_gate, capsys):
    run, *_ = run_gate
    assert run([MD_REWRITE, MD_ANCHOR], MARKER) == 1
    out = capsys.readouterr().out
    assert "MD_ANCHOR" in out and "REGRESSION" in out


def test_marker_wrong_notebook_inert_on_verdict(run_gate, capsys):
    run, *_ = run_gate
    wrong = "enrich-quality: reecriture assumee -- autre_serie.ipynb : raison"
    assert run([MD_REWRITE], wrong) == 1
    assert "REGRESSION" in capsys.readouterr().out


def test_env_var_channel_respected(run_gate, monkeypatch, capsys):
    run, head, tmp_path = run_gate
    monkeypatch.setattr(enrich_quality_ci, "regressions", lambda *a, **k: [MD_REWRITE])
    monkeypatch.setenv("ENRICH_QUALITY_PR_BODY", MARKER)
    rc = enrich_quality_ci.main(["--base", "x", "--head", str(head)])
    assert rc == 0
    assert "JUSTIFIED_BY_BODY" in capsys.readouterr().out
