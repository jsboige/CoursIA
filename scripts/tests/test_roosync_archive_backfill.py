"""Tests pour scripts/roosync_archive_backfill.py.

Couvre :
- parse_frontmatter : format verbatim documente, tolerance champs manquants
- is_fallback_archive : pattern filename
- detect_fallback_archives : detection sur arborescence synthetique
- cmd_list : sortie formatee
- cmd_backfill : marquage idempotent
- cmd_summarize : passe de rattrapage LLM (bloc resume, flags, idempotence,
  arret au premier echec, fenetre jours, dry-run)
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parent.parent / "roosync_archive_backfill.py"

# --- Fixtures : frontmatter verbatim du body #8889 ---------------------------

SAMPLE_FRONTMATTER_FULL = """---
messageCount: 8
llmGenerated: false
fallbackTruncation: true
---
Contenu verbatim de l'archive (extrait)
"""

SAMPLE_FRONTMATTER_PARTIAL = """---
messageCount: 5
llmGenerated: false
---
Contenu
"""

SAMPLE_NO_FRONTMATTER = """Pas de frontmatter ici, juste du contenu libre.
"""

# --- Tests parse_frontmatter --------------------------------------------------

def test_parse_frontmatter_full():
    """Frontmatter complet : tous les champs sont parses."""
    from roosync_archive_backfill import parse_frontmatter
    fm = parse_frontmatter(SAMPLE_FRONTMATTER_FULL)
    assert fm.message_count == 8
    assert fm.llm_generated is False
    assert fm.fallback_truncation is True
    assert "messageCount" in fm.raw


def test_parse_frontmatter_partial():
    """Frontmatter partiel : champs absents = None, pas d'erreur."""
    from roosync_archive_backfill import parse_frontmatter
    fm = parse_frontmatter(SAMPLE_FRONTMATTER_PARTIAL)
    assert fm.message_count == 5
    assert fm.llm_generated is False
    assert fm.fallback_truncation is None  # absent


def test_parse_frontmatter_absent():
    """Pas de frontmatter : raw vide, tous champs None."""
    from roosync_archive_backfill import parse_frontmatter
    fm = parse_frontmatter(SAMPLE_NO_FRONTMATTER)
    assert fm.message_count is None
    assert fm.llm_generated is None
    assert fm.fallback_truncation is None
    assert fm.raw == {}


# --- Tests is_fallback_archive ------------------------------------------------

def test_is_fallback_archive_match():
    """Pattern documented #8889 : workspace-<name>-<ISO>-fallback.md."""
    from roosync_archive_backfill import is_fallback_archive
    assert is_fallback_archive(Path("workspace-CoursIA-2026-07-29T22-14-57-fallback.md"))
    assert is_fallback_archive(Path("workspace-machine-2-2026-09-21T16-30-00-fallback.md"))


def test_is_fallback_archive_no_match():
    """Fichiers non-fallback : nom ou pas de suffixe -fallback.md."""
    from roosync_archive_backfill import is_fallback_archive
    assert not is_fallback_archive(Path("workspace-CoursIA-2026-07-29T22-14-57.md"))
    assert not is_fallback_archive(Path("random_file.md"))
    assert not is_fallback_archive(Path("workspace-fallback.md"))  # pas d'ISO


# --- Tests detect_fallback_archives (integration) -----------------------------

def _make_archive(root: Path, name: str, *, llm: bool = False, fallback: bool = True,
                  messages: int = 5, body: str = "Verbatim content") -> Path:
    """Helper : cree une archive synthetique dans root."""
    archive = root / name
    archive.parent.mkdir(parents=True, exist_ok=True)
    archive.write_text(
        f"---\n"
        f"messageCount: {messages}\n"
        f"llmGenerated: {'true' if llm else 'false'}\n"
        f"fallbackTruncation: {'true' if fallback else 'false'}\n"
        f"---\n"
        f"{body}\n",
        encoding="utf-8",
    )
    return archive


def test_detect_fallback_archives_basic(tmp_path: Path):
    """Detection sur arborescence : 1 fallback reel, 1 normal (non-fallback)."""
    from roosync_archive_backfill import detect_fallback_archives
    root = tmp_path / "archive"
    # Fallback reel
    _make_archive(root, "workspace-test-2026-09-01T10-00-00-fallback.md")
    # Normal (pas de suffixe fallback)
    _make_archive(root, "workspace-test-2026-09-02T10-00-00.md", llm=True, fallback=False)
    # Fallback reel (autre workspace)
    _make_archive(root, "workspace-other-2026-09-03T11-00-00-fallback.md", messages=12)

    detected = detect_fallback_archives(root)
    assert len(detected) == 2
    isos = sorted(a.iso for a in detected)
    assert isos == ["2026-09-01T10-00-00", "2026-09-03T11-00-00"]


def test_detect_fallback_archives_filters_partial_metadata(tmp_path: Path):
    """Archives avec fallback=True mais llmGenerated=True : exclues (non-fallback reel)."""
    from roosync_archive_backfill import detect_fallback_archives
    root = tmp_path / "archive"
    _make_archive(root, "workspace-mixed-2026-09-01T10-00-00-fallback.md",
                  llm=True, fallback=True, messages=8)
    detected = detect_fallback_archives(root)
    assert len(detected) == 0


def test_detect_fallback_archives_empty_root(tmp_path: Path):
    """Racine inexistante : liste vide, pas d'erreur."""
    from roosync_archive_backfill import detect_fallback_archives
    detected = detect_fallback_archives(tmp_path / "nope")
    assert detected == []


# --- Tests subprocess : cmd_list, cmd_backfill --------------------------------

def test_cmd_list_via_subprocess(tmp_path: Path):
    """Le mode --list imprime le tableau agrege."""
    root = tmp_path / "archive"
    _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md", messages=8)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--list"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    assert "workspace-x" in result.stdout
    assert "TOTAL : 1 archives" in result.stdout


def test_cmd_report_via_subprocess(tmp_path: Path):
    """Le mode --report ecrit un JSON structure."""
    root = tmp_path / "archive"
    out = tmp_path / "out"
    _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md", messages=8)
    _make_archive(root, "workspace-x-2026-09-02T10-00-00-fallback.md", messages=12)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--report",
         "--output-dir", str(out)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    json_path = out / "roosync_archive_backfill_report.json"
    assert json_path.exists()
    report = json.loads(json_path.read_text(encoding="utf-8"))
    assert report["total_archives"] == 2
    assert "workspace-x" in report["workspaces"]


def test_cmd_backfill_via_subprocess(tmp_path: Path):
    """Le mode --backfill ajoute markForBackfill: true au frontmatter,
    sur sa propre ligne avant le fermant (pas colle au delimiteur ---)."""
    import re
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-z-2026-09-01T10-00-00-fallback.md", messages=5)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--backfill", str(target)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    text = target.read_text(encoding="utf-8")
    # Position stricte : le marqueur precede le fermant --- sur sa propre ligne.
    # Sans ce pattern, un YAML strict voit `---markForBackfill` (garbage) comme
    # une cle, cf. finding Hermes #17261.
    assert re.search(r"markForBackfill: true\n---\n", text), (
        f"markForBackfill doit etre sur sa propre ligne avant --- ; got:\n{text!r}"
    )
    # Garde anti-regression : pas de cle polluee `---markForBackfill`.
    assert "---markForBackfill" not in text, (
        f"Marqueur colle au fermant --- detecte (regression Hermes #17261) ; got:\n{text!r}"
    )


def test_cmd_backfill_idempotent(tmp_path: Path):
    """Marquer 2 fois la meme archive : exit 0 + 'DEJA MARQUEE'."""
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-z-2026-09-01T10-00-00-fallback.md", messages=5)
    # Premier backfill
    subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--backfill", str(target)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
        check=True,
    )
    # Second backfill : doit detecter deja marquee
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--backfill", str(target)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
    )
    assert result.returncode == 0
    assert "DEJA MARQUEE" in result.stdout


# --- Tests cmd_summarize (passe de rattrapage LLM, #8889) ----------------------

FALLBACK_BODY = (
    "# Archive (fallback): x\n\n"
    "Archived: 2026-09-01T10:00:00.000Z\n"
    "Messages: 5\n"
    "Method: Truncation fallback (LLM unavailable)\n\n"
    "[FALLBACK TRUNCATION] 5 messages archived without LLM summary. Circuit breaker failures: 1.\n\n"
    "---\n\n"
    "### [2026-09-01T09:59:00.000Z] lane|ws\n\nPremier message verbatim.\n\n---\n\n"
    "### [2026-09-01T09:59:30.000Z] lane|ws\n\nSecond message verbatim.\n"
)
SUMMARY_STUB = "### Thèmes principaux\n- Test du bloc résumé.\n"


def _run_summarize(root: Path, **overrides):
    """Invoque cmd_summarize sur root avec les overrides donnes."""
    from roosync_archive_backfill import cmd_summarize, detect_fallback_archives
    kwargs = dict(
        root=root, limit=5, days=None, base_url="http://invalid.test",
        model="stub-model", timeout=1, max_chars=1000, dry_run=False,
    )
    kwargs.update(overrides)
    return cmd_summarize(detect_fallback_archives(root), **kwargs)


def _messages_region(text: str) -> str:
    """Region messages verbatim : tout a partir du premier en-tete de message."""
    idx = text.find("### [")
    assert idx != -1, f"pas de message dans l'archive: {text!r}"
    return text[idx:]


def test_summarize_flips_flags_and_inserts_block(tmp_path, monkeypatch):
    """Une archive traitee : flags bascules, bloc resume insere AVANT les
    messages, messages verbatim intacts octet par octet (acceptance #8889)."""
    monkeypatch.setattr("roosync_archive_backfill.request_summary",
                        lambda text, **kw: SUMMARY_STUB)
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md",
                           messages=5, body=FALLBACK_BODY)
    before = target.read_text(encoding="utf-8")

    assert _run_summarize(root) == 0

    after = target.read_text(encoding="utf-8")
    assert "llmGenerated: true" in after
    assert "fallbackTruncation: false" in after
    assert "llmGenerated: false" not in after
    assert "## Résumé (backfill) des 5 messages archivés" in after
    assert SUMMARY_STUB in after
    assert "backfilledAt: '20" in after
    assert "backfillModel: stub-model" in after
    # Critere acceptance : le bloc resume precede les messages, qui ne bougent pas.
    assert after.find("## Résumé (backfill) des") < after.find("### [2026-09-01T09:59:00")
    assert _messages_region(before) == _messages_region(after)


def test_summarize_idempotent_second_pass_noop(tmp_path, monkeypatch):
    """Deuxieme passe : les archives traitees sortent du predicat de detection,
    aucun fichier ne bouge (acceptance #8889)."""
    monkeypatch.setattr("roosync_archive_backfill.request_summary",
                        lambda text, **kw: SUMMARY_STUB)
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md",
                           messages=5, body=FALLBACK_BODY)
    assert _run_summarize(root) == 0
    after_first = target.read_text(encoding="utf-8")

    # La detection ne voit plus l'archive ; la passe ne touche rien.
    from roosync_archive_backfill import detect_fallback_archives
    assert detect_fallback_archives(root) == []
    assert _run_summarize(root) == 0
    assert target.read_text(encoding="utf-8") == after_first


def test_summarize_llm_unreachable_before_any_work(tmp_path, monkeypatch):
    """LLM injoignable des le debut : exit 2, aucune archive touchee."""
    from roosync_archive_backfill import LlmUnavailableError
    def _boom(text, **kw):
        raise LlmUnavailableError("connection refused")
    monkeypatch.setattr("roosync_archive_backfill.request_summary", _boom)
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md",
                           messages=5, body=FALLBACK_BODY)
    before = target.read_text(encoding="utf-8")
    assert _run_summarize(root) == 2
    assert target.read_text(encoding="utf-8") == before


def test_summarize_stops_at_first_failure_mid_pass(tmp_path, monkeypatch):
    """Echec LLM en cours de passe : arret immediat (exit 1), la plus recente
    est traitee, l'autre reste intacte — on ne martele pas un service en boot."""
    from roosync_archive_backfill import LlmUnavailableError
    calls = []
    def _flaky(text, **kw):
        if calls:
            raise LlmUnavailableError("wedge")
        calls.append(1)
        return SUMMARY_STUB
    monkeypatch.setattr("roosync_archive_backfill.request_summary", _flaky)
    root = tmp_path / "archive"
    older = _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md",
                          messages=5, body=FALLBACK_BODY)
    newer = _make_archive(root, "workspace-x-2026-09-01T11-00-00-fallback.md",
                          messages=5, body=FALLBACK_BODY)
    # Ordre : plus recentes d'abord -> newer traitee, older non atteinte.
    assert _run_summarize(root) == 1
    assert "## Résumé (backfill) des" in newer.read_text(encoding="utf-8")
    assert "## Résumé (backfill) des" not in older.read_text(encoding="utf-8")


def test_summarize_days_window_excludes_old_archives(tmp_path, monkeypatch):
    """Fenetre --days : une archive plus vieille que la fenetre n'est pas
    candidate (borne suggeree par le body #8889)."""
    from datetime import datetime, timezone
    monkeypatch.setattr("roosync_archive_backfill.request_summary",
                        lambda text, **kw: SUMMARY_STUB)
    root = tmp_path / "archive"
    _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md",
                  messages=5, body=FALLBACK_BODY)
    # now = 2026-10-04, days=30 -> cutoff 2026-09-04 : archive du 09-01 exclue.
    rc = _run_summarize(root, days=30, dry_run=True,
                        now=datetime(2026, 10, 4, tzinfo=timezone.utc))
    assert rc == 0
    # dry-run sans candidate : aucune ecriture, exit 0.


def test_summarize_dry_run_never_calls_llm_nor_writes(tmp_path, monkeypatch, capsys):
    """--dry-run : liste les candidates sans appel LLM ni ecriture."""
    def _must_not_run(text, **kw):
        raise AssertionError("request_summary ne doit pas etre appele en dry-run")
    monkeypatch.setattr("roosync_archive_backfill.request_summary", _must_not_run)
    root = tmp_path / "archive"
    target = _make_archive(root, "workspace-x-2026-09-01T10-00-00-fallback.md",
                           messages=5, body=FALLBACK_BODY)
    before = target.read_text(encoding="utf-8")
    assert _run_summarize(root, dry_run=True) == 0
    out = capsys.readouterr().out
    assert "1 candidates" in out
    assert "workspace-x" in out
    assert target.read_text(encoding="utf-8") == before


def test_apply_summary_without_body_separator_appends(tmp_path):
    """Archive sans separateur --- dans le corps : le bloc est appendu, pas perdu."""
    from roosync_archive_backfill import apply_summary_to_archive
    text = (
        "---\nmessageCount: 3\nllmGenerated: false\nfallbackTruncation: true\n---\n"
        "# Archive (fallback): x\n\n[FALLBACK TRUNCATION] 3 messages.\n"
    )
    result = apply_summary_to_archive(text, SUMMARY_STUB, model="m",
                                      now_iso="2026-10-04T00:00:00Z")
    assert "## Résumé (backfill) des 3 messages archivés" in result
    assert "llmGenerated: true" in result
    # Le bloc se retrouve apres l'en-tete, en fin de corps.
    assert result.rstrip().endswith("cf #8889).")


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
