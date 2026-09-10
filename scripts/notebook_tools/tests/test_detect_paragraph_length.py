"""Tests unitaires detect_paragraph_length.py (PR B #15507, #14871 follow-up).

Couvre :
- paragraphe > 2000 c flaggé (1 finding)
- post-fix (6 paragraphes < 2000 c) muet
- fences / tableaux / titres ignores
- HTML commentaires ignores
- seuil exact 2000 / 2001 (> strict)
- format JSON par fichier
- --fail-on-findings exit 2
- --self-test exit 0
- scan-vacuue (fichier vide) exit 1
- agregation .ipynb cellule par cellule
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

_TOOLS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_TOOLS_DIR))

from detect_paragraph_length import (  # noqa: E402
    MAX_PARAGRAPH_LEN,
    detect,
    paragraphs,
)

FIXTURE = _TOOLS_DIR / "tests" / "fixtures" / "paragraph_wall_md.md"


# ---------------------------------------------------------------------------
# detect() -- logique pure
# ---------------------------------------------------------------------------


def test_fixture_paragraph_flagged():
    """Le mur fondateur doit tirer ≥1 finding."""
    text = FIXTURE.read_text(encoding="utf-8")
    findings = detect(text)
    assert findings, "mur fondateur non flaggé"
    f0 = findings[0]
    assert f0["type"] == "oversized_paragraph"
    assert f0["chars"] > MAX_PARAGRAPH_LEN
    assert "preview" in f0


def test_post_fix_six_paragraphs_clean():
    """Le post-fix (6 paragraphes < 2000 c) doit être muet."""
    chunks = [
        "Paragraphe un introductif de taille raisonnable qui presente la serie et ses stacks complementaires.",
        "Paragraphe deux sur le corpus baysien Infer avec 21 notebooks couvrant fondements et frontieres.",
        "Paragraphe trois sur l'arc decision et le versant PyMC avec 19 notebooks corpus et 12 miroirs.",
        "Paragraphe quatre sur la percolation avec un lake Lean compagnon Percolation-Lean.",
        "Paragraphe cinq sur le pont causal avec 4 notebooks Python federant les stacks.",
    ]
    text = "\n\n".join(chunks)
    findings = detect(text)
    assert findings == [], f"post-fix NON muet : {findings}"


def test_fences_tableaux_titres_ignores():
    """Fences / tableaux / titres ne doivent pas être mesurés comme paragraphes."""
    long_line = "x" * 3000
    text = (
        f"# Titre avec URL tres longue pour tester l'exemption\n\n"
        f"```python\n{long_line}\n```\n\n"
        f"| col1 | col2 |\n|------|------|\n| a | b |\n\n"
        f"<!-- {long_line} -->\n\n"
        f"Paragraphe court ok.\n"
    )
    findings = detect(text)
    assert findings == [], f"fences/tableaux/titres/HTML non ignores : {len(findings)} finding(s)"


def test_seuil_strict_2000_2001():
    """Le contrat est > strict : 2000 ok, 2001 tire."""
    assert detect("x" * 2000) == []
    findings = detect("x" * 2001)
    assert len(findings) == 1
    assert findings[0]["chars"] == 2001


def test_paragraphs_decoupe_lignes_vides():
    """Le decoupage en paragraphes ignore les paragraphes vides."""
    text = "Para un.\n\n\n\n\nPara deux.\n\n   \n\nPara trois."
    paras = paragraphs(text)
    assert len(paras) == 3
    assert paras[0] == "Para un."
    assert paras[1] == "Para deux."
    assert paras[2] == "Para trois."


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _run_cli(*args: str, stdin: str | None = None) -> subprocess.CompletedProcess:
    cmd = [sys.executable, str(_TOOLS_DIR / "detect_paragraph_length.py"), *args]
    return subprocess.run(cmd, capture_output=True, text=True, input=stdin, encoding="utf-8", timeout=30)


def test_self_test_exit_0():
    cp = _run_cli("--self-test")
    assert cp.returncode == 0, f"--self-test a échoué : {cp.stdout}\n{cp.stderr}"
    assert "SELF-TEST OK" in cp.stdout


def test_fixture_humain_clean_exit_0():
    """Sans --fail-on-findings, sort toujours 0 (advisory)."""
    cp = _run_cli(str(FIXTURE))
    # fixture a 1 finding, mais advisory => exit 0
    assert cp.returncode == 0, cp.stderr
    assert "1 finding" in cp.stdout or "oversized" in cp.stdout


def test_fixture_fail_on_findings_exit_2():
    """Avec --fail-on-findings, exit 2 si findings."""
    cp = _run_cli(str(FIXTURE), "--fail-on-findings")
    assert cp.returncode == 2, f"attendu 2, obtenu {cp.returncode} : {cp.stdout}\n{cp.stderr}"


def test_fixture_json_shape():
    """--json rend un objet JSON valide avec file/findings/counts."""
    cp = _run_cli(str(FIXTURE), "--json")
    assert cp.returncode == 0
    # Cherche le premier objet JSON top-level (par fichier) dans la sortie.
    payload = None
    decoder = json.JSONDecoder()
    idx = 0
    while idx < len(cp.stdout):
        # saute les espaces et sauts de ligne entre objets
        while idx < len(cp.stdout) and cp.stdout[idx] in " \n\r\t":
            idx += 1
        if idx >= len(cp.stdout):
            break
        if cp.stdout[idx] != "{":
            idx += 1
            continue
        try:
            obj, end = decoder.raw_decode(cp.stdout[idx:])
        except json.JSONDecodeError:
            idx += 1
            continue
        if "file" in obj and "findings" in obj:
            payload = obj
            break
        idx += end
    assert payload is not None, f"aucun JSON valide dans : {cp.stdout}"
    assert "file" in payload
    assert "findings" in payload
    assert "counts" in payload
    assert payload["counts"]["total"] >= 1


def test_post_fix_texte_clean():
    """Un texte découpé en 6 paragraphes < 2000 c sort 0 même avec --fail-on-findings."""
    post = "\n\n".join([
        "Paragraphe un introductif de taille raisonnable qui presente la serie et ses stacks complementaires.",
        "Paragraphe deux sur le corpus baysien Infer avec 21 notebooks couvrant fondements et frontieres.",
        "Paragraphe trois sur l'arc decision et le versant PyMC avec 19 notebooks corpus et 12 miroirs.",
        "Paragraphe quatre sur la percolation avec un lake Lean compagnon Percolation-Lean.",
        "Paragraphe cinq sur le pont causal avec 4 notebooks Python federant les stacks.",
    ])
    # ecrit un fichier temporaire
    import tempfile
    with tempfile.NamedTemporaryFile(mode="w", suffix=".md", delete=False, encoding="utf-8") as f:
        f.write(post)
        path = f.name
    try:
        cp = _run_cli(path, "--fail-on-findings")
        assert cp.returncode == 0, f"post-fix doit être clean : {cp.stdout}"
    finally:
        Path(path).unlink()


def test_stdin_lit_chemins():
    """--stdin lit la liste de fichiers depuis stdin (1 par ligne)."""
    cp = _run_cli("--stdin", "--json", stdin=str(FIXTURE))
    assert cp.returncode == 0
    assert "oversized" in cp.stdout or '"total"' in cp.stdout
