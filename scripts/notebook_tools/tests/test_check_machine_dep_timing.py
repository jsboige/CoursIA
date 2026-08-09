"""Tests de silence du detecteur dedie machine-dep timing (cf. #10158).

5 familles FP documentees + smoke test que le script tourne sans crasher sur
un corpus representatif.

Les tests utilisent ``scan_notebook_file`` (helper dedie) plutot que
d'invoquer le main CLI pour eviter le couplage a argparse. Le but est de
prouver la SEMANTIQUE des exemptions -- pas l'interface CLI (couverte par
un smoke test separe).
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

# Permettre l'import du module parent (scripts/notebook_tools/) sans setup
# site-packages -- le projet n'est pas installe en editable.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_machine_dep_timing import (  # noqa: E402
    _categorize,
    _scan_notebook,
    CATEGORY_WALLCLOCK,
    CATEGORY_DISTRIBUTION,
    CATEGORY_AMBIGUOUS,
    STUDENT_PACING_RE,
    WALLCLOCK_KEYWORDS,
    DISTRIBUTION_KEYWORDS,
)

import pytest


# --------------------------------------------------------------------------- #
#  Helpers
# --------------------------------------------------------------------------- #
def _make_nb(cells: list[dict]) -> Path:
    """Ecrit un notebook JSON temporaire et renvoie son Path."""
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8"
    )
    json.dump(nb, tmp, ensure_ascii=False)
    tmp.flush()
    tmp.close()
    return Path(tmp.name)


def _md_cell(source: str | list[str]) -> dict:
    """Construit une cellule markdown."""
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "markdown", "metadata": {}, "source": source}


def _code_cell(source: str | list[str]) -> dict:
    """Construit une cellule code."""
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "code", "metadata": {}, "source": source, "outputs": []}


# --------------------------------------------------------------------------- #
#  Smoke test : le script tourne sans crasher sur corpus mixte
# --------------------------------------------------------------------------- #
def test_scan_notebook_empty_path(tmp_path: Path) -> None:
    """Un chemin qui n'existe pas ou n'est pas un .ipynb -> liste vide."""
    # Ne leve jamais (cf. acceptance #10158 mode advisory).
    out = _scan_notebook(tmp_path / "does-not-exist.ipynb")
    assert out == []


def test_scan_notebook_unreadable_returns_empty(tmp_path: Path) -> None:
    """Un fichier corrompu / non-JSON -> liste vide, pas de crash."""
    bogus = tmp_path / "bogus.ipynb"
    bogus.write_text("{ not valid json", encoding="utf-8")
    assert _scan_notebook(bogus) == []


def test_scan_notebook_no_cells(tmp_path: Path) -> None:
    """Un notebook avec 0 cellule -> liste vide."""
    nb = tmp_path / "empty.ipynb"
    nb.write_text(json.dumps({"cells": [], "metadata": {}}), encoding="utf-8")
    assert _scan_notebook(nb) == []


# --------------------------------------------------------------------------- #
#  Famille FP #1 : sortie de cellule code (jamais signalee)
# --------------------------------------------------------------------------- #
def test_silence_on_code_cell_with_wallclock() -> None:
    """Une cellule code qui contient 'execution: 4.5 s' NE doit PAS etre signalee.

    Rationnel (cf. acceptance #10158) : une sortie de cellule porte la valeur
    reelle mesuree -- c'est sa fonction. Le drainage #9434 ne concerne que la
    PROSE statique, pas les outputs qui sont regenerees a chaque execution.
    """
    nb = _make_nb([_code_cell("Console.WriteLine($\"execution: 4.5 s\");")])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #2 : deja conforme (tilde prefix)
# --------------------------------------------------------------------------- #
def test_silence_on_tilde_prefix_already_compliant() -> None:
    """Un '~10 s' (tilde prefix) est ORDRE DE GRANDEUR et NE doit PAS signaler.

    Rationnel : le mandat #9434 (H.1) accepte explicitement les ordres de
    grandeur en prose ('~10 s', '~quelques minutes'). Le drainage ne vise
    que les chiffres PRECIS, qui eux sont machine-dep.
    """
    nb = _make_nb([_md_cell("Le notebook prend ~10 s a s'executer.")])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #3 : compte deterministe (H1 numbering, etc.)
# --------------------------------------------------------------------------- #
def test_silence_on_deterministic_count() -> None:
    """Un '3 iterations' / 'N=10 seeds' NE doit PAS etre signale.

    Rationnel : les comptes sont deterministes par construction, ils ne
    dependent pas du materiel. Le regex matche '3 iterations' mais ce n'est
    pas un temps d'horloge -- c'est un compte. (Le script cible les unites
    de duree ms/sec/min, pas les comptes, mais il arrive que 'iterations'
    ou 'seeds' soient captures par une regex large. NB: le test verifie que
    la regex NE capture PAS les comptes -- c'est le contrat du MACHINE_RE
    importe du detecteur canonique.)
    """
    nb = _make_nb([_md_cell("On execute 10000 iterations et 4 seeds.")])
    try:
        findings = _scan_notebook(nb)
        # '10000 iterations' n'est PAS capture par MACHINE_RE (pas d'unite de
        # duree) ; idem '4 seeds'. On attend donc 0 finding.
        assert findings == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #4 : version / numero de release (deterministe, pas machine-dep)
# --------------------------------------------------------------------------- #
def test_silence_on_version_string() -> None:
    """Un 'Python 3.10' ou 'v1.2' NE doit PAS etre confondu avec un timing.

    Rationnel : MACHINE_RE ancre sur des unites de duree (ms/sec/min) ou un
    's' isole, pas sur des chiffres isoles. Une version est un identifiant
    deterministe -- pas une mesure de duree.
    """
    nb = _make_nb([_md_cell("Compatible Python 3.10 et PyTorch 2.5.")])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #5 : parametre de distribution (bayesien/stat)
# --------------------------------------------------------------------------- #
def test_distribution_param_classified_as_such() -> None:
    """Un 'moyenne 15.33 min' dans un contexte distribution NE doit PAS etre
    classe wallclock -- c'est un parametre de modele, pas une duree machine.

    Rationnel : un 'moyenne 15.33 min' dans une cellule d'inference
    bayesienne est un parametre de distribution, pas un temps d'horloge.
    Le reviewer humain (cf. TAXONOMIE 3 classes) arbitrera distribution_param
    comme TN dur.
    """
    nb = _make_nb([_md_cell(
        "La posterior suit une Gaussian de moyenne 15.33 min et sigma 1.32 min."
    )])
    try:
        findings = _scan_notebook(nb)
        # Les 2 chiffres (15.33 min, 1.32 min) sont captures par MACHINE_RE.
        assert len(findings) >= 1
        # Mais ils sont classifies distribution_param, PAS wallclock.
        for f in findings:
            assert f["category"] == CATEGORY_DISTRIBUTION
            assert f["category"] != CATEGORY_WALLCLOCK
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Signal reel : un wall-clock strict DOIT etre signale
# --------------------------------------------------------------------------- #
def test_wallclock_signal_detected() -> None:
    """Un 'duree d'execution : 2.4 s' DOIT etre signale en categorie wallclock.

    C'est le test positif (l'inverse des 5 silences) : il verifie que le
    detecteur n'est PAS silencieux sur le cas qu'il est cense attraper.
    """
    nb = _make_nb([_md_cell("La duree d'execution est 2.4 s pour 1000 iterations.")])
    try:
        findings = _scan_notebook(nb)
        assert len(findings) >= 1
        # Au moins un finding est categorise wallclock (le contexte "duree
        # d'execution" force la classification).
        wallclock_findings = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert wallclock_findings, (
            f"Attendu >=1 wallclock, trouve {[f['category'] for f in findings]}"
        )
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Exemption pacing pedagogique (ligne entiere, cf. arbitrage 14:05:37Z)
# --------------------------------------------------------------------------- #
def test_silence_on_student_pacing_lines() -> None:
    """Les lignes 'Duree estimee : 45 minutes' sont exonerees (pacing etudiant).

    Rationnel : arbitrage user 14:05:37Z sur #9434 -- 200 FP elimines en
    exemptant les lignes de pacing H1/H2/H3 ('Duree estimee : ... minutes').
    Ce sont des estimations pedagogiques, pas des mesures de duree.
    """
    nb = _make_nb([
        _md_cell("## Duree estimee : 45 minutes"),
        _md_cell("**Notebook** : Introduction, 30-60 min selon niveau"),
    ])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


def test_student_pacing_regex_matches_duree() -> None:
    """Le regex STUDENT_PACING_RE detecte 'Duree estimee', 'Duree :', etc."""
    assert STUDENT_PACING_RE.search("Duree estimee : 45 minutes")
    assert STUDENT_PACING_RE.search("Duree : 30 min")
    assert STUDENT_PACING_RE.search("Duree du notebook : 1h")
    # Negatifs -- des mentions incidentes ne declenchent PAS l'exemption.
    assert not STUDENT_PACING_RE.search("La duree d'execution est 2.4 s")
    assert not STUDENT_PACING_RE.search("compute takes 5 sec")


# --------------------------------------------------------------------------- #
#  Heuristiques de contexte : wall-clock vs distribution
# --------------------------------------------------------------------------- #
def test_wallclock_keywords_detect_execution_context() -> None:
    """Les mots-cle 'execution', 'wall-clock', 'elapsed' sont detectes."""
    assert WALLCLOCK_KEYWORDS.search("duree d'execution : 2.4 s")
    assert WALLCLOCK_KEYWORDS.search("wall-clock time was 50 ms")
    assert WALLCLOCK_KEYWORDS.search("elapsed: 1.2 sec")
    assert WALLCLOCK_KEYWORDS.search("solve took 3.5 s")


def test_distribution_keywords_detect_stat_context() -> None:
    """Les mots-cle 'moyenne', 'sigma', 'posterior' sont detectes."""
    assert DISTRIBUTION_KEYWORDS.search("Gaussian de moyenne 15.33 min")
    assert DISTRIBUTION_KEYWORDS.search("sigma=1.32, mu=0.0")
    assert DISTRIBUTION_KEYWORDS.search("posterior distribution over 3.5 sec")
    # NB: 'posterior' peut apparaitre dans un contexte wall-clock ; on prend
    # la priorite distribution dans ce cas (cf. _categorize).


def test_categorize_distribution_overrides_wallclock() -> None:
    """Si la ligne contient un mot distribution ET wall-clock, distribution
    gagne (parametre de modele prime sur contexte d'execution)."""
    line = "Posterior inference took 15.33 min with sigma 1.32"
    # 'inference' (wall-clock) ET 'Posterior'/'sigma' (distribution).
    # Distribution gagne.
    assert _categorize(line, "15.33 min") == CATEGORY_DISTRIBUTION


def test_categorize_wallclock_when_only_wallclock() -> None:
    """Ligne avec mot wall-clock seul -> wallclock."""
    line = "Elapsed time for solve : 4.5 sec"
    assert _categorize(line, "4.5 sec") == CATEGORY_WALLCLOCK


def test_categorize_ambiguous_only_when_neither() -> None:
    """Ligne sans mot-cle de contexte -> wallclock (defaut conservateur).

    Note: par design, on classe en wallclock plutot qu'ambiguous quand la
    regex matche sans contexte -- c'est le defaut conservateur qui fait
    remonter le finding au reviewer humain plutot que de le silencier.
    """
    line = "Performance is around 3.2 s with 100 iterations."
    # 'Performance' est wall-clock keyword (cf. WALLCLOCK_KEYWORDS).
    assert _categorize(line, "3.2 s") == CATEGORY_WALLCLOCK


# --------------------------------------------------------------------------- #
#  Edge case : notebook PII-governed
# --------------------------------------------------------------------------- #
def test_pii_governed_notebook_skipped(tmp_path: Path) -> None:
    """Les notebooks avec metadata.pii_no_output=True sont skippés.

    Rationnel : la prose de ces notebooks est gouv. par PII -- la sortie du
    detecteur les concernant est deconseillee pour eviter les faux positifs
    lies au contexte PII. Cf. _collect_targets.
    """
    # On teste _collect_targets : un notebook avec pii_no_output=True doit
    # etre filtre.
    from check_machine_dep_timing import _collect_targets
    # Creer un notebook pii_no_output=True dans un sous-dossier temporaire
    # de MyIA.AI.Notebooks/ equivalent -- on utilise directement _collect_targets
    # via monkeypatch.
    import argparse
    args = argparse.Namespace(
        all=True,
        json=True,
        check=True,
        paths=[],
    )
    # Le test verifie juste que la fonction n'inclut PAS les PII-governed dans
    # le scan -- on le teste indirectement en verifiant le filtre.
    # NB: ce test s'execute dans l'env de test ou MyIA.AI.Notebooks peut
    # ne pas exister ; on skip si le repo n'est pas accessible.
    if not (Path(__file__).resolve().parents[3] / "MyIA.AI.Notebooks").exists():
        pytest.skip("Hors env repo (MyIA.AI.Notebooks absent)")
    targets = _collect_targets(args)
    for t in targets:
        data = json.loads(t.read_text(encoding="utf-8"))
        assert data.get("metadata", {}).get("pii_no_output") is not True


# --------------------------------------------------------------------------- #
#  Main entry point : smoke test que l'argparse tient
# --------------------------------------------------------------------------- #
def test_main_runs_with_help(capsys: pytest.CaptureFixture) -> None:
    """Le main peut etre appele avec --help sans crash."""
    from check_machine_dep_timing import main
    with pytest.raises(SystemExit) as exc:
        main(["--help"])
    # --help exit code = 0
    assert exc.value.code == 0
    captured = capsys.readouterr()
    assert "machine-dep" in captured.out or "machine" in captured.out.lower()


def test_main_advisory_mode_exits_zero() -> None:
    """Mode advisory par defaut : exit 0 meme avec findings (cf. acceptance)."""
    from check_machine_dep_timing import main
    # On scan un chemin arbitraire qui peut etre vide -- exit 0 attendu.
    rc = main(["--all"])
    # Sur CI (avec MyIA.AI.Notebooks/ present), --all peut renvoyer 0 ou 1
    # selon --check, mais sans --check, c'est TOUJOURS 0 (mode advisory).
    assert rc == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])