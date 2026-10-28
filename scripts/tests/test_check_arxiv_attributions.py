"""Tests pour scripts/check_arxiv_attributions.py.

Couvre :
  1. Chargement du registre YAML (valide / malformé)
  2. Vérification de chaque entrée (PASS / FAIL / RENAMED)
  3. Filtrage par scope (--paths)
  4. Mode --strict (RENAMED devient FAIL)
  5. Sortie --json structurée
  6. Erreurs : registre manquant, notebook introuvable, cell_index hors borne

Fixture strategy : on crée un mini-dépôt temporaire avec 1-2 notebooks,
un registre YAML temporaire, et on lance le check dessus. Pas de mocks —
vrai subprocess `python scripts/check_arxiv_attributions.py`.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPT = REPO_ROOT / "scripts" / "check_arxiv_attributions.py"


def _make_notebook(tmp: Path, rel_path: str, cells: list[dict]) -> Path:
    """Crée un notebook minimal avec les cellules données."""
    nb_path = tmp / rel_path
    nb_path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": [
            {
                "cell_type": c.get("type", "markdown"),
                "metadata": {},
                "source": c["source"] if isinstance(c["source"], list) else [c["source"]],
                "outputs": [] if c.get("type", "markdown") == "markdown" else c.get("outputs", []),
                "execution_count": None if c.get("type", "markdown") == "markdown" else c.get("execution_count", 1),
            }
            for c in cells
        ],
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"}
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    nb_path.write_text(json.dumps(nb, indent=2, ensure_ascii=False), encoding="utf-8")
    return nb_path


def _make_registry(tmp: Path, entries: list[dict]) -> Path:
    """Crée un registre YAML."""
    import yaml

    reg_path = tmp / "arxiv_attributions_registry.yaml"
    reg_path.write_text(
        yaml.safe_dump({"attributions": entries}, allow_unicode=True, sort_keys=False),
        encoding="utf-8",
    )
    return reg_path


def _run_check(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess:
    """Lance check_arxiv_attributions.py et retourne le résultat."""
    cmd = [sys.executable, str(SCRIPT), *args]
    return subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=cwd or REPO_ROOT,
    )


# ===== 1. Chargement du registre YAML =====


def test_registry_missing(tmp_path: Path) -> None:
    """Registre introuvable → exit 2, message clair."""
    reg = tmp_path / "nope.yaml"
    result = _run_check("--registry", str(reg), "--repo-root", str(tmp_path))
    assert result.returncode == 2
    assert "registre introuvable" in result.stderr.lower()


def test_registry_malformed_no_attributions_key(tmp_path: Path) -> None:
    """YAML valide mais sans clé 'attributions' → exit 2."""
    reg = tmp_path / "bad.yaml"
    reg.write_text("just_a_string: not_a_dict\n", encoding="utf-8")
    result = _run_check("--registry", str(reg), "--repo-root", str(tmp_path))
    assert result.returncode == 2
    assert "attributions" in result.stderr.lower()


def test_registry_attributions_not_list(tmp_path: Path) -> None:
    """'attributions' doit être une liste, pas un dict."""
    import yaml

    reg = tmp_path / "bad2.yaml"
    reg.write_text(
        yaml.safe_dump({"attributions": "string_instead_of_list"}),
        encoding="utf-8",
    )
    result = _run_check("--registry", str(reg), "--repo-root", str(tmp_path))
    assert result.returncode == 2
    assert "liste" in result.stderr.lower()


# ===== 2. Vérification PASS / FAIL / RENAMED =====


def test_pass_when_citation_present(tmp_path: Path) -> None:
    """Cas PASS : notebook existe, cellule index 1 contient la chaîne attendue."""
    _make_notebook(
        tmp_path,
        "Test.ipynb",
        [
            {"type": "markdown", "source": "# Heading"},
            {"type": "markdown", "source": ["See Schulman et al. 2015 (arXiv:1502.01555)."]},
        ],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Test.ipynb",
                "cell_index": 1,
                "expected_citation": "Schulman et al. 2015 (arXiv:1502.01555)",
                "source_pr": "#TEST",
                "correction": "test",
                "date": "2026-08-25",
            }
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
    )
    assert result.returncode == 0
    assert "1 PASS" in result.stdout


def test_fail_when_citation_missing(tmp_path: Path) -> None:
    """Cas FAIL : notebook existe mais cellule ne contient pas la chaîne."""
    _make_notebook(
        tmp_path,
        "Test.ipynb",
        [
            {"type": "markdown", "source": ["See Wrong Citation."]}
        ],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Test.ipynb",
                "cell_index": 0,
                "expected_citation": "Schulman et al. 2015 (arXiv:1502.01555)",
                "source_pr": "#TEST",
                "correction": "test",
                "date": "2026-08-25",
            }
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
    )
    assert result.returncode == 1
    assert "1 FAIL" in result.stdout
    assert "expected_citation absent" in result.stdout


def test_fail_when_cell_index_out_of_range(tmp_path: Path) -> None:
    """Cas FAIL : cell_index > nombre de cellules."""
    _make_notebook(
        tmp_path,
        "Test.ipynb",
        [{"type": "markdown", "source": "Only one cell"}],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Test.ipynb",
                "cell_index": 5,
                "expected_citation": "anything",
                "source_pr": "#TEST",
                "correction": "test",
                "date": "2026-08-25",
            }
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
    )
    assert result.returncode == 1
    assert "hors borne" in result.stdout


def test_renamed_by_default(tmp_path: Path) -> None:
    """Cas RENAMED (non-strict) : notebook introuvable mais registre pas strict → exit 0."""
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Renamed.ipynb",
                "cell_index": 0,
                "expected_citation": "anything",
                "source_pr": "#TEST",
                "correction": "test",
                "date": "2026-08-25",
            }
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
    )
    # RENAMED n'est pas un FAIL par défaut
    assert result.returncode == 0
    assert "1 RENAMED" in result.stdout


def test_renamed_with_strict_flag(tmp_path: Path) -> None:
    """Cas RENAMED avec --strict → FAIL rouge."""
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Renamed.ipynb",
                "cell_index": 0,
                "expected_citation": "anything",
                "source_pr": "#TEST",
                "correction": "test",
                "date": "2026-08-25",
            }
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
        "--strict",
    )
    assert result.returncode == 1
    assert "1 RENAMED" in result.stdout


# ===== 3. Filtrage par scope =====


def test_paths_scope_filters_out(tmp_path: Path) -> None:
    """Avec --paths, les notebooks hors scope sont ignorés."""
    _make_notebook(
        tmp_path,
        "A.ipynb",
        [{"type": "markdown", "source": ["OK A"]}],
    )
    _make_notebook(
        tmp_path,
        "B.ipynb",
        [{"type": "markdown", "source": ["OK B"]}],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "A.ipynb",
                "cell_index": 0,
                "expected_citation": "OK A",
                "source_pr": "#T",
                "correction": "x",
                "date": "2026-08-25",
            },
            {
                "arxiv_id": "1506.02438",
                "notebook": "B.ipynb",
                "cell_index": 0,
                "expected_citation": "OK B",
                "source_pr": "#T",
                "correction": "x",
                "date": "2026-08-25",
            },
        ],
    )
    # cwd=tmp_path pour que `A.ipynb` soit résolu depuis tmp_path, pas REPO_ROOT
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
        "--paths", "A.ipynb",
        cwd=tmp_path,
    )
    assert result.returncode == 0
    # Seule A doit être checkée
    assert "A.ipynb" in result.stdout
    # B ne doit pas apparaître dans le tableau results
    assert "B.ipynb" not in result.stdout or "B.ipynb#0" not in result.stdout


def test_paths_scope_recursive_glob(tmp_path: Path) -> None:
    """Le scope accepte les globs récursifs (ex: MyIA.AI.Notebooks/ML/**/*.ipynb)."""
    _make_notebook(
        tmp_path,
        "MyIA.AI.Notebooks/ML/Test1.ipynb",
        [{"type": "markdown", "source": ["X"]}],
    )
    _make_notebook(
        tmp_path,
        "MyIA.AI.Notebooks/GameTheory/Test2.ipynb",
        [{"type": "markdown", "source": ["Y"]}],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "MyIA.AI.Notebooks/ML/Test1.ipynb",
                "cell_index": 0,
                "expected_citation": "X",
                "source_pr": "#T",
                "correction": "x",
                "date": "2026-08-25",
            },
            {
                "arxiv_id": "1506.02438",
                "notebook": "MyIA.AI.Notebooks/GameTheory/Test2.ipynb",
                "cell_index": 0,
                "expected_citation": "Y",
                "source_pr": "#T",
                "correction": "x",
                "date": "2026-08-25",
            },
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
        "--paths", "MyIA.AI.Notebooks/ML/*.ipynb",
        cwd=tmp_path,
    )
    assert result.returncode == 0
    # Test1 doit apparaître, Test2 non
    assert "Test1.ipynb" in result.stdout
    assert "Test2.ipynb" not in result.stdout


# ===== 4. Sortie --json structurée =====


def test_json_output(tmp_path: Path) -> None:
    """Sortie JSON valide, avec summary + results structurés."""
    _make_notebook(
        tmp_path,
        "Test.ipynb",
        [{"type": "markdown", "source": ["OK citation"]}],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Test.ipynb",
                "cell_index": 0,
                "expected_citation": "OK citation",
                "source_pr": "#T",
                "correction": "x",
                "date": "2026-08-25",
            }
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
        "--json",
    )
    assert result.returncode == 0
    payload = json.loads(result.stdout)
    assert payload["checked"] == 1
    assert payload["summary"]["PASS"] == 1
    assert payload["summary"]["FAIL"] == 0
    assert len(payload["results"]) == 1
    assert payload["results"][0]["arxiv_id"] == "1502.01555"


def test_json_output_includes_failures(tmp_path: Path) -> None:
    """Sortie JSON inclut les détails d'échec."""
    _make_notebook(
        tmp_path,
        "Test.ipynb",
        [{"type": "markdown", "source": ["Wrong content"]}],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Test.ipynb",
                "cell_index": 0,
                "expected_citation": "Expected citation",
                "source_pr": "#T",
                "correction": "x",
                "date": "2026-08-25",
            }
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
        "--json",
    )
    assert result.returncode == 1
    payload = json.loads(result.stdout)
    assert payload["summary"]["FAIL"] == 1
    assert "expected_citation absent" in payload["results"][0]["detail"]


# ===== 5. Vérifications multiples (mix PASS/FAIL) =====


def test_multiple_entries_summary(tmp_path: Path) -> None:
    """Avec plusieurs entrées, summary agrège correctement."""
    _make_notebook(
        tmp_path,
        "Good.ipynb",
        [{"type": "markdown", "source": ["This one is fine"]}],
    )
    _make_notebook(
        tmp_path,
        "Bad.ipynb",
        [{"type": "markdown", "source": ["Wrong stuff"]}],
    )
    _make_registry(
        tmp_path,
        [
            {
                "arxiv_id": "1502.01555",
                "notebook": "Good.ipynb",
                "cell_index": 0,
                "expected_citation": "This one is fine",
                "source_pr": "#T1",
                "correction": "x",
                "date": "2026-08-25",
            },
            {
                "arxiv_id": "1506.02438",
                "notebook": "Bad.ipynb",
                "cell_index": 0,
                "expected_citation": "Expected but missing",
                "source_pr": "#T2",
                "correction": "x",
                "date": "2026-08-25",
            },
        ],
    )
    result = _run_check(
        "--registry", str(tmp_path / "arxiv_attributions_registry.yaml"),
        "--repo-root", str(tmp_path),
    )
    assert result.returncode == 1
    assert "1 PASS" in result.stdout
    assert "1 FAIL" in result.stdout


# ===== 6. Cas réel : registre de l'EPIC #11168 =====


def test_real_registry_passes_when_no_drift(tmp_path: Path) -> None:
    """Sanity check : si on monte le vrai registre + un sous-ensemble de notebooks
    fictifs qui matchent les cell_index, le check doit passer.

    Note : ce test utilise un registre COPIE depuis arxiv_attributions_registry.yaml
    à la racine du dépôt, avec des notebooks créés à la volée qui contiennent
    les expected_citation aux bons cell_index.
    """
    import yaml

    real_reg = REPO_ROOT / "arxiv_attributions_registry.yaml"
    if not real_reg.exists():
        pytest.skip("Registre réel absent (devrait être livré par #12853)")

    with real_reg.open(encoding="utf-8") as f:
        data = yaml.safe_load(f)
    entries = data["attributions"]

    # Pour chaque entrée : créer UN notebook UNIQUE (chemin unique par entrée)
    # avec expected_citation en cellule 1.
    seen_paths: set[str] = set()
    for entry in entries:
        nb_rel = entry["notebook"]
        # Garantir l'unicité : si doublon, suffixer avec arxiv_id
        suffix = ""
        candidate = nb_rel
        while candidate in seen_paths:
            suffix += "_" + entry["arxiv_id"].replace(".", "")
            base = nb_rel.rsplit(".", 1)
            candidate = f"{base[0]}_{suffix}.{base[1]}" if "." in nb_rel else nb_rel + suffix
        seen_paths.add(candidate)
        entry_copy = dict(entry)
        entry_copy["notebook"] = candidate
        entry_copy["cell_index"] = 1
        _make_notebook(
            tmp_path,
            candidate,
            [
                {"type": "markdown", "source": ["placeholder"]},
                {"type": "markdown", "source": [entry["expected_citation"]]},
            ],
        )
        entries[entries.index(entry)] = entry_copy

    tmp_reg = tmp_path / "reg.yaml"
    tmp_reg.write_text(
        yaml.safe_dump({"attributions": entries}, allow_unicode=True, sort_keys=False),
        encoding="utf-8",
    )

    result = _run_check(
        "--registry", str(tmp_reg),
        "--repo-root", str(tmp_path),
    )
    # Le check crée un notebook par entrée avec la expected_citation : tous PASS.
    assert result.returncode == 0
    assert f"{len(entries)} PASS" in result.stdout
    # Sanity : aucune entrée ne doit sortir en RENAMED/FAIL avec ce fixture.
    assert "0 RENAMED, 0 FAIL" in result.stdout or "RENAMED 0" not in result.stdout


# ===== 7. Vivacité du registre contre le main réel (anti-fabrication) =====


def test_real_registry_lives_against_main_repo() -> None:
    """Verdict anti-fabrication : chaque entrée du registre RÉEL doit pointer vers
    un notebook EXISTANT dans le dépôt, avec un cell_index VALIDE.

    Ce test ferme l'angle mort identifié par Hermes sur #12900 : le registre
    livré en v1 référençait 16 notebooks inexistants (et des arXiv IDs inexacts),
    et le test `test_real_registry_passes_when_no_drift` ne le détectait pas
    (il crée un notebook fictif à la volée pour chaque entrée). Cette clause
    protège contre la régression silencieuse d'un registre fabriqué.

    Si ce test échoue : le registre a dérivé, NE PAS le patcher — corriger la
    cause (renommer / mettre à jour cell_index / régénérer depuis les diffs
    des PRs sources). Cf leçon #11145 durcie #12836.

    Skip conditionnel retiré (cf #12939) : les 3 PRs sources
    (#12832/#12824/#12838) sont MERGED sur main depuis. Le test est désormais
    actif par défaut ; il échoue franchement si le registre dérive.
    """
    import yaml

    real_reg = REPO_ROOT / "arxiv_attributions_registry.yaml"
    if not real_reg.exists():
        pytest.skip("Registre réel absent (devrait être livré par #12853)")

    with real_reg.open(encoding="utf-8") as f:
        data = yaml.safe_load(f)
    entries = data.get("attributions", [])

    # Le check doit tourner contre REPO_ROOT (le vrai dépôt), pas un tmp_path.
    result = _run_check(
        "--registry", str(real_reg),
        "--repo-root", str(REPO_ROOT),
        "--strict",  # RENAMED doit être FAIL
        "--json",
    )

    payload = json.loads(result.stdout)
    summary = payload["summary"]

    # Zéro RENAMED : tous les notebooks référencés doivent exister sur disque
    assert summary.get("RENAMED", 0) == 0, (
        f"Le registre référence {summary.get('RENAMED', 0)} notebook(s) inexistant(s) "
        f"sur le dépôt. NE PAS patcher le test : régénérer le registre depuis "
        f"les diffs des PRs sources. Détails : "
        f"{[r for r in payload['results'] if r['status'] == 'RENAMED']}"
    )

    # Zéro FAIL : toutes les expected_citation doivent être dans la cellule indiquée
    assert summary.get("FAIL", 0) == 0, (
        f"Le registre a {summary.get('FAIL', 0)} entrée(s) FAIL — la citation "
        f"attendue n'est pas dans la cellule référencée. Régénérer depuis les "
        f"diffs ou mettre à jour cell_index. Détails : "
        f"{[r for r in payload['results'] if r['status'] == 'FAIL']}"
    )

    # Toutes les entrées doivent être PASS
    assert summary.get("PASS", 0) == len(entries), (
        f"Sur {len(entries)} entrées, seulement {summary.get('PASS', 0)} PASS. "
        f"RENAMED={summary.get('RENAMED', 0)}, FAIL={summary.get('FAIL', 0)}. "
        f"Le registre doit être régénéré depuis les diffs des PRs sources."
    )
    # Exit code 0 (tout PASS en mode strict)
    assert result.returncode == 0


def test_workflow_paths_cover_every_registry_notebook() -> None:
    """Chaque notebook du registre REEL figure dans le filtre `paths:` de
    `arxiv-attributions-guard.yml`.

    Sans cela, une PR qui ne modifie qu'un notebook enregistre (cellules
    inserees, citation reecrite) n'active pas la garde bloquante : la derive
    n'apparait qu'apres merge, sur main. Mesure fondatrice (2026-09-29) :
    #18320 a decale les cellules d'ICT-37, ajoute au registre par la passe 6
    (#17622) sans que le filtre suive ; main est reste rouge sur Scripts Tests
    jusqu'a #18343.
    """
    import yaml

    real_reg = REPO_ROOT / "arxiv_attributions_registry.yaml"
    workflow = REPO_ROOT / ".github" / "workflows" / "arxiv-attributions-guard.yml"
    if not real_reg.exists() or not workflow.exists():
        pytest.skip("Registre ou workflow absent")

    with real_reg.open(encoding="utf-8") as f:
        entries = yaml.safe_load(f).get("attributions", [])
    with workflow.open(encoding="utf-8") as f:
        wf = yaml.safe_load(f)
    # PyYAML lit la cle `on` comme le booleen True.
    triggers = wf.get("on", wf.get(True, {}))
    paths = set(triggers["pull_request"]["paths"])

    missing = sorted({e["notebook"] for e in entries} - paths)
    assert not missing, (
        "Notebooks du registre absents du filtre paths: de "
        f"arxiv-attributions-guard.yml : {missing}. Les ajouter au filtre, "
        "sinon une PR qui ne touche que ces notebooks esquive la garde."
    )


# ===== 6. Mode détection (#22566) =====
#
# Pas de réseau dans la suite : le seam `ARXIV_DETECT_RESOLUTIONS` rejoue un
# JSON `{id: {verdict, title, authors}}` à la place de l'API arXiv.


def _write_resolutions(tmp: Path, data: dict) -> Path:
    p = tmp / "resolutions.json"
    p.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    return p


class TestDetectMode:
    """Mode `--detect` : identifiants hors registre + contrôle d'identité."""

    def test_mismatch_positive_control_1505_04322(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Contrôle positif de l'issue : le notebook cite `arXiv:1505.04322`
        comme un article de Hoffman, mais l'API le résout vers l'article de
        Huan Wang mesuré sur #22537 (géométrie complexe) → concordance nulle
        → MISMATCH, exit 1. Le titre est le RÉEL, tel que l'API l'a rendu
        dans le récit de #22537."""
        _make_notebook(
            tmp_path,
            "MyIA.AI.Notebooks/X.ipynb",
            [
                {"type": "markdown",
                 "source": "See arXiv:1505.04322 for the survey — Hoffman et al."},
            ],
        )
        _make_registry(tmp_path, [])
        fixture = _write_resolutions(tmp_path, {
            "1505.04322": {
                "verdict": "ok",
                "title": "On the growth of von Neumann dimension of harmonic "
                          "spaces of semipositive line bundles over covering "
                          "manifolds",
                "authors": ["Huan Wang"],
            }
        })
        monkeypatch.setenv("ARXIV_DETECT_RESOLUTIONS", str(fixture))
        result = _run_check("--detect", "--repo-root", str(tmp_path), "--json",
                            cwd=tmp_path)
        payload = json.loads(result.stdout)
        assert payload["summary"]["MISMATCH"] == 1
        r = payload["results"][0]
        assert r["arxiv_id"] == "1505.04322"
        assert r["status"] == "MISMATCH"
        assert "concorde pas" in r["detail"]
        assert result.returncode == 1

    def test_ok_when_title_concords(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Concordance de titre dans le contexte de citation → OK, exit 0."""
        _make_notebook(
            tmp_path,
            "MyIA.AI.Notebooks/X.ipynb",
            [
                {"type": "markdown",
                 "source": "We use arXiv:1810.04805 — Universal Character "
                            "Autocoders for generative modeling (Baevski)."},
            ],
        )
        _make_registry(tmp_path, [])
        fixture = _write_resolutions(tmp_path, {
            "1810.04805": {
                "verdict": "ok",
                "title": "Universal Character Autocoders for Generative Modeling",
                "authors": ["Alexey Baevski"],
            }
        })
        monkeypatch.setenv("ARXIV_DETECT_RESOLUTIONS", str(fixture))
        result = _run_check("--detect", "--repo-root", str(tmp_path), "--json",
                            cwd=tmp_path)
        payload = json.loads(result.stdout)
        assert payload["summary"]["OK"] == 1
        assert result.returncode == 0

    def test_registered_ids_are_not_re_resolved(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Un ID déjà au registre est exclu de la détection : il ne figure ni
        dans les résultats, ni dans les résolutions demandées."""
        _make_notebook(
            tmp_path,
            "MyIA.AI.Notebooks/X.ipynb",
            [
                {"type": "markdown",
                 "source": "Attention arXiv:1706.03762 — transformer paper."},
            ],
        )
        _make_registry(tmp_path, [{
            "arxiv_id": "1706.03762",
            "notebook": "MyIA.AI.Notebooks/X.ipynb",
            "cell_index": 0,
            "expected_citation": "arXiv:1706.03762",
            "source_pr": 0,
        }])
        # Fixture VIDE : si l'ID enregistré était re-résolu, il serait
        # "notfound" et rougirait — c'est précisément ce que le test réfute.
        fixture = _write_resolutions(tmp_path, {})
        monkeypatch.setenv("ARXIV_DETECT_RESOLUTIONS", str(fixture))
        result = _run_check("--detect", "--repo-root", str(tmp_path), "--json",
                            cwd=tmp_path)
        payload = json.loads(result.stdout)
        assert payload["unregistered"] == 0
        assert payload["results"] == []
        assert result.returncode == 0

    def test_transport_is_skipped_never_red(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Un transport (API injoignable) n'est jamais un MISMATCH : SKIPPED,
        exit 0 (défaut repare le 2026-09-21, EPIC #11168)."""
        _make_notebook(
            tmp_path,
            "MyIA.AI.Notebooks/X.ipynb",
            [{"type": "markdown", "source": "And arXiv:1810.04805 here."}],
        )
        _make_registry(tmp_path, [])
        fixture = _write_resolutions(tmp_path, {
            "1810.04805": {"verdict": "transport", "error": "HTTP 429"}
        })
        monkeypatch.setenv("ARXIV_DETECT_RESOLUTIONS", str(fixture))
        result = _run_check("--detect", "--repo-root", str(tmp_path), "--json",
                            cwd=tmp_path)
        payload = json.loads(result.stdout)
        assert payload["summary"]["SKIPPED"] == 1
        assert payload["summary"]["MISMATCH"] == 0
        assert "aucun verdict" in payload["results"][0]["detail"]
        assert result.returncode == 0

    def test_notfound_is_red(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Un ID non résolu par l'API est un article inexistant : MISMATCH."""
        _make_notebook(
            tmp_path,
            "MyIA.AI.Notebooks/X.ipynb",
            [{"type": "markdown", "source": "Cf. arXiv:9999.99999 for details."}],
        )
        _make_registry(tmp_path, [])
        fixture = _write_resolutions(tmp_path, {
            "9999.99999": {"verdict": "notfound", "title": None, "authors": []}
        })
        monkeypatch.setenv("ARXIV_DETECT_RESOLUTIONS", str(fixture))
        result = _run_check("--detect", "--repo-root", str(tmp_path), "--json",
                            cwd=tmp_path)
        payload = json.loads(result.stdout)
        assert payload["summary"]["MISMATCH"] == 1
        assert "inexistant" in payload["results"][0]["detail"]
        assert result.returncode == 1

    def test_paths_scope_limits_enumeration(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """`--paths` (globs de fichiers en mode détection) borne l'énumération."""
        _make_notebook(
            tmp_path,
            "MyIA.AI.Notebooks/A.ipynb",
            [{"type": "markdown", "source": "Cf. arXiv:9999.99999 here."}],
        )
        _make_notebook(
            tmp_path,
            "MyIA.AI.Notebooks/B.ipynb",
            [{"type": "markdown", "source": "Cf. arXiv:8888.88888 there."}],
        )
        _make_registry(tmp_path, [])
        fixture = _write_resolutions(tmp_path, {})
        monkeypatch.setenv("ARXIV_DETECT_RESOLUTIONS", str(fixture))
        result = _run_check(
            "--detect", "--repo-root", str(tmp_path), "--json",
            "--paths", "MyIA.AI.Notebooks/A.ipynb", cwd=tmp_path)
        payload = json.loads(result.stdout)
        assert payload["enumerated"] == 1
        assert payload["results"][0]["arxiv_id"] == "9999.99999"
