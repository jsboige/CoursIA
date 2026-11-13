from __future__ import annotations

import importlib.util
import shutil
import subprocess
from pathlib import Path

import pytest

HERE = Path(__file__).resolve()
SCRIPT = HERE.parents[1] / "check_readme_series_form.py"
FIXTURES = HERE.parent / "fixtures" / "readme_series"
spec = importlib.util.spec_from_file_location("readme_series_form", SCRIPT)
check = importlib.util.module_from_spec(spec)
assert spec.loader
spec.loader.exec_module(check)


def test_conforming_planners_fixture():
    result = check.inspect_text("Planners/01-Foundation/README.md", (FIXTURES / "conforming.md").read_text())
    assert result == {"path": "Planners/01-Foundation/README.md", "conforming": True, "missing": [], "extra": []}


def test_nonconforming_fixture():
    result = check.inspect_text("bad/README.md", (FIXTURES / "nonconforming.md").read_text())
    assert result["conforming"] is False
    assert len(result["missing"]) == 3


def test_v2_catches_lettered_main_table_that_passes_v1():
    result = check.inspect_text("series/README.md", (FIXTURES / "v1_only.md").read_text())
    assert result["missing"] == []
    assert result["conforming"] is False
    assert "lettres_dans_parcours_principal" in result["extra"]


def _git(path: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=path, check=True, capture_output=True)


def test_delta_ignores_existing_backlog_and_detects_regression(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    folder = repo / "MyIA.AI.Notebooks" / "Series"
    folder.mkdir(parents=True)
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text((FIXTURES / "conforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, encoding="utf-8", errors="replace", capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    # No changed README: the historical backlog elsewhere cannot create a delta.
    assert check._delta(base, None) == []
    (folder / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    assert check._delta(base, None)


def test_delta_pairs_git_proven_series_rename(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    folder = repo / "MyIA.AI.Notebooks" / "Series"
    folder.mkdir(parents=True)
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, encoding="utf-8", errors="replace", capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    _git(repo, "mv", "MyIA.AI.Notebooks/Series", "MyIA.AI.Notebooks/Renamed")
    assert check._delta(base, None) == []


def test_delta_allows_partial_improvement(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    folder = repo / "MyIA.AI.Notebooks" / "Series"
    folder.mkdir(parents=True)
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, encoding="utf-8", errors="replace", capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    (folder / "README.md").write_text("## Comment lire ce README\n" + (FIXTURES / "nonconforming.md").read_text())
    assert check._delta(base, None) == []


def test_delta_respects_paths_scope(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    notebooks = repo / "MyIA.AI.Notebooks"
    for name in ("Included", "Excluded"):
        folder = notebooks / name
        folder.mkdir(parents=True)
        (folder / "a.ipynb").write_text("{}")
        (folder / "b.ipynb").write_text("{}")
        (folder / "README.md").write_text((FIXTURES / "conforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, encoding="utf-8", errors="replace", capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", notebooks)
    (notebooks / "Excluded" / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    assert check._delta(base, None, ["MyIA.AI.Notebooks/Included"]) == []
    assert check._delta(base, None, ["MyIA.AI.Notebooks/Excluded"])


def test_delta_allows_new_series_with_two_of_three_markers(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    (repo / "MyIA.AI.Notebooks").mkdir(parents=True)
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "--allow-empty", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, encoding="utf-8", errors="replace", capture_output=True).stdout.strip()
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    folder = repo / "MyIA.AI.Notebooks" / "AddedSeries"
    folder.mkdir()
    (folder / "a.ipynb").write_text("{}")
    (folder / "b.ipynb").write_text("{}")
    (folder / "README.md").write_text("## Comment lire ce README\n\n## Approfondissements\n")
    _git(repo, "add", ".")
    assert check.inspect_text("x", (folder / "README.md").read_text())["conforming"]
    assert check._delta(base, None) == []


def test_paths_with_head_ref_use_reference_inventory(tmp_path, monkeypatch, capsys):
    repo = tmp_path / "repo"
    folder = repo / "MyIA.AI.Notebooks" / "Series"
    folder.mkdir(parents=True)
    for name in ("a.ipynb", "b.ipynb"):
        (folder / name).write_text("{}")
    (folder / "README.md").write_text((FIXTURES / "conforming.md").read_text())
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.com")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True, text=True, encoding="utf-8", errors="replace", capture_output=True).stdout.strip()
    (folder / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    other = repo / "MyIA.AI.Notebooks" / "GitOnly"
    other.mkdir()
    for name in ("a.ipynb", "b.ipynb"):
        (other / name).write_text("{}")
    (other / "README.md").write_text((FIXTURES / "nonconforming.md").read_text())
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "head")
    (folder / "README.md").write_text((FIXTURES / "conforming.md").read_text())
    shutil.rmtree(other)
    monkeypatch.setattr(check, "ROOT", repo)
    monkeypatch.setattr(check, "NOTEBOOKS", repo / "MyIA.AI.Notebooks")
    assert check.main(["--base-ref", base, "--head-ref", "HEAD", "--paths", "MyIA.AI.Notebooks", "--json"]) == 1
    import json
    data = json.loads(capsys.readouterr().out)
    assert {x["path"] for x in data["results"]} == {"MyIA.AI.Notebooks/Series/README.md", "MyIA.AI.Notebooks/GitOnly/README.md"}
    assert all(not x["conforming"] for x in data["results"])
    assert {x["path"] for x in data["delta"]} == {x["path"] for x in data["results"]}
    assert check.main(["--base-ref", base, "--head-ref", "HEAD", "--paths", "MyIA.AI.Notebooks/GitOnly/README.md", "--json"]) == 1
    assert [x["path"] for x in json.loads(capsys.readouterr().out)["results"]] == ["MyIA.AI.Notebooks/GitOnly/README.md"]


# --- Regle V2 et doctrine #3973 : la forme autorisee n'est pas un defaut
#
# La mesure fondatrice (2026-11-12, `origin/main`) : sur les 132 READMEs de
# series inspectes par l'organe, 9 portaient `lettres_dans_parcours_principal`
# et les 9 etaient des faux positifs. Aucune de leurs lignes ne commence par
# une lettre ; chaque lien lettre siege dans la DERNIERE colonne
# (« Pour approfondir »), la forme que la doctrine autorise explicitement.
# L'organe comptait `LETTER_LINK.search(row)` sur la ligne entiere, donc la
# forme autorisee etait exactement celle qu'il sanctionnait.
#
# Chaque controle positif est double d'un controle negatif : la regle doit
# rester mordante sur les formes qui sont de vrais defauts.

HEADER = "| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |"
SEPARATOR = "|---|---|---|---|---|"


def _readme(main_rows, approfond_rows=None):
    """Assemble un README minimal portant les trois marqueurs V1."""
    lines = [
        "# Serie de test",
        "",
        "## Comment lire ce README",
        "",
        "Vous decouvrez : lisez le parcours principal.",
        "",
        "## Structure",
        "",
        "### Parcours principal",
        "",
        HEADER,
        SEPARATOR,
        *main_rows,
        "",
    ]
    if approfond_rows is not None:
        lines += [
            "### Approfondissements",
            "",
            "#### Autour de 01",
            "",
            "| # | Notebook | Ce qu'il ajoute |",
            "|---|---|---|",
            *approfond_rows,
            "",
        ]
    return "\n".join(lines)


def _inspect(main_rows, approfond_rows=None):
    return check.inspect_text("Serie/README.md", _readme(main_rows, approfond_rows))


@pytest.mark.parametrize(
    "row",
    [
        # Lien court dans la derniere colonne : la forme que la doctrine autorise.
        "| 01 | [Shannon-Fano](Compression-01-ShannonFano-Prefixe-Python.ipynb) "
        "| Construire un arbre de code | Decouverte | [01b - preuves Lean](#autour-de-01) |",
        # Plusieurs liens lettres dans la derniere colonne.
        "| 02 | [Huffman](Compression-02-Huffman-Python.ipynb) "
        "| Reconstruire les mots de code | Decouverte | [02b - codecs](#a), [02c - fronts](#b) |",
        # Ligne sans aucun lien lettre.
        "| 03 | [LZ77](Compression-03-LZ77-Python.ipynb) "
        "| Remplacer une repetition par une reference | Intermediaire | - |",
    ],
)
def test_derniere_colonne_est_conforme(row):
    item = _inspect(
        [row],
        [
            "| 01b | [Preuves Lean](P.ipynb) | Certificats |",
            "| 02b | [Codecs](C.ipynb) | Encodage |",
            "| 02c | [Fronts](F.ipynb) | Frontiere |",
        ],
    )
    assert "lettres_dans_parcours_principal" not in item["extra"], item
    assert item["conforming"] is True


def test_ligne_entete_et_separateur_ne_sont_pas_des_defauts():
    item = _inspect(
        ["| 01 | [A](a.ipynb) | Apprendre | Decouverte | - |"],
        ["| 01b | [B](b.ipynb) | Approfondir |"],
    )
    assert item["extra"] == []


def test_lettre_en_premiere_cellule_est_un_defaut():
    """Un palier deguise en etape du parcours."""
    item = _inspect(
        ["| 01b | [Preuves Lean](p.ipynb) | Certificats | Avance | - |"],
        ["| 01b | [Preuves Lean](p.ipynb) | Certificats |"],
    )
    assert "lettres_dans_parcours_principal" in item["extra"], item
    assert item["conforming"] is False


def test_lien_lettre_en_colonne_intermediaire_est_un_defaut():
    """Le palier est cite au milieu de la ligne, donc presente comme une etape."""
    item = _inspect(
        ["| 01 | [A](a.ipynb) | Voir aussi [01b - Lean](#x) | Decouverte | - |"],
        ["| 01b | [B](b.ipynb) | Approfondir |"],
    )
    assert "lettres_dans_parcours_principal" in item["extra"], item


def test_lettre_absente_des_approfondissements_est_un_defaut():
    """Le palier figure dans le parcours et nulle part sous Approfondissements."""
    item = _inspect(
        ["| 01b | [A](a.ipynb) | Apprendre | Decouverte | - |"],
        ["| 01 | [A](a.ipynb) | Parcours |"],
    )
    assert "lettres_absentes_d_Approfondissements" in item["extra"], item


def test_pipe_echappe_ne_coupe_pas_la_cellule():
    """Le decoupage en cellules respecte les pipes echappes."""
    row = "| 01 | [A](a.ipynb) | Un `a \\| b` dans le texte | Decouverte | [01b - Lean](#x) |"
    assert check._cells(row) == [
        " 01 ",
        " [A](a.ipynb) ",
        " Un `a \\| b` dans le texte ",
        " Decouverte ",
        " [01b - Lean](#x) ",
    ]
    item = _inspect([row], ["| 01b | [B](b.ipynb) | Approfondir |"])
    assert "lettres_dans_parcours_principal" not in item["extra"], item


def test_lien_lettre_derniere_colonne_sans_approfondissements_est_un_defaut():
    """La forme autorisee n'exempte pas de la contrepartie : le palier doit etre traite.

    Relecture ai-01 du 13/11 : un lien lettre en derniere colonne ne produisait
    plus de `bad_main`, donc la verification « paliers absents
    d'Approfondissements » ne tournait plus du tout pour cette forme. Une table
    qui cite `[03a]` sans aucune section « Approfondissements » passait.
    """
    item = _inspect(
        ["| 03 | [C](c.ipynb) | Apprendre | Decouverte | [03a - preuves](#x) |"],
        None,
    )
    assert "lettres_absentes_d_Approfondissements" in item["extra"], item
    assert item["conforming"] is False


def test_lien_lettre_prose_d_approfondissements_couvre_le_palier():
    """Un palier traite en prose est traite : la section se lit entiere, pas sa seule table."""
    text = "\n".join([
        "# Serie de test",
        "",
        "## Comment lire ce README",
        "",
        "Vous decouvrez : lisez le parcours principal.",
        "",
        "### Parcours principal",
        "",
        HEADER,
        SEPARATOR,
        "| 03 | [C](c.ipynb) | Apprendre | Decouverte | [03a - preuves](#x) |",
        "",
        "### Approfondissements",
        "",
        "Le palier 03a est traite ci-dessous en prose, sans ligne de tableau.",
        "",
    ])
    item = check.inspect_text("Serie/README.md", text)
    assert "lettres_absentes_d_Approfondissements" not in item["extra"], item


def test_entete_sans_approfondir_n_exempte_pas_la_derniere_colonne():
    """Sans « approfondir » dans l'en-tete, un palier en derniere colonne est une etape deguisee."""
    text = "\n".join([
        "# Serie de test",
        "",
        "## Comment lire ce README",
        "",
        "Vous decouvrez : lisez le parcours principal.",
        "",
        "### Parcours principal",
        "",
        "| # | Notebook | Ce qu'on y apprend | Public | Notebook |",
        "|---|---|---|---|---|",
        "| 03 | [C](c.ipynb) | Apprendre | Decouverte | [03a - preuves](#x) |",
        "",
        "### Approfondissements",
        "",
        "| # | Notebook | Ce qu'il ajoute |",
        "|---|---|---|",
        "| 03a | [P](p.ipynb) | Preuves |",
        "",
    ])
    item = check.inspect_text("Serie/README.md", text)
    assert "lettres_dans_parcours_principal" in item["extra"], item
