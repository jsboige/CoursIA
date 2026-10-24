"""Coherence des planchers `pyarrow` de la flotte (issue #21764).

Sous pyarrow 26, le noyau ipykernel meurt (`Unhandled SIGSEGV`) au chargement
de pyarrow, sur la chaine `torch -> dask -> xarray -> pandas -> pyarrow`.
Mesure : 24.0.0 crash, 26.0.0 OK ; l'image CI portait 25.0.1, non mesure.

Ce test verrouille les TROIS formes que doit prendre le plancher :

1. les deux workflows qui installent pyarrow imposent une version ** bornee** ;
2. chaque workflow **affiche la version resolue** (un plancher non affiche
   n'est pas prouve) ;
3. le plancher vit dans un **fichier de dependances lisible** de la famille,
   que les images d'agents peuvent reprendre -- pas seulement en ligne de
   commande de workflow.

Il se valide par ses faux negatifs : une suppression du plancher, une
regression vers `pyarrow` sans borne, ou la disparition de l'affichage de la
version doivent le faire rougir.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

WORKFLOWS = [
    REPO_ROOT / ".github" / "workflows" / "scripts-tests.yml",
    REPO_ROOT / ".github" / "workflows" / "ml-tests.yml",
]

FAMILY_REQUIREMENTS = REPO_ROOT / "MyIA.AI.Notebooks" / "GameTheory" / "requirements.txt"

FLOOR = "pyarrow>=26"

# Une installation de pyarrow SANS borne : `pip install ... pyarrow ...`.
UNBOUNDED_RE = re.compile(r"pip\s+install[^\n]*?(?<![\w>=.-])pyarrow(?![\w>=.-])")

# L'affichage de la version RESOLUE, dans sa forme EXECUTABLE :
# `python -c "import pyarrow; print('pyarrow resolu:', pyarrow.__version__)"`.
# La commande et la mention de `pyarrow.__version__` doivent etre sur la MEME
# ligne : une ligne commentee ne repond pas a l'acceptance #1.
PRINT_VERSION_RE = re.compile(r"python\s+-c\s+[^\n]*pyarrow\.__version__")


def _without_comment_lines(text: str) -> str:
    """Le texte sans ses lignes de commentaire.

    Un commentaire qui MENTIONNE `pip install pyarrow` (pour expliquer le
    defaut) n'est pas une installation : le scanner ne doit pas le lire comme
    tel. On ne retire donc que les lignes dont le contenu est un commentaire,
    pas les commentaires de fin de ligne (ceux-ci precedent la commande).
    """
    kept = []
    for line in text.splitlines():
        if line.strip().startswith("#"):
            continue
        kept.append(line)
    return "\n".join(kept)


def _code_lines(path: Path) -> str:
    """Le workflow sans ses lignes de commentaire."""
    return _without_comment_lines(path.read_text(encoding="utf-8"))


def test_workflows_install_a_bounded_pyarrow():
    """Les deux workflows imposent pyarrow>=26, pas `pyarrow` nu."""
    for wf in WORKFLOWS:
        text = _code_lines(wf)
        assert FLOOR in text, f"{wf.name}: plancher {FLOOR} absent"
        unbounded = UNBOUNDED_RE.findall(text)
        assert not unbounded, (
            f"{wf.name}: installation de pyarrow sans borne -- le plancher "
            f"serait satisfait par la version deja presente dans l'image "
            f"(25.0.1, non mesure) : {unbounded}"
        )


def _prints_resolved_version(text: str) -> bool:
    """Le texte execute-t-il l'affichage de la version resolue ?

    On ne lit que les lignes EXECUTABLES : une commande commentee n'affiche
    rien dans le log. Le faux negatif (une commande passee en commentaire
    laissait la suite verte) a ete mesure par la relecture tierce de #21783.
    """
    return bool(PRINT_VERSION_RE.search(_without_comment_lines(text)))


def test_workflows_print_the_resolved_version():
    """Chaque workflow affiche la version RESOLUE de pyarrow (acceptance #1)."""
    for wf in WORKFLOWS:
        assert _prints_resolved_version(wf.read_text(encoding="utf-8")), (
            f"{wf.name}: la version resolue de pyarrow n'est pas affichee par "
            f"une ligne EXECUTABLE -- le log doit la porter, pas seulement la "
            f"contrainte"
        )


def test_a_commented_command_does_not_count_as_printing_the_version():
    """Controle negatif : une commande commentee n'affiche pas la version.

    C'est le faux negatif qui a ete mesure : commenting la commande laissait
    la suite verte alors que le job n'affichait plus aucune version.
    """
    commented = (
        '        # Version RESOLUE de pyarrow (#21764) : le log doit la porter\n'
        '        # python -c "import pyarrow; print(pyarrow.__version__)"\n'
    )
    assert not _prints_resolved_version(commented), (
        "une commande commentee ne doit pas satisfaire l'acceptance #1"
    )
    executable = '        python -c "import pyarrow; print(pyarrow.__version__)"\n'
    assert _prints_resolved_version(executable), (
        "la forme executable doit etre reconnue"
    )


def test_floor_lives_in_a_readable_dependency_file():
    """Le plancher est dans le requirements lisible de la famille (#21764)."""
    text = FAMILY_REQUIREMENTS.read_text(encoding="utf-8")
    assert FLOOR in text, (
        f"{FAMILY_REQUIREMENTS.name}: plancher {FLOOR} absent -- les images "
        f"d'agents doivent pouvoir le reprendre sans lire un workflow"
    )


def test_floor_matches_the_requirement_file():
    """Le plancher du workflow et celui du fichier de dependances coincident.

    La comparaison est REELLE : les versions lues dans les workflows (lignes
    executables) et celles du requirements sont mises en egale. La version
    precedente ne lisait aucun workflow -- son nom promettait une comparaison
    que le corps ne faisait pas (reserve non bloquante de la relecture
    tierce de #21783).
    """
    floor_in_file = re.search(r"pyarrow>=(\d+)", FAMILY_REQUIREMENTS.read_text(encoding="utf-8"))
    assert floor_in_file is not None, "plancher illisible dans le requirements"
    version = int(floor_in_file.group(1))
    assert version >= 26, f"plancher pyarrow>={version} sous le seuil mesure (26)"
    for wf in WORKFLOWS:
        floors = {int(v) for v in re.findall(r"pyarrow>=(\d+)", _code_lines(wf))}
        assert floors, f"{wf.name}: plancher illisible dans les lignes executables"
        assert floors == {version}, (
            f"{wf.name}: plancher workflow {sorted(floors)} != plancher "
            f"requirements {version} -- les deux doivent coincider"
        )


if __name__ == "__main__":
    for fn in (
        test_workflows_install_a_bounded_pyarrow,
        test_workflows_print_the_resolved_version,
        test_a_commented_command_does_not_count_as_printing_the_version,
        test_floor_lives_in_a_readable_dependency_file,
        test_floor_matches_the_requirement_file,
    ):
        fn()
        print(f"OK: {fn.__name__}")
    print("All tests passed.")
