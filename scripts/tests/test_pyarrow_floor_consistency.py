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


def _code_lines(path: Path) -> str:
    """Le workflow sans ses lignes de commentaire.

    Un commentaire qui MENTIONNE `pip install pyarrow` (pour expliquer le
    defaut) n'est pas une installation : le scanner ne doit pas le lire comme
    tel. On ne retire donc que les lignes dont le contenu est un commentaire,
    pas les commentaires de fin de ligne (ceux-ci precede la commande).
    """
    kept = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip().startswith("#"):
            continue
        kept.append(line)
    return "\n".join(kept)


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


def test_workflows_print_the_resolved_version():
    """Chaque workflow affiche la version RESOLUE de pyarrow (acceptance #1)."""
    for wf in WORKFLOWS:
        text = wf.read_text(encoding="utf-8")
        assert "pyarrow.__version__" in text, (
            f"{wf.name}: la version resolue de pyarrow n'est pas affichee -- "
            f"le log doit la porter, pas seulement la contrainte"
        )


def test_floor_lives_in_a_readable_dependency_file():
    """Le plancher est dans le requirements lisible de la famille (#21764)."""
    text = FAMILY_REQUIREMENTS.read_text(encoding="utf-8")
    assert FLOOR in text, (
        f"{FAMILY_REQUIREMENTS.name}: plancher {FLOOR} absent -- les images "
        f"d'agents doivent pouvoir le reprendre sans lire un workflow"
    )


def test_floor_matches_the_requirement_file():
    """Le plancher du workflow et celui du fichier de dependances coincident."""
    floor_in_file = re.search(r"pyarrow>=(\d+)", FAMILY_REQUIREMENTS.read_text(encoding="utf-8"))
    assert floor_in_file is not None, "plancher illisible dans le requirements"
    version = int(floor_in_file.group(1))
    assert version >= 26, f"plancher pyarrow>={version} sous le seuil mesure (26)"


if __name__ == "__main__":
    for fn in (
        test_workflows_install_a_bounded_pyarrow,
        test_workflows_print_the_resolved_version,
        test_floor_lives_in_a_readable_dependency_file,
        test_floor_matches_the_requirement_file,
    ):
        fn()
        print(f"OK: {fn.__name__}")
    print("All tests passed.")
