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

Une QUATRIEME forme est venue de #25521 : le job peut **deleguer** son
installation a un script partage (`scripts/ci/install_scripts_tests_deps.sh`,
appele par `scripts-tests.yml` et par le lot quotidien de `slow-lane.yml`).
Le garde regarde alors les commandes **effectives** du job : le workflow PLUS
les scripts qu'il appelle. On elargit la LECTURE, jamais le CONTRAT -- les
trois formes ci-dessus restent exigees, et les controles negatifs du fichier
prouvent que la resolution ne masque ni une suppression du plancher, ni une
installation sans borne, ni une version non affichee.

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


# Un job peut deleguer son installation a un script partage de `scripts/`
# (#25521). Le garde doit alors.watchdog les commandes EFFECTIVES du job.
DELEGATED_SCRIPT_RE = re.compile(r"bash\s+(scripts/[\w./-]+\.sh)")


def _delegated_scripts(text: str, root: Path) -> list[Path]:
    """Les scripts de `scripts/` appeles par le texte executable."""
    found: list[Path] = []
    seen: set[str] = set()
    for match in DELEGATED_SCRIPT_RE.finditer(text):
        rel = match.group(1)
        if rel in seen:
            continue
        seen.add(rel)
        path = root / rel
        if path.exists():
            found.append(path)
    return found


def _effective_code_lines(path: Path, root: Path = REPO_ROOT, _depth: int = 0) -> str:
    """Les lignes executables du job : le workflow ET ses scripts delegates.

    La profondeur est bornee : une delegation circulaire ne doit pas faire
    boucler la lecture.
    """
    text = _code_lines(path)
    if _depth >= 3:
        return text
    for script in _delegated_scripts(text, root):
        text = text + "\n" + _effective_code_lines(script, root, _depth + 1)
    return text


def _assert_bounded_floor(text: str, label: str) -> None:
    """Le plancher est present ET borne dans le texte executable."""
    assert FLOOR in text, f"{label}: plancher {FLOOR} absent"
    unbounded = UNBOUNDED_RE.findall(text)
    assert not unbounded, (
        f"{label}: installation de pyarrow sans borne -- le plancher "
        f"serait satisfait par la version deja presente dans l'image "
        f"(25.0.1, non mesure) : {unbounded}"
    )


def test_workflows_install_a_bounded_pyarrow():
    """Les deux workflows imposent pyarrow>=26, pas `pyarrow` nu."""
    for wf in WORKFLOWS:
        _assert_bounded_floor(_effective_code_lines(wf), wf.name)


def _prints_resolved_version(text: str) -> bool:
    """Le texte execute-t-il l'affichage de la version resolue ?

    On ne lit que les lignes EXECUTABLES : une commande commentee n'affiche
    rien dans le log. Le faux negatif (une commande passee en commentaire
    laissait la suite verte) a ete mesure par la relecture tierce de #21783.
    """
    return bool(PRINT_VERSION_RE.search(_without_comment_lines(text)))


def _assert_prints_version(text: str, label: str) -> None:
    """Le texte executable affiche la version resolue de pyarrow."""
    assert _prints_resolved_version(text), (
        f"{label}: la version resolue de pyarrow n'est pas affichee par "
        f"une ligne EXECUTABLE -- le log doit la porter, pas seulement la "
        f"contrainte"
    )


def test_workflows_print_the_resolved_version():
    """Chaque workflow affiche la version RESOLUE de pyarrow (acceptance #1)."""
    for wf in WORKFLOWS:
        _assert_prints_version(_effective_code_lines(wf), wf.name)


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
        floors = {int(v) for v in re.findall(r"pyarrow>=(\d+)", _effective_code_lines(wf))}
        assert floors, f"{wf.name}: plancher illisible dans les lignes executables"
        assert floors == {version}, (
            f"{wf.name}: plancher workflow {sorted(floors)} != plancher "
            f"requirements {version} -- les deux doivent coincider"
        )


# --- Controles de la resolution de delegation -----------------------------
# Sans eux, l'extension « le script delegue compte comme le workflow » serait
# une affirmation : rien ne prouverait qu'elle atteint le script, ni qu'elle
# ne masque une suppression.

def _write_delegating_job(tmp_path: Path, script_body: str) -> Path:
    """Un workflow factice qui delegue son installation a un script."""
    (tmp_path / "scripts").mkdir(parents=True, exist_ok=True)
    (tmp_path / "scripts" / "install_deps.sh").write_text(script_body, encoding="utf-8")
    workflow = tmp_path / "workflow.yml"
    workflow.write_text(
        "      - name: Install dependencies\n"
        "        run: bash scripts/install_deps.sh\n",
        encoding="utf-8",
    )
    return workflow


def test_delegation_resolution_reaches_the_delegated_script(tmp_path):
    """Controle POSITIF : la resolution atteint le script delegue."""
    workflow = _write_delegating_job(tmp_path, 'pip install "pyarrow>=26"\n')
    text = _effective_code_lines(workflow, root=tmp_path)
    assert FLOOR in text, "la resolution doit atteindre le script delegue"
    _assert_bounded_floor(text, "job factice")


def test_a_delegated_script_without_the_floor_is_caught(tmp_path):
    """Controle NEGATIF : un script delegue sans plancher doit rougir."""
    workflow = _write_delegating_job(tmp_path, "pip install pytest\n")
    text = _effective_code_lines(workflow, root=tmp_path)
    try:
        _assert_bounded_floor(text, "job factice")
    except AssertionError:
        return
    raise AssertionError("un plancher absent du script delegue doit etre refuse")


def test_an_unbounded_install_in_a_delegated_script_is_caught(tmp_path):
    """Controle NEGATIF : `pip install pyarrow` nu dans le script doit rougir."""
    workflow = _write_delegating_job(
        tmp_path, 'pip install "pyarrow>=26"\npip install pyarrow\n'
    )
    text = _effective_code_lines(workflow, root=tmp_path)
    try:
        _assert_bounded_floor(text, "job factice")
    except AssertionError:
        return
    raise AssertionError("une installation sans borne doit etre refusee")


def test_a_delegated_script_that_prints_no_version_is_caught(tmp_path):
    """Controle NEGATIF : un script delegue muet sur la version doit rougir."""
    workflow = _write_delegating_job(tmp_path, 'pip install "pyarrow>=26"\n')
    text = _effective_code_lines(workflow, root=tmp_path)
    try:
        _assert_prints_version(text, "job factice")
    except AssertionError:
        return
    raise AssertionError("une version resolue non affichee doit etre refusee")


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
