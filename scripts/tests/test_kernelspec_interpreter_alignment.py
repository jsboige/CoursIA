"""Le kernelspec `python3` du job pointe l'interpreteur que `pip` remplit (#28500).

`pip install ipykernel` installe le MODULE ; il n'ecrit AUCUN kernelspec.
Le job comptait donc sur un `python3` deja present dans l'image -- dont
l'interpreteur n'est pas force de celui que `pip` a rempli.

Mesure du 2026-11-25 (PR #28485, jobs 138965717984 slot-6 et 138980845410
slot-5) : sur le parc auto-heberge `CoursIA-runners-p0`,
`pip install "axelrod>=4.0.0"` REUSSIT ("Requirement already satisfied:
axelrod 4.14.0") et pourtant `import axelrod` echoue en cellule 56 de
GameTheory-06 -- le noyau papermill `-k python3` tourne sous un autre
interpreteur. Deux slots differents, meme echec ; le runner heberge passe
(job 139001135192) : c'est l'image du parc qui decide.

Ce test verrouille le couplage :

1. les commandes EFFECTIVES du job (le workflow ET les scripts qu'il
   appelle) ENREGISTRENT un kernelspec `python3` ;
2. le nom de noyau que papermill demande (`-k`) est celui qui est
   enregistre -- un deschange des deux doit rougir.

Il se valide par ses faux negatifs : une commande commentee, ou un script
delegue sans enregistrement, doivent le faire rougir.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

WORKFLOW = REPO_ROOT / ".github" / "workflows" / "scripts-tests.yml"

# L'enregistrement du kernelspec : `python -m ipykernel install ... --name python3`.
REGISTER_RE = re.compile(
    r"python\s+-m\s+ipykernel\s+install[^\n]*?--name\s+[\"']?(python3)[\"']?"
)

# Le noyau que papermill demande : `-k python3` ou `--kernel-name python3`.
KERNEL_ARG_RE = re.compile(r"(?:-k|--kernel-name)[\s=]+[\"']?(python3)[\"']?")


def _without_comment_lines(text: str) -> str:
    """Le texte sans ses lignes de commentaire.

    Un commentaire qui MENTIONNE la commande (pour expliquer le defaut)
    n'est pas une execution : le scanner ne doit pas le lire comme tel.
    """
    kept = []
    for line in text.splitlines():
        if line.strip().startswith("#"):
            continue
        kept.append(line)
    return "\n".join(kept)


def _code_lines(path: Path) -> str:
    """Le fichier sans ses lignes de commentaire."""
    return _without_comment_lines(path.read_text(encoding="utf-8"))


def _delegated_scripts(text: str, root: Path) -> list[Path]:
    """Les scripts de `scripts/` appeles par le texte executable."""
    found: list[Path] = []
    seen: set[str] = set()
    for match in re.finditer(r"bash\s+(scripts/[\w./-]+\.sh)", text):
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


def test_the_job_registers_the_python3_kernelspec():
    """Le job enregistre un kernelspec `python3` (acceptance #1)."""
    text = _effective_code_lines(WORKFLOW)
    assert REGISTER_RE.search(text), (
        "scripts-tests.yml : aucun enregistrement de kernelspec `python3` dans "
        "les commandes EFFECTIVES du job -- `pip install ipykernel` installe "
        "le module, il n'ecrit aucun kernelspec ; le noyau papermill peut "
        "alors partir d'un interpreteur que `pip` n'a pas rempli "
        "(mesure #28500 : `ModuleNotFoundError: No module named 'axelrod'` "
        "sur le parc auto-heberge, etape verte sur le runner heberge)"
    )


def test_the_registration_is_in_the_user_scope():
    """L'enregistrement est `--user` : le repertoire utilisateur gagne.

    Dans l'ordre de recherche de Jupyter, le repertoire utilisateur
    (`~/.local/share/jupyter/kernels`) passe AVANT le prefixe systeme et
    avant `/usr/share/jupyter` -- c'est donc lui qui gagne, meme si
    l'image porte deja un `python3`.
    """
    text = _effective_code_lines(WORKFLOW)
    match = REGISTER_RE.search(text)
    assert match is not None
    assert "--user" in match.group(0), (
        "l'enregistrement du kernelspec doit etre `--user` -- sans lui, le "
        "kernelspec de l'image peut gagner la recherche"
    )


def test_the_registered_name_is_the_one_papermill_asks_for():
    """Le nom enregistre est celui que papermill demande (acceptance #2)."""
    text = _effective_code_lines(WORKFLOW)
    registered = {match.group(1) for match in REGISTER_RE.finditer(text)}
    asked = {match.group(1) for match in KERNEL_ARG_RE.finditer(text)}
    assert asked, (
        "scripts-tests.yml : aucun appel papermill avec `-k` dans les "
        "commandes effectives -- le couplage noyau/kernelspec ne serait "
        "pas mesurable"
    )
    assert asked <= registered, (
        f"noyau demande par papermill {sorted(asked)} mais enregistre "
        f"{sorted(registered)} -- le noyau lancer ne serait pas celui "
        f"enregistre"
    )


def test_a_commented_registration_does_not_count():
    """Controle NEGATIF : une commande commentee n'enregistre aucun noyau."""
    commented = _without_comment_lines(
        "# python -m ipykernel install --user --name python3\n"
    )
    assert not REGISTER_RE.search(commented), (
        "une commande commentee ne doit pas satisfaire l'acceptance #1"
    )
    executable = 'python -m ipykernel install --user --name python3\n'
    assert REGISTER_RE.search(executable), (
        "la forme executable doit etre reconnue"
    )


def test_a_delegated_script_without_the_registration_is_caught(tmp_path):
    """Controle NEGATIF : un script delegue sans enregistrement doit rougir."""
    (tmp_path / "scripts").mkdir(parents=True, exist_ok=True)
    (tmp_path / "scripts" / "install_deps.sh").write_text(
        "pip install ipykernel\n", encoding="utf-8"
    )
    workflow = tmp_path / "workflow.yml"
    workflow.write_text(
        "      - name: Install dependencies\n"
        "        run: bash scripts/install_deps.sh\n",
        encoding="utf-8",
    )
    text = _effective_code_lines(workflow, root=tmp_path)
    assert not REGISTER_RE.search(text), (
        "un script delegue sans enregistrement doit etre refuse"
    )


if __name__ == "__main__":
    for fn in (
        test_the_job_registers_the_python3_kernelspec,
        test_the_registration_is_in_the_user_scope,
        test_the_registered_name_is_the_one_papermill_asks_for,
        test_a_commented_registration_does_not_count,
        test_a_delegated_script_without_the_registration_is_caught,
    ):
        fn()
        print(f"OK: {fn.__name__}")
    print("All tests passed.")
