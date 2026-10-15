"""Le verdict de drift doit NOMMER l'environnement canonique quand il en existe un.

Issue #17185. Le constat de l'issue impute le drift a une **absence** d'env
canonique pour la serie ICT. Verification firsthand de ce point avant d'ecrire :
l'env ICT est epingle et documente (`IIT/ICT-Series/pyproject.toml` et
`IIT/requirements.txt` : Python 3.9, `pyphi==1.2.0`, `numpy>=1.21,<2.0`,
`pyemd==0.5.1` connu-bon, avec le pourquoi de chaque pin). Ce qui manquait est
le POINTEUR vers lui au moment ou la lane lit le verdict : `--explain` nommait
le mecanisme du drift (« un autre interpreteur, 3.11 -> 3.13 », « NumPy 1.x ->
2.x ») sans dire ou rejouer, et la lane re-executait avec son env local -- ce
qui reproduisait exactement le drift signale.

Ces tests pincent les deux moities : la resolution (quelle serie -> quel
artefact) et le fait que le verdict la porte effectivement.
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve()
sys.path.insert(0, str(HERE.parent.parent))

import check_kernel_drift as ckd

REPO_ROOT = HERE.parents[3]

ICT_NOTEBOOK = ("MyIA.AI.Notebooks/IIT/ICT-Series/"
                "ICT-01-PhiTrajectories-Python.ipynb")


def _write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


# === Resolution : quelle serie -> quel artefact ===

def test_ict_notebook_resolves_to_its_pinned_env():
    """L'instance fondatrice : l'env de la serie ICT existe et doit etre nomme."""
    hint = ckd.canonical_env_hint(ICT_NOTEBOOK, root=str(REPO_ROOT))

    assert hint is not None, (
        "l'env ICT est epingle dans IIT/ICT-Series/pyproject.toml -- "
        "le garde doit le nommer plutot que de laisser la lane deviner"
    )
    assert hint["artifact"].endswith("IIT/ICT-Series/pyproject.toml")
    assert hint["requires_python"] == ">=3.9,<3.10"
    # Le pin numpy est la cause de drift que le message nomme deja : il doit
    # voyager avec le pointeur, sinon la lane doit rouvrir le fichier.
    assert "<2.0" in hint["numpy_pin"]


def test_requires_python_is_reported_when_the_artifact_declares_it(tmp_path):
    nb = tmp_path / "Serie" / "nb.ipynb"
    _write(tmp_path / "Serie" / "pyproject.toml",
           '[project]\nrequires-python = ">=3.11,<3.12"\n')

    hint = ckd.canonical_env_hint("Serie/nb.ipynb", root=str(tmp_path))

    assert hint == {"artifact": "Serie/pyproject.toml",
                    "requires_python": ">=3.11,<3.12"}


def test_requirements_txt_is_the_fallback_artifact(tmp_path):
    """Sans pyproject, un requirements.txt enonce quand meme l'env."""
    nb = tmp_path / "Serie" / "nb.ipynb"
    _write(tmp_path / "Serie" / "requirements.txt",
           "# env de la serie\nnumpy>=1.26,<2.0\nscipy\n")

    hint = ckd.canonical_env_hint("Serie/nb.ipynb", root=str(tmp_path))

    assert hint["artifact"] == "Serie/requirements.txt"
    assert hint["numpy_pin"] == "numpy>=1.26,<2.0"
    assert "requires_python" not in hint


def test_no_artifact_returns_none(tmp_path):
    """L'absence est une information : pas de chemin invente."""
    (tmp_path / "Serie").mkdir()

    assert ckd.canonical_env_hint("Serie/nb.ipynb", root=str(tmp_path)) is None


def test_walk_stops_at_the_series_boundary(tmp_path):
    """Falsifiable : l'artefact au 3e niveau est trouve, celui du 4e ne l'est pas.

    Sans la borne, la remontee atteindrait la racine du depot et nommerait un
    artefact qui ne couvre plus la serie -- un chemin qui a l'apparence d'une
    reponse. Ce test echoue si la borne est retiree : le 4e niveau serait rendu.
    """
    nb_rel = "s1/s2/s3/s4/nb.ipynb"  # niveaux remontes : s4, s3, s2
    _write(tmp_path / "s1" / "s2" / "pyproject.toml",
           '[project]\nrequires-python = ">=3.7"\n')
    _write(tmp_path / "s1" / "pyproject.toml",
           '[project]\nrequires-python = ">=3.8"\n')

    # 3e niveau (s1/s2) : trouve.
    assert ckd.canonical_env_hint(nb_rel, root=str(tmp_path)) is not None

    # Au 4e niveau (s1) seulement : non trouve -- c'est la borne qui parle.
    (tmp_path / "s1" / "s2" / "pyproject.toml").unlink()
    assert ckd.canonical_env_hint(nb_rel, root=str(tmp_path)) is None


# === Le verdict porte effectivement le pointeur ===

def test_explain_branch_calls_the_env_hint():
    """Pin structurel : la cause nommee dans la branche --explain inclut le pointeur."""
    source = (Path(ckd.__file__)).read_text(encoding="utf-8")

    start = source.index("if args_obj.explain:")
    end = source.index('finding["probable_causes"] = causes')
    explain_branch = source[start:end]

    assert "canonical_env_hint(" in explain_branch, (
        "le pointeur d'env doit etre produit DANS la branche --explain : "
        "c'est ce que le workflow consomme (--explain --json)"
    )


# === Arbre partiel : l'artefact existe dans HEAD mais pas sur disque ===
# (issue #20868, troisieme mode de #20200). Avant le fix, la fonction
# rendait None en silence sur OSError -- le verdict pretendait que la serie
# n'epingle rien, fait faux sur le depot. Apres le fix :
#  1) si l'artefact est joignable via `git show HEAD:<rel>`, le hint est
#     rendu (memes champs qu'avant), les pins (requires-python, numpy_pin)
#     sont lus depuis l'object store.
#  2) si l'artefact git est lu mais les regex de pin ne trouvent rien,
#     un dict {"status": "unknown", "artifact": "..."} est rendu -- un
#     "unknown" explicite, pas un silence couvert par None.
#  3) si l'artefact n'est ni sur disque ni dans HEAD, on continue la
#     remontee, et None est rendu seulement si aucun candidat n'existe.


def test_partial_tree_falls_back_to_git_object_store(tmp_path):
    """L'artefact absent du disque mais present dans HEAD est rendu en hint 'git'.

    Cas reel : checkout sparse-checkout / blob:none sur un runner CI ou le
    detecteur voit la serie ICT mais ne materialise pas pyproject.toml.
    Le verdict doit TOUJOURS pointer vers l'artefact, pas se taire.
    """
    nb = tmp_path / "Serie" / "nb.ipynb"
    nb.parent.mkdir(parents=True, exist_ok=True)
    nb.write_text("{}", encoding="utf-8")
    # L'artefact existe UNIQUEMENT dans l'object store git (HEAD) -- on
    # simule l'arbre partiel en initialisant un mini-repo, en y commitant
    # un pyproject.toml, puis en effacant le fichier du worktree par
    # `git rm --cached` + checkout pour le rendre absent du disque mais
    # present dans l'index de la prochaine remontee.
    import subprocess as _sp
    _sp.run(["git", "init", "-q"], cwd=str(tmp_path), check=True)
    _sp.run(["git", "config", "user.email", "t@t"], cwd=str(tmp_path), check=True)
    _sp.run(["git", "config", "user.name", "t"], cwd=str(tmp_path), check=True)
    pp_dir = tmp_path / "Serie"
    pp_dir.mkdir(parents=True, exist_ok=True)
    pp = pp_dir / "pyproject.toml"
    pp.write_text(
        '[project]\nrequires-python = ">=3.11,<3.12"\n'
        'dependencies = ["numpy>=1.26,<2.0"]\n',
        encoding="utf-8",
    )
    _sp.run(["git", "add", "Serie/pyproject.toml"],
            cwd=str(tmp_path), check=True)
    _sp.run(["git", "commit", "-q", "-m", "init"],
            cwd=str(tmp_path), check=True)
    # Maintenant on retire le fichier du worktree (mais on garde l'index).
    _sp.run(["git", "rm", "--cached", "-q", "Serie/pyproject.toml"],
            cwd=str(tmp_path), check=True)
    _sp.run(["git", "commit", "-q", "-m", "drop worktree"],
            cwd=str(tmp_path), check=True)
    # Et on restaure le fichier dans l'index (mais pas dans le worktree)
    # pour simuler le cas sparse-checkout ou le fichier est dans l'index
    # mais absent du worktree.
    _sp.run(["git", "reset", "--hard", "HEAD~1", "-q"],
            cwd=str(tmp_path), check=True)
    # Le fichier est de retour sur disque apres reset --hard : on l'efface
    # directement pour creer le cas "absent du disque mais committe".
    pp.unlink()
    assert not pp.exists(), "le test repose sur l'absence du fichier"

    hint = ckd.canonical_env_hint("Serie/nb.ipynb", root=str(tmp_path))

    # Le hint DOIT etre non-None : l'artefact est dans HEAD.
    assert hint is not None, (
        "l'artefact est committe sur HEAD mais absent du disque -- "
        "le hint DOIT le rendre via le fallback git object store"
    )
    assert hint["artifact"].endswith("Serie/pyproject.toml")
    # Les pins sont parses depuis le texte de l'object store -- preuve
    # que la remontee a emprunte le fallback git (sans elle, l'OSError
    # du `read_text` aurait fait `continue` et le hint serait None).
    assert hint["requires_python"] == ">=3.11,<3.12"
    assert "numpy" in hint["numpy_pin"]


def test_partial_tree_unknown_when_pins_unparseable(tmp_path):
    """L'artefact committe mais sans pin reconnu -> hint 'unknown'.

    Edge case : le fichier est dans HEAD, git le lit, mais les regex de
    pin ne trouvent rien. Le verdict doit le DIRE ('environment exists
    but pins unreadable'), pas se taire.
    """
    import subprocess as _sp
    _sp.run(["git", "init", "-q"], cwd=str(tmp_path), check=True)
    _sp.run(["git", "config", "user.email", "t@t"], cwd=str(tmp_path), check=True)
    _sp.run(["git", "config", "user.name", "t"], cwd=str(tmp_path), check=True)
    pp_dir = tmp_path / "Serie"
    pp_dir.mkdir(parents=True, exist_ok=True)
    pp = pp_dir / "pyproject.toml"
    pp.write_text("# pas de pin reconnu\nfoo = bar\n", encoding="utf-8")
    _sp.run(["git", "add", "Serie/pyproject.toml"],
            cwd=str(tmp_path), check=True)
    _sp.run(["git", "commit", "-q", "-m", "init"],
            cwd=str(tmp_path), check=True)
    pp.unlink()  # artefact absent du disque

    hint = ckd.canonical_env_hint("Serie/nb.ipynb", root=str(tmp_path))

    assert hint == {"status": "unknown", "artifact": "Serie/pyproject.toml"}, (
        f"hint={hint!r} ; attendu {{'status': 'unknown', 'artifact': "
        f"'Serie/pyproject.toml'}} (artefact git, pins muets)"
    )
