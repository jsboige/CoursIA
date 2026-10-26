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


# === #20868 : arbre partiel (sparse-checkout, blob:none) ===

def test_sparse_checkout_falls_back_to_object_store(tmp_path):
    """#20868 : un fichier absent du disque mais present dans HEAD doit etre
    lu depuis l'object store, pas laisse pour None en silence.

    Mesure du constat : sur le depot reel, ICT-Series/pyproject.toml est
    materialise ; le test reproduit la situation d'un sparse-checkout qui
    detient le blob dans HEAD sans l'avoir pose sur disque. Le verdict doit
    alors nommer l'env, en le signalant par `from_object_store=True`.
    """
    import subprocess
    # Depot git jetable pour eviter de polluer le working tree reel.
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "config",
                    "user.email", "test@example.com"], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "config",
                    "user.name", "Test"], check=True)
    serie = tmp_path / "SerieSparse"
    serie.mkdir()
    pyproject = serie / "pyproject.toml"
    pyproject.write_text('[project]\nrequires-python = ">=3.11,<3.12"\n',
                         encoding="utf-8")
    nb = serie / "nb.ipynb"
    nb.write_text("{}", encoding="utf-8")
    subprocess.run(["git", "-C", str(tmp_path), "add", "."], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "commit", "-q",
                    "-m", "sparse fixture"], check=True)
    # Sparse-checkout simule : on garde le commit, on retire le fichier.
    pyproject.unlink()
    assert not pyproject.exists()

    hint = ckd.canonical_env_hint("SerieSparse/nb.ipynb", root=str(tmp_path))

    assert hint is not None, (
        "l'env epingle existe dans HEAD (commit) : le garde doit le trouver "
        "via l'object store, pas rendre None en silence sur OSError"
    )
    assert hint["artifact"] == "SerieSparse/pyproject.toml"
    assert hint["requires_python"] == ">=3.11,<3.12"
    assert hint.get("from_object_store") is True, (
        "le hint doit signaler qu'il vient de l'object store, pour que le "
        "lecteur sache que le verdict de drift est sensible a la materialisation"
    )


def test_sparse_checkout_no_artifact_in_head_returns_none(tmp_path):
    """#20868 contre-test : si l'OSError est lie a un fichier vraiment absent
    du depot (pas un sparse-checkout, juste pas la), le garde ne doit pas
    inventer un pointeur. None reste la bonne reponse -- l'absence EST
    l'information, cf docstring de `canonical_env_hint`.

    Sur un `tmp_path` qui n'est pas un depot git, `_git_show_head` rend None
    (pas de git, ou git sans objet) ; le `continue` ramene au comportement
    anterieur a #20868, qui etait correct dans ce cas.
    """
    serie = tmp_path / "Serie"
    serie.mkdir()
    (serie / "nb.ipynb").write_text("{}", encoding="utf-8")
    # Pas de pyproject, pas de requirements, pas de .git.
    assert ckd.canonical_env_hint("Serie/nb.ipynb", root=str(tmp_path)) is None


# === #22297 : un pointeur vers un intervalle qui ne peut pas heberger la base ===

def test_requires_python_allows_truth_table():
    """La comparaison d'intervalle, ses bornes, et ses refus de conclure."""
    allows = ckd._requires_python_allows

    # Heberge : la base est dans l'intervalle epingle.
    assert allows(">=3.9,<3.10", "3.9.25") is True
    assert allows(">=3.11,<3.14", "3.13.14") is True
    assert allows("==3.9", "3.9.25") is True

    # N'heberge pas : c'est le cas fondateur #22297 (base 3.13, pin 3.9).
    assert allows(">=3.9,<3.10", "3.13.14") is False
    assert allows(">=3.9,<3.10", "3.12.13") is False
    assert allows(">=3.11,<3.14", "3.9.25") is False
    assert allows("!=3.13", "3.13.14") is False

    # Non mesurable : on ne rend PAS une autorisation, on rend None.
    assert allows("~=3.9", "3.13.14") is None
    assert allows("", "3.13.14") is None
    assert allows("n importe quoi", "3.13.14") is None
    assert allows(">=3.9,<3.10", "") is None


def test_ict_pin_conflicts_with_a_313_base():
    """Le cas mesure de #22297 : la serie epingle 3.9, la base enregistre 3.13.

    Suivre l'indice ferait passer `language_info.version` de 3.13 a 3.9, une
    descente major.minor que ce meme garde refuse. L'indice doit donc porter le
    conflit plutot que laisser la lane le decouvrir a la prochaine execution.
    """
    nb = ("MyIA.AI.Notebooks/IIT/ICT-Series/"
          "ICT-40a-TriangulationCausale-Python.ipynb")

    conflit = ckd.canonical_env_hint(
        nb, root=str(REPO_ROOT), base_language_version="3.13.14")
    assert conflit is not None
    assert conflit["requires_python"] == ">=3.9,<3.10"   # le pin reste nomme
    assert "version_conflict" in conflit, (
        "une base 3.13 avec un pin >=3.9,<3.10 doit etre signalee : "
        "re-executer sous 3.9 est une descente refusee par le garde"
    )
    assert "3.13.14" in conflit["version_conflict"]
    assert "DOWNGRADE" in conflit["version_conflict"]

    # Controle positif du silence : les carnets ICT qui tournent REELLEMENT
    # sur le 3.9 epingle ne doivent porter aucun conflit.
    sain = ckd.canonical_env_hint(
        nb, root=str(REPO_ROOT), base_language_version="3.9.25")
    assert sain is not None
    assert "version_conflict" not in sain, (
        "une base 3.9 est hebergee par >=3.9,<3.10 : aucun conflit a declarer"
    )


def test_no_conflict_without_a_base_version():
    """Sans version de base, le hint garde exactement sa forme d'avant."""
    hint = ckd.canonical_env_hint(ICT_NOTEBOOK, root=str(REPO_ROOT))
    assert "version_conflict" not in hint


def test_a_compatible_pin_raises_no_conflict(tmp_path):
    """Controle negatif : un pin qui heberge la base ne doit pas crier au loup."""
    serie = tmp_path / "Serie"
    _write(serie / "pyproject.toml",
           '[project]\nrequires-python = ">=3.11,<3.14"\n'
           'dependencies = ["numpy>=2.0"]\n')
    (serie / "nb.ipynb").write_text("{}", encoding="utf-8")

    hint = ckd.canonical_env_hint(
        "Serie/nb.ipynb", root=str(tmp_path), base_language_version="3.13.14")
    assert hint["requires_python"] == ">=3.11,<3.14"
    assert "version_conflict" not in hint


def test_explain_branch_reports_the_conflict_instead_of_the_remedy():
    """Pin structurel : la branche --explain doit brancher sur le conflit.

    Sans ce branchement, le verdict continuerait d'affirmer qu'un rejeu sous
    l'env epingle « garde le repr commite stable » -- exactement le conseil qui
    produit la descente refusee.
    """
    source = (Path(ckd.__file__)).read_text(encoding="utf-8")
    start = source.index("if args_obj.explain:")
    end = source.index('finding["probable_causes"] = causes')
    explain_branch = source[start:end]

    assert "base_language_version=" in explain_branch, (
        "le hint doit recevoir la version de la base : sans elle, il ne peut "
        "pas mesurer que l'intervalle epingle ne l'heberge pas"
    )
    assert 'env_hint.get("version_conflict")' in explain_branch, (
        "le verdict doit distinguer un pointeur suivable d'un pointeur qui "
        "nous ferait descendre de version"
    )
