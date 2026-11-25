"""Conftest : ajoute scripts/ au sys.path pour les imports des tests."""
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

# Ajoute scripts/ (parent de tests/) au sys.path pour permettre
# `import roosync_archive_backfill` direct dans les tests.
_SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(_SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS_DIR))

# T3-c (#25366) : les outils internes reloges dans leur famille (audit,
# bibliography, ci, coordination, notebook_tools, slides) restent importables
# a nu par les tests de scripts/tests/, comme ils l etaient a la racine.
# V3 #13737 tranche 1 : familles genai et quantconnect ajoutees (meme geste).
for _fam in ("audit", "bibliography", "ci", "coordination", "notebook_tools", "slides", "genai", "quantconnect"):
    _fam_dir = _SCRIPTS_DIR / _fam
    if _fam_dir.is_dir() and str(_fam_dir) not in sys.path:
        sys.path.insert(0, str(_fam_dir))


class ShellEscape(BaseException):
    """Un test a lance un processus alors que ses sources sont simulees.

    Herite de ``BaseException`` et non de ``Exception`` : le code sous test
    enveloppe ses appels sortants dans des ``except (OSError, RuntimeError,
    CalledProcessError, ...)`` pour rendre ``(resultat, erreur)``. Un
    ``AssertionError`` serait alors avale, et le test passerait sur un corpus
    VIDE presente comme une mesure -- exactement le vert muet que la
    sentinelle existe pour empecher.
    """


@pytest.fixture
def bash() -> str:
    """Bash capable d'exécuter les scripts du dépôt depuis un process natif.

    Sous Windows, le ``bash`` du PATH peut être celui de WSL (System32), qui
    ne monte pas les chemins ``D:/`` du worktree ; le bash de Git pour
    Windows (``bin/bash.exe``) initialise son contexte msys seul. Ailleurs
    (Linux, CI), ``bash`` du PATH suffit. Issue #27685.
    """
    if os.name != "nt":
        return "bash"
    for env_var, fallback in (("ProgramFiles", r"C:\Program Files"),
                              ("ProgramFiles(x86)", r"C:\Program Files (x86)")):
        candidate = Path(os.environ.get(env_var) or fallback) / "Git" / "bin" / "bash.exe"
        if candidate.is_file():
            return str(candidate)
    return shutil.which("bash") or "bash"


@pytest.fixture
def stub_as_function():
    """Windows : expose les stubs bash comme fonctions via BASH_ENV.

    msys place /usr/bin AVANT le PATH hérité : un stub portant le nom d'un
    coreutil (mkdir, mv, uname, python3) est toujours masqué par le vrai.
    BASH_ENV est sourcé par tout bash non interactif et une fonction gagne
    sur la résolution PATH (issue #27685). Sans effet ailleurs.
    """
    def _install(commands: Path, names: tuple, env: dict) -> None:
        if os.name != "nt":
            return
        lines = [
            "# Généré par les tests : stubs prioritaires sur les coreutils",
            "# msys, toujours premiers dans le PATH hérité (issue #27685).",
        ]
        for name in names:
            lines.append(f'{name}() {{ "{(commands / name).as_posix()}" "$@"; }}')
        env_file = commands / "stub_functions.sh"
        env_file.write_text("\n".join(lines) + "\n", newline="\n")
        env["BASH_ENV"] = env_file.as_posix()
    return _install


@pytest.fixture
def forbid_shell_escape(monkeypatch):
    """Sentinelle : refuser toute execution de processus pendant le test.

    Un test de `pick_idle_grain` ne doit jamais atteindre le reseau : ses
    sources sont simulees une par une. Une source NON simulee ne se voyait
    pas -- elle tombait sur le cache chaud de la machine (vert) ou sur `gh`
    (lent, et dependant de l'etat du reseau). L'appel non simule devient ici
    un echec immediat qui NOMME la commande refusee.

    On patche les attributs du module ``subprocess`` lui-meme, pas un alias
    local : chacun des modules de la chaine (`pick_idle_grain`,
    `series_saturation`, `ci/fetch_merged_prs_since`) appelle
    ``subprocess.run`` par son propre global. Patcher le seul namespace de
    l'entree laisserait passer les appels des voisins.
    """

    def _refuse(argv, *args, **kwargs):
        rendered = (" ".join(str(x) for x in argv)
                    if isinstance(argv, (list, tuple)) else str(argv))
        raise ShellEscape(
            f"reseau non simule : ce test a lance un processus ({rendered})."
            " Simuler la source (monkeypatch) au lieu de sortir."
        )

    class _RefusedPopen:
        def __init__(self, argv, *args, **kwargs):
            _refuse(argv)

    monkeypatch.setattr(subprocess, "run", _refuse)
    monkeypatch.setattr(subprocess, "Popen", _RefusedPopen)
    monkeypatch.setattr(subprocess, "check_output", _refuse)


class GhTokenEnv:
    """Capture de ``GH_TOKEN`` autour d'un test, avec restauration explicite.

    ``gh_identity.pin_gh_token()`` ecrit ``os.environ["GH_TOKEN"]`` DIRECTEMENT :
    quand la variable etait ABSENTE, ni ``monkeypatch.setenv`` ni
    ``monkeypatch.delenv`` n'enregistrent rien a restaurer -- l'ecriture
    survit donc au test qui l'a provoque. Un jeton fictif restait ainsi pose
    pour TOUTE la session pytest, et il masquait des echecs REELS : 12 tests
    du picker qui, sans jeton dans l'environnement, tentaient un vrai
    ``gh auth token`` (processus refuse par la sentinelle) passaient des que
    le fichier polluant ait ete execute avant eux. La suite devenait
    dependante de l'ORDRE de ses fichiers (#21994).
    """

    def __init__(self, saved):
        self.saved = saved

    def restore(self):
        """Remet ``GH_TOKEN`` dans l'etat capture ; rend sa valeur finale."""
        if self.saved is None:
            os.environ.pop("GH_TOKEN", None)
        else:
            os.environ["GH_TOKEN"] = self.saved
        return os.environ.get("GH_TOKEN")


@pytest.fixture
def gh_token_env():
    """Capture et restaure ``GH_TOKEN`` autour du test (#21994)."""
    env = GhTokenEnv(os.environ.get("GH_TOKEN"))
    yield env
    env.restore()


@pytest.fixture(autouse=True)
def _gh_token_hermetique():
    """Filet de securite : aucun test ne laisse de jeton derriere lui.

    Un test qui ecrit ``GH_TOKEN`` dans ``os.environ`` sans passer par
    ``monkeypatch`` contaminerait tous les tests suivants -- et la suite
    deviendrait dependante de l'ordre de ses fichiers. Le filet restaure
    silencieusement l'etat capture : la contamination devient impossible,
    meme chez un test qui l'ignore.
    """
    env = GhTokenEnv(os.environ.get("GH_TOKEN"))
    yield
    env.restore()


def _reset_belt_deadline() -> None:
    mod = sys.modules.get("pick_idle_grain")
    deadline = getattr(mod, "_BELT_DEADLINE", None) if mod else None
    if deadline:
        deadline[0] = None


@pytest.fixture(autouse=True)
def _belt_deadline_hermetique():
    """Filet de securite : aucun test n'herite du mur du tapis d'un autre.

    ``pick_idle_grain._BELT_DEADLINE`` est un etat de module, lu par
    ``_clamp_timeout`` a chaque sonde. Un test qui l'arme sans le desarmer
    (un ``main(--belt)`` sorti avant son ``_disarm_belt_run_clock``, par
    exemple) borne les timeouts de tous les tests suivants du meme worker
    xdist : ``test_timeout_valeur_explicite_120_pour_transport_principal``
    lisait alors le budget restant (43,8 s) au lieu de 120 (CI du
    2026-11-01, job 124823477304). Remis a ``None`` avant ET apres chaque
    test : le test suivant part d'un mur desarme, quel que soit l'ordre.
    """
    _reset_belt_deadline()
    yield
    _reset_belt_deadline()


@pytest.fixture(autouse=True)
def _gh_etag_desactive(monkeypatch):
    """Filet de securite (#26631, CR coordinateur) : ETag persiste DESACTIVE.

    Les tests qui mockent ``subprocess.run`` servent un stdout SANS bloc
    d'en-tetes de ``gh api -i`` : si le chemin conditionnel etait pris, le
    corps lu serait vide (incident : test_gh_json_porte_une_borne_par_appel,
    run 43651006619 -- rouge sur le runner Linux la ou le garde
    ``cache_dir()`` de gh_etag suffit sur machine sans LOCALAPPDATA ; ce
    filet couvre AUSSI Windows ou LOCALAPPDATA est pose). Sans cache
    (``COURSIA_GH_ETAG=0``), ``etag_applicable`` rend None et les organes
    reprennent leur chemin d'origine octet pour octet. Les tests de gh_etag
    eux-memes re-activent explicitement dans leur fixture ``cache_isole``.
    """
    monkeypatch.setenv("COURSIA_GH_ETAG", "0")
    yield


@pytest.fixture(autouse=True)
def _tapis_lourd_en_diagnostic(monkeypatch):
    """#26926 : les tests exercent le tapis lourd comme outil de diagnostic.

    Hors diagnostic, ``pick_idle_grain.py --belt`` refuse et nomme le tapis
    rapide. Les suites du tapis lourd testent ses mecanismes : elles le lancent
    donc en diagnostic. Le test du refus retire la variable explicitement.
    """
    monkeypatch.setenv("COURSIA_HEAVY_BELT_DIAGNOSTIC", "1")
    yield
