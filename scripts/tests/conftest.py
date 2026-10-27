"""Conftest : ajoute scripts/ au sys.path pour les imports des tests."""
import os
import subprocess
import sys
from pathlib import Path

import pytest

# Ajoute scripts/ (parent de tests/) au sys.path pour permettre
# `import roosync_archive_backfill` direct dans les tests.
_SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(_SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS_DIR))


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
