"""Ancrage du scratch de test hors du volume partage et hors du depot.

pytest ecrit par defaut ses repertoires `tmp_path` dans le `%TEMP%` systeme.
Mais une session qui passe `--basetemp` a la main ecrit souvent a la
**racine du volume partage** : le 27/10/2026, 30 de ces repertoires
(`tmp-pytest-*`, `tmp-c2259-rg*`) etaient poses a la racine de `D:` (mandat
user de rangement du volume, mesure `myia-ai-01:CoursIA-2` : 30 dossiers +
3 fichiers).

Ce `conftest.py` impose un scratch **par session**, sous
`%LOCALAPPDATA%/CoursIA/pytest/<projet>/run-<pid>/` (POSIX :
`$XDG_STATE_HOME/CoursIA/pytest/...`, sinon `~/.local/state/...`), et le
supprime a la fin de la session.

**Pourquoi pas dans le depot** (`<rootdir>/.tmp/pytest`) : le ledger de
dette REFUSE un repertoire d'etat a l'interieur d'un arbre git
(`REPO_PATH_REFUSED`, `scripts/coordination/debt_ledger.py` -- « ledger
state is not repo content »). Les tests du ledger utilisent `tmp_path`
comme repertoire d'etat : un scratch ancre dans le depot fait echouer 32 de
ces tests. Mesure sur cette machine, `pytest scripts/tests/test_debt_ledger.py` :
**32 failed, 107 passed** avec l'ancrage dans le depot, **1 failed, 138
passed** hors arbre git (le rouge restant est `jupyter-nbconvert` absent de
la machine, independant du scratch).

**Pourquoi un dossier par session** : pytest VIDE le `--basetemp` au
demarrage. Un scratch partage entre deux sessions concurrentes de la meme
machine (le cluster en lance plusieurs) se marcherait dessus. Le `pid`
donne l'unicite, et `pytest_sessionfinish` nettoie.

Un `--basetemp` passe en ligne de commande reste **prioritaire** : c'est lui
qui fait foi quand une execution a besoin d'un scratch particulier (xdist
derive deja le sien par worker : `basetemp/<worker>`,
`xdist/workermanage.py`).
"""

import os
import shutil
from pathlib import Path


def _scratch_base(rootpath: Path) -> Path:
    """Racine machine du scratch de test, hors de tout arbre git."""
    local = os.environ.get("LOCALAPPDATA")
    if local:
        base = Path(local) / "CoursIA" / "pytest"
    else:
        xdg = os.environ.get("XDG_STATE_HOME")
        root = Path(xdg) if xdg else Path.home() / ".local" / "state"
        base = root / "CoursIA" / "pytest"
    return base / (rootpath.name or "racine")


def pytest_configure(config):
    if config.getoption("basetemp", None):
        return
    session = _scratch_base(Path(config.rootpath)) / f"run-{os.getpid()}"
    session.parent.mkdir(parents=True, exist_ok=True)
    config.option.basetemp = str(session)
    config._coursia_scratch = session


def pytest_sessionfinish(session, exitstatus):
    """Supprime le scratch de la session : il ne laisse pas de trace."""
    scratch = getattr(session.config, "_coursia_scratch", None)
    if scratch is None:
        return
    shutil.rmtree(scratch, ignore_errors=True)
