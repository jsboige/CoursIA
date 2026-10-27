"""Ancrage du scratch de test dans le workspace.

pytest ecrit par defaut ses repertoires `tmp_path` dans le `%TEMP%` systeme, et
une session qui passe `--basetemp` a la main ecrit souvent a la **racine du
volume partage** : le 27/10/2026, 30 de ces repertoires (`tmp-pytest-*`,
`tmp-c2259-rg*`) etaient poses a la racine de `D:` (mandat user de rangement du
volume, mesure `ai-ai-01:CoursIA-2` : 30 dossiers + 3 fichiers).

Ici, le scratch vit sous `<rootdir>/.tmp/pytest` -- la racine du depot ou du
worktree courant, un dossier deja gitignore (`.gitignore` : `*.tmp`). Il
disparait avec le workspace et ne touche jamais le volume partage.

Un `--basetemp` passe en ligne de commande reste **prioritaire** : c'est lui
qui fait foi quand une execution a besoin d'un scratch particulier (xdist
derive deja le sien par worker : `basetemp/<worker>`, `xdist/workermanage.py`).
"""

from pathlib import Path


def pytest_configure(config):
    if config.getoption("basetemp", None):
        return
    scratch = Path(config.rootpath) / ".tmp" / "pytest"
    # pytest cree le basetemp sans `parents=True` : le parent `.tmp` doit
    # exister, sinon la session echoue sur un `FileNotFoundError`.
    scratch.parent.mkdir(parents=True, exist_ok=True)
    config.option.basetemp = str(scratch)
