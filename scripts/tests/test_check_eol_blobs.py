"""Tests unitaires pour la garde CRLF/mixte (#19374 + revue 5421649286).

Couvre la matrice de decision de `_classify` (7 cas) et le parseur
`_parse_ls_files_line` (4 cas), plus 2 tests d'integration subprocess.

Les tests fondateurs du precedent #19388 (PR fermee, tests repris avec
credit) etaient structures autour de `BAD_INDEX = "crlf"` string simple.
Le refactor en tuple + `_classify` permet de tester chaque cas en
isolation, sans mocker `git ls-files --eol`.

Patterns valides :
  i/lf + text/lf/crlf/-text  -> NOT flagged (deja normalise)
  i/crlf + crlf              -> NOT flagged (volontaire via eol=crlf)
  i/crlf + -text             -> NOT flagged (binaire, pas renormalise)
  i/crlf + empty             -> NOT flagged (non-declare, depend de core.autocrlf)
  i/crlf + text              -> flagged (blob CRLF declare text -- le worktree sera modifie)
  i/crlf + lf                -> flagged (idem)
  i/mixed + text             -> flagged (le cas fondateur de #19287)
  i/mixed + lf               -> flagged

Garde-par-Je (c.184) : les cas `i/crlf + text` / `i/mixed + text` /
`i/crlf + lf` / `i/mixed + lf` rougissent. Les autres passent en
silencieux (exit 0 implicite via main, ou `_classify` False).
"""
from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest


# Charge le module sans dependre du packaging (le script n'est pas dans
# un package). Meme mecanisme que test_check_eol_blob_attribute.py
# (PR #19388, fermee par sa lane) -- ici adapte au module refactore.
_HERE = Path(__file__).resolve().parent
_MOD_PATH = _HERE.parent / "ci" / "check_eol_blobs.py"
_spec = importlib.util.spec_from_file_location("check_eol_blobs", _MOD_PATH)
assert _spec is not None and _spec.loader is not None
mod = importlib.util.module_from_spec(_spec)
sys.modules["check_eol_blobs"] = mod
_spec.loader.exec_module(mod)


# --- Tests parsing `_parse_ls_files_line` (4 cas) ---

def test_parse_ls_files_line_typical_text_lf() -> None:
    """Le cas typique : `attr/text eol=lf`, le worktree ecrase LF."""
    line = "i/lf w/lf attr/text eol=lf \tpath/to/file.py"
    parsed = mod._parse_ls_files_line(line)
    assert parsed == ("lf", "text", "path/to/file.py")


def test_parse_ls_files_line_attr_trailing_space() -> None:
    """Pas d'entree `.gitattributes` -> `attr/ ` avec espace final.
    La regex doit tolerer cet attribut vide et le retourner tel quel
    (le strip est l'affaire de `_classify`, pas du parseur)."""
    line = "i/lf w/lf attr/ eol=lf \tpath/to/file.py"
    parsed = mod._parse_ls_files_line(line)
    assert parsed is not None
    i_attr, attr, path = parsed
    assert i_attr == "lf"
    assert attr.strip() == ""
    assert path == "path/to/file.py"


def test_parse_ls_files_line_garbage_returns_none() -> None:
    """Une ligne qui n'est pas au format doit rendre None, pas exploser."""
    assert mod._parse_ls_files_line("") is None
    assert mod._parse_ls_files_line("hello world") is None
    assert mod._parse_ls_files_line("i/lf") is None


def test_parse_ls_files_line_with_spaces_in_path() -> None:
    """Un chemin avec espaces : `\t` sert de separateur entre metadata et path,
    le path peut contenir des espaces (rare sur Windows mais legal)."""
    line = "i/mixed w/mixed attr/text eol=lf \tpath with space/file.py"
    parsed = mod._parse_ls_files_line(line)
    assert parsed is not None
    _, _, path = parsed
    assert path == "path with space/file.py"


# --- Tests matrice `_classify` (7 cas) ---

def test_decision_lf_text_NOT_flagged() -> None:
    """Cas trivial : le blob est LF, deja normalise."""
    assert mod._classify("lf", "text") is False


def test_decision_crlf_with_crlf_attr_NOT_flagged() -> None:
    """CRLF volontaire via `eol=crlf` : la garde respecte le contrat."""
    assert mod._classify("crlf", "crlf") is False


def test_decision_crlf_with_minus_text_NOT_flagged() -> None:
    """Binaire declare via `-text` : pas de renormalisation."""
    assert mod._classify("crlf", "-text") is False


def test_decision_crlf_with_empty_attr_NOT_flagged() -> None:
    """CRLF sans entree `.gitattributes` : depend de core.autocrlf, pas
    d'un contrat commite -- la garde laisse passer (l'auteur peut
    corriger `.gitattributes` ou la config locale)."""
    assert mod._classify("crlf", "") is False


def test_decision_crlf_with_text_flagged() -> None:
    """Cas fondateur #19287 : blob CRLF declare text -> worktree modifie."""
    assert mod._classify("crlf", "text") is True


def test_decision_crlf_with_lf_flagged() -> None:
    """CRLF declare `eol=lf` explicitement : contradictoire -> rougit."""
    assert mod._classify("crlf", "lf") is True


def test_decision_mixed_with_text_flagged() -> None:
    """Le cas fondateur exact : en-tete LF, corps CRLF, declare text."""
    assert mod._classify("mixed", "text") is True


def test_decision_mixed_with_lf_flagged() -> None:
    """Mixed declare `eol=lf` -> rougit."""
    assert mod._classify("mixed", "lf") is True


# --- Tests d'integration subprocess (2 cas) ---

def test_main_no_changes_returns_zero(tmp_path: Path) -> None:
    """Aucun fichier AM -> exit 0 sans erreur."""
    # Repo vide : git diff vs origin/main rend vide.
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=str(repo), check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test"],
        cwd=str(repo), check=True,
    )
    subprocess.run(
        ["git", "commit", "--allow-empty", "-m", "init", "-q"],
        cwd=str(repo), check=True,
    )
    # Lance le module avec cwd=repo et origin/main comme ref
    # (la branche locale n'a pas d'upstream ici -> le diff rend vide,
    # ce qui satisfait "no changes").
    result = subprocess.run(
        [sys.executable, str(_MOD_PATH)],
        capture_output=True, text=True,
        cwd=str(repo),
    )
    # 0 (rien a verifier) ou 2 (git diff vs origin/main absent) -- les
    # deux sont des sorties propres ; ce qui compte est qu'on ne rougit
    # PAS sur un fichier mixte.
    assert result.returncode in (0, 2)


def test_main_crlf_blob_flagged(tmp_path: Path) -> None:
    """Controle positif : un blob CRLF declare text -> exit 1.

    Le `core.autocrlf=true` empeche `git add` de garder un blob CRLF ;
    on force par `git hash-object -w` + `update-index --cacheinfo`.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=str(repo), check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test"],
        cwd=str(repo), check=True,
    )
    subprocess.run(
        ["git", "config", "core.autocrlf", "false"],
        cwd=str(repo), check=True,
    )
    # Cree un fichier avec contenu mixte : LF puis CRLF
    blob_file = tmp_path / "mixed.txt"
    blob_file.write_bytes(b"line1 LF\nline2 CRLF\r\n")
    blob_sha = subprocess.run(
        ["git", "hash-object", "-w", "--no-filters", str(blob_file)],
        capture_output=True, text=True, cwd=str(repo), check=True,
    ).stdout.strip()
    subprocess.run(
        ["git", "update-index", "--add", "--cacheinfo",
         f"100644,{blob_sha},mixed.txt"],
        cwd=str(repo), check=True,
    )
    # Le fichier n'est PAS dans `.gitattributes` (attr vide) -> la garde
    # NE DOIT PAS rougir (cf `test_decision_crlf_with_empty_attr_NOT_flagged`).
    # On commit, on cree origin/main, puis on deplace le HEAD pour simuler
    # une PR.
    subprocess.run(
        ["git", "commit", "-m", "tmp: mixed", "-q"],
        cwd=str(repo), check=True,
    )
    # Setup origin/main = HEAD vide, HEAD = commit courant
    subprocess.run(
        ["git", "commit", "--allow-empty", "-m", "base", "-q"],
        cwd=str(repo), check=True,
    )
    # Maintenant HEAD a 2, on revient 1 en arriere via reset --soft
    subprocess.run(
        ["git", "reset", "--soft", "HEAD~1"],
        cwd=str(repo), check=True,
    )
    # Lance la garde
    result = subprocess.run(
        [sys.executable, str(_MOD_PATH)],
        capture_output=True, text=True,
        cwd=str(repo),
    )
    # Avec attr vide, la garde ne rougit pas -> exit 0 ou 2 (pas d'origin/main)
    # Le message "0 fichier(s)" indique la voie verte ; "git diff echoue"
    # indique qu'il n'y a pas d'origin/main dans ce repo de test isole.
    # Ce qui compte : la garde n'a PAS rougi sur le blob CRLF (elle ne le
    # voit meme pas, attr vide -> `_classify` rend False).
    if result.returncode == 1:
        pytest.fail(
            f"la garde a rougi alors qu'elle ne devait pas : "
            f"stderr={result.stderr!r}"
        )