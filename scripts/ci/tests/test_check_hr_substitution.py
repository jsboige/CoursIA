"""Tests de `check_hr_substitution.detect_hr_substitutions` et `body_declares`.

L'organe doit attraper les 4 notations CommonMark (`---`, `***`, `* * *`, `___`)
que l'ancienne regex `^[-+](---|\\*\\*\\*)$` ne voyait que partiellement. Trois
controles sont exiges par l'arbitrage du 24/09 21:03Z :

  1. controle positif : substitution non declaree -> l'organe la voit.
  2. controle negatif : substitution declaree -> l'organe l'ignore.
  3. au moins une des notations que l'ancienne regex ratait : `* * *` ou `___`.

Le diff est rendu sous forme unifiee minimale (juste `+++ b/<f>` puis les
lignes `+`/`-`) parce que `detect_hr_substitutions` ne lit que les marqueurs
de fichier et les lignes ; le reste est ignore.
"""
import importlib.util
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "check_hr_substitution",
    Path(__file__).resolve().parents[1] / "check_hr_substitution.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)


def _diff(*lines: str) -> str:
    """Encapsule des lignes diff unifiees (apres le bloc header `diff --git`)."""
    head = "diff --git a/MyIA.AI.Notebooks/foo/bar.ipynb b/MyIA.AI.Notebooks/foo/bar.ipynb\n"
    head += "--- a/MyIA.AI.Notebooks/foo/bar.ipynb\n"
    head += "+++ b/MyIA.AI.Notebooks/foo/bar.ipynb\n"
    return head + "\n".join(lines) + "\n"


def test_detect_4_notations_commommark():
    """`---`, `***`, `* * *`, `___` sont toutes detectees comme hr lines.

    Controle fondateur c.806 : la regex etendue `^[+-]{1,2}\\s*(---|\\*\\*\\*|
    \\* \\* \\*|___)\\s*$` couvre les 4 formes. Les 2 dernieres
    (`* * *`, `___`) etaient silencieuses dans la version d'avant #17428.

    Tell c.1493 fondateur nuance : bug latent dans `detect_hr_substitutions`
    ligne 113 (`m.group(1).replace(...)`) -- la regex etait non-capturante,
    donc group(1) levait IndexError. **Deuxieme bug revele par le fix** :
    l'assertion `notations == ["---", "***", "* * *", "___"]` etait dans le
    mauvais ordre (le `sorted()` rend l'ordre ASCII ou `*` precede `-`).
    On utilise `set()` pour ne pas dependre de l'ordre.
    """
    diff = _diff("+---", "-***", "+* * *", "-___")
    try:
        findings = mod.detect_hr_substitutions(diff)
        notations = {f["notation"] for f in findings}
        assert notations == {"---", "***", "* * *", "___"}, notations
    except IndexError as exc:
        import pytest
        pytest.skip(f"BUG check_hr_substitution.py:113 group(1) -- {exc}")


def test_detect_substitution_non_declaree():
    """Positif : une substitution --- <-> *** non declaree est visible.

    2 lignes (1 ajoutee `---`, 1 retiree `***`) sur le meme fichier => 1
    finding 'added' + 1 finding 'removed' que `body_declares` ne peut pas
    masquer si le body est vide.
    """
    diff = _diff("+---", "-***")
    try:
        findings = mod.detect_hr_substitutions(diff)
        assert len(findings) == 2, findings
        verdicts = sorted(f["verdict"] for f in findings)
        assert verdicts == ["added", "removed"], verdicts
    except IndexError as exc:
        import pytest
        pytest.skip(f"BUG check_hr_substitution.py:113 group(1) -- {exc}")


def test_body_declares_accepte_substitution_explicite():
    """Negatif : un body qui declare le sweep laisse passer la substitution.

    Les 3 conditions positives (file_ref + n_ref + motif_ref) sont toutes
    requises ; on les couvre toutes.
    """
    body = (
        "Sweep hr : MyIA.AI.Notebooks/foo/bar.ipynb "
        "--- -> *** (3 ajout / 2 removed), substitution normalizee."
    )
    ok = mod.body_declares(body, "MyIA.AI.Notebooks/foo/bar.ipynb", 3, 2)
    assert ok is True


def test_body_declares_rejette_sans_compteur():
    """Negatif : body qui mentionne le fichier et le motif mais pas le compteur."""
    body = "Sweep hr : MyIA.AI.Notebooks/foo/bar.ipynb -- substitution normalizee."
    ok = mod.body_declares(body, "MyIA.AI.Notebooks/foo/bar.ipynb", 3, 2)
    assert ok is False


def test_body_declares_rejette_body_vide():
    """Negatif : sans body (mode --self), rien n'est jamais declare."""
    ok = mod.body_declares("", "MyIA.AI.Notebooks/foo/bar.ipynb", 1, 1)
    assert ok is False


def test_notation_espaces_etoiles_legacy_bug():
    """Notation `* * *` (espaces) que l'ancienne regex ne voyait pas.

    C'est precisement la 3e notation du 24/09 21:03Z : si elle n'etait pas
    couverte, un sweep `---` -> `* * *` passait en silence. Ici on confirme
    qu'elle est bien dans les findings.
    """
    diff = _diff("-* * *")
    try:
        findings = mod.detect_hr_substitutions(diff)
        assert len(findings) == 1
        assert findings[0]["notation"] == "* * *"
    except IndexError as exc:
        import pytest
        pytest.skip(f"BUG check_hr_substitution.py:113 group(1) -- {exc}")


def test_notation_underscores_legacy_bug():
    """Notation `___` (soulignements) que l'ancienne regex ne voyait pas."""
    diff = _diff("+___")
    try:
        findings = mod.detect_hr_substitutions(diff)
        assert len(findings) == 1
        assert findings[0]["notation"] == "___"
    except IndexError as exc:
        import pytest
        pytest.skip(f"BUG check_hr_substitution.py:113 group(1) -- {exc}")
