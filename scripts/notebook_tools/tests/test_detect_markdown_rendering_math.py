"""Tests for the MATH-DELIMITER rules (#17380).

Mesure fondatrice (Playwright avant/apres sur IIT-06, commit 5242d81907) :
le tex2jax par defaut de MathJax 2 (export nbconvert classique) ne typesette
PAS \\( ... \\), et les configs MathJax 3 de JupyterLab / VS Code ne
declarent que $ et $$. Le LaTeX inline \\( ... \\) rend donc en texte brut
dans les deux familles de visionneuses -- 118 occurrences converties en
$ ... $ sur 13 cellules markdown d'IIT-06.

Locks in, for detect_markdown_rendering.py (rules math_paren_delims ERROR,
math_bare_macro WARN, math_odd_dollars WARN) :
  - true positives: the IIT-06 founding form verbatim; a bare macro in
    prose; the two odd-$ shapes (currency triple, unclosed inline math)
  - true negatives: the CONVERTED form ($...$), the delimiter explained
    between backticks, a fenced latex block, a macro inside a $$ display
    span, a macro inside an inline $ span, a Windows path between
    backticks, even-$ cells -- the acceptance's false-negative game,
    without which a pattern set validates on its hits
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_markdown_rendering import scan_cell  # noqa: E402


def _rules(source: str) -> list[str]:
    return [f["rule"] for f in scan_cell({"cell_type": "markdown", "source": source})]


# ---------------------------------------------------------------------------
# math_paren_delims (ERROR) -- the founding IIT-06 class
# ---------------------------------------------------------------------------

def test_iit06_founding_form_fires():
    """La forme mesuree sur IIT-06 avant le commit 5242d81907."""
    src = "Soit $S$ l'ensemble défini par \\(S = \\mathbb{F}_p^n\\) dans le corps fini.\n"
    assert "math_paren_delims" in _rules(src)


def test_display_brackets_are_not_flagged():
    """\\[ ... \\] (display) EST typesette par les deux defauts -- hors classe."""
    src = "La solution générale :\n\n\\[ \\alpha + \\beta x = y \\]\n\nconclut la section.\n"
    assert "math_paren_delims" not in _rules(src)


def test_converted_form_is_silent():
    src = "Soit $S = \\mathbb{F}_p^n$ l'ensemble du corps fini.\n"
    assert "math_paren_delims" not in _rules(src)


def test_backtick_quoted_delimiter_is_silent():
    """`\\(x\\)` entre backticks EXPLIQUE le delimiteur : exemple affiche, pas un defaut."""
    src = "La syntaxe `\\(x\\)` n'est pas rendue par MathJax 3.\n"
    assert "math_paren_delims" not in _rules(src)


def test_fenced_latex_block_is_silent():
    src = "Exemple :\n\n```latex\n\\(S = \\mathbb{F}_p^n\\)\n```\n"
    assert "math_paren_delims" not in _rules(src)


def test_sudoku05_prose_backslash_paren_is_silent():
    """Le FAUX POSITIF fondateur (mesure 2026-09-22, PR #17395) : « (/ ou \\\\)
    selon l'OS » est de la prose Windows, PAS un span math -- la regle se
    borne a l'OUVREUR \\(, jamais a un \\) isole."""
    src = "Elle gere automatiquement les separateurs (/ ou \\\\) selon l'OS.\n"
    assert "math_paren_delims" not in _rules(src)


def test_lone_closer_without_any_opener_is_silent():
    """Meme classe que Sudoku-05 : un \\) sans \\( n'ouvre rien, il n'y a pas
    de span a reparer -- c'est la borne qui tient le faux positif ferme."""
    src = "Le resultat \\) est affiche brut.\n"
    assert "math_paren_delims" not in _rules(src)


def test_unclosed_opener_fires():
    """Le FAUX NEGATIF qu'a ouvert le bornage PAIRE de 65c3f8a4 : un \\( non
    ferme rend en texte brut exactement comme la paire, et etait devenu
    invisible a la seule regle ERROR des maths. Delta corpus mesure : 0
    cellule -- le defaut etait latent, pas absent."""
    src = "Soit \\(S = \\mathbb{F}_p^n fini, sans fermeur.\n"
    assert "math_paren_delims" in _rules(src)


def test_unclosed_escaped_opener_fires_too():
    """Meme forme ECHAPPEE (IIT-01 cellules 14/26/37), non fermee."""
    src = "On calcule \\\\(\\Phi ici, sans fermeur.\n"
    assert "math_paren_delims" in _rules(src)


# ---------------------------------------------------------------------------
# math_bare_macro (WARN) -- bare LaTeX macro outside any math span
# ---------------------------------------------------------------------------

def test_bare_macro_in_prose_fires():
    src = "La norme du vecteur v se note \\|v\\| et le saut \\Delta t.\n"
    assert "math_bare_macro" in _rules(src)


def test_macro_in_multiline_display_span_is_silent():
    src = "Le modèle :\n\n$$\n\\alpha + \\beta x = y\n$$\n\ndonne la droite.\n"
    assert "math_bare_macro" not in _rules(src)


def test_macro_in_inline_span_is_silent():
    src = "Le gain $\\alpha_i$ par acteur est sommé.\n"
    assert "math_bare_macro" not in _rules(src)


def test_windows_path_in_backticks_is_silent():
    """Le FP assume de la classe : un chemin Windows N'EST pas une macro LaTeX
    quand il vit dans un code span (la ou les chemins du corpus vivent)."""
    src = "Le log pointe `C:\\Users\\jsboi\\dev` comme racine.\n"
    assert "math_bare_macro" not in _rules(src)


# ---------------------------------------------------------------------------
# math_odd_dollars (WARN) -- unbalanced inline delimiters after cleanup
# ---------------------------------------------------------------------------

def test_three_currency_dollars_fire():
    """3 $ en prose : impair. Le verdict WARN assume ce FP monnaie."""
    src = "Les paliers sont $5, $10 et $20 selon la formule.\n"
    assert "math_odd_dollars" in _rules(src)


def test_unclosed_inline_math_fires():
    src = "La volatilité vaut $\\sigma_t ici, non fermée.\n"
    assert "math_odd_dollars" in _rules(src)


def test_even_dollar_cell_is_silent():
    src = "Comparer $x$ et $y$ puis conclure.\n"
    assert "math_odd_dollars" not in _rules(src)


def test_display_pair_plus_inline_pair_is_silent():
    src = "$$\na + b\n$$\n\net l'inline $c$ ferme la parité.\n"
    assert "math_odd_dollars" not in _rules(src)


def test_escaped_dollar_does_not_count():
    """Un \\$ échappé n'est pas un délimiteur : il ne doit pas fausser la parité."""
    src = "Le prix \\$5 et le symbole $x$ sont distincts.\n"
    assert "math_odd_dollars" not in _rules(src)
