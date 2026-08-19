"""Garde de classe : une apostrophe echappee par backslash dans une expression
GitHub Actions casse le workflow AU DEMARRAGE -- zero job cree, aucun log.

Incident fondateur (2026-08-19) : `render-volume-delta-advisory.yml` a echoue
**100 fois sur 100** depuis sa creation (15:24:30Z), sans jamais reussir une
seule fois. Le YAML etait valide (`yaml.safe_load` passait), le fichier etait
relu par des humains, et le workflow etant *advisory* son rouge permanent a ete
lu comme du bruit non-bloquant. L'organe de #11656 -- celui qui doit detecter
la destruction de volume de rendu dans les notebooks -- n'a donc jamais tourne.

La cause : dans une expression `${{ ... }}`, GitHub Actions n'echappe PAS
l'apostrophe par un backslash. On la **double** (`''`), comme en SQL. Un
`s\'abstient` a l'interieur d'une chaine d'expression rend l'expression
inanalysable, et GitHub abandonne le run avant de creer le moindre job.

Ce que ce test ajoute, qu'aucune relecture ne donne : le defaut est **muet**
par construction (`total_count: 0` jobs, `--log` vide, `--log-failed` vide).
« Rien trouve » et « pas regarde » y rendent la meme chose -- exactement la
famille de defauts que le depot corrige par un organe plutot que par de la
vigilance.
"""

import glob
import io
import os
import re

import pytest

BACKSLASH = chr(92)

# Une expression GHA, non-gourmande, multi-lignes (les blocs `with: body: |`
# en contiennent regulierement qui s'etalent sur plusieurs lignes).
_EXPRESSION = re.compile(r"\$\{\{.*?\}\}", re.S)
_ESCAPED_QUOTE = re.compile(re.escape(BACKSLASH) + r"'")

_WORKFLOW_DIR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    ".github",
    "workflows",
)


def _workflow_files():
    pats = ("*.yml", "*.yaml")
    out = []
    for p in pats:
        out.extend(glob.glob(os.path.join(_WORKFLOW_DIR, p)))
    return sorted(out)


def _offenders(text):
    """Retourne les expressions du texte qui portent un backslash-apostrophe."""
    return [m.group(0) for m in _EXPRESSION.finditer(text) if _ESCAPED_QUOTE.search(m.group(0))]


def test_positive_control_detects_the_known_bad_form():
    """Le controle positif du detecteur, dans la meme invocation que son usage.

    Sans lui, un motif casse (backslash mange par un transport heredoc, regex
    mal echappee) rendrait 0 offender sur tout le depot -- un vert qui ne
    mesure rien, indiscernable d'un vert qui mesure tout.
    """
    bad = "${{ steps.x.outputs.y == '0' && 'il s" + BACKSLASH + "'abstient' || 'ok' }}"
    assert _offenders(bad), "le detecteur ne voit pas la forme fautive connue"

    good = "${{ steps.x.outputs.y == '0' && 'il s''abstient' || 'ok' }}"
    assert not _offenders(good), "le detecteur accuse la forme correcte (doublement)"


def test_no_backslash_escaped_quote_in_any_workflow_expression():
    found = []
    for path in _workflow_files():
        text = io.open(path, encoding="utf-8").read()
        for expr in _offenders(text):
            line = text[: text.index(expr)].count("\n") + 1
            found.append(f"{os.path.basename(path)}:{line}: {expr[:120]}")

    assert not found, (
        "apostrophe echappee par backslash dans une expression GitHub Actions -- "
        "le workflow echouera AU DEMARRAGE (0 job, aucun log). Doubler "
        "l'apostrophe (`''`) au lieu de la prefixer d'un backslash :\n  "
        + "\n  ".join(found)
    )


def test_workflow_dir_is_non_empty():
    """Un scan qui ne trouve aucun fichier rendrait « aucun defaut » a tort."""
    files = _workflow_files()
    assert len(files) > 20, f"repertoire de workflows introuvable ou vide : {_WORKFLOW_DIR} ({len(files)})"


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-v"]))
