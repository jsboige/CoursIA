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

Ce qu'il ne doit PAS faire (correctif 2026-08-20) : accuser la *prose qui
documente* le defaut. La premiere version scannait le texte brut, donc un
commentaire YAML citant la forme fautive -- precisement la note d'incident
deposee en tete de `degraded-mode-advisory.yml` -- comptait comme occurrence.
Les deux PRs (#11861 le detecteur, #11863 la note) etaient vertes isolement et
rouges combinees : `main` a passe ~1 h 20 rouge sur une jambe portant **zero**
defaut reel, ce qui bloque toute la file. Un gate peut sur-accuser autant que
sous-compter, et sa sur-accusation se paie en PRs qui vieillissent.

Le scan porte donc sur ce que GitHub **rend** : les valeurs de l'arbre YAML.
Les commentaires en sont absents (le parser les jette) ; les blocs `run: |` y
sont presents (ce sont des chaines), donc une expression fautive glissee dans
un commentaire *shell* d'un bloc `run:` reste attrapee -- GitHub rend
l'expression avant que le shell ne voie le `#`, et meurt pareil. Ce dernier
point porte son propre test : un detecteur se recette par ses faux negatifs,
jamais par ses hits.
"""

import glob
import io
import os
import re

import pytest
import yaml

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


def _rendered_strings(doc):
    """Toutes les chaines de l'arbre YAML -- ce que GitHub Actions rendra.

    Les commentaires YAML n'y sont pas (le parser les jette) ; les blocs
    scalaires (`run: |`, `body: |`) y sont, ainsi que les cles.
    """
    out = []
    stack = [doc]
    while stack:
        node = stack.pop()
        if isinstance(node, str):
            out.append(node)
        elif isinstance(node, dict):
            for key, value in node.items():
                stack.append(key)
                stack.append(value)
        elif isinstance(node, (list, tuple)):
            stack.extend(node)
    return out


def _offenders_in_source(text):
    """Offenders d'un source de workflow, commentaires YAML exclus."""
    found = []
    for chunk in _rendered_strings(yaml.safe_load(text)):
        found.extend(_offenders(chunk))
    return found


def _locate(raw, expr):
    """Ligne de `expr` dans `raw`, en sautant les lignes de commentaire YAML."""
    lines = raw.splitlines()
    fallback = 0
    for match in re.finditer(re.escape(expr), raw):
        line = raw[: match.start()].count("\n") + 1
        fallback = fallback or line
        if not lines[line - 1].lstrip().startswith("#"):
            return line
    return fallback


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


def test_bad_form_inside_a_run_block_is_still_caught():
    """Le faux negatif a ne PAS ouvrir en corrigeant la sur-accusation.

    Un bloc `run: |` est une chaine rendue par GitHub : une expression fautive
    posee dans un commentaire *shell* y tue le run exactement pareil, car
    l'expression est rendue avant que le shell ne voie le `#`. Exclure les
    commentaires YAML ne doit pas aveugler le detecteur ici.
    """
    src = (
        "on: push\n"
        "jobs:\n"
        "  j:\n"
        "    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - run: |\n"
        "          # ${{ github.event_name == 'push' && 'il s"
        + BACKSLASH
        + "'abstient' || 'ok' }}\n"
        "          echo hello\n"
    )
    assert _offenders_in_source(src), "un bloc run: est rendu par GitHub : il doit rester scanne"


def test_yaml_comment_quoting_the_bad_form_is_not_an_offender():
    """Regression #11861 x #11863 : la prose qui documente n'est pas le defaut.

    Une note d'incident citant la forme fautive dans un commentaire YAML n'est
    jamais rendue par GitHub. L'accuser rougit `main` et bloque la file entiere
    pour zero defaut reel.
    """
    src = (
        "# Note : `${{ x == '0' && 'il s"
        + BACKSLASH
        + "'abstient' || 'ok' }}` a tue le run.\n"
        "on: push\n"
        "jobs:\n"
        "  j:\n"
        "    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - run: echo ok\n"
    )
    assert _offenders(src), "controle : le texte brut porte la forme, sinon ce test ne prouve rien"
    assert not _offenders_in_source(src), "un commentaire YAML ne doit pas etre accuse"


def test_no_backslash_escaped_quote_in_any_workflow_expression():
    found = []
    for path in _workflow_files():
        text = io.open(path, encoding="utf-8").read()
        try:
            offenders = _offenders_in_source(text)
        except yaml.YAMLError as exc:
            found.append(f"{os.path.basename(path)}: YAML invalide -- {exc}")
            continue
        for expr in offenders:
            found.append(f"{os.path.basename(path)}:{_locate(text, expr)}: {expr[:120]}")

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
