"""Les diagnostics du picker ne corrompent plus sa sortie JSON (#24823).

Incident mesure le 2026-11-11 : ``belt.json`` produit par ``--belt --json``
commencait par une ligne de diagnostic et ``belt_queues.py board`` le refusait
avec ``JSONDecodeError``. La regression de #25411 est fermee ici pour toute la
classe des notes de fonctionnement entre parentheses.
"""

import ast
from pathlib import Path


PICKER = Path(__file__).resolve().parents[1] / "pick_idle_grain.py"

# Ces deux appels sont des fragments d'un rapport texte multiligne, pas des
# notes de fonctionnement independantes. Leur premier fragment ne commence pas
# par une parenthese : les diriger seuls vers stderr couperait le rapport lu
# par la lane, sans proteger aucun flux JSON.
#
# Identite par CONTENU, jamais par numero de ligne : tout merge qui touche le
# picker decale les fragments et perime une liste epinglee (mesure 2026-11-12 :
# #25906 a decale les deux fragments de 41 lignes et rendu ce garde rouge sur
# main, bloquant ensuite toute PR qui touche scripts/pick_idle_grain.py).
TEXT_REPORT_CONTINUATION_PREFIXES = (
    "(conseil sur donnee non mesuree)",
    "(aucun grain de contenu dans sa capability",
)


def _first_text(argument: ast.expr) -> str | None:
    """Premier fragment litteral de l'argument, ou ``None`` s'il n'en a pas."""
    if isinstance(argument, ast.Constant) and isinstance(argument.value, str):
        return argument.value
    if not isinstance(argument, ast.JoinedStr):
        return None
    for part in argument.values:
        if isinstance(part, ast.Constant) and isinstance(part.value, str):
            return part.value
        if isinstance(part, ast.FormattedValue):
            return None
    return None


def _starts_with_parenthesis(argument: ast.expr) -> bool:
    """Vrai pour une chaine ou une f-string dont le texte commence par ``(``."""
    text = _first_text(argument)
    return text is not None and text.startswith("(")


def test_parenthesized_diagnostics_are_written_to_stderr() -> None:
    """Chaque note ``(...)`` porte ``file=``, sans imposer une valeur precise.

    La forme ``file=`` laisse le test mesurer l'absence de fuite vers stdout
    sans figer un alias d'import. Les continuations de rapport texte sont les
    seules exceptions, documentees ci-dessus par le debut de leur premier
    fragment -- jamais par un numero de ligne, qui se perime au premier merge.
    """
    tree = ast.parse(PICKER.read_text(encoding="utf-8"), filename=str(PICKER))
    offenders = []
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "print"
                and node.args
                and _starts_with_parenthesis(node.args[0])):
            continue
        if any(keyword.arg == "file" for keyword in node.keywords):
            continue
        text = _first_text(node.args[0]) or ""
        if text.startswith(TEXT_REPORT_CONTINUATION_PREFIXES):
            continue
        offenders.append(node.lineno)

    assert not offenders, (
        "Diagnostics sur stdout aux lignes "
        f"{offenders} de scripts/pick_idle_grain.py. Ajouter file=sys.stderr : "
        "un diagnostic sur stdout corrompt la sortie --json consommee par "
        "belt_queues.py (regression #25411, belt.json illisible le 2026-11-11). "
        "Si la ligne est la continuation d'un rapport texte, la documenter "
        "dans TEXT_REPORT_CONTINUATIONS."
    )
