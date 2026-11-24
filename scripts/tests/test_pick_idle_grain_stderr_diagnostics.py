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
# Cles par TEXTE du fragment, pas par numero de ligne. La premiere version
# epinglait {11952, 12253}, exacts au commit 662eb99757 puis perimes par les
# 41 lignes ajoutees en amont par e6a66f1b65 (#25906) : main est reste rouge
# sur toutes les PRs jusqu'a la reparation. Un fragment de phrase ne bouge
# pas quand le fichier bouge.
TEXT_REPORT_CONTINUATIONS = {
    "(conseil sur donnee non mesuree). Les trois gestes generiques",
    "(aucun grain de contenu dans sa capability -- GPU-only, vision-only),",
}


def _literal_text(argument: ast.expr) -> str:
    """Texte d'une chaine litterale ; vide si l'argument n'en est pas une."""
    if isinstance(argument, ast.Constant) and isinstance(argument.value, str):
        return argument.value
    return ""


def _starts_with_parenthesis(argument: ast.expr) -> bool:
    """Vrai pour une chaine ou une f-string dont le texte commence par ``(``."""
    if isinstance(argument, ast.Constant) and isinstance(argument.value, str):
        return argument.value.startswith("(")
    if not isinstance(argument, ast.JoinedStr):
        return False
    for part in argument.values:
        if isinstance(part, ast.Constant) and isinstance(part.value, str):
            return part.value.startswith("(")
        if isinstance(part, ast.FormattedValue):
            return False
    return False


def test_parenthesized_diagnostics_are_written_to_stderr() -> None:
    """Chaque note ``(...)`` porte ``file=``, sans imposer une valeur precise.

    La forme ``file=`` laisse le test mesurer l'absence de fuite vers stdout
    sans figer un alias d'import. Les continuations de rapport texte sont les
    seules exceptions, documentees ci-dessus avec leur ligne de creation.
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
        if _literal_text(node.args[0]) in TEXT_REPORT_CONTINUATIONS:
            continue
        offenders.append(node.lineno)

    assert not offenders, (
        "Diagnostics sur stdout aux lignes "
        f"{offenders} de scripts/pick_idle_grain.py. Ajouter file=sys.stderr : "
        "un diagnostic sur stdout corrompt la sortie --json consommee par "
        "belt_queues.py (regression #25411, belt.json illisible le 2026-11-11). "
        "Si la ligne est la continuation d'un rapport texte, l'ajouter a "
        "TEXT_REPORT_CONTINUATIONS par son texte litteral (jamais par son "
        "numero de ligne : il se decale au premier ajout en amont)."
    )
