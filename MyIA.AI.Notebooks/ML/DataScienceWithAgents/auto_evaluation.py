"""Dispositif d'auto-évaluation formatif des carnets de la série (issue #18207).

Trois moments dans un carnet :

- **avant** : un diagnostic de prérequis, avant de commencer ;
- **pendant** : une à trois vérifications, juste après la notion qu'elles testent ;
- **après** : une à deux questions de transfert, en fin de parcours.

Le dispositif est **formatif** : aucune note, aucun score, rien n'est stocké.
La cellule qui pose la question s'exécute sans erreur même quand l'apprenant
n'a pas répondu (règle C.1), et la correction ne s'affiche **que** si une
réponse est fournie — la sortie committée montre donc l'état « non répondu »
(règle C.2).

Usage dans un carnet :

    from auto_evaluation import question

    question(
        "Pourquoi séparer les données en train et test ?",
        choix=[
            "Pour accélérer l'entraînement",
            "Pour mesurer la performance sur des données jamais vues à l'entraînement",
            "Pour équilibrer les classes",
        ],
        bonne="B",
        explication="Le test simule des données que le modèle n'a jamais vues...",
        reponse=None,        # remplacez None par la lettre de votre choix, puis ré-exécutez
        moment="avant",
    )

Les lettres des choix sont posées par ce module : l'auteur du carnet passe les
textes dans l'ordre, et désigne la bonne réponse par sa lettre.
"""

from __future__ import annotations

MOMENTS = ("avant", "pendant", "apres")

_TITRES = {
    "avant": "Diagnostic de prérequis",
    "pendant": "Vérification",
    "apres": "Transfert",
}

_LETTRES = "ABCDEFGH"

_INVITE = (
    "Réponse non donnée. Remplacez `reponse=None` par la lettre de votre choix "
    "dans cette cellule, puis ré-exécutez-la pour afficher la correction."
)


def _lettres(n: int) -> list[str]:
    return list(_LETTRES[:n])


def question(
    texte: str,
    choix: list[str],
    bonne: str,
    explication: str,
    reponse: str | None = None,
    moment: str = "pendant",
) -> bool | None:
    """Affiche une question, puis la correction si une réponse est fournie.

    Retourne ``True`` si la réponse donnée est juste, ``False`` si elle est
    fausse, ``None`` si l'apprenant n'a pas répondu.

    Lève ``ValueError`` sur une entrée mal formée : c'est une erreur d'auteur du
    carnet, pas une réponse d'apprenant, et elle doit être vue à l'exécution.
    """
    if moment not in MOMENTS:
        raise ValueError(f"moment inconnu : {moment!r} (attendu : {', '.join(MOMENTS)})")
    if not 2 <= len(choix) <= len(_LETTRES):
        raise ValueError(f"choix : {len(choix)} propositions (attendu : 2 à {len(_LETTRES)})")
    if not texte.strip():
        raise ValueError("texte : la question est vide")
    if not explication.strip():
        raise ValueError("explication : la correction doit dire pourquoi")
    lettres = _lettres(len(choix))
    if bonne not in lettres:
        raise ValueError(f"bonne : {bonne!r} (attendu : une lettre parmi {''.join(lettres)})")
    if reponse is not None and reponse not in lettres:
        raise ValueError(
            f"reponse : {reponse!r} (attendu : None, ou une lettre parmi {''.join(lettres)})"
        )

    lignes = [f"{_TITRES[moment]} — {texte}", ""]
    lignes += [f"  {lettre}. {option}" for lettre, option in zip(lettres, choix)]
    lignes.append("")

    if reponse is None:
        verdict: bool | None = None
        lignes.append(_INVITE)
    else:
        verdict = reponse == bonne
        lignes.append(f"Votre réponse : {reponse}")
        lignes.append("Juste." if verdict else f"Incorrect — la bonne réponse est {bonne}.")
        lignes.append(f"Pourquoi : {explication}")

    print("\n".join(lignes))
    return verdict