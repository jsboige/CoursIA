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

# --- session (port des ajouts #18885, voir #19027) -----------------------------

# Mémoire des résultats de la session, indexée par énoncé. Le bilan de session
# parcourt cette structure pour rendre le décompte (réussies, manquées, etc.).
# Tolère les énoncés identiques (collision de hash) par suffixe monotonique.
import hashlib as _hashlib  # noqa: E402

_REPONSES_CONNUES: dict[str, dict[str, object]] = {}


def _enregistrer(enonce: str, resultat: dict[str, object]) -> None:
    """Mémorise le résultat par énoncé pour le bilan de session."""
    clef = _hashlib.sha1(enonce.encode("utf-8")).hexdigest()[:12]
    suffixe = 0
    while f"{clef}#{suffixe}" in _REPONSES_CONNUES:
        suffixe += 1
    _REPONSES_CONNUES[f"{clef}#{suffixe}"] = dict(resultat)


def _normaliser(texte: str) -> str:
    """Normalise un texte pour la résolution par valeur exacte (lower + strip)."""
    return texte.strip().lower()


def _resoudre_bonne(bonne: str, choix: list[str]) -> str:
    """Accepte la bonne réponse par son texte exact ou par sa lettre.

    Porte la rétrocompatibilité : un appelant qui passe `bonne="B"` continue
    de fonctionner ; un appelant qui passe le texte complet du bon choix aussi.
    Lève `ValueError` si ni l'une ni l'autre ne résout.
    """
    lettres = _lettres(len(choix))
    if bonne in lettres:
        return bonne
    cible = _normaliser(bonne)
    for lettre, option in zip(lettres, choix):
        if _normaliser(option) == cible:
            return lettre
    raise ValueError(
        f"bonne : {bonne!r} (attendu : une lettre parmi {''.join(lettres)}, "
        f"ou le texte exact d'un choix)"
    )


def _resoudre_reponse(reponse: str | None, choix: list[str]) -> str | None:
    """Symétrique de ``_resoudre_bonne`` pour la réponse de l'apprenant.

    Rend ``None`` si la réponse est absente (l'apprenant n'a pas répondu),
    lève ``ValueError`` si elle est donnée mais ne résout ni par lettre ni
    par texte.
    """
    if reponse is None:
        return None
    lettres = _lettres(len(choix))
    if reponse in lettres:
        return reponse
    cible = _normaliser(reponse)
    for lettre, option in zip(lettres, choix):
        if _normaliser(option) == cible:
            return lettre
    raise ValueError(
        f"reponse : {reponse!r} (attendu : None, une lettre parmi "
        f"{''.join(lettres)}, ou le texte exact d'un choix)"
    )


def _collecter_reponse(choix: list[str]) -> str | None:
    """Collecte interactive de la réponse.

    Rend ``None`` silencieusement sous Papermill (ou si stdin n'est pas
    interactif) pour respecter C.1 : pas d'erreur volontaire, la cellule
    continue.
    """
    try:
        saisie = input(f"Votre réponse (lettre ou texte) : ")
    except (EOFError, KeyboardInterrupt):
        return None
    if not saisie:
        return None
    try:
        return _resoudre_reponse(saisie, choix)
    except ValueError:
        return None


def bilan_session() -> dict[str, int]:
    """Rend le décompte de la session courante.

    Sortie :
        - ``posees`` : nombre de questions enregistrées ;
        - ``repondues`` : nombre avec réponse (lettre ou texte) ;
        - ``bonnes`` : nombre de réponses justes ;
        - ``manquees`` : nombre de questions sans réponse ;
        - ``fausses`` : nombre de réponses fausses.

    L'appelant peut utiliser le rendu ou l'ignorer.
    """
    decompte = {"posees": 0, "repondues": 0, "bonnes": 0, "manquees": 0, "fausses": 0}
    for resultat in _REPONSES_CONNUES.values():
        decompte["posees"] += 1
        reponse = resultat.get("reponse")
        verdict = resultat.get("verdict")
        if reponse is None:
            decompte["manquees"] += 1
        else:
            decompte["repondues"] += 1
            if verdict is True:
                decompte["bonnes"] += 1
            elif verdict is False:
                decompte["fausses"] += 1
    return decompte


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
    bonne_lettre = _resoudre_bonne(bonne, choix)
    reponse_lettre = _resoudre_reponse(reponse, choix)

    lignes = [f"{_TITRES[moment]} — {texte}", ""]
    lignes += [f"  {lettre}. {option}" for lettre, option in zip(lettres, choix)]
    lignes.append("")

    if reponse_lettre is None:
        verdict: bool | None = None
        lignes.append(_INVITE)
    else:
        verdict = reponse_lettre == bonne_lettre
        lignes.append(f"Votre réponse : {reponse}")
        lignes.append("Juste." if verdict else f"Incorrect — la bonne réponse est {bonne}.")
        lignes.append(f"Pourquoi : {explication}")

    print("\n".join(lignes))

    _enregistrer(
        texte,
        {
            "moment": moment,
            "reponse": reponse,
            "verdict": verdict,
            "bonne": bonne_lettre,
        },
    )
    return verdict