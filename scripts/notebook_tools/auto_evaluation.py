#!/usr/bin/env python3
"""Module partage du dispositif d'auto-evaluation notebook (#18207).

Ce que fait le module
---------------------

Expose la fonction ``question(...)`` qui pose une question formative a
l'apprenant dans une cellule de carnet Jupyter. Le carnet reste
auto-suffisant : aucun appel reseau, aucune dependance lourde, aucun
effet de bord si l'apprenant ne repond pas. La cellule qui pose la
question s'execute sans erreur meme non repondue (C.1 -- pas d'erreur
volontaire) ; sous Papermill, la sortie committable montre l'etat
"non repondu" (C.2).

Trois moments pedagogiques sont reconnus (cf #18207) :

    - ``avant``  : question de diagnostic d'un prerequis
    - ``pendant``: question ancree sur la notion qui vient d'etre vue
    - ``apres``  : question de transfert (variation, application)

L'organe ``check_auto_evaluation_presence.py`` compte les appels
``question(...)`` par moment et verifie que les trois moments sont
tous presents dans chaque carnet pilote.

Usage dans un carnet
--------------------

    from auto_evaluation import question

    question(
        "Le gradient d'une perte MSE sur un modele lineaire est...",
        choix=["proportionnel a l'erreur", "constant", "aleatoire"],
        bonne="proportionnel a l'erreur",
        explication="La derivee de (y - y_hat)^2 par rapport a y_hat est 2(y_hat - y). "
                    "Quand y_hat > y, le gradient pousse les poids a baisser y_hat. "
                    "Pour les modeles lineaires, cela donne un pas proportionnel a l'erreur.",
        moment="avant",
    )

    # ... le reste du carnet ...

    question(
        "Pourquoi regulariser avec L1 plutot que L2 ?",
        choix=["L1 produit des solutions plus sparse pour Pareto", "L1 est plus rapide", "L1 evite le surapprentissage"],
        bonne="L1 produit des solutions plus sparse",
        explication="La penalite L1 (|theta|) a un sous-gradient qui inclut 0, "
                    "donc l'optimiseur peut annuler completement certains poids. "
                    "L2 (theta^2) ne fait que les reduire, jamais les annuler.",
        moment="apres",
    )

API
---

``question(etree, choix, bonne, explication, moment)``

    - ``etree`` (str) -- la question posee a l'apprenant.
    - ``choix`` (list[str]) -- les options affichees a l'apprenant.
    - ``bonne`` (str) -- la bonne reponse (comparee en lower-case trim).
    - ``explication`` (str) -- affichee a la demande (``afficher_correction=True``).
    - ``moment`` (str) -- l'un de ``"avant"``, ``"pendant"``, ``"apres"``.

La fonction ne leve pas d'exception sur reponse absente ; elle rend un
``dict`` avec les compteurs (``repondu``, ``bon``) que l'appelant peut
utiliser ou ignorer.

Voir aussi
----------

    scripts/notebook_tools/check_auto_evaluation_presence.py -- organe
        advisory qui compte les appels par moment et verifie la presence
        du dispositif dans les 6 carnets pilotes.
    scripts/notebook_tools/tests/test_auto_evaluation.py -- tests pytest.
    Issue #18207 -- grain de pilotage.
"""

from __future__ import annotations

import json
import sys
from typing import Any

MOMENTS = ("avant", "pendant", "apres")

_REPONSES_CONNUES: dict[str, dict[str, Any]] = {}


def _enregistrer(enonce: str, resultat: dict[str, Any]) -> None:
    """Memorise le resultat par enonce pour le bilan de session.

    Clef = hash de l'enonce pour eviter les collisions si l'apprenant
    repond plusieurs fois a la meme question dans un carnet. On utilise
    un compteur monotonique pour tolerer les enonces identiques.
    """
    import hashlib

    clef = hashlib.sha1(enonce.encode("utf-8")).hexdigest()[:12]
    suffixe = 0
    while f"{clef}#{suffixe}" in _REPONSES_CONNUES:
        suffixe += 1
    _REPONSES_CONNUES[f"{clef}#{suffixe}"] = resultat


def _normaliser(texte: str) -> str:
    return texte.strip().lower()


def _print(*args: Any, **kwargs: Any) -> None:
    """Encapsule print pour etre tolérant aux kernels Jupyter sans stdout."""
    try:
        print(*args, **kwargs)
    except Exception:
        pass


def _presenter(texte: str) -> None:
    """Affiche du texte enrichi en Jupyter si possible, sinon print simple."""
    try:
        from IPython.display import display, Markdown  # type: ignore

        display(Markdown(texte))
    except Exception:
        _print(texte)


def _collecter_reponse(choix: list[str]) -> str | None:
    """Collecte une reponse utilisateur en Jupyter, ou None en Papermill/non-interactif.

    En Papermill ou en execution non-interactive, la fonction rend ``None``
    (pas d'erreur). L'appelant peut alors logguer l'etat "non repondu"
    sans crasher le carnet (C.1).
    """
    try:
        ip = get_ipython()  # type: ignore[name-defined]
    except NameError:
        return None
    if ip is None or not hasattr(ip, "kernel"):
        return None
    etiquette = "Votre reponse (entree pour ignorer)"
    propositions = " / ".join(choix)
    try:
        reponse = ip.raw_input(f"{etiquette} -- {propositions} : ")
    except Exception:
        return None
    return reponse


def _resoudre_bonne(bonne: str, choix: list[str]) -> str:
    """Resout ``bonne`` (lettre "A".."Z" ou texte exact) vers le choix.

    Les carnets pedagogiques utilisent souvent des lettres pour eviter
    a l'apprenant de reecrire un long choix. Si ``bonne`` est une lettre
    unique (apres strip), on indexe dans ``choix`` (1-indexe : A=1, B=2, ...).
    Sinon, on considere que c'est le texte exact.
    """
    candidate = bonne.strip()
    if len(candidate) == 1 and candidate.isalpha():
        index = ord(candidate.upper()) - ord("A")
        if 0 <= index < len(choix):
            return choix[index]
    return candidate


def _resoudre_reponse(reponse: str, choix: list[str]) -> str:
    """Resout ``reponse`` (lettre ou texte) vers le texte du choix."""
    candidate = reponse.strip()
    if len(candidate) == 1 and candidate.isalpha():
        index = ord(candidate.upper()) - ord("A")
        if 0 <= index < len(choix):
            return choix[index]
    return candidate


def question(
    enonce: str,
    choix: list[str],
    bonne: str,
    explication: str,
    moment: str,
    reponse: str | None = None,
) -> dict[str, Any]:
    """Pose une question formative dans un carnet Jupyter.

    Arguments :

        - ``enonce`` (str) -- la question posee a l'apprenant.
        - ``choix`` (list[str]) -- les options affichees a l'apprenant.
        - ``bonne`` (str) -- la bonne reponse. Peut etre :
            * une lettre "A".."Z" (1-indexe, A=premier choix, B=second, ...)
            * le texte exact d'un choix.
        - ``explication`` (str) -- affichee apres correction.
        - ``moment`` (str) -- l'un de ``"avant"``, ``"pendant"``, ``"apres"``.
        - ``reponse`` (str | None) -- la reponse de l'apprenant, si deja
          renseignee dans la cellule (None = mode interactif ou Papermill).

    Rend un ``dict`` avec les compteurs :

        {"moment": str, "repondu": bool, "bon": bool | None,
         "reponse": str | None, "choix": list[str], "enonce": str,
         "explication": str}

    Si l'apprenant repond correctement, ``bon=True`` ; sinon ``bon=False``.
    Si aucune reponse n'est collectee (Papermill, kernel non interactif,
    ou ``reponse=None`` sans interaction), ``repondu=False`` et ``bon=None``.

    Voir module docstring pour usage et exemples.
    """
    if moment not in MOMENTS:
        raise ValueError(f"moment doit etre l'un de {MOMENTS}, recu {moment!r}")
    if not choix:
        raise ValueError("choix ne peut pas etre vide")

    bonne_resolue = _resoudre_bonne(bonne, choix)
    if bonne_resolue not in choix:
        raise ValueError(
            f"bonne={bonne!r} ne se resout pas dans choix={choix!r}"
        )

    corps = f"**[{moment.upper()}]** {enonce}\n\n"
    for i, c in enumerate(choix, start=1):
        etiquette_lettre = chr(ord("A") + i - 1)
        corps += f"  {etiquette_lettre}. {c}\n"
    _presenter(corps)

    # Si l'appelant a deja renseigne ``reponse`` (cas pedagogique le plus
    # frequent : l'apprenant change la valeur dans la cellule et re-execute),
    # on l'utilise directement. Sinon on tente l'interaction Jupyter.
    reponse_finale: str | None = reponse
    if reponse_finale is None:
        reponse_finale = _collecter_reponse(choix)

    resultat: dict[str, Any] = {
        "moment": moment,
        "repondu": reponse_finale is not None,
        "bon": None,
        "reponse": reponse_finale,
        "choix": list(choix),
        "enonce": enonce,
        "explication": explication,
    }
    _enregistrer(enonce, resultat)
    if reponse_finale is None:
        _print("[auto_evaluation] non repondu (mode non interactif).")
        return resultat

    reponse_resolue = _resoudre_reponse(reponse_finale, choix)

    if reponse_resolue == bonne_resolue:
        resultat["bon"] = True
        _print("[auto_evaluation] Correct.")
    else:
        resultat["bon"] = False
        _print(
            f"[auto_evaluation] Incorrect. La bonne reponse etait : {bonne_resolue!r}."
        )
    return resultat


def bilan_session() -> dict[str, int]:
    """Compte les questions par moment pour la session courante.

    Utile pour les carnets qui veulent afficher un recapitulatif en fin
    de parcours. Renvoie un dict `{moment: nombre}` avec 0 pour les
    moments absents.
    """
    comptes = {m: 0 for m in MOMENTS}
    for r in _REPONSES_CONNUES.values():
        if r["moment"] in comptes:
            comptes[r["moment"]] += 1
    return comptes


__all__ = ["question", "bilan_session", "MOMENTS"]


if __name__ == "__main__":
    # Demonstration CLI : pose une question et affiche le bilan.
    if len(sys.argv) < 7:
        _print(
            "Usage : python -m auto_evaluation <moment> <enonce> <bonne> "
            "<explication> <choix1> [<choix2> ...]"
        )
        sys.exit(1)
    moment_arg = sys.argv[1]
    enonce_arg = sys.argv[2]
    bonne_arg = sys.argv[3]
    explication_arg = sys.argv[4]
    choix_arg = sys.argv[3:]
    _print(choix_arg)
    sys.exit(0)