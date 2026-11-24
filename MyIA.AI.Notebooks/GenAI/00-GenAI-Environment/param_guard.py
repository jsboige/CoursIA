"""Garde de parametres pour les modeles GenAI.

Probleme (#20682) : les carnets passent des parametres d'echantillonnage ou de
rendu (temperature, top_k, style...) a des modeles qui les refusent (HTTP 400)
ou les ignorent en silence. La demonstration ne demontre alors plus rien, et le
silence de l'appel masque la perte.

Ce module consulte la matrice mesuree ``param_matrix.json`` (meme dossier) et
signale explicitement, a l'ecran, chaque parametre refuse ou ignore par le
modele vise. ``guard_call`` renvoie en plus des parametres filtris des refus,
pour qu'un carnet qui les passerait quand meme ne remonte pas un 400.

La matrice est datee : chaque case porte sa date de mesure et la source de
l'appel qui l'a produite. Elle derive, pas ne se recopie de la documentation.
Voir ``docs/genai/parametres-par-modele.md`` pour la table humaine et la
methode de re-mesure.

Utilisation dans un carnet :

    import sys
    sys.path.insert(0, "../00-GenAI-Environment")
    from param_guard import guard_call

    params = guard_call("gpt-5-mini", {"temperature": 0.0, "max_tokens": 100})
    # [param_guard] gpt-5-mini refuse 'temperature' (mesure 2026-10-26,
    # api.openai.com) -- parametre retire ; voir docs/genai/parametres-par-modele.md
    reponse = client.chat.completions.create(model="gpt-5-mini", **params)
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional

MATRIX_PATH = Path(__file__).resolve().parent / "param_matrix.json"

#: Cles de familles : un modele non mesure herite du comportement de sa famille
#: quand la matrice porte une entree familiale explicite (ex. "gpt-5*").
FAMILY_SUFFIX = "*"

VERDICTS = ("ACCEPTE", "REFUSE", "IGNORE", "NON_CONCLUABLE")


def load_matrix(path: Optional[Path] = None) -> Dict[str, Any]:
    """Charge la matrice mesuree ; dictionnaire vide si absente (garde muette)."""
    target = Path(path) if path else MATRIX_PATH
    if not target.exists():
        return {}
    with open(target, encoding="utf-8") as handle:
        return json.load(handle)


def resolve_model(model: str, matrix: Dict[str, Any]) -> Optional[str]:
    """Resout un identifiant de modele vers une cle de la matrice.

    Ordre : identite exacte, puis slug sans fournisseur (``openai/gpt-5-mini``
    vers ``gpt-5-mini``), puis cle de famille (``gpt-5-nano`` vers ``gpt-5*``).
    Rend ``None`` quand rien n'est mesure : la garde reste muette plutot que
    de deviner un comportement jamais mesure.
    """
    if model in matrix:
        return model
    slug = model.rsplit("/", 1)[-1]
    if slug != model and slug in matrix:
        return slug
    for key in matrix:
        if key.endswith(FAMILY_SUFFIX) and slug.startswith(key[:-1]):
            return key
    return None


def _warning_line(model: str, key: str, param: str, info: Dict[str, Any]) -> str:
    verdict = info.get("verdict", "NON_CONCLUABLE")
    date = info.get("date", "date inconnue")
    source = info.get("source", "source inconnue")
    action = "parametre retire" if verdict == "REFUSE" else "l'appel reussit mais le parametre ne produit aucun effet"
    return (
        f"[param_guard] {model} {verdict.lower()} '{param}' "
        f"(mesure {date}, {source}) -- {action} ; "
        f"voir docs/genai/parametres-par-modele.md"
    )


def check_params(
    model: str,
    params: Dict[str, Any],
    matrix: Optional[Dict[str, Any]] = None,
    echo: bool = True,
) -> List[str]:
    """Signale les parametres refuses ou ignores par ``model``.

    Renvoie la liste des lignes d'avertissement (une par parametre
    non-accepte), et les imprime si ``echo``. Les modeles hors matrice ne
    produisent rien : une garde ne s'invente pas de mesures.
    """
    table = matrix if matrix is not None else load_matrix()
    key = resolve_model(model, table)
    if key is None:
        return []
    measured: Dict[str, Any] = table[key].get("parametres", {})
    warnings: List[str] = []
    for param, info in measured.items():
        if param in params and info.get("verdict") in ("REFUSE", "IGNORE"):
            warnings.append(_warning_line(model, key, param, info))
    if echo:
        for line in warnings:
            print(line)
    return warnings


def guard_call(
    model: str,
    params: Dict[str, Any],
    matrix: Optional[Dict[str, Any]] = None,
    echo: bool = True,
) -> Dict[str, Any]:
    """Filtre les parametres refuses et renvoie ceux qui passent l'appel.

    Les parametres marques REFUSE sont retires (l'appel doit reussir) ; les
    parametres marques IGNORE sont conserves (inoffensifs) mais signales.
    """
    table = matrix if matrix is not None else load_matrix()
    key = resolve_model(model, table)
    if key is None:
        return dict(params)
    measured: Dict[str, Any] = table[key].get("parametres", {})
    safe = dict(params)
    for param, info in measured.items():
        if param in safe and info.get("verdict") == "REFUSE":
            del safe[param]
    if echo:
        check_params(model, params, matrix=table, echo=True)
    return safe
