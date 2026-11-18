#!/usr/bin/env python3
"""#27012 -- le conseil du plafond nomme une FILLE REELLE de l'EPIC plafonne.

Module frere de `check_lane_claim.py`. Le module-maitre est cible par la
scission T4 (son plafond de taille, releve au 16/11, ne peut pas grossir) :
ce qui concerne la **redaction du conseil** et la **liste des filles** vit
ici, et `check_lane_claim.py` ne fait que l'appeler.

Le defaut mesure (lane `myia-po-2023:CoursIA-2`, ~5 min perdues par
tentative) : le message de refus du plafond #22500 conseillait « servir un
sous-grain DEJA OUVERT de l'EPIC » en citant **#26414** -- qui est une issue
META (une decision), pas une fille de l'EPIC plafonne. La lane qui suivait
le conseil ne trouvait donc aucune fille a servir, et le blocage se
reproduisait.

Ce que fait ce module :

  - `open_daughters` : les issues ouvertes dont le corps ou le titre nomme
    l'EPIC plafonne -- la definition de « fille » est celle de
    `pick_idle_grain.parent_refs`, donc **le meme oracle** que le reste de
    l'organe (aucune seconde grammaire) ;
  - `cap_action_line` : la ligne ACTION du message, qui nomme ces filles
    et, quand il n'y en a pas, garde l'echappatoire generique. Elle n'invente
    jamais de fille.

Run: aucune (module importe par `check_lane_claim.py`).
"""
from __future__ import annotations

#: Nombre de filles nommees dans le conseil (au-dela, la ligne devient
#: illisible ; le reste reste dans le pool, nomme par l'organe du tapis).
MAX_DAUGHTERS = 3

#: Longueur du titre cite -- le titre entier rend le message illisible.
TITLE_MAX = 60


def open_daughters(pool, epic_number, parent_refs) -> list[dict]:
    """Les filles ouvertes de l'EPIC plafonne, mesurees dans le pool.

    Args:
        pool: les issues ouvertes du picker (forme `fetch_pool`).
        epic_number: le numero de l'EPIC plafonne ; `None` -> aucune fille
            (le plafond peut venir d'un parent, pas d'un sujet nomme).
        parent_refs: `pick_idle_grain.parent_refs` -- meme oracle que
            l'organe, donc meme definition de « fille ».

    Returns:
        Une liste de `{"number": int, "title": str}`, au plus `MAX_DAUGHTERS`.
    """
    if epic_number is None:
        return []
    out: list[dict] = []
    for item in pool:
        number = item.get("number")
        if number is None:
            continue
        if epic_number in parent_refs(item):
            out.append({"number": number, "title": item.get("title")})
            if len(out) >= MAX_DAUGHTERS:
                break
    return out


def cap_action_line(where, daughters) -> str:
    """La ligne ACTION du message de plafond (#22500 point 3).

    Quand des filles sont connues, elles sont nommees -- la lane qui lit le
    message a alors un grain a servir. La decision #26414 reste citee comme
    decision (les filles existantes ne sont plus des sujets du plafond) et
    non comme si elle etait elle-meme la fille a servir.
    """
    if daughters:
        named = ", ".join(
            f"#{d.get('number')}"
            + (f" ({(d.get('title') or '')[:TITLE_MAX]})" if d.get("title") else "")
            for d in daughters
        )
        return (
            f"  ACTION: servir un sous-grain DEJA OUVERT de l'EPIC {where} "
            f"-- {named} (filles ouvertes mesurees de cet EPIC) -- ou "
            f"prendre un autre grain du pool. Seul le claim pose sur l'EPIC "
            f"lui-meme est plafonne (decision #26414 : les filles existantes "
            f"ne sont plus des sujets). Re-scoper avec `--paths` ne leve pas "
            f"ce plafond ; `--force` reste reserve a l'arbitrage coordinateur."
        )
    return (
        f"  ACTION: servir un sous-grain DEJA OUVERT de l'EPIC {where} "
        f"(decision #26414 : une fille existante se sert librement, seul le "
        f"claim pose sur l'EPIC est plafonne), ou prendre un autre grain du "
        f"pool. Re-scoper avec `--paths` ne leve pas ce plafond ; `--force` "
        f"reste reserve a l'arbitrage coordinateur."
    )
