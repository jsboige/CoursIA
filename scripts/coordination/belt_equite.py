#!/usr/bin/env python3
"""L'equite du DISPATCH : les premieres visites avant les reprises (19/11).

La **repartition** des files est un jugement du coordinateur -- cet organe ne
la fait pas. Mais il la **MESURE** : il nomme les grains **deja servis** qu'une
file place devant des issues **jamais servies**.

Le cas reel (#27338, 19/11) : une issue creee le matin a ete servie huit fois
dans la journee (huit PRs distinctes sur huit carnets), pendant que des issues
anciennes n'attendaient aucune PR. Le mandat du 16/11 dit l'inverse -- « toute
issue doit etre visitee au moins une fois avant qu'une autre le soit deux fois
» -- et le compteur de visites ne voyait pas le travail en cours : l'umbrella
comptait ZERO visite, donc elle passait en tete (voir `coordination.tapis_citations`).

Deux exceptions, nommees et explicites :

- la lane declare un **mandat** (`mandate` dans son bloc) : la mesure est rendue,
  mais notee exempte -- une campagne assumee n'est pas une faute ;
- le grain est **deja dans la file de la lane** (une correction en cours) : elle
  finit son travail, elle n'est pas penalisee.

La mesure est **non mesuree** quand la source ne porte pas le compte (le tapis
lourd n'expose pas les visites) : une mesure absente n'est pas une mesure de
zero. Doc : docs/reference/tapis-rapide.md.
"""
from __future__ import annotations


def etat_de_visite(p: dict) -> str:
    """L'etat de visite d'un grain du tirage : `servie`, `jamais`, `inconnu`.

    `inconnu` quand la source ne porte pas le compte : une mesure absente n'est
    pas une mesure de zero.
    """
    v = p.get("visites")
    if v is None:
        return "inconnu"
    return "servie" if int(v) > 0 else "jamais"


def etat_du_pool(grains: list[dict]) -> dict:
    """L'etat de visite du pool tire : les jamais servies et les deja servies.

    C'est la meme regle que le classement (`tapis_equilibre`) : une issue
    **jamais servie** passe devant une issue deja servie. Le tableau de decision
    rend les deux groupes, pour que le coordinateur compose ses files en voyant
    l'equite du pool.
    """
    jamais, servies = [], []
    for g in grains:
        item = {"number": int(g["number"]), "title": g.get("title") or "",
                "visites": int(g.get("visites") or 0)}
        (jamais if etat_de_visite(g) == "jamais" else servies).append(item)
    servies.sort(key=lambda i: -i["visites"])
    mesure = "visites" if any(g.get("visites") is not None
                               for g in grains) else "non mesuree"
    return {"mesure": mesure, "jamais": jamais, "servies": servies,
            "total": len(grains)}


def equite_dispatch(assignment: dict, grains: list[dict],
                    previous: dict | None = None) -> dict:
    """Les grains deja servis qu'une file place devant les issues jamais servies.

    `grains` : le tirage normalise (numero, visites). `previous` : la
    repartition precedente (`lanes` -> `queue`), pour ne pas penaliser un grain
    deja dans la file de la lane.
    """
    titles = {int(g["number"]): g for g in grains}
    jamais = sorted(n for n, g in titles.items() if etat_de_visite(g) == "jamais")
    deja: set[int] = set()
    if previous:
        for info in (previous.get("lanes") or {}).values():
            for item in info.get("queue") or []:
                if isinstance(item, dict) and item.get("number") is not None:
                    deja.add(int(item["number"]))
    flags = []
    for lane, info in assignment["lanes"].items():
        mandat = info.get("mandate")
        for n in info["queue"]:
            n = int(n)
            g = titles.get(n, {})
            if etat_de_visite(g) != "servie" or not jamais:
                continue
            correction = n in deja
            flags.append({
                "lane": lane, "number": n,
                "visites": int(g.get("visites") or 0),
                "jamais_servies": len(jamais),
                "motif": (f"#{n} est deja servie alors que {len(jamais)} issues "
                          f"n'ont jamais ete servies"),
                "exempt": bool(mandat) or correction,
                "raison": (str(mandat) if mandat else
                           ("deja dans la file de la lane (correction en cours)"
                            if correction else ""))})
    return {"mesure": ("visites" if any(g.get("visites") is not None
                                        for g in grains) else "non mesuree"),
            "jamais_servies": len(jamais), "signales": flags}
