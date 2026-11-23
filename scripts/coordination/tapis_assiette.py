#!/usr/bin/env python3
"""L'assiette du tapis : feuilles servies contre conteneurs servis (#25082).

Pourquoi ce module existe
-------------------------
Le triage du tapis rapide fait son travail : au tirage du 21/11, 29 issues
sur 475 etaient servables, et **28 d'entre elles etaient des conteneurs**
(EPIC ou umbrella) -- une seule feuille (#20316). Ce qui manquait n'etait
donc pas le tri, mais la **composition du pool** : « le tapis ne manque pas
de tri ; il manque de feuilles. » (coordinateur, 21/11, sur le tirage de 07:55Z)

Ce module mesure cette composition a deux niveaux :

- **le pool** (un tirage) : combien de feuilles, combien de conteneurs, et
  **ou** les feuilles se perdent -- le code d'ecart qui en retient le plus ;
- **le service** (le journal du service effectif, le meme magasin que
  l'acceptance de #25082) : ce qui a reellement ete servi, tirage par tirage.

Il ne fixe **aucun seuil** : la mesure est un fait, la politique d'assiette
appartient au coordinateur. Le module expose la mesure, rien d'autre.

Usage : ``--draw <tirage.json>`` pour le pool, ``--stat`` pour le service
(``--journal`` pour viser un autre magasin) ; les deux sorties acceptent
``--json``.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_acceptance, tirage_journal

MODE = tapis_acceptance.MODE
"""Le service effectif : le meme mode que le journal de l'acceptance."""


def _part(n: int | None, d: int | None) -> float | None:
    """Une part, ou ``None`` quand elle ne se calcule pas (jamais 0 %)."""
    if n is None or not d:
        return None
    return n / d


def mesurer_pool(draw: dict) -> dict:
    """La composition du pool d'un tirage : feuilles contre conteneurs.

    Le tirage porte deux choses : les compteurs de la lecture (``servables``,
    ``servables_feuilles``, ``servables_conteneurs``) et les ecartees par
    code, dont chaque entree dit desormais si l'issue est une feuille.

    Un tirage anterieur a cette mesure ne porte pas le flag : les entrees
    non mesurees sont comptees a part, jamais assimilees a des feuilles.
    """
    lecture = draw.get("lecture") or {}
    ecartees = draw.get("ecartees") or {}
    par_code: dict[str, dict[str, int]] = {}
    feuilles_ec = conteneurs_ec = non_mesure = 0
    for code, entrees in ecartees.items():
        f = sum(1 for e in entrees if e.get("feuille") is True)
        c = sum(1 for e in entrees if e.get("feuille") is False)
        par_code[code] = {"feuilles": f, "conteneurs": c}
        feuilles_ec += f
        conteneurs_ec += c
        non_mesure += len(entrees) - f - c
    serv_f = lecture.get("servables_feuilles")
    serv_c = lecture.get("servables_conteneurs")
    feuilles = feuilles_ec + serv_f if serv_f is not None else None
    conteneurs = conteneurs_ec + serv_c if serv_c is not None else None
    return {
        "issues": lecture.get("issues"),
        "feuilles": feuilles,
        "conteneurs": conteneurs,
        "servables": lecture.get("servables"),
        "servables_feuilles": serv_f,
        "servables_conteneurs": serv_c,
        "part_feuilles_servables": _part(serv_f, feuilles),
        "feuilles_ecartees": feuilles_ec,
        "conteneurs_ecartees": conteneurs_ec,
        "non_mesure": non_mesure,
        "ecartees_par_code": par_code,
        "code_qui_retient_les_feuilles": _code_le_plus_feuilles(par_code),
    }


def _code_le_plus_feuilles(par_code: dict[str, dict[str, int]]) -> str | None:
    """Le code d'ecart qui retient le plus de feuilles (l'ordre du rapport tranche)."""
    if not par_code:
        return None
    return max(par_code.items(), key=lambda kv: (kv[1]["feuilles"], kv[0]))[0]


def mesurer_service(records: list[tirage_journal.TirageRecord]) -> dict:
    """Ce que le service effectif a servi : feuilles contre conteneurs.

    Seuls les enregistrements du service effectif comptent (le rejeu ``belt``
    mesure autre chose). L'unite reste le **tirage** : un tirage qui ne sert
    que des conteneurs est un tirage sterile, meme si ses grains sont
    techniquement servables.
    """
    servies = [r for r in records if r.mode == MODE]
    connus = [r for r in servies if "conteneur" in (r.extras or {})]
    feuilles = sum(1 for r in connus if not (r.extras or {})["conteneur"])
    conteneurs = len(connus) - feuilles
    tirages = _tirages(servies)
    steriles = sum(1 for t in tirages if t and all(
        (r.extras or {}).get("conteneur") for r in t if "conteneur" in (r.extras or {})))
    return {
        "tirages": len(tirages),
        "grains": len(servies),
        "grains_mesures": len(connus),
        "grains_sans_mesure": len(servies) - len(connus),
        "feuilles": feuilles,
        "conteneurs": conteneurs,
        "part_feuilles": _part(feuilles, len(connus)),
        "tirages_sans_feuille": steriles,
    }


def _tirages(servies: list[tirage_journal.TirageRecord]) -> list[list[tirage_journal.TirageRecord]]:
    """Les enregistrements regroupes par tirage (le ``draw_id``)."""
    groupes: dict[str, list[tirage_journal.TirageRecord]] = {}
    for r in servies:
        groupes.setdefault(r.draw_id or f"__sans_draw_id__:{len(groupes)}", []).append(r)
    return list(groupes.values())


def texte_pool(m: dict) -> str:
    """La lecture courte du pool : combien de feuilles, et ou elles se perdent."""
    def part(v: float | None) -> str:
        return "n/a" if v is None else f"{v * 100:.1f} %"
    lignes = [
        "Assiette du pool (tirage) -- feuilles contre conteneurs",
        (f"issues lues : {m['issues']} -- feuilles : {m['feuilles']} "
         f"-- conteneurs : {m['conteneurs']}"),
        (f"servables : {m['servables']} (feuilles {m['servables_feuilles']}, "
         f"conteneurs {m['servables_conteneurs']})"),
        f"part des feuilles servables : {part(m['part_feuilles_servables'])}",
    ]
    codes = [(c, v["feuilles"]) for c, v in m["ecartees_par_code"].items() if v["feuilles"]]
    if codes:
        detail = ", ".join(f"{c} {n}" for c, n in sorted(codes, key=lambda kv: -kv[1]))
        lignes.append(f"feuilles retenues par code d'ecart : {detail}")
    if m["non_mesure"]:
        lignes.append(f"issues ecartees sans mesure feuille : {m['non_mesure']} "
                      "(tirage anterieur a la mesure)")
    return "\n".join(lignes)


def texte_service(m: dict) -> str:
    """La lecture courte du service : ce qui a ete servi, tirage par tirage."""
    def part(v: float | None) -> str:
        return "n/a" if v is None else f"{v * 100:.1f} %"
    lignes = [
        "Assiette du service effectif -- ce qui a ete servi",
        (f"tirages servis : {m['tirages']} -- grains servis : {m['grains']} "
         f"(mesures : {m['grains_mesures']})"),
        (f"feuilles servies : {m['feuilles']} -- conteneurs servis : {m['conteneurs']} "
         f"-- part feuilles : {part(m['part_feuilles'])}"),
        f"tirages sans aucune feuille : {m['tirages_sans_feuille']} / {m['tirages']}",
    ]
    if m["grains_sans_mesure"]:
        lignes.append(f"grains servis avant la mesure : {m['grains_sans_mesure']} "
                      "(le flag conteneur n'etait pas encore journalise)")
    return "\n".join(lignes)


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Assiette du tapis : feuilles contre conteneurs.")
    p.add_argument("--draw", default=None, help="tirage JSON (la composition du pool)")
    p.add_argument("--stat", action="store_true", help="mesurer le service effectif")
    p.add_argument("--journal", default=None, help="magasin du service (sinon le magasin machine)")
    p.add_argument("--json", action="store_true")
    return p


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if not args.draw and not args.stat:
        _parser().print_help()
        return 2
    if args.draw:
        draw = json.loads(Path(args.draw).read_text(encoding="utf-8"))
        m = mesurer_pool(draw)
        print(json.dumps(m, ensure_ascii=False, indent=1) if args.json else texte_pool(m))
    if args.stat:
        chemin = Path(args.journal) if args.journal else tapis_acceptance.default_store()
        m = mesurer_service(tirage_journal.read_journal(chemin))
        print(json.dumps(m, ensure_ascii=False, indent=1) if args.json else texte_service(m))
    return 0


if __name__ == "__main__":
    sys.exit(main())
