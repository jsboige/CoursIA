#!/usr/bin/env python3
"""Comparateur base/tete de la surface auto-chargee du harnais (#15204).

Le mandat user porte sur la surface **auto-chargee** du harnais (les regles
sans frontmatter `paths:` + le `CLAUDE.md` du depot), pas sur le poids total
du depot. L'instrument canonique qui la mesure est
`scripts/audit/measure_autoloaded_harness.py` ; ses deux instantanes JSON
(base et tete) sont produites par la voie rapide, qui bascule l'arbre a la
base entre les deux passes.

Ce script ne REMESURE rien : il compare deux instantanes deja mesurees. La
mesure reste dans l'organe canonique, la reimplementation serait un second
compte qui derive (cf. le compte derive a la main du ticket, refute par
l'instrument).

Verdict :
  rc=0 -- la surface auto-chargee de la tete n'a pas grandi, et aucune surface
          n'a disparu sans qu'on sache ou elle est allee ;
  rc=1 -- CROISSANCE : la PR ajoute du contexte a toutes les sessions ;
       -- SUPPRESSION : une surface auto-chargee a disparu (et n'est pas
          retrouvee ailleurs sous un autre nom) -- le cliquet ne refuse pas
          seulement la croissance, il refuse aussi la DISPARITION muette,
          qui fait baisser le total sans que personne ne l'ait demandee ;
  rc=2 -- incident d'entree (JSON illisible, cle absente) ou MESURE INCOMPLETE :
          un depot sans verdict reste un depot sans garde, l'incident n'est
          pas un quitus.

Trois distinctions que ce comparateur porte, chacune mesuree par un test :

  1. **Migration vers `path_gated_rules` != suppression.** Une regle qui perd
     son frontmatter `paths:` quitte la surface auto-chargee : le cliquet
     accepte (c'est le levier A du mandat). Une regle qui DISPARAIT du depot
     n'a pas de destination : le cliquet refuse. Les deux se ressemblent dans
     le diff (le total baisse), ils ne se ressemblent pas dans les faits.
  2. **Renommage != suppression.** Une regle renommee garde son contenu, donc
     son `sha256` : l'organe l'emeet par surface, le comparateur apparie les
     surfaces disparues et les surfaces apparues par empreinte. Sans cela, un
     renommage serait accuse a tort de suppression.
  3. **Mesure incomplete != verdict.** `measurement_complete` faux signifie
     qu'une surface demandee n'a pas ete lue : le total ne certifie rien.
     C'est un incident (rc=2), pas une reponse. Le rc=2 doit etre
     ATTEIGNABLE : sans surface du depot declaree manquante par l'organe, il
     ne l'est pas.

Le cliquet porte sur le **delta**, jamais sur un seuil absolu : la surface
actuelle est deja au-dessus de la cible du mandat (mesure du 2026-11-06 :
181 722 o pour le depot seul, cible 157 500 o). Un garde qui accuse la dette
pre-existante serait rouge des sa naissance et ferait echouer toutes les PRs
sans qu'aucune ne l'ait causee.

Usage :
    python scripts/ci/check_harness_weight_delta.py <base.json> <head.json>
    python scripts/ci/check_harness_weight_delta.py <base.json> <head.json> --json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Cles exigees dans chaque instantane. Leur absence rend le verdict
# INCONNU (rc=2) : mieux vaut un incident visible qu'un verdict invente.
# `ratio_bytes_per_token` y figure : le ratio vient de la MESURE (l'organe
# l'emet), jamais d'une constante recopiee ici -- deux sources pour un
# meme nombre deriveient des que l'une des deux change.
REQUIRED_KEYS = ("autoloaded_total_bytes", "autoloaded_rules",
                  "path_gated_rules", "root_file", "measurement_complete",
                  "ratio_bytes_per_token")

# Verdict -> code de sortie. Un GROWTH et une SUPPRESSION bloquent (1) ;
# une MESURE INCOMPLETE est un incident (2) ; OK passe (0).
RC = {"OK": 0, "GROWTH": 1, "SUPPRESSION": 1, "MESURE INCOMPLETE": 2}


class Incident(Exception):
    """Entree illisible ou cle absente : verdict inconnu (rc=2)."""


def load_snapshot(path: str) -> dict:
    """Charge un instantane JSON de l'organe canonique, ou leve Incident.

    `measurement_complete` n'est PAS verifie ici : c'est un fait de mesure,
    pas une integrite de fichier. Le comparer decide de ce qu'il signifie
    (une surface disparue explique-t-elle l'incompletude ?), et le tranches.
    """
    try:
        raw = Path(path).read_text(encoding="utf-8")
    except OSError as exc:
        raise Incident(f"instantane illisible : {path} ({exc})") from exc
    try:
        data = json.loads(raw)
    except ValueError as exc:
        raise Incident(f"instantane JSON invalide : {path} ({exc})") from exc
    if not isinstance(data, dict):
        raise Incident(f"instantane JSON inattendu (objet attendu) : {path}")
    missing = [k for k in REQUIRED_KEYS if k not in data]
    if missing:
        raise Incident(f"instantane incomplet : {path} (cles absentes : "
                       f"{', '.join(missing)})")
    return data


def _auto_surfaces(snapshot: dict) -> dict[str, dict]:
    """Surfaces AUTO-CHARGEES, fichier par fichier.

    Le `CLAUDE.md` du depot et les regles auto-chargees sont deux surfaces
    de meme nature : le poids que TOUTE session paie. On les melange pour
    que le delta se lise comme une surface unique.
    """
    out: dict[str, dict] = {}
    root = snapshot.get("root_file") or {}
    if root.get("name"):
        out[str(root["name"])] = root
    for rule in snapshot.get("autoloaded_rules") or []:
        out[str(rule["name"])] = rule
    return out


def _all_surfaces(snapshot: dict) -> dict[str, dict]:
    """Toutes les surfaces du depot, GATEES comprises.

    Une regle migree vers `path_gated_rules` n'a pas disparu : elle a change
    de statut. La chercher ici, et non dans les seules surfaces auto-chargees,
    est ce qui distingue une migration d'une suppression.
    """
    out = dict(_auto_surfaces(snapshot))
    for rule in snapshot.get("path_gated_rules") or []:
        out.setdefault(str(rule["name"]), rule)
    return out


def surfaces(snapshot: dict) -> dict[str, int]:
    """Surface auto-chargee, fichier par fichier (poids en octets)."""
    return {name: int(entry.get("bytes") or 0)
            for name, entry in _auto_surfaces(snapshot).items()}


def suppressions(base: dict, head: dict) -> list[str]:
    """Surfaces auto-chargees de la base ABSENTES de la tete.

    Absente de la tete = introuvable dans les surfaces auto-chargees, dans
    les surfaces path-gatees ET dans le fichier racine. Une regle migree vers
    `path_gated_rules` est donc trouvee (migration, pas suppression), et une
    regle renommee est appariee par son `sha256` (renommage, pas
    suppression).
    """
    base_s = _auto_surfaces(base)
    head_all = _all_surfaces(head)
    head_hashes = {str(e.get("sha256")) for e in head_all.values()
                   if e.get("sha256")}
    out = []
    for name, entry in sorted(base_s.items()):
        if name in head_all:
            continue
        digest = str(entry.get("sha256") or "")
        if digest and digest in head_hashes:
            continue            # renommee : meme contenu sous un autre nom
        out.append(name)
    return out


def compare(base: dict, head: dict) -> dict:
    """Delta de la surface auto-chargee entre la base et la tete."""
    base_s = surfaces(base)
    head_s = surfaces(head)
    base_bytes = int(base["autoloaded_total_bytes"])
    head_bytes = int(head["autoloaded_total_bytes"])

    deltas = []
    for name in sorted(set(base_s) | set(head_s)):
        b = base_s.get(name)
        h = head_s.get(name)
        if b is None:
            kind = "ajoute"
        elif h is None:
            kind = "retire"
        else:
            kind = "modifie"
        if b == h:
            continue
        deltas.append({
            "surface": name,
            "kind": kind,
            "base_bytes": b,
            "head_bytes": h,
            "delta_bytes": (h or 0) - (b or 0),
        })
    deltas.sort(key=lambda d: -d["delta_bytes"])

    ratio_base = float(base["ratio_bytes_per_token"])
    ratio_head = float(head["ratio_bytes_per_token"])
    disparues = suppressions(base, head)
    complete = bool(base.get("measurement_complete")) and \
        bool(head.get("measurement_complete"))

    if disparues:
        verdict = "SUPPRESSION"
    elif not complete:
        verdict = "MESURE INCOMPLETE"
    elif head_bytes > base_bytes:
        verdict = "GROWTH"
    else:
        verdict = "OK"

    return {
        "verdict": verdict,
        "base_bytes": base_bytes,
        "head_bytes": head_bytes,
        "delta_bytes": head_bytes - base_bytes,
        "base_tokens_derived": round(base_bytes / ratio_base),
        "head_tokens_derived": round(head_bytes / ratio_head),
        "bytes_per_token": ratio_base,
        "ratio_changed_by_pr": ratio_base != ratio_head,
        "tokens_are_derived_not_tokenized": True,
        "surfaces": deltas,
        "surfaces_supprimees": disparues,
        "measurement_complete_base": bool(base.get("measurement_complete")),
        "measurement_complete_head": bool(head.get("measurement_complete")),
    }


def render(result: dict) -> str:
    lines = []
    lines.append("Surface auto-chargee du harnais -- delta base -> tete")
    lines.append(f"  base : {result['base_bytes']:>8} o "
                 f"(~{result['base_tokens_derived']} tok derives)")
    lines.append(f"  tete : {result['head_bytes']:>8} o "
                 f"(~{result['head_tokens_derived']} tok derives)")
    lines.append(f"  delta: {result['delta_bytes']:>+8} o")
    if result["surfaces"]:
        lines.append("")
        lines.append(f"{'surface':<48} {'base':>8} {'tete':>8} {'delta':>9}  etat")
        for d in result["surfaces"]:
            lines.append(f"{d['surface'][:48]:<48} "
                         f"{(d['base_bytes'] if d['base_bytes'] is not None else 0):>8} "
                         f"{(d['head_bytes'] if d['head_bytes'] is not None else 0):>8} "
                         f"{d['delta_bytes']:>+9}  {d['kind']}")
    lines.append("")
    if result["verdict"] == "GROWTH":
        lines.append("VERDICT: CROISSANCE -- la PR ajoute du contexte a "
                     "toutes les sessions.")
        lines.append("Remede : path-gater la regle concernee (frontmatter "
                     "`paths:`), ou trimmer son contenu vers docs/.")
    elif result["verdict"] == "SUPPRESSION":
        lines.append("VERDICT: SUPPRESSION -- une surface auto-chargee a "
                     "disparu : " + ", ".join(result["surfaces_supprimees"]))
        lines.append("Une regle path-gatee reste listee : elle n'a pas "
                     "disparu. Une suppression de fichier, elle, fait baisser "
                     "le total sans que personne ne l'ait demandee -- si elle "
                     "est voulue, elle doit etre dite.")
    elif result["verdict"] == "MESURE INCOMPLETE":
        lines.append("VERDICT: MESURE INCOMPLETE -- une surface demandee "
                     "n'a pas ete lue ; le total ne certifie rien.")
        lines.append("Incident de mesure, pas reponse : rejouer la mesure "
                     "sur un depot complet.")
    else:
        lines.append("VERDICT: pas de croissance, aucune surface disparue.")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("base_json", help="instantane JSON de la base")
    parser.add_argument("head_json", help="instantane JSON de la tete")
    parser.add_argument("--json", action="store_true", dest="as_json",
                        help="sortie machine (JSON)")
    args = parser.parse_args(argv)

    try:
        base = load_snapshot(args.base_json)
        head = load_snapshot(args.head_json)
    except Incident as exc:
        print(f"INCIDENT : {exc}", file=sys.stderr)
        return 2

    result = compare(base, head)
    if args.as_json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        print(render(result))
    return RC[result["verdict"]]


if __name__ == "__main__":
    sys.exit(main())
