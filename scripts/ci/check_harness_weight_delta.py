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
  rc=0 -- la surface auto-chargee de la tete n'a pas grandi (elle a baisse ou
          stayed egal) ;
  rc=1 -- la surface auto-chargee de la tete a GRANDI : la PR ajoute du
          contexte a toutes les sessions ;
  rc=2 -- incident d'entree (JSON illisible, cle absente, mesure incomplete) :
          un depot sans verdict reste un depot sans garde, l'incident n'est
          pas un quitus.

Le cliquet porte sur le **delta**, jamais sur un seuil absolu : la surface
actuelle est deja au-dessus de la cible du mandat (mesure du 2026-11-06 :
181 722 o pour le depot seul, cible 157 500 o). Un garde qui accuse la dette
pre-existante serait rouge des sa naissance et ferait echouer toutes les PR
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
REQUIRED_KEYS = ("autoloaded_total_bytes", "autoloaded_rules", "root_file",
                  "measurement_complete")


class Incident(Exception):
    """Entree illisible ou mesure incomplete : verdict inconnu (rc=2)."""


def load_snapshot(path: str) -> dict:
    """Charge un instantane JSON de l'organe canonique, ou leve Incident."""
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
    if not data["measurement_complete"]:
        raise Incident(f"mesure incomplete : {path} (une surface demandee "
                       f"manque ; le total ne certifie rien)")
    return data


def surfaces(snapshot: dict) -> dict[str, int]:
    """Surface auto-chargee, fichier par fichier.

    Le `CLAUDE.md` du depot et les regles auto-chargees sont deux surfaces
    de meme nature : le poids que TOUTE session paie. On les melange pour
    que le delta se lise comme une surface unique.
    """
    out: dict[str, int] = {}
    root = snapshot.get("root_file") or {}
    if root.get("name"):
        out[str(root["name"])] = int(root["bytes"])
    for rule in snapshot.get("autoloaded_rules") or []:
        out[str(rule["name"])] = int(rule["bytes"])
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

    ratio = float(base.get("ratio_bytes_per_token") or 0) or 2.25
    return {
        "verdict": "GROWTH" if head_bytes > base_bytes else "OK",
        "base_bytes": base_bytes,
        "head_bytes": head_bytes,
        "delta_bytes": head_bytes - base_bytes,
        "base_tokens_derived": round(base_bytes / ratio),
        "head_tokens_derived": round(head_bytes / ratio),
        "bytes_per_token": ratio,
        "tokens_are_derived_not_tokenized": True,
        "surfaces": deltas,
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
    else:
        lines.append("VERDICT: pas de croissance.")
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
    return 1 if result["verdict"] == "GROWTH" else 0


if __name__ == "__main__":
    sys.exit(main())
