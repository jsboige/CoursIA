#!/usr/bin/env python3
"""Pre-dispatch grounding guard -- la commande unique AVANT d'ecrire un steer.

Pourquoi cet outil existe
-------------------------

Le 2026-08-16, le coordinateur a dispatche **deux** grains fantomes dans la
meme journee, sur une regle qui existait deja par ecrit (L898 de
`proactive-coordination.md`, qui couvre explicitement « rediger un steer »).
Deux violations le meme jour d'une regle ecrite ne se corrigent pas en relisant
la regle : c'est un defaut d'organe (cf `rule-needs-an-organ-not-more-vigilance`).

Les deux ratés, et ce qu'ils ont en commun :

  * **#10990** -- l'issue etait OPEN et non claim. Mais son acceptance disait
    « *Aucune PR ouverte uniquement pour ce changement* », donc le rollout
    frontal dispatche echouait le gate de sa propre cible **par construction**.
    Lire le body ne suffit pas : un body decrit un *probleme*, une acceptance
    decrit la *forme admissible* -- souvent en nommant les formes interdites.

  * **#11264** -- l'issue etait OPEN et non claim. Mais une PR ouverte
    (#11273) la traitait deja, et le residuel etait route ailleurs. `gh issue
    view` ne voit pas les PRs ouvertes ; `check_lane_claim.py` ne voit que les
    claims ; `check_lane_claim.py --paths` voit les PRs ouvertes mais exige de
    connaitre les chemins -- ce qu'on n'a justement pas encore au moment de
    dispatcher.

Une issue OPEN et non claim n'est pas un grain libre. C'est un grain dont on
n'a pas verifie la liberte, et la difference ne se voit pas dans la sortie de
la commande. D'ou cet agregateur.

Surfaces interrogees
--------------------

  1. **Etat** de l'issue (OPEN/CLOSED) et labels.
  2. **Contraintes de forme** dans l'acceptance : les cases `- [ ]` non cochees
     dont le texte porte une negation (« aucune PR », « ne pas », « jamais »,
     « sans ouvrir »...). Ce sont celles qui interdisent une forme de livraison.
  3. **PRs ouvertes** referencant l'issue -- quelqu'un y travaille deja.
  4. **PRs mergees** referencant l'issue -- le travail est peut-etre livre sans
     que l'issue soit fermee (le `See #N` ne ferme pas).
  5. **Claims** -- delegue a `check_lane_claim.py`, qui est l'autorite (ne pas
     reimplementer : le reducteur d'evenements y vit, avec les `[OVERRIDE]`).

Propriete de robustesse (le point le plus important du fichier)
--------------------------------------------------------------

**« rien trouve » et « pas regarde » ne doivent JAMAIS partager la meme valeur
de retour.** Toute surface dont l'interrogation echoue est rapportee comme
`ERROR`, jamais comme une liste vide -- et la sortie globale devient `UNKNOWN`
avec un code de retour non nul. Un outil qui rend « 0 PR ouverte » parce que
`gh` a echoue rendrait un resultat *plus petit et plus propre* que la verite,
qui est exactement la forme de panne que ce depot a deja payee quatre fois.

Usage
-----

    python scripts/check_grain_free.py 10990
    python scripts/check_grain_free.py 11264 --lane myia-po-2025:CoursIA
    python scripts/check_grain_free.py 10990 --json

Codes de retour :
    0  CLEAR    -- rien ne s'oppose au dispatch (lire quand meme les notes)
    1  FLAGGED  -- au moins une surface demande une lecture avant de dispatcher
    2  UNKNOWN  -- une surface n'a pas pu etre interrogee : ne rien conclure
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO = "jsboige/CoursIA"

# Une case d'acceptance qui porte une de ces formes contraint la FORME de la
# livraison (elle interdit quelque chose) plutot que d'en decrire le contenu.
# Volontairement large : un faux positif coute une lecture de 5 secondes, un
# faux negatif coute un cycle de worker (incident #10990).
NEGATION_PATTERNS = [
    r"\baucun(?:e|s)?\b",
    r"\bne\s+(?:pas|plus|jamais)\b",
    r"\bjamais\b",
    r"\bsans\s+(?:ouvrir|creer|passer|re-?exec)",
    r"\binterdit(?:e|s)?\b",
    r"\bpas\s+de\s+PR\b",
    r"\bno\s+standalone\b",
    r"\bmust\s+not\b",
]
_NEG_RE = re.compile("|".join(NEGATION_PATTERNS), re.IGNORECASE)

# `- [ ] texte` / `* [ ] texte`, case NON cochee uniquement : une case cochee
# decrit un acquis, pas une contrainte a respecter.
_UNCHECKED_RE = re.compile(r"^\s*[-*]\s*\[\s\]\s*(.+?)\s*$", re.MULTILINE)


class SurfaceError(RuntimeError):
    """Une surface n'a pas pu etre interrogee -- distinct d'un resultat vide."""


def _gh(args: list[str]) -> str:
    """Appelle `gh` et REMONTE l'echec au lieu de le convertir en vide."""
    if shutil.which("gh") is None:
        raise SurfaceError("binaire `gh` introuvable dans le PATH")
    proc = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        err = (proc.stderr or "").strip().splitlines()
        raise SurfaceError(f"gh {' '.join(args[:3])}… -> exit {proc.returncode}: "
                           f"{err[-1] if err else 'aucun message'}")
    return proc.stdout


def _gh_json(args: list[str]):
    raw = _gh(args)
    try:
        return json.loads(raw) if raw.strip() else []
    except json.JSONDecodeError as exc:
        raise SurfaceError(f"sortie gh non-JSON: {exc}") from exc


def surface_issue(number: str) -> dict:
    data = _gh_json([
        "issue", "view", number, "--repo", REPO,
        "--json", "state,title,labels,body,updatedAt",
    ])
    return {
        "state": data.get("state"),
        "title": data.get("title", ""),
        "labels": [lbl["name"] for lbl in data.get("labels", [])],
        "body": data.get("body") or "",
        "updatedAt": data.get("updatedAt"),
    }


def form_constraints(body: str) -> list[str]:
    """Cases d'acceptance NON cochees qui interdisent une forme de livraison."""
    return [m.group(1).strip() for m in _UNCHECKED_RE.finditer(body)
            if _NEG_RE.search(m.group(1))]


def surface_prs(number: str, state: str) -> list[dict]:
    """PRs (open|merged) referencant l'issue dans le titre ou le body.

    `--search` plutot qu'un filtre local : le plafond silencieux de 30 de
    `gh pr list` mordrait sur un depot a 26 PRs ouvertes et des centaines de
    mergees (cf `gh-list-default-limit-30-silent`).

    La recherche GitHub est plein-texte et tokenisee : « 11264 » matche aussi
    des PRs qui portent ce nombre pour une tout autre raison (mesure sur
    #11264 : 2 faux positifs sur 2 mergees). On re-filtre donc cote client sur
    la forme `#<N>`, la seule qui denote une reference. Un outil bruyant sur
    une ligne apprend a ignorer cette ligne -- c'est ce qui perd les gates.
    """
    rows = _gh_json([
        "pr", "list", "--repo", REPO, "--state", state, "--limit", "60",
        "--search", f"{number} in:title,body",
        "--json", "number,title,author,headRefName,mergedAt,body",
    ])
    ref = re.compile(rf"#{re.escape(number)}\b")
    return [
        {
            "number": r["number"],
            "title": r.get("title", "")[:70],
            "author": (r.get("author") or {}).get("login", "?"),
            "branch": r.get("headRefName", ""),
            "mergedAt": (r.get("mergedAt") or "")[:10],
        }
        for r in rows
        if ref.search(r.get("title") or "") or ref.search(r.get("body") or "")
    ]


def surface_claims(number: str, lane: str | None) -> dict:
    """Delegue a l'autorite -- ne PAS reimplementer le reducteur de claims."""
    script = Path(__file__).with_name("check_lane_claim.py")
    if not script.exists():
        raise SurfaceError(f"{script.name} introuvable (autorite des claims)")
    # `check_lane_claim.py` n'expose PAS de `--json` : sa sortie est textuelle
    # et son verdict vit dans le code de retour. On ne parse donc pas son
    # texte (fragile), on lit son exit et on rapporte ses lignes telles quelles.
    cmd = [sys.executable, str(script), number, "--lane", lane]
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    # Semantique documentee de check_lane_claim.py, MODE ISSUE (sans --paths) :
    #   0 = libre, 1 = claim bloquant d'une autre lane, 2 = erreur io-ou-gh.
    # Le 2 n'est PAS un resultat : le traiter comme tel afficherait une panne
    # sous les traits d'un constat benin -- la faute exacte que ce fichier
    # existe pour empecher. (En mode --paths, que l'on n'utilise pas ici, le 2
    # signifie « collision de PR cross-lane » : ne pas transposer.)
    if proc.returncode not in (0, 1):
        err = (proc.stderr or "").strip().splitlines()
        raise SurfaceError(f"check_lane_claim.py -> exit {proc.returncode}: "
                           f"{err[-1] if err else 'aucun message'}")
    return {
        "exit": proc.returncode,
        "output": [ln for ln in (proc.stdout or "").splitlines() if ln.strip()],
    }


def collect(number: str, lane: str | None) -> dict:
    out: dict = {"issue_number": number, "surfaces": {}, "errors": []}

    def run(name, fn):
        try:
            out["surfaces"][name] = fn()
        except SurfaceError as exc:
            out["surfaces"][name] = None       # None != [] -- jamais confondus
            out["errors"].append(f"{name}: {exc}")

    run("issue", lambda: surface_issue(number))
    issue = out["surfaces"].get("issue")
    out["surfaces"]["form_constraints"] = (
        form_constraints(issue["body"]) if issue else None
    )
    run("open_prs", lambda: surface_prs(number, "open"))
    run("merged_prs", lambda: surface_prs(number, "merged"))
    run("claims", lambda: surface_claims(number, lane))

    flags: list[str] = []
    if issue and issue["state"] != "OPEN":
        flags.append(f"issue {issue['state']}")
    if out["surfaces"].get("form_constraints"):
        flags.append(f"{len(out['surfaces']['form_constraints'])} contrainte(s) de forme")
    if out["surfaces"].get("open_prs"):
        flags.append(f"{len(out['surfaces']['open_prs'])} PR(s) ouverte(s)")
    if out["surfaces"].get("merged_prs"):
        flags.append(f"{len(out['surfaces']['merged_prs'])} PR(s) mergee(s)")
    claims = out["surfaces"].get("claims")
    if claims and claims.get("exit") == 1:
        flags.append("claim bloquant d'une autre lane")

    out["flags"] = flags
    out["verdict"] = "UNKNOWN" if out["errors"] else ("FLAGGED" if flags else "CLEAR")
    return out


def render(res: dict) -> str:
    lines: list[str] = []
    issue = res["surfaces"].get("issue")
    head = f"GRAIN #{res['issue_number']} — verdict: {res['verdict']}"
    lines.append(head)
    lines.append("=" * len(head))

    if issue:
        lines.append(f"  {issue['state']} | {issue['title'][:70]}")
        lines.append(f"  labels: {', '.join(issue['labels']) or '(aucun)'}"
                     f" | maj: {(issue['updatedAt'] or '')[:16]}")
    else:
        lines.append("  issue: NON INTERROGEE (voir erreurs)")

    fc = res["surfaces"].get("form_constraints")
    if fc:
        lines.append("")
        lines.append("  CONTRAINTES DE FORME (acceptance non cochee, negation) :")
        for c in fc:
            lines.append(f"    - [ ] {c[:100]}")
        lines.append("    → la forme de livraison dispatchee doit satisfaire CHAQUE case.")
    elif fc == []:
        lines.append("  contraintes de forme : aucune")

    for key, label in (("open_prs", "PRs OUVERTES"), ("merged_prs", "PRs MERGEES")):
        rows = res["surfaces"].get(key)
        if rows is None:
            lines.append(f"  {label} : NON INTERROGEES")
        elif rows:
            lines.append("")
            lines.append(f"  {label} referencant l'issue :")
            for r in rows[:8]:
                stamp = f" {r['mergedAt']}" if r["mergedAt"] else ""
                lines.append(f"    #{r['number']}{stamp} [{r['author']}] {r['title']}")
            if len(rows) > 8:
                lines.append(f"    … et {len(rows) - 8} autre(s)")
        else:
            lines.append(f"  {label} : aucune")

    claims = res["surfaces"].get("claims")
    if claims is None:
        lines.append("  claims : NON INTERROGES")
    else:
        verdict = {0: "libre", 1: "BLOQUANT (autre lane)"}
        lines.append(f"  claims : {verdict.get(claims['exit'], claims['exit'])}")

    if res["errors"]:
        lines.append("")
        lines.append("  ERREURS — ne rien conclure de ce qui suit :")
        for e in res["errors"]:
            lines.append(f"    ! {e}")

    lines.append("")
    if res["verdict"] == "CLEAR":
        lines.append("  Rien ne s'oppose au dispatch.")
    elif res["verdict"] == "FLAGGED":
        lines.append(f"  A LIRE AVANT DE DISPATCHER : {' ; '.join(res['flags'])}")
    else:
        lines.append("  Surface(s) non interrogee(s) : verdict impossible, "
                     "ne PAS lire l'absence comme une absence.")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Agrege les surfaces de grounding d'un grain avant dispatch.",
        epilog="Exit: 0 CLEAR, 1 FLAGGED, 2 UNKNOWN (surface non interrogee).",
    )
    ap.add_argument("issue", help="numero d'issue")
    # Obligatoire parce que `check_lane_claim.py` l'exige : sans elle, la
    # surface des claims ne peut pas etre interrogee, et un grounding a
    # quatre surfaces sur cinq n'est pas un grounding -- il rendrait CLEAR
    # sur une issue tenue par une autre lane.
    ap.add_argument("--lane", required=True,
                    help="lane servie, ex. myia-po-2025:CoursIA (obligatoire : "
                         "la surface des claims en depend)")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="sortie JSON brute")
    args = ap.parse_args()

    res = collect(str(args.issue).lstrip("#"), args.lane)
    print(json.dumps(res, ensure_ascii=False, indent=2) if args.as_json
          else render(res))
    return {"CLEAR": 0, "FLAGGED": 1, "UNKNOWN": 2}[res["verdict"]]


if __name__ == "__main__":
    sys.exit(main())
