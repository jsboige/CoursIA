"""Mesure d'autorite des levees de reserves (concern 2 de #11145) + compteur "re" pre-marqueur (concern 1).

Question posee par #11145 AVANT tout durcissement de l'organe :
« combien de levées actuelles viennent d'un tiers ? »

Borner la levee d'une reserve a son auteur (piste Hermes) rendrait l'organe
plus strict ; la decision exige la mesure. Ce script compagnon NE TOUCHE PAS
l'organe gate (`check_unaddressed_nits.py`) : il reutilise son modele de
donnees et ses memes predicats (classify, can_lift, LIFT_MARKERS,
CONDITIONAL_LIFT, CITERS) pour classifier chaque levee observee sur un
corpus de PRs mergees :

  SELF      — la reserve est levee par son propre auteur
  PR_AUTHOR — la reserve est levee par l'auteur de la PR (le flux sain :
              le worker repond a la reserve du reviewer)
  BYSTANDER — la reserve est levee par un tiers qui n'est NI l'auteur de la
              reserve NI l'auteur de la PR (la classe #10761, celle que la
              borne viserait)
  UNLIFTED  — aucune levee avant le merge (les findings de l'organe)

Regimes distincts, copies de analyse() :

  review:CHANGES_REQUESTED  leve par (a) re-review APPROVED du MEME auteur,
                            (b) phrase explicite de levee (LIFT_MARKER non
                            conditionnel), de n'importe quel auteur ;
  nit en commentaire        leve par tout commentaire capable de lever
                            (can_lift) ou toute review APPROVED, tiers inclus —
                            c'est exactement le chemin que la borne viserait.

Concern 1 : compte les occurrences de marqueur precdees du mot « re » (CITER
nu, fenetre 30 chars) et croise avec classify() du commentaire porteur —
une emission classee reserve malgre son « re » serait un faux negatif mesure.

Sortie : JSON (resume + detail par PR), exit 0 toujours (mesure, pas gate).
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_unaddressed_nits as nits  # noqa: E402


def measure_pr(pr_data: dict) -> dict:
    """Autorite de chaque levee pour une PR mergee (meme collecte que analyse())."""
    merged = nits.ts(pr_data.get("mergedAt"))
    cutoff = merged or datetime.now(timezone.utc)

    # Reserves (meme collecte que analyse) : (t, kind, author, src)
    nits_signals: list[tuple] = []
    for c in pr_data.get("comments") or []:
        login = (c.get("author") or {}).get("login", "")
        kind = nits.classify(login, c.get("body", ""))
        if kind:
            nits_signals.append(
                (nits.ts(c.get("createdAt")), kind, login, "comment"))
    for r in pr_data.get("reviews") or []:
        if r.get("state") == "DISMISSED":
            continue
        login = (r.get("author") or {}).get("login", "")
        kind = nits.classify(login, r.get("body", ""))
        if r.get("state") == "CHANGES_REQUESTED":
            kind = "BOT-CONCERN" if kind is None else kind
        if kind:
            nits_signals.append(
                (nits.ts(r.get("submittedAt")), kind, login,
                 f"review:{r.get('state')}"))

    # Levées, chacune AVEC son auteur.
    comment_lifts = [  # regime general : leve un nit en commentaire
        (nits.ts(c.get("createdAt")), (c.get("author") or {}).get("login", ""))
        for c in (pr_data.get("comments") or []) if nits.can_lift(c)
    ]
    approved_rereviews = [
        (nits.ts(r.get("submittedAt")), (r.get("author") or {}).get("login", ""))
        for r in (pr_data.get("reviews") or [])
        if r.get("state") == "APPROVED"
        and (r.get("author") or {}).get("login", "") not in nits.BOT_LOGINS
    ]
    explicit_lifts = [
        (nits.ts(c.get("createdAt")), (c.get("author") or {}).get("login", ""))
        for c in (pr_data.get("comments") or [])
        if nits.can_lift(c)
        and nits.has_marker(c.get("body", ""), nits.LIFT_MARKERS)
        and not nits.CONDITIONAL_LIFT.search(nits._strip_quoted(c.get("body", "")))
    ]
    comment_lifts = [(t, a) for (t, a) in comment_lifts if t is not None]
    explicit_lifts = [(t, a) for (t, a) in explicit_lifts if t is not None]
    approved_rereviews = [(t, a) for (t, a) in approved_rereviews if t is not None]

    rows = []
    for (t_nit, kind, author, src) in nits_signals:
        if t_nit is None or t_nit >= cutoff:
            continue
        if src == "review:CHANGES_REQUESTED":
            eligible = ([(t, a) for (t, a) in approved_rereviews if a == author]
                        + explicit_lifts)
        else:
            eligible = comment_lifts + approved_rereviews
        later = sorted(((t, a) for (t, a) in eligible if t_nit < t < cutoff),
                       key=lambda x: x[0])
        pr_author = (pr_data.get("author") or {}).get("login", "")
        if not later:
            authority, lifter, at = "UNLIFTED", None, None
        else:
            t_lift, lifter = later[0]
            at = t_lift.isoformat()
            if lifter == author:
                authority = "SELF"
            elif lifter == pr_author:
                # Le flux sain : l'auteur de la PR repond a la reserve du
                # reviewer. Borner la levee au seul auteur de la reserve
                # casserait ce parcours standard de la flotte.
                authority = "PR_AUTHOR"
            else:
                authority = "BYSTANDER"
        rows.append({"kind": kind, "author": author, "src": src,
                     "at": t_nit.isoformat(), "authority": authority,
                     "lifter": lifter, "lifted_at": at})

    # Concern 1 : occurrences de marqueur precdees de « re » nu.
    re_cited = 0
    re_cited_in_reserve = 0
    for c in (pr_data.get("comments") or []) + [
        {"body": r.get("body") or "", "author": r.get("author"),
         "createdAt": r.get("submittedAt")}
        for r in (pr_data.get("reviews") or [])
    ]:
        body = c.get("body") or ""
        if not body:
            continue
        login = (c.get("author") or {}).get("login", "")
        is_reserve = nits.classify(login, body) is not None
        normalised = nits._unaccent(body)
        for marker in nits.CONCERN_MARKERS:
            m = nits._unaccent(marker)
            start = 0
            while (i := normalised.find(m, start)) != -1:
                window = normalised[max(0, i - 30):i]
                w = window
                while w and not w[-1].isalnum():
                    w = w[:-1]
                w = w.lower()
                if w == "re" or (w.endswith("re") and not w[-3].isalnum()):
                    re_cited += 1
                    if is_reserve:
                        re_cited_in_reserve += 1
                start = i + 1

    return {"pr": pr_data.get("number"), "rows": rows,
            "re_precited": re_cited, "re_precited_in_reserve": re_cited_in_reserve}


def run(limit: int, search: str | None, per_pr_out: bool = True) -> int:
    # LIST_FIELDS + author : le role du lifter (auteur de PR vs bystander)
    # exige de connaitre l'auteur de la PR.
    cmd = ["pr", "list", "--repo", nits.REPO, "--state", "merged",
           "--limit", str(limit), "--json", nits.LIST_FIELDS + ",author"]
    if search:
        cmd += ["--search", search]
    prs = nits.gh_json(cmd)

    per_pr = []
    totals = {"SELF": 0, "PR_AUTHOR": 0, "BYSTANDER": 0, "UNLIFTED": 0}
    third_by_pair: dict[str, int] = {}  # prefixes PA/BS = PR_AUTHOR/BYSTANDER
    re_tot = {"re_precited": 0, "re_precited_in_reserve": 0}
    for p in prs:
        if not p.get("mergedAt"):
            continue
        res = measure_pr(p)
        per_pr.append(res)
        for row in res["rows"]:
            totals[row["authority"]] = totals.get(row["authority"], 0) + 1
            if row["authority"] in ("PR_AUTHOR", "BYSTANDER"):
                key = f"{row['authority'][:2]}: {row['author']} -> {row['lifter']}"
                third_by_pair[key] = third_by_pair.get(key, 0) + 1
        re_tot["re_precited"] += res["re_precited"]
        re_tot["re_precited_in_reserve"] += res["re_precited_in_reserve"]

    lifted = totals["SELF"] + totals["PR_AUTHOR"] + totals["BYSTANDER"]
    out = {
        "scanned": len(prs),
        "search": search,
        "oldest_merged": min((p["mergedAt"] for p in prs if p.get("mergedAt")),
                             default=None),
        "newest_merged": max((p["mergedAt"] for p in prs if p.get("mergedAt")),
                             default=None),
        "totals": totals,
        "third_share_of_lifted": (round(
            (totals["PR_AUTHOR"] + totals["BYSTANDER"]) / lifted, 3)
            if lifted else None),
        "bystander_share_of_lifted": (round(totals["BYSTANDER"] / lifted, 3)
                                      if lifted else None),
        "third_by_pair": dict(sorted(third_by_pair.items(),
                                     key=lambda kv: -kv[1])),
        "re_precited": re_tot,
    }
    if per_pr_out:
        out["per_pr"] = per_pr
    print(json.dumps(out, indent=1, ensure_ascii=False))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--limit", type=int, default=200,
                    help="nombre de PRs mergees a scanner")
    ap.add_argument("--search", help="filtre gh (ex: 'merged:2026-05-01..2026-07-01')")
    ap.add_argument("--no-per-pr", action="store_true",
                    help="omettre le detail par PR (resume seul)")
    args = ap.parse_args()
    return run(args.limit, args.search, per_pr_out=not args.no_per_pr)


if __name__ == "__main__":
    sys.exit(main())
