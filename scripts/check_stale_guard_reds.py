#!/usr/bin/env python3
"""Signal les PR ouvertes dont un rouge date d'une base ANTERIEURE au fix de son garde.

Pourquoi cet organe existe (#13321)
-----------------------------------
Onze PR ouvertes (#13156 #13167 #13168 #13169 #13172 #13177 #13181 #13183
#13191 #13203 #13204 -- plancher mesure sur un tiers du pool) portaient un rouge
`Scripts Tests (CPU)` sur une assertion qui N'EXISTE PLUS sur main : le test
`test_current_repository_has_explicit_zero_self_hosted_baseline` a ete renomme
par 62d47eb7d (#13148) le 2026-08-27T08:53Z, et TOUS les rouges de la bande
precedent ce correctif de 2 h 43 au minimum.

`pr-gate-stale-sweep.yml` rafraichit les verdicts perimes, mais sa semantique
est bornee aux PR ou « aucun rouge hormis PR gate lui-meme ». Une PR rouge sur
un AUTRE garde corrige depuis n'est JAMAIS reexaminee : elle reste BLOCKED
jusqu'a ce qu'un humain la date a la main.

La distinction mecanique que cet organe encode :
  `gh run rerun`        rejoue la BASE GELEE  -> il rend le MEME rouge ;
  `gh pr update-branch` recalcule la base    -> seul remede.

Comment il date le rouge (criterion 1)
--------------------------------------
PAS par `completedAt` (horodatage du run, muet sur CE QUE le run a teste) et
PAS par le `merge_commit_sha` COURANT de la PR -- mesure 2026-08-28 sur
#13156 : GitHub RECALCULE la merge-ref quand main bouge, meme sans push sur la
PR (head du 2026-08-26T18:47, run rouge 21:59, fix 62d47eb7d 2026-08-27T08:53,
et pourtant le parent du merge_commit_sha courant CONTIENT le fix -- la base
courante n'est pas la base testee).

Seconde decouverte d'instrument (mesure 2026-08-28 au dry-run, #13156) :
`run.head_sha` d'un run `pull_request` (GET /actions/runs/{id}, id extrait de
details_url) est la TETE DE PR, PAS le merge commit -- le premier parent du head
n'est donc PAS la base testee. L'ancre juste est un champ du run EMBARQUE a sa
creation : `run.pull_requests[0].base.sha` = la base de la PR enregistree au
moment du run. Un objet run est IMMUABLE : ce champ ne derive pas quand main
bouge. Le rouge est « perime » ssi cette base ne CONTIENT PAS le commit qui a
rendu le garde vert sur main -- une relation d'ancestre, pas une comparaison
d'horodatages : immune au clock skew et aux runs rejoues.

Cas ecarte nommement : un run `push` (branche seule, pas de merge) n'a teste
AUCUNE base -- indatable, exclusion nommee. Angle mort borne (declare honnete) :
`pulls[].base.sha` reste inactif jusqu'a un sync de la PR ; une PR ouverte AVANT
le fix mais dont un run tournerait APRES le fix contre main courant verrait son
snapshot sous-estimer la vraie base et prescrire update-branch -- remede
idempotent et auto-correcteur, qui reconstruit le merge sur main courant.

Localisation du fix (generique, AUCUN mappage nom de test -> fichier) :
  1. le check rouge porte `details_url` -> run_id -> workflow du run emetteur ;
  2. l'historique des runs de CE workflow sur `main` donne, par run, le verdict
     du check de meme nom (attribution par run_id dans details_url, comme le
     fold du sweep PR gate -- #11808) ;
  3. la transition rouge->vert la plus recente localise le fix : `fix_head` =
     head_sha du premier run VERT apres le dernier run ROUGE ;
  4. rouge perime ssi : check vert sur main a SA VERSION COURANTE (dernier run)
     ET `fix_head` n'est PAS ancetre de la base de la PR.

Controle positif (criterion 4) : si la base CONTIENT deja `fix_head`, le rouge
a ete rendu CONTRE le garde corrige -- c'est un vrai defaut, il n'est PAS
signale. Un organe qui blanchirait toute la classe serait pire que rien.

S'il n'y a AUCUNE transition rouge->vert dans la fenetre (garde vert de tout
temps sur main), le rouge est vraisemblablement propre a la PR : non signale,
exclusion nommee. Conservateur par construction.

Sortie : advisory. `--apply` pose le label `stale-guard-red` + un commentaire
par PR (dedupe par label). Il ne rebase JAMAIS, ne rerun JAMAIS, exit 0 toujours.

    python scripts/check_stale_guard_reds.py [--json]
    python scripts/check_stale_guard_reds.py --apply --max-posts 8
    python scripts/check_stale_guard_reds.py --from-json replay.json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from typing import Callable

LABEL = "stale-guard-red"
# Meme asymetrie que pr-gate-stale-sweep.yml : neutral/skipped ne rougissent
# pas un rollup ; cancelled/stale/action_required sont des etats sans verdict.
# RED = verdict RENDU d_echec. "cancelled" (cancel-storm par concurrency, frequent
# ici) et "action_required" (case a cocher, ex. env) ne sont PAS des echecs du
# garde : les inclure fabriquerait des faux rouges. cf #13156 (cancel-storms).
RED = {"failure", "timed_out"}
GREEN = {"success", "neutral", "skipped"}
# Le rouge `PR gate` a SON sweep (pr-gate-stale-sweep.yml) : le traiter ici
# ferait deux organes sur la meme classe.
EXCLUDED_CHECKS = {"PR gate"}
# Fenetre d'historique des runs du garde sur main : il faut voir la transition
# rouge->vert. Mesure 2026-08-28 (#13321) : a ~65 pushes/jour sur main, une
# fenetre de 30 runs couvre ~11 h -- le fix 62d47eb7d du garde Scripts Tests
# datait de 24 h et la transition etait DEJA sortie de fenetre, la bande
# fondatrice (#13156...) passait en exclusion "aucune transition". 120 runs
# couvre ~2 jours de cadence soutenue. Cout borne : un call check-runs par run
# (cache par sha), uniquement pour les workflows emettant un rouge.
MAIN_RUNS_WINDOW = 120


def _run_gh(args: list[str]) -> str:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args[:3])}... -> {proc.returncode}: {proc.stderr[:200]}")
    return proc.stdout


def _fold_key(check: dict) -> tuple[str, str]:
    """(run_id, name) -- JAMAIS le nom seul (#11808) : plusieurs workflows
    emettent des jobs de meme nom ; le run_id vient de details_url."""
    m = re.search(r"/runs/(\d+)/", check.get("details_url") or "")
    return (m.group(1) if m else "unattributed", check.get("name") or "?")


def collect(repo: str) -> dict:
    """Collecte les donnees brutes via gh (reseau). analyse() reste pure."""
    prs = []
    for line in _run_gh(["api", f"repos/{repo}/pulls?state=open&base=main&per_page=100",
                         "--paginate", "--jq",
                         ".[] | {number, draft, merge_commit_sha, "
                         "head_sha: .head.sha, fork: .head.repo.fork}"]).splitlines():
        if line.strip():
            prs.append(json.loads(line))

    checks_cache: dict[str, list] = {}
    wf_cache: dict[int, dict] = {}
    run_base_cache: dict[str, dict] = {}

    def checks_on(sha: str) -> list:
        if sha not in checks_cache:
            out = _run_gh(["api", f"repos/{repo}/commits/{sha}/check-runs?per_page=100",
                           "--jq", ".check_runs[] | {name, status, conclusion, details_url}"])
            checks_cache[sha] = [json.loads(l) for l in out.splitlines() if l.strip()]
        return checks_cache[sha]

    def tested_base(run_id: str):
        """Base main GEELEE que CE run a testee, ou None si saturee.

        Decouverte d_instrument au dry-run reel (#13156) : run.head_sha d_un run
        pull_request est la TETE DE PR, PAS le merge commit -- le parent du head
        n_est donc PAS la base testee. L_ancre juste est le snapshot embarque dans
        l_objet run (immuable) : run.pull_requests[0].base.sha = la base enregistree
        au moment du run, qui ne derive pas quand main bouge. Un run push-event
        teste la branche seule : aucune base de merge.

        Angle mort borne : pulls[].base.sha est un champ du PR laisse inactif
        jusqu_a un sync -- PR ouverte AVANT le fix mais run APRES le fix contre
        main courant => snapshot sous-estime la vraie base et peut prescrire
        update-branch (remede idempotent et auto-correcteur). """
        if run_id not in run_base_cache:
            try:
                r = json.loads(_run_gh(["api", f"repos/{repo}/actions/runs/{run_id}",
                                        "--jq",
                                        "{event: .event, base: (.pull_requests[0].base.sha // \"\")}"]))
            except RuntimeError:
                r = {}
            run_base_cache[run_id] = r
        r = run_base_cache[run_id]
        if not r:
            return None
        if (r.get("event") or "") != "pull_request":
            return None  # run push-event sur la branche : aucune base merge testee
        return r.get("base") or None

    def main_history(run_id: str) -> dict:
        """Runs main du workflow emetteur + verdict du check par run_id."""
        run = json.loads(_run_gh(["api", f"repos/{repo}/actions/runs/{run_id}",
                                  "--jq", "{workflow_id}"]))
        wf = run["workflow_id"]
        if wf in wf_cache:
            return wf_cache[wf]
        out = _run_gh(["api", f"repos/{repo}/actions/workflows/{wf}/runs?branch=main"
                         f"&per_page={MAIN_RUNS_WINDOW}",
                         "--jq", ".workflow_runs[] | {id, head_sha}"])
        runs = [json.loads(l) for l in out.splitlines() if l.strip()]  # recent d'abord
        history = wf_cache[wf] = {"runs": runs, "check_by_run": {}}
        for r in runs:
            for c in checks_on(r["head_sha"]):
                if f"/runs/{r['id']}/" in (c.get("details_url") or ""):
                    by_name = history["check_by_run"].setdefault(r["id"], {})
                    by_name[c.get("name") or "?"] = {
                        "conclusion": c.get("conclusion"), "status": c.get("status")}
        return history

    out_prs = []
    for pr in prs:
        checks = checks_on(pr["head_sha"])
        red_runs = sorted({m.group(1) for c in checks
                           if (c.get("conclusion") or "") in RED
                           and c.get("name") not in EXCLUDED_CHECKS
                           and (m := re.search(r"/runs/(\d+)/", c.get("details_url") or ""))})
        entry = {**pr, "checks": checks, "main_histories": {}, "tested_bases": {}}
        # Un historique PAR workflow emetteur de rouge (les rouges d'une PR
        # peuvent venir de gardes distincts) ; le cache deduplique par workflow.
        # tested_bases : par run rouge, la base main GELEE que CE run a testee
        # (merge-ref au moment du run -- pas la merge-ref courante, qui derive).
        for rid in red_runs:
            try:
                entry["main_histories"][rid] = main_history(rid)
            except RuntimeError as e:
                entry["main_histories"][rid] = {"error": str(e)}
            entry["tested_bases"][rid] = tested_base(rid)
        out_prs.append(entry)
    return {"prs": out_prs}


def locate_fix_head(history: dict, check_name: str) -> tuple[str, str | None]:
    """(statut du garde sur main, head_sha du commit qui l'a rendu vert).

    statut : "green" (vert a sa version courante), "red_on_main" (rouge au
    dernier run : vrai probleme), "absent_on_main" (le check ne tourne jamais
    sur main, p.ex. garde pull_request-only : indatable).

    Marche les runs main du plus recent au plus ancien. `fix_head` = head du
    premier run VERT qui suit (dans le temps) un run ROUGE. Aucune transition
    dans la fenetre -> (green, None) : pas de preuve de fix, non signale
    (conservateur : un garde vert de tout temps rend le rouge propre a la PR).
    """
    runs = history.get("runs") or []
    verdicts = []
    for r in runs:  # recent d'abord
        c = (history.get("check_by_run") or {}).get(r["id"], {}).get(check_name)
        if not c or (c.get("status") or "") != "completed":
            continue
        concl = c.get("conclusion") or ""
        verdicts.append((concl in GREEN, concl in RED, r["head_sha"]))
    if not verdicts:
        return "absent_on_main", None
    current_green = verdicts[0][0]
    fix_head = None
    for i, (green, _red, sha) in enumerate(verdicts):
        if green and i + 1 < len(verdicts) and verdicts[i + 1][1]:
            fix_head = sha  # vert immediatement precede d'un rouge (plus ancien)
            break
    return ("green" if current_green else "red_on_main"), fix_head


def is_ancestor_status(status: str | None) -> bool:
    """compare/a...b status == 'ahead' => b est en avance sur a => a ancetre de b."""
    return status == "ahead"


def analyse(data: dict, compare_fn: Callable[[str, str], str | None]) -> dict:
    """Pure : data = sortie de collect() ; compare_fn(fix_head, base) -> status
    de compare/fix_head...base ('ahead' = fix ancetre de base). Seam de test :
    on injecte un dict ; en production, un appel REST cache.
    """
    flagged, excluded = [], []
    for pr in data.get("prs") or []:
        num = pr.get("number")
        if pr.get("draft"):
            excluded.append({"pr": num, "reason": "draft"}); continue
        if pr.get("fork"):
            excluded.append({"pr": num, "reason": "fork (update-branch indisponible)"}); continue
        # fold (run_id, name) latest-wins sur les COMPLETED : une tentative
        # supersedee du meme workflow ne compte plus (#11808).
        latest: dict[tuple[str, str], dict] = {}
        for c in pr.get("checks") or []:
            if (c.get("status") or "") != "completed":
                continue
            key = _fold_key(c)
            cur = latest.get(key)
            if cur is None or (c.get("details_url") or "") >= (cur.get("details_url") or ""):
                latest[key] = c
        reds = [(key, c) for key, c in latest.items()
                if (c.get("conclusion") or "") in RED and key[1] not in EXCLUDED_CHECKS]
        if not reds:
            continue  # pas de rouge hors PR gate : hors scope
        # Disjointness avec pr-gate-stale-sweep.yml : un vert de MEME nom pose sur
        # la MEME tete par un AUTRE run prouve que le garde PASSE a cette base --
        # le rouge est un flake, son remede est `gh run rerun` (rejouer la meme
        # base), pas update-branch. Le prescrire ici serait la fausse piste
        # exacte que le criterion 3 interdit.
        # un vert de MEME nom sur la MEME base GEEELEE (meme conditions testees)
        # prouve que le garde passe a cette base : le rouge est un flake, remede
        # `gh run rerun`, pas update-branch. Un vert de meme nom mais d_une base
        # AUTRE (p.ex. post-fix) n_est PAS un flake : c_est la signature du rouge
        # perime (le merge-ref recent passe, celui teste par le run rouge non).
        green_bases = {}
        for k, c in latest.items():
            if (c.get("conclusion") or "") in GREEN:
                mid = re.search(r"/runs/(\d+)/", c.get("details_url") or "")
                gbase = (pr.get("tested_bases") or {}).get(mid.group(1)) if mid else None
                green_bases[k[1]] = gbase
        new_reds = []
        for k, c in reds:
            m = re.search(r"/runs/(\d+)/", c.get("details_url") or "")
            rbase = (pr.get("tested_bases") or {}).get(m.group(1)) if m else None
            if k[1] in green_bases and green_bases[k[1]] == rbase and rbase is not None:
                excluded.append({"pr": num, "check": k[1],
                                 "reason": "vert coexistant du meme nom sur la meme base "
                                           "gelee (flake) : voie gh run rerun, cf "
                                           "pr-gate-stale-sweep"})
            else:
                new_reds.append((k, c))
        reds = new_reds
        if not reds:
            continue
        for key, c in reds:
            name = key[1]
            m = re.search(r"/runs/(\d+)/", c.get("details_url") or "")
            rid = m.group(1) if m else ""
            # base GELEE testee par CE run (criterion 1) -- pas la merge-ref
            # courante de la PR, que GitHub recalcule quand main bouge.
            base = (pr.get("tested_bases") or {}).get(rid)
            if not base:
                excluded.append({"pr": num, "check": name,
                                 "reason": "base testee indisponible (run push-event sur la branche, "
                                           "ou run sans snapshot de merge : indatable"}); continue
            hist = (pr.get("main_histories") or {}).get(rid, {})
            if hist.get("error"):
                excluded.append({"pr": num, "check": name,
                                 "reason": f"historique main injoignable: {hist['error'][:80]}"}); continue
            status, fix_head = locate_fix_head(hist, name)
            if status == "red_on_main":
                excluded.append({"pr": num, "check": name,
                                 "reason": "garde rouge sur main a sa version courante "
                                           "(vrai probleme, pas un rouge perime)"}); continue
            if status == "absent_on_main":
                excluded.append({"pr": num, "check": name,
                                 "reason": "le check ne tourne jamais sur main (garde "
                                           "pull_request-only ?) : indatable, non signale"}); continue
            if fix_head is None:
                excluded.append({"pr": num, "check": name,
                                 "reason": "aucune transition rouge->vert sur main dans la "
                                           "fenetre : rouge vraisemblablement propre a la PR"}); continue
            status = compare_fn(fix_head, base)
            if status is None:
                excluded.append({"pr": num, "check": name,
                                 "reason": f"compare indisponible ({fix_head[:8]}...{base[:8]})"}); continue
            if is_ancestor_status(status):
                # CONTROLE POSITIF (criterion 4) : la base CONTIENT deja le fix.
                # Le rouge a ete rendu contre le garde corrige : vrai defaut.
                excluded.append({"pr": num, "check": name,
                                 "reason": f"base {base[:8]} POSTERIEURE au fix {fix_head[:8]} "
                                           ": vrai defaut, ne pas signaler"}); continue
            flagged.append({
                "pr": num, "check": name, "merge_base": base, "fix_head": fix_head,
                "remedy": "update-branch",
                "why_not_rerun": (f"gh run rerun rejouerait la base gelee {base[:8]} "
                                  f"(le fix {fix_head[:8]} n'y est PAS) et rendrait le meme "
                                  "rouge ; seul gh pr update-branch recalcule la base"),
            })
    n = len(data.get("prs") or [])
    return {
        "examined": n,
        "denominator": {"examined": n, "flagged": len(flagged), "excluded": len(excluded)},
        "flagged": flagged,
        "excluded": excluded,
        "label": LABEL,
    }


def apply(repo: str, result: dict, max_posts: int) -> None:
    """Pose label + commentaire, dedupe par label. Advisory : n'echoue jamais."""
    try:
        _run_gh(["label", "create", LABEL, "--repo", repo, "--color", "BFD4F2",
                 "--description",
                 "Rouge datant d'une base anterieure au fix du garde (sweep #13321)"])
    except RuntimeError:
        pass  # existe deja : normal
    for f in result["flagged"][:max_posts]:
        try:
            labeled = _run_gh(["pr", "view", str(f["pr"]), "--repo", repo, "--json",
                               "labels", "--jq",
                               '[.labels[].name] | index("stale-guard-red") != null']).strip()
            if labeled == "true":
                print(f"[stale-guard-red] #{f['pr']}: label deja pose, skip")
                continue
            body = (f"[{LABEL}] `{f['check']}` -- rouge date de la base "
                    f"`{f['merge_base'][:12]}`, ANTERIEURE au fix `{f['fix_head'][:12]}` "
                    f"du garde sur main (garde vert a sa version courante).\n"
                    f"Remede : `gh pr update-branch {f['pr']}` (recalcule la base). "
                    f"NE PAS `gh run rerun` : {f['why_not_rerun']}.")
            _run_gh(["pr", "comment", str(f["pr"]), "--repo", repo, "--body", body])
            _run_gh(["pr", "edit", str(f["pr"]), "--repo", repo, "--add-label", LABEL])
            print(f"[stale-guard-red] #{f['pr']}: signale ({f['check']})")
        except RuntimeError as e:
            print(f"[stale-guard-red] #{f['pr']}: echec non fatal ({e})", file=sys.stderr)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default="jsboige/CoursIA")
    ap.add_argument("--from-json", help="rejeu d'une collecte (--dump)")
    ap.add_argument("--dump", help="ecrit la collecte + compares pour rejeu")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--apply", action="store_true",
                    help="pose label + commentaire (defaut : lecture seule)")
    ap.add_argument("--max-posts", type=int, default=8)
    args = ap.parse_args()

    recorded: dict[tuple[str, str], str] = {}

    def compare_fn(a: str, b: str) -> str | None:
        if (a, b) in recorded:
            return recorded[(a, b)]
        try:
            # --jq .status emet une CHAINE NUE ("behind"), pas du JSON :
            # json.loads dessus renvoie ValueError et faisait rendre None a
            # chaque compare (mesure #13156 au v4 : compare OK via l'API brute).
            status = _run_gh(["api", f"repos/{args.repo}/compare/{a}...{b}",
                              "--jq", ".status"]).strip().strip('"')
            recorded[(a, b)] = status
            return status
        except (RuntimeError, ValueError):
            # 404 (pas d'ancetre commun), sortie non-JSON, timeout : le verdict
            # manque -> analyse() exclut nomme "compare indisponible". Un
            # compare rate-limite ne doit pas tuer le sweep entier.
            return None

    if args.from_json:
        payload = json.load(open(args.from_json, encoding="utf-8"))
        data, recorded = payload["data"], {tuple(k): v for k, v in payload["compares"].items()}
        def replay_fn(a: str, b: str) -> str | None:
            return recorded.get((a, b))
        result = analyse(data, replay_fn)
    else:
        data = collect(args.repo)
        result = analyse(data, compare_fn)

    if args.dump:
        json.dump({"data": data, "compares": {f"{a}|{b}": s for (a, b), s in recorded.items()}},
                  open(args.dump, "w", encoding="utf-8"), indent=1, ensure_ascii=False)

    if args.json:
        print(json.dumps(result, indent=1, ensure_ascii=False))
    else:
        print(f"[stale-guard-red] PR examinees: {result['examined']} "
              f"(denominateur: ouvertes examinees) | signalees: {len(result['flagged'])} "
              f"| exclues: {len(result['excluded'])}")
        for f in result["flagged"]:
            print(f"  #{f['pr']} {f['check']} base={f['merge_base'][:8]} "
                  f"fix={f['fix_head'][:8]} -> {f['remedy']}")
        for e in result["excluded"]:
            print(f"  #{e['pr']} exclu: {e.get('check', '')} {e['reason']}", file=sys.stderr)
    if args.apply:
        apply(args.repo, result, args.max_posts)
    return 0  # advisory : ne bloque jamais


if __name__ == "__main__":
    sys.exit(main())
