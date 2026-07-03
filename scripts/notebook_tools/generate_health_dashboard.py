#!/usr/bin/env python3
"""#4210 acceptance #4 — derive a public health dashboard from COURSE_CATALOG.generated.json.
Snapshot doc (generated, not hand-maintained). Mirrors docs/archive/qc-strategies-status.md precedent.
Read-only generator -> writes docs/reference/HEALTH_DASHBOARD.md."""
import json, pathlib, collections, datetime

CAT = pathlib.Path("COURSE_CATALOG.generated.json")
OUT = pathlib.Path("docs/reference/HEALTH_DASHBOARD.md")

d = json.loads(CAT.read_text(encoding="utf-8"))
assert isinstance(d, list) and d, "catalog must be a non-empty list"

# Today date from last_validation max (catalogue-derived, not Date.now which is forbidden in some contexts)
dates = [x.get("last_validation","") for x in d if x.get("last_validation")]
snapshot_date = max(dates) if dates else "n/a"

# Global aggregates
status_global = collections.Counter(x.get("status","?") for x in d)
maturity_global = collections.Counter(x.get("maturity","?") for x in d)
kernel_global = collections.Counter(x.get("kernel","?") for x in d)

# Requirement badges (acceptance #2 feed): local-executable vs needs-GPU/cloud/wsl
req_gpu = sum(1 for x in d if x.get("requires_gpu"))
req_cloud = sum(1 for x in d if x.get("requires_cloud"))
req_wsl = sum(1 for x in d if x.get("requires_wsl"))
req_api = sum(1 for x in d if x.get("requires_api"))
local_exec = sum(1 for x in d if x.get("executable_locally"))

# Per-serie breakdown
series = collections.defaultdict(lambda: collections.Counter())
for x in d:
    s = x.get("serie","?")
    series[s][x.get("status","?")] += 1

# BROKEN detail (actionable)
broken = [x for x in d if x.get("status")=="BROKEN"]

lines = []
a = lines.append
a("# Tableau de santé du dépôt — snapshot dérivé du catalogue")
a("")
a(f"> Snapshot statique généré depuis `COURSE_CATALOG.generated.json` (date catalogue : **{snapshot_date}**).")
a("> Ce fichier **n'est pas maintenu à la main** : il est dérivé du catalogue (acceptance #4 de #4210).")
a("> Pour le régénérer : `python scripts/notebook_tools/generate_health_dashboard.py`.")
a("")
a(f"**{len(d)}** notebooks référencés au catalogue.")
a("")
a("## État global")
a("")
a("| Statut | Count | % |")
a("|--------|-------|---|")
for st in ["READY","DEMO","BROKEN"]:
    n = status_global.get(st,0)
    a(f"| {st} | {n} | {100*n/len(d):.1f}% |")
a("")
a("## Exigences d'environnement (badges)")
a("")
a("| Exigence | Notebooks concernés |")
a("|----------|---------------------|")
a(f"| **local** (exécutable sans GPU/cloud/WSL) | {local_exec} |")
a(f"| WSL requis | {req_wsl} |")
a(f"| GPU requis | {req_gpu} |")
a(f"| Cloud requis (QC / GenAI Docker) | {req_cloud} |")
a(f"| API key requise | {req_api} |")
a("")
a("## Distribution par série")
a("")
a("| Série | READY | DEMO | BROKEN | Total | % READY |")
a("|-------|-------|------|--------|-------|---------|")
for s in sorted(series):
    c = series[s]
    total = sum(c.values())
    rdy = c.get("READY",0)
    pct = 100*rdy/total if total else 0
    a(f"| {s} | {rdy} | {c.get('DEMO',0)} | {c.get('BROKEN',0)} | {total} | {pct:.0f}% |")
a("")
a("## Kernels")
a("")
a("| Kernel | Count |")
a("|--------|-------|")
for k,n in kernel_global.most_common():
    a(f"| {k} | {n} |")
a("")
if broken:
    a(f"## BROKEN ({len(broken)} — à traiter en priorité)")
    a("")
    a("| Série | Notebook | Maturité | Dernière validation |")
    a("|-------|----------|----------|---------------------|")
    for x in broken:
        a(f"| {x.get('serie','?')} | {x.get('title','?')} | {x.get('maturity','?')} | {x.get('last_validation','?')} |")
    a("")
a("## Voir aussi")
a("")
a("- [Catalogue source](../../COURSE_CATALOG.generated.md) — données brutes régénérées par `catalog-cron.yml`.")
a("- See #4210 (onboarding/packaging, acceptance #4).")
a("- See #4208 (CoursIA → référence publique).")
a("")

OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text("\n".join(lines), encoding="utf-8")
print(f"=== wrote {OUT} ({OUT.stat().st_size} bytes, {len(lines)} lines) ===")
print(f"total notebooks: {len(d)} | READY {status_global.get('READY',0)} DEMO {status_global.get('DEMO',0)} BROKEN {status_global.get('BROKEN',0)}")
