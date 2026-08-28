"""QC-research monitor : detecte les nouveaux articles quantconnect.com/research/ et seme les sous-issues.

Epic #11698 (moissonnage quantconnect.com/research/). Le mecanisme prevu par
l'Epic : chaque nouvel article = une sous-issue labellee quantconnect-research,
que les workers piochent pour lecture analytique (verdict CONSOLIDATION /
PEDAGOGIQUE / NOUVEAU / IGNORE). Sans detection du flux nouveau, l'Epic est
en deadlock : personne ne sait qu'un article est apparu.

Source : https://www.quantconnect.com/research.posts.sitemap.xml (sitemap XML
statique, ~145 articles avec <lastmod>). La page /research/ elle-meme est
JS-rendue (Algolia) et non scrapable statiquement — le sitemap est le chemin
canonique.

Comportement :
  - bootstrap (etat absent ou vide) : amorce l'etat avec TOUS les IDs actuels
    SANS creer d'issue (sinon ~145 issues d'un coup = spam). Les articles
    existants restent semables a la demande par ai-01/workers (le cron ne
    couvre que le flux NOUVEAU).
  - runs suivants : IDs absents de l'etat -> gh issue create avec le template
    docs/qc/qc-research-issue-template.md prerempli (URL + titre), cap --max-issues
    par run (defaut 5), etat mis a jour uniquement pour les IDs reellement
    semes (un echec de creation laisse l'ID hors etat -> retente au run suivant).
  - dedup contre les issues EXISTANTES du label avant toute creation : l'etat
    JSON n'est la verite que s'il a ete commitE. Un semis reussi suivi d'un
    echec de commit d'etat (run 32690576863 : push rejete fetch-first apres
    3h33 de queue runner sur un main a ~65 merges/jour) laisserait l'ID hors
    etat et le run suivant re-semerait l'article en double. Une issue
    existante rattape l'etat sans creer.

Usage :
  python scripts/notebook_tools/qc_research_monitor.py --dry-run
  python scripts/notebook_tools/qc_research_monitor.py            # GH_TOKEN requis hors dry-run
  python scripts/notebook_tools/qc_research_monitor.py --max-issues 3
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.request
from pathlib import Path

SITEMAP_URL = "https://www.quantconnect.com/research.posts.sitemap.xml"
STATE_PATH = Path("docs/qc/qc-research-seeded.json")
TEMPLATE_PATH = Path("docs/qc/qc-research-issue-template.md")
LABEL = "quantconnect-research"
USER_AGENT = "CoursIA-qc-research-monitor/1.0 (github.com/jsboige/CoursIA #11698)"
ARTICLE_RE = re.compile(r"/research/(\d+)/([a-z0-9-]+)/")


def fetch_sitemap(url: str) -> str:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return resp.read().decode("utf-8", errors="replace")


def parse_articles(xml: str) -> list[dict]:
    """Extrait (id, slug, url, lastmod) des entrees /research/<id>/<slug>/ du sitemap.

    Les entrees forum/list/* sont ignorees (listings, pas des articles).
    Tri par id decroissant = ordre chronologique decroissant (QC utilise des
    IDs de forum croissants dans le temps).
    """
    entries = []
    for m in re.finditer(
        r"<loc>([^<]+)</loc>\s*(?:<lastmod>([^<]+)</lastmod>)?", xml
    ):
        url, lastmod = m.group(1).strip(), (m.group(2) or "").strip()
        am = ARTICLE_RE.search(url)
        if not am:
            continue
        entries.append(
            {
                "id": int(am.group(1)),
                "slug": am.group(2),
                "url": url,
                "lastmod": lastmod,
            }
        )
    entries.sort(key=lambda e: -e["id"])
    return entries


def load_state(path: Path) -> dict:
    if path.exists():
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("seeded"):
            return data
    return {"seeded": {}}


def title_from_slug(slug: str) -> str:
    return slug.replace("-", " ").strip().capitalize()


def list_seeded_issues(dry_run: bool) -> list[dict]:
    """Issues du label (tous etats) pour la dedup. Best-effort : un echec gh
    (token absent en dry-run local, API indisponible) rend [] et le run garde
    le comportement pre-dedup plutôt que d'echouer pour un garde optionnel."""
    proc = subprocess.run(
        ["gh", "issue", "list", "--label", LABEL, "--state", "all",
         "--json", "number,title", "--limit", "300"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        if not dry_run:
            print(f"[WARN] echec gh issue list (dedup sautee) : {proc.stderr.strip()}",
                  file=sys.stderr)
        return []
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return []


def find_existing_issue(articles: list[dict], known: list[dict]) -> dict[int, int]:
    """Map article_id -> issue number pour les articles deja semees.

    Le suffixe du titre "(#<article_id>)" pose par create_issue est
    deterministe : c'est la cle de jointure etat <-> issues.
    """
    by_id: dict[int, int] = {}
    for row in known:
        m = re.search(r"\(#(\d+)\)$", (row.get("title") or "").strip())
        if m:
            by_id[int(m.group(1))] = int(row["number"])
    return by_id


def issue_body(article: dict) -> str:
    # Un template introuvable est une erreur de config (chemin deplace), pas un
    # cas nominal : produire un corps vide en silence semerait des issues vides
    # pendant des semaines avant que quelqu'un n'en lise une. Fail loud.
    if not TEMPLATE_PATH.is_file():
        raise FileNotFoundError(
            f"template introuvable : {TEMPLATE_PATH} — verifier le chemin "
            f"(le template vit sous docs/qc/)"
        )
    template = TEMPLATE_PATH.read_text(encoding="utf-8", errors="replace")
    # retirer les commentaires de mode d'emploi du template s'il en embarque
    template = re.sub(r"<!--.*?-->", "", template, flags=re.DOTALL)
    header = (
        f"## Article source\n"
        f"- URL : {article['url']}\n"
        f"- Slug : {article['slug']} (ID QC {article['id']})\n"
        f"- lastmod sitemap : {article['lastmod'] or 'n/a'}\n"
        f"- Auteur(s) : a verifier sur la page (ne jamais cru sans verifier)\n"
        f"- Catégorie putative : a determiner (alpha / framework / ML / RL / factor / vol / risk / pedagogy)\n"
        f"- Date de publication : a verifier sur la page\n\n"
        f"*(Sous-issue semee automatiquement par qc-research-monitor, Epic #11698. "
        f"Completer la lecture analytique selon le template ci-dessous.)*\n\n---\n\n"
    )
    return header + template


def create_issue(article: dict, dry_run: bool) -> int | None:
    title = f"[QC-research] {title_from_slug(article['slug'])} (#{article['id']})"
    if dry_run:
        print(f"[dry-run] gh issue create : {title}")
        return None
    proc = subprocess.run(
        [
            "gh", "issue", "create",
            "--title", title,
            "--body", issue_body(article),
            "--label", LABEL,
        ],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        print(f"[WARN] echec gh issue create pour {article['id']}: {proc.stderr.strip()}", file=sys.stderr)
        return None
    out = proc.stdout.strip()
    m = re.search(r"/issues/(\d+)$", out)
    return int(m.group(1)) if m else None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dry-run", action="store_true",
                    help="ne cree aucune issue, n'ecrit pas l'etat")
    ap.add_argument("--max-issues", type=int, default=5,
                    help="cap de sous-issues creees par run (defaut 5, anti-spam)")
    args = ap.parse_args()

    xml = fetch_sitemap(SITEMAP_URL)
    articles = parse_articles(xml)
    if not articles:
        print("FAIL : 0 article extrait du sitemap (format change ?)", file=sys.stderr)
        return 2

    state = load_state(STATE_PATH)
    seeded: dict[str, dict] = state["seeded"]
    bootstrap = not seeded
    fresh = [a for a in articles if str(a["id"]) not in seeded]

    # Garde precoce : en mode flux, un template introuvable doit arreter le run
    # AVANT la premiere creation d'issue (sinon des issues a corps vide sont
    # semees et l'etat les marque semees — defaut decouvert en review #12036).
    if not bootstrap and fresh and not args.dry_run and not TEMPLATE_PATH.is_file():
        print(f"FAIL : template introuvable : {TEMPLATE_PATH} "
              f"(chemin deplace ?) — aucun semis n'a eu lieu", file=sys.stderr)
        return 2

    print(f"sitemap : {len(articles)} articles ; etat : {len(seeded)} semes ; "
          f"nouveaux : {len(fresh)} ; mode : {'BOOTSTRAP' if bootstrap else 'flux'}")

    if bootstrap:
        # Amorce silencieuse : tout le stock existant est marque connu, 0 issue.
        for a in articles:
            seeded[str(a["id"])] = {"url": a["url"], "lastmod": a["lastmod"],
                                    "seeded_at": None, "issue": None}
        print(f"bootstrap : {len(seeded)} IDs amortces, 0 issue creee "
              f"(les articles existants restent semables a la demande)")
    else:
        dedup = find_existing_issue(articles, list_seeded_issues(args.dry_run))
        created = 0
        for a in fresh:
            existing = dedup.get(a["id"])
            if existing is not None:
                seeded[str(a["id"])] = {"url": a["url"], "lastmod": a["lastmod"],
                                        "seeded_at": None, "issue": existing}
                print(f"dedup : article {a['id']} deja seme en #{existing} "
                      f"— etat rattrape, pas de nouvelle issue")
                continue
            if created >= args.max_issues:
                print(f"cap --max-issues={args.max_issues} atteint ; "
                      f"{len(fresh) - created} restent pour les runs suivants")
                break
            num = create_issue(a, args.dry_run)
            if num or args.dry_run:
                seeded[str(a["id"])] = {"url": a["url"], "lastmod": a["lastmod"],
                                        "seeded_at": None, "issue": num}
                created += 1

    if not args.dry_run:
        STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
        STATE_PATH.write_text(
            json.dumps(state, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
        print(f"etat ecrit : {STATE_PATH} ({len(seeded)} IDs)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
