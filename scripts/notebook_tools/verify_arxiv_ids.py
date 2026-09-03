#!/usr/bin/env python3
"""Verifier les IDs arXiv via l'API arXiv et poser un verdict par ID.

Pour chaque ID : GET https://export.arxiv.org/api/query?id_list=<ID>, recupere
title/authors/published, et sort un verdict par defaut OK si l'API renvoie
un totalResults > 0. Optionnellement, on peut annoter la provenance (notebooks
ou l'ID apparait) pour le rapport final.

Garde-fou obligatoire : asserter totalResults == len(ids), sinon FAIL --
un audit qui ne distingue pas "API n'a rien repondu" de "ID n'existe pas"
est l'exact fabricant de faux ID-FANTOME que l'EPIC #11168 existe pour eviter.
"""
import argparse
import json
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

NS = {"a": "http://www.w3.org/2005/Atom"}


def query_arxiv(ids):
    """Interroge l'API arXiv pour une liste d'IDs.

    Retourne une liste de dicts {id, title, authors, published, ok, error}.
    """
    url = "https://export.arxiv.org/api/query?id_list=" + ",".join(ids)
    req = urllib.request.Request(url, headers={"User-Agent": "CoursIA-rescan/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            body = resp.read()
    except urllib.error.URLError as e:
        return [{"id": i, "ok": False, "error": f"network: {e}"} for i in ids]
    if not body:
        return [{"id": i, "ok": False, "error": "empty body (network issue?)"} for i in ids]
    try:
        root = ET.fromstring(body)
    except ET.ParseError as e:
        return [{"id": i, "ok": False, "error": f"parse: {e}"} for i in ids]
    # Validation du garde-fou : totalResults doit etre coherent
    total_results_elem = root.find(".//{http://a9.com/-/spec/opensearch/1.1/}totalResults")
    if total_results_elem is None:
        # Namespace alternativement place dans opensearch
        for ns_uri in ("http://a9.com/-/spec/opensearch/1.1/",):
            el = root.find(f".//{{{ns_uri}}}totalResults")
            if el is not None:
                total_results_elem = el
                break
    total = int(total_results_elem.text) if total_results_elem is not None else None
    if total is None:
        return [{"id": i, "ok": False, "error": "no totalResults in body"} for i in ids]
    if total != len(ids):
        return [{"id": i, "ok": False,
                 "error": f"totalResults={total} != requested={len(ids)} (garde-fou)"} for i in ids]
    # OK, on parse les entrees
    entries = root.findall("a:entry", NS)
    results = []
    for entry in entries:
        eid_full = entry.findtext("a:id", default="", namespaces=NS)
        # Strip "http://arxiv.org/abs/" prefix
        eid = re.sub(r"^https?://arxiv\.org/abs/", "", eid_full).strip()
        title = (entry.findtext("a:title", default="", namespaces=NS) or "").strip()
        title = re.sub(r"\s+", " ", title)
        authors = [a.findtext("a:name", default="", namespaces=NS).strip()
                   for a in entry.findall("a:author", NS)]
        published = entry.findtext("a:published", default="", namespaces=NS).strip()
        results.append({
            "id": eid,
            "title": title,
            "authors": authors,
            "published": published,
            "ok": True,
            "error": None,
        })
    return results


def verify_ids(ids, batch_size=10, delay=3.0):
    """Verifier une liste d'IDs par batches, avec delai entre batches."""
    all_results = []
    for i in range(0, len(ids), batch_size):
        batch = ids[i:i + batch_size]
        results = query_arxiv(batch)
        all_results.extend(results)
        if len(ids) > batch_size and i + batch_size < len(ids):
            time.sleep(delay)
    return all_results


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ids", required=True,
                    help="Liste d'IDs separes par des virgules, OU chemin d'un fichier (un ID par ligne)")
    ap.add_argument("--out", default=None, help="JSON de sortie")
    ap.add_argument("--batch-size", type=int, default=10)
    ap.add_argument("--delay", type=float, default=3.0)
    args = ap.parse_args()
    p = Path(args.ids)
    if p.exists():
        ids = [line.strip() for line in p.read_text(encoding="utf-8").splitlines()
               if line.strip() and not line.startswith("#")]
    else:
        ids = [s.strip() for s in args.ids.split(",") if s.strip()]
    print(f"[verify] {len(ids)} IDs a verifier par batches de {args.batch_size}")
    results = verify_ids(ids, batch_size=args.batch_size, delay=args.delay)
    ok = sum(1 for r in results if r.get("ok"))
    err = len(results) - ok
    print(f"[verify] {ok} OK, {err} en erreur")
    for r in results:
        if r.get("ok"):
            title = r["title"][:80] + "..." if len(r["title"]) > 80 else r["title"]
            n_auth = len(r.get("authors", []))
            year = r.get("published", "")[:4]
            print(f"  arXiv:{r['id']:>14}  ({year}, {n_auth} auth)  {title}")
        else:
            print(f"  arXiv:{r.get('id', '?'):>14}  ERROR: {r.get('error')}")
    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(
            json.dumps(results, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"[verify] -> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
