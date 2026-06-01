"""P0 — Narrative Research via SearXNG + LLM synthesis.

Builds narrative_context.json: structured knowledge base about
"Boule de Suif" that feeds every downstream LLM call.

Steps:
1. SearXNG targeted searches (6 queries)
2. LLM selection of best sources
3. Deep reading via web_url_read
4. LLM synthesis into NarrativeContext

Output: outputs/narrative_context.json
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv

from .schemas import (
    NarrativeContext, CharacterProfile, ActDefinition,
    SourceSelection, SourceSelectionItem,
)
from .llm_client import call_structured

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
OUTPUTS.mkdir(exist_ok=True)

SOURCE_TEXT = Path(__file__).parent.parent / "boule_de_suif_full.txt"

SEARCH_QUERIES = [
    "Boule de Suif Maupassant analyse personnages",
    "Boule de Suif analyse thematique hypocrisie classe sociale",
    "Boule de Suif structure narrative progression dramatique",
    "Guerre franco-prussienne 1870 Normandie occupation contexte historique",
    "Boule de Suif prosodie lecture expressive voix narrateur",
    "Boule de Suif Maupassant ironie narration style",
]


def run_searxng_searches() -> list[dict]:
    """Run 6 targeted SearXNG queries and collect results."""
    try:
        from mcp_searxng import searxng_web_search
    except ImportError:
        print("[P0] mcp_searxng not available, using requests fallback")
        return _search_via_requests()

    all_results = []
    for query in SEARCH_QUERIES:
        print(f"  [P0] Searching: {query}")
        try:
            results = searxng_web_search(query=query, pageno=1, language="fr")
            for r in results[:10]:
                all_results.append({
                    "query": query,
                    "title": r.get("title", ""),
                    "url": r.get("url", ""),
                    "snippet": r.get("content", ""),
                })
        except Exception as e:
            print(f"  [P0] Search error for '{query}': {e}")
    return all_results


def _search_via_requests() -> list[dict]:
    """Fallback: search via direct HTTP to SearXNG instance."""
    import requests

    searxng_url = "https://search.myia.io"
    all_results = []
    for query in SEARCH_QUERIES:
        print(f"  [P0] Searching: {query}")
        try:
            resp = requests.get(
                f"{searxng_url}/search",
                params={"q": query, "format": "json", "language": "fr"},
                timeout=30,
            )
            resp.raise_for_status()
            data = resp.json()
            for r in data.get("results", [])[:10]:
                all_results.append({
                    "query": query,
                    "title": r.get("title", ""),
                    "url": r.get("url", ""),
                    "snippet": r.get("content", ""),
                })
        except Exception as e:
            print(f"  [P0] Search error: {e}")
    return all_results


def select_best_sources(results: list[dict]) -> list[dict]:
    """Use LLM to select the 8-12 best sources from search results."""
    if not results:
        return []

    results_text = "\n".join(
        f"[{i}] {r['title']} | {r['url']}\n    {r['snippet']}"
        for i, r in enumerate(results)
    )

    system = """Tu es un expert en analyse littéraire française. Sélectionne les 8-12 meilleures sources parmi ces résultats de recherche sur "Boule de Suif" de Maupassant.

Critères: profondeur d'analyse, expertise littéraire, pertinence pour la prosodie et l'interprétation vocale."""

    user = f"""Résultats de recherche:\n{results_text}

Sélectionne les meilleures sources. Pour chacune, indique l'URL, la raison de la sélection, et un score de pertinence (1-10)."""

    try:
        result = call_structured(SourceSelection, system, user)
        selected_urls = [item["url"] for item in result.get("selected", [])]
        return [r for r in results if r["url"] in selected_urls]
    except Exception as e:
        print(f"  [P0] Source selection error: {e}, using top 10 by snippet length")
        return sorted(results, key=lambda r: len(r.get("snippet", "")), reverse=True)[:10]


def read_sources_deep(urls: list[str]) -> dict[str, str]:
    """Read full content from selected URLs via SearXNG web_url_read."""
    contents = {}
    for url in urls:
        print(f"  [P0] Reading: {url[:80]}...")
        try:
            from mcp_searxng import web_url_read
            content = web_url_read(url=url)
            contents[url] = str(content)[:8000]
        except ImportError:
            contents[url] = _read_via_jina(url)
        except Exception as e:
            print(f"  [P0] Read error: {e}")
    return contents


def _read_via_jina(url: str) -> str:
    """Fallback: read via jina.ai reader."""
    import requests
    try:
        resp = requests.get(f"https://r.jina.ai/{url}", timeout=30)
        resp.raise_for_status()
        return resp.text[:8000]
    except Exception as e:
        print(f"  [P0] Jina read error: {e}")
        return ""


def synthesize_narrative_context(
    source_contents: dict[str, str],
    search_results: list[dict],
) -> NarrativeContext:
    """LLM synthesis of all sources into structured NarrativeContext."""
    sources_summary = "\n\n".join(
        f"--- Source: {url[:80]} ---\n{content[:3000]}"
        for url, content in source_contents.items()
    )

    system = """Tu es un expert en littérature française et en analyse narrative. Tu vas synthétiser des recherches sur "Boule de Suif" de Maupassant en un contexte narratif structuré.

Contexte: ce travail servira à générer un audiobook expressif avec synthèse vocale. Les profils de personnages et la structure dramatique guideront chaque décision de voix, prosodie et interprétation."""

    user = f"""Voici les sources collectées sur "Boule de Suif":

{sources_summary}

Synthétise ces informations en un contexte narratif structuré avec:
1. Contexte historique (Guerre franco-prussienne 1870-1871)
2. Thèmes (hypocrisie, classe sociale, sacrifice, patriotisme)
3. Technique narrative (ironie maupassantienne, narrateur omniscient)
4. Structure en 4 actes:
   - act1_diligence_aller: solidarité forcée, chaud, amical (tension=3)
   - act2_auberge_jours: impatience croissante, de plus en plus froid (tension=5)
   - act3_pressing_collectif: manipulation collective, onctueux, persuasif (tension=8)
   - act4_diligence_retour: mépris, exclusion, sanglot (tension=9)
5. Profils détaillés de chaque personnage (traits, registre vocal, arc émotionnel, prosodie par défaut, relations)
6. Guide prosodique (état émotionnel → tag FishAudio)

Tous les textes doivent être en français."""

    result = call_structured(NarrativeContext, system, user)
    return NarrativeContext(**result)


def run(force: bool = False) -> Path:
    """Run P0 — narrative research. Returns path to narrative_context.json."""
    output_path = OUTPUTS / "narrative_context.json"

    if output_path.exists() and not force:
        print(f"[P0] Cached: {output_path}")
        return output_path

    print("[P0] Running narrative research...")

    # Step 1: Search
    print("[P0] Step 1: SearXNG searches...")
    results = run_searxng_searches()
    print(f"  Found {len(results)} results")

    # Step 2: Select best sources
    print("[P0] Step 2: Selecting best sources...")
    best = select_best_sources(results)
    print(f"  Selected {len(best)} sources")

    # Step 3: Deep reading
    print("[P0] Step 3: Deep reading...")
    urls = [r["url"] for r in best]
    contents = read_sources_deep(urls)
    print(f"  Read {len(contents)} articles")

    # Step 4: Synthesize
    print("[P0] Step 4: LLM synthesis...")
    ctx = synthesize_narrative_context(contents, results)

    # Save
    output_path.write_text(ctx.model_dump_json(indent=2), encoding="utf-8")
    print(f"[P0] Saved: {output_path}")
    print(f"  Characters: {len(ctx.characters)}")
    print(f"  Acts: {len(ctx.acts)}")
    print(f"  Sources: {len(ctx.source_urls)}")

    return output_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
