#!/usr/bin/env python3
"""
populate_semantickernel_cost.py — Peuple `metadata.cost` pour les notebooks GenAI/SemanticKernel.

Issue #8056 (P1) — matrice cout/ressource par notebook. EPIC #8056 burn-down
par famille. GenAI famille rollout c.831+ : Texte 100% (#8220/#8225/#8226/#8384/#8385),
Image 95% (9 NBs PR #8580), Audio 90% (#8518/#8579), Video 100%, FineTuning 100%
(#8389), PostTraining 100% (#8403). SemanticKernel = **26 NBs sans cost** au
debut du c.942 (0/26 couvert), plus grosse sous-serie residuelle du rollout GenAI.

Profil SemanticKernel detecte (firsthand c.945, scan 32 OpenAI/3 Azure/1 Anthropic
+ SK SDK 76 refs) : API-heavy (gpt-4o/4o-mini ou Azure OpenAI), kernel Python
majoritaire (`python3`), quelques jumeaux `.net-csharp` (Microsoft.SemanticKernel).
Stack : `semantic-kernel` SDK Python, `.env` avec `OPENAI_API_KEY` ou
`AZURE_OPENAI_*`, plugins/agents/filters/vector-stores/process-framework/MCP.

Idempotent : JAMAIS ecraser un bloc `cost` existant (un notebook deja peuple
est skippé). Hand-edits byte-surgical sur `nb.metadata['cost']` ; LF-only CR=0
post-write (L965 ★ + L925-E ★).

Usage :
  # Dry-run (par defaut) — affiche ce qui serait peuple
  python scripts/audit/populate_semantickernel_cost.py --tranche 1

  # Appliquer
  python scripts/audit/populate_semantickernel_cost.py --tranche 1 --apply \\
      --by myia-po-2023:CoursIA-2

  # Lister les NBs SK sans cost (audit gap)
  python scripts/audit/populate_semantickernel_cost.py --audit

Voir aussi : scripts/audit/populate_gametheory_cost.py (precedent tranche par
famille, po-2023 c.927). Meme canevas.
"""

import argparse
import datetime as _dt
import json
import sys
from pathlib import Path


# === Profils canoniques par NB (tranche 1, SK-01..09) ===
#
# Schema calque sur `01-SemanticKernel-Intro` costfm legacy (migre vers
# metadata.cost via PR c.942) + `GameTheory-1-Setup` precedent po-2023 :
# - api_provider=openai (defaut), azure_openai en variante (NB 02 mentionne azure)
# - gpu_required=false (inference cote serveur OpenAI/Azure)
# - api_usd_est : estimation par comptage de cellules `kernel.invoke` / chat calls
# - cpu_min : heuristique 1-3 min pour setup local + execution cellules
# - free_alternative : self (NB lui-meme est la voie principale) ou Texte/10_LocalLlama
#   comme fallback local LLM
# - validator : manual (notebooks OpenAI API non re-exec ce cycle, RECOVERABLE-USER-HAND)
# - notes : resume pedagogique aligne sur la prose du costfm legacy
#
# Comptages API : effectues par c.945 (scan regex openai/gpt-4o/chat.completions sur
# les sources .ipynb), cf dashboard workspace-CoursIA-2 c.945 [CLAIMED].

PROFILES = {
    "01-SemanticKernel-Intro": {
        "api_usd_est": 0.10,
        "api_provider": "openai",
        "cpu_min": 1,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Semantic Kernel fundamentals : plugins, kernel.invoke, prompts. ~5 appels kernel.invoke gpt-4o (~800 tokens/call). Cout estime depuis le decompte des sites d'appel (G.1 firsthand).",
    },
    "02-SemanticKernel-Advanced": {
        "api_usd_est": 0.15,
        "api_provider": "openai",
        "cpu_min": 2,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Function calling avance, memoire conversationnelle, plugins natifs. ~6 appels gpt-4o (function_choice + history). Azure OpenAI mentionne en variante.",
    },
    "03-SemanticKernel-Agents": {
        "api_usd_est": 0.15,
        "api_provider": "openai",
        "cpu_min": 1,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Agent Framework : ChatCompletionAgent, multi-turn, handoffs. ~6 appels (4 invoke + 2 chat) gpt-4o. Cout legerement superieur a SK-1 (agent = plusieurs tours).",
    },
    "04-SemanticKernel-Filters-Observability": {
        "api_usd_est": 0.08,
        "api_provider": "openai",
        "cpu_min": 1,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Filtres et observabilite (FunctionInvocationContextFilter, LoggingFilter, OpenTelemetry). ~4 appels gpt-4o (filter prompts + tracing).",
    },
    "05-SemanticKernel-VectorStores": {
        "api_usd_est": 0.10,
        "api_provider": "openai",
        "cpu_min": 2,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Vector stores avec Qdrant (Docker local). ~3 chat gpt-4o + embeddings text-embedding-3-small. Qdrant = service Docker local (qdrant/qdrant:latest).",
    },
    "06-SemanticKernel-ProcessFramework": {
        "api_usd_est": 0.12,
        "api_provider": "openai",
        "cpu_min": 2,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Process Framework : workflows multi-etapes, kernels imbriques. ~5 appels gpt-4o pour etapes du process. Workflow declaratif (KernelProcess + steps).",
    },
    "07-SemanticKernel-MultiModal": {
        "api_usd_est": 0.30,
        "api_provider": "openai",
        "cpu_min": 3,
        "network": True,
        "external_account": "openai",
        "free_alternative": None,
        "reproducibility": "LOW",
        "notes": "Multi-modal : images (gpt-4o vision), audio (Whisper), text. ~6 appels gpt-4o + cout vision/image. Pas d'alternative gratuite equivalente (vision = lock-in OpenAI).",
    },
    "08-SemanticKernel-MCP": {
        "api_usd_est": 0.10,
        "api_provider": "anthropic",
        "cpu_min": 2,
        "network": True,
        "external_account": "anthropic",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Model Context Protocol (MCP) : integration outils externes via SK. ~3 appels Anthropic claude-3-5-sonnet (exemple MCP serveur). Compte Anthropic optionnel (cle OPENAI_API_KEY suffit pour variantes).",
    },
    "09-SemanticKernel-Building-CLR": {
        "api_usd_est": 0.05,
        "api_provider": "openai",
        "cpu_min": 2,
        "network": True,
        "external_account": "openai",
        "free_alternative": None,
        "reproducibility": "MED",
        "notes": "Interoperabilite Python/.NET via pythonnet : appel .NET CLR depuis Python (rare, 1 appel chat gpt-4o pour exemple). Cout faible mais build CLR necessite .NET 9.0 SDK.",
    },
    # === Tranche 2 (c.946) = NBs SK restants (10/10a/10b NotebookMaker, Createur
    # de mail, Notebook-Generated, Notebook-Template, Workbook-Template-Python,
    # Workbook-Template, Semantic-kernel-AutoInteractive, fort-boyard-python). ===
    "10-SemanticKernel-NotebookMaker": {
        "api_usd_est": 0.20,
        "api_provider": "openai",
        "cpu_min": 3,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Systeme multi-agents (Admin/Coder/Reviewer) pour generation de notebooks. ~8 appels OpenAIChatCompletion gpt-4o (3-4 tours x 2-3 agents). Cout superieur a SK-03 (rotation d'agents).",
    },
    "10a-SemanticKernel-NotebookMaker-batch": {
        "api_usd_est": 0.40,
        "api_provider": "openai",
        "cpu_min": 5,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Variante batch du NotebookMaker : plusieurs notebooks generes en sequence. ~16 appels gpt-4o (~4 batch x 4 agents). Cout proportionnel au batch_size.",
    },
    "10b-SemanticKernel-NotebookMaker-batch-parameterized": {
        "api_usd_est": 0.40,
        "api_provider": "openai",
        "cpu_min": 5,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Variante parametree du NotebookMaker batch : prompts/config injectes via parametres. ~16 appels gpt-4o (memes ordre de grandeur que 10a).",
    },
    "Créateur de mail personnalisé": {
        "api_usd_est": 0.10,
        "api_provider": "openai",
        "cpu_min": 1,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Generation de mail personnalise via OpenAIChatCompletion. ~2 appels gpt-4o (1 generation + 1 variante). Cout faible (mail = sortie courte).",
    },
    "Notebook-Generated": {
        "api_usd_est": 0.0,
        "api_provider": "none",
        "cpu_min": 2,
        "network": False,
        "external_account": None,
        "free_alternative": "self",
        "reproducibility": "HIGH",
        "notes": "NB generique pandas/numpy/sklearn (Iris dataset). Pas d'API LLM : 0 appel. NB pedagogique pour AutoGen/SK NotebookMaker (lui-meme produit par l'agent). Cout CPU seul.",
    },
    "Notebook-Template": {
        "api_usd_est": 0.0,
        "api_provider": "none",
        "cpu_min": 0,
        "network": False,
        "external_account": None,
        "free_alternative": "self",
        "reproducibility": "MED",
        "notes": "Template squelette (5 cellules de stub) pour instanciation par NotebookMaker. Pas d'API ni CPU effectif : squelette a remplir. Provenance: SK-10.",
    },
    "Workbook-Template": {
        "api_usd_est": 0.0,
        "api_provider": "none",
        "cpu_min": 0,
        "network": False,
        "external_account": None,
        "free_alternative": "self",
        "reproducibility": "MED",
        "notes": "Template workbook (squelette) pour AutoInteractive workflow. Pas d'API ni CPU : instantiation par agent. Couplé a WorkbookUpdateInteraction.cs.",
    },
    "Workbook-Template-Python": {
        "api_usd_est": 0.05,
        "api_provider": "openai",
        "cpu_min": 1,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Variante Python du Workbook template : 1 appel kernel.invoke pour exemple d'instanciation. Cout unitaire (template = 1 chat pour demo).",
    },
    "Semantic-kernel-AutoInteractive": {
        "api_usd_est": 0.10,
        "api_provider": "openai",
        "cpu_min": 1,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Boucle interactive SK (user <-> kernel). ~1 appel completion par tour. Cout unitaire (interactif = usage ponctuel).",
    },
    "fort-boyard-python": {
        "api_usd_est": 0.30,
        "api_provider": "openai",
        "cpu_min": 3,
        "network": True,
        "external_account": "openai",
        "free_alternative": "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb",
        "reproducibility": "LOW",
        "notes": "Jeu Fort-Boyard : 42 enigmes generees par OpenAIChatCompletion. Cout eleve (NB pedagogique = beaucoup de generations). Variante csharp (fort-boyard-csharp) sans LLM.",
    },
}

# Tranche 1 = SK-01..09 (9 NBs pedagogiques Python du chapitre fundamentals).
# Tranche 2 = 10..10b + Createur de mail + Notebook-Generated/Template + Workbook-Template-(Python) + AutoInteractive + fort-boyard-python (10 NBs restants).
TRANCHES = {
    1: [k for k in PROFILES.keys() if k.startswith(("01-", "02-", "03-", "04-", "05-", "06-", "07-", "08-", "09-"))],
    2: [
        "10-SemanticKernel-NotebookMaker",
        "10a-SemanticKernel-NotebookMaker-batch",
        "10b-SemanticKernel-NotebookMaker-batch-parameterized",
        "Créateur de mail personnalisé",
        "Notebook-Generated",
        "Notebook-Template",
        "Workbook-Template",
        "Workbook-Template-Python",
        "Semantic-kernel-AutoInteractive",
        "fort-boyard-python",
    ],
}


def build_cost(notebook_name: str, by: str, today: str) -> dict:
    """Construit le bloc `metadata.cost` selon le profil canonique du NB."""
    p = PROFILES[notebook_name]
    cost = {
        "api_usd_est": p["api_usd_est"],
        "api_provider": p["api_provider"],
        "qcc_tokens_est": 0,
        "cpu_min": p["cpu_min"],
        "gpu_min": 0,
        "gpu_required": False,
        "vram_gb": 0,
        "vram_tier": "LITE",
        "network": p["network"],
        "external_account": p["external_account"],
        "free_alternative": p["free_alternative"],
        "reduced_pedagogical": None,
        "reproducibility": p["reproducibility"],
        "metadata_written": today,
        "validator": "manual",
        "notes": p["notes"] + f" Provenance: {by} (c.946).",
    }
    return cost


def populate_notebook(path: Path, by: str, today: str, apply: bool = False, force: bool = False) -> str:
    """Peuple metadata.cost selon profil canonique. Retourne un code statut."""
    notebook_name = path.name.replace(".ipynb", "")
    if notebook_name not in PROFILES:
        return f"skipped-no-profile ({notebook_name})"

    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return f"error: {e}"

    meta = nb.setdefault("metadata", {})
    if "cost" in meta and not force:  # idempotent : ne JAMAIS écraser un bloc existant
        return "skipped-has-cost"

    cost = build_cost(notebook_name, by=by, today=today)
    if not apply:
        return "populated"  # dry-run

    meta["cost"] = cost
    # Round-trip json indent=1 (convention repo) ; LF-only ; pas de churn inutile.
    new_content = json.dumps(nb, indent=1, ensure_ascii=False) + "\n"
    # LF-fix post-write sur Windows (L965 ★ + L925-E ★)
    if "\r\n" in new_content:
        new_content = new_content.replace("\r\n", "\n")
    path.write_bytes(new_content.encode("utf-8"))
    return "populated"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument(
        "--tranche", type=int, default=1,
        help="Tranche SK costfm à peupler (1 = SK-01..09, 2 = 10..10b + Createur de mail + Templates + AutoInteractive + fort-boyard-python)",
    )
    ap.add_argument(
        "--by", default="anonymous",
        help="machine:workspace (provenance, pour le rapport)",
    )
    ap.add_argument(
        "--apply", action="store_true",
        help="Écrire les modifications (défaut : dry-run)",
    )
    ap.add_argument(
        "--today", default=None,
        help="Date ISO pour metadata_written (défaut : aujourd'hui)",
    )
    ap.add_argument(
        "--audit", action="store_true",
        help="Lister les NBs SK sans cost metadata (sans rien écrire)",
    )
    ap.add_argument(
        "--force", action="store_true",
        help="Réécrire le bloc cost même si déjà présent (cycle-id mismatch)",
    )
    args = ap.parse_args(argv)

    if args.audit:
        sk_dir = Path("MyIA.AI.Notebooks/GenAI/SemanticKernel")
        nbs = sorted([p for p in sk_dir.glob("*.ipynb") if "_output" not in p.name])
        n_with_cost = 0
        n_without = 0
        for nb in nbs:
            try:
                data = json.loads(nb.read_text(encoding="utf-8"))
                cost = data.get("metadata", {}).get("cost")
                if cost:
                    n_with_cost += 1
                    print(f"  HAS_COST  {nb.name}")
                else:
                    n_without += 1
                    print(f"  MISSING   {nb.name}")
            except Exception:
                pass
        print(f"\n[AUDIT] {n_with_cost} WITH cost / {n_without} WITHOUT cost (total {len(nbs)})")
        return 0

    if args.tranche not in TRANCHES:
        print(f"ERROR: tranche {args.tranche} pas encore implémentée (1 ou 2)", file=sys.stderr)
        return 2

    today = args.today or _dt.date.today().isoformat()
    nb_names = TRANCHES[args.tranche]
    sk_dir = Path("MyIA.AI.Notebooks/GenAI/SemanticKernel")
    counts = {"populated": 0, "skipped-has-cost": 0}
    for name in nb_names:
        nb_path = sk_dir / f"{name}.ipynb"
        if not nb_path.exists():
            print(f"  WARN  {nb_path} introuvable")
            continue
        status = populate_notebook(nb_path, by=args.by, today=today, apply=args.apply, force=args.force)
        if status in counts:
            counts[status] += 1
        marker = "WRITE" if args.apply else "DRY-RUN"
        print(f"  [{marker:7s}] {status:25s} {nb_path.name}")

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] tranche={args.tranche} by={args.by} today={today}")
    print(f"  populated        : {counts['populated']}")
    print(f"  skipped-existing : {counts['skipped-has-cost']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())