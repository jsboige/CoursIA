#!/usr/bin/env python3
"""Patch c.917 repli v2 — full rewrite of 12 markdown cells.

Strategy (per ai-01 c.26 CHANGES_REQUESTED, repli path):
- The MAIN code cells (34, 41, 44, 51, 54) were re-executed by c.917 against
  ONLY `local-mini-v2` (po-2023 has no internet, no .env with cloud keys).
- Cells 12/15/18/24/27/31/38 still show 2-endpoint cloud outputs from PR #8281
  (myia-po-2023, merged 2026-07-24).
- The 12 markdown cells (0, 13, 16, 28, 32, 35, 39, 42, 47, 52, 55, 61) MUST
  clearly distinguish: (a) which tables are from the previous cloud run #8281,
  (b) which tables are from the current local-only run c.917, (c) provide a
  pointer to a sub-issue for the cloud<->local comparison.

For cells [35, 42, 47, 52, 55], we FULLY REWRITE the markdown body to describe
ONLY what the current run actually produced (local-mini-v2 only). For cells
[13, 16, 28, 32, 39], we PREPEND a small italic blockquote noting the source
(#8281 vs c.917). For cell[0], we add a top-of-notebook note. For cell[61], we
add a sub-issue pointer at the tail.

Constraints:
- Markdown-only edits (C.2 exception: no re-execution required).
- Preserve nbformat `source` format (string/line-list/char-split) per cell
  (L925-A ★★).
- LF-only CR=0 (L965 ★).
- Preserve cell IDs (L948 ★★: NO output scrubbing).
"""

import json, pathlib, sys

NB = pathlib.Path('MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb')


def _detect_source_format(src):
    """L925-A ★★ : detect nbformat source format (string/line-list/char-split)."""
    if isinstance(src, str):
        return 'string'
    if not src:
        return 'line-list'
    has_newline = any('\n' in (e or '') for e in src)
    if has_newline:
        return 'line-list'
    return 'char-split'


def _write_text(src, new_text):
    fmt = _detect_source_format(src)
    if fmt == 'string':
        return new_text
    elif fmt == 'line-list':
        return new_text.splitlines(keepends=True)
    else:  # char-split
        return list(new_text)


def _set_cell_source(cell, new_text):
    cell['source'] = _write_text(cell['source'], new_text)


# Header note to insert in cell[0]
CELL0_HEADER = (
    "> **Périmètre du run notebook** : ce notebook décrit un deploiement multi-endpoints\n"
    "> (cloud + local), mais le run effectif sur cette machine worker (po-2023, 2026-07-27)\n"
    "> n'a execute que **1 endpoint** : `local-mini-v2` (Qwen2.5-0.5B-Instruct\n"
    "> via le serveur FastAPI c.911, port 8185). Les chiffres cloud des cellules\n"
    "> d'interpretation 13/16/28/32/39 proviennent d'un run anterieur (PR #8281,\n"
    "> myia-po-2023, 2026-07-24) sur 2 endpoints (cloud-gpt5.2 + openweight-llama4).\n"
    "> Les chiffres locaux des cellules 35/42/47/52/55 proviennent du run c.917\n"
    "> (2026-07-27, ce notebook) sur 1 endpoint local. La comparaison cloud ↔ local\n"
    "> sur la même machine est trackee par une sub-issue ; voir cellule 61 et\n"
    "> sous-section 'Sub-issue cloud<->local' en fin de notebook.\n"
    "\n"
)


# Per-cell FULL rewrites for cells 35/42/47/52/55 (based on actual local-only outputs)
CELL35_FULL = (
    "### Interpretation du test de function calling\n"
    "\n"
    "Ce test verifie le **support natif du function/tool calling** sur le endpoint\n"
    "local (le code source cell[34] itere toujours `for ep in endpoints`, mais\n"
    "`endpoints[]` ne contient qu'une entree sur po-2023 -- pas de `.env` cloud,\n"
    "pas d'internet).\n"
    "\n"
    "**Résultat observe sur le run c.917** (1 endpoint local, 2026-07-27) :\n"
    "\n"
    "| Endpoint | Statut | Details |\n"
    "|----------|--------|---------|\n"
    "| **local-mini-v2** (Qwen2.5-0.5B-Instruct) | **Pas de tool_call** | "
    "Modele 0.5B refuse d'appeler l'outil, repond en texte libre "
    "(\"Je ne peux pas fournir des informations meteorologiques...\"). "
    "`finish_reason` = `\"stop\"`, `usage.total_tokens` = 147 "
    "(47 prompt + 100 completion). |\n"
    "\n"
    "**Points pedagogiques** :\n"
    "\n"
    "1. **Pas de tool_call sur 0.5B-Instruct** : ce petit modele n'a pas ete\n"
    "   fine-tune pour le format `tool_calls` OpenAI ; il genere du texte\n"
    "   libre a la place. Sur un modele plus gros (8B+) ou fine-tune pour les\n"
    "   tools, `tool_choice='auto'` declenche un `tool_calls` natif avec\n"
    "   `finish_reason='tool_calls'`.\n"
    "2. **Verdict** : RECOVERABLE-MACHINE (regle F) -- pour demontrer le tool\n"
    "   calling local, il faudrait un modele 7B+ (Qwen2.5-7B-Instruct,\n"
    "   Llama-3.1-8B-Instruct) sur la meme machine. Pas un workaround\n"
    "   degrade, juste un effet de la taille du modele.\n"
    "\n"
    "> Sur un **deploiement local complet** (vLLM lance avec `--enable-auto-tool-choice`\n"
    "> et un `--tool-call-parser` adequat), les modeles 7B+ supportent les tools\n"
    "> nativement, sans restriction de politique de donnees.\n"
)


CELL42_FULL = (
    "### Interpretation du test de reasoning\n"
    "\n"
    "Ce test demande un **calcul mathematique** (`253 * 73 - 287 = ?`) pour\n"
    "observer le raisonnement sur le endpoint local :\n"
    "\n"
    "**Résultat observe sur le run c.917** (1 endpoint local, 2026-07-27) :\n"
    "\n"
    "| Endpoint | Reponse | Correct? | Reasoning content |\n"
    "|----------|---------|----------|-------------------|\n"
    "| **local-mini-v2** (Qwen2.5-0.5B-Instruct) | `1 405,5` | **Non** (calcul faux : `253*73-287 = 18 172`) | Pas de champ `reasoning_content` |\n"
    "\n"
    "**Points pedagogiques** :\n"
    "\n"
    "1. **Calcul rate** : Le 0.5B-Instruct repond `1 405,5` -- c'est un artefact\n"
    "   classique des petits LLM sur l'arithmetique multi-chiffres : ils\n"
    "   hallucinent un chiffre plausible au lieu de poser le calcul.\n"
    "2. **Pas de `reasoning_content`** : Le champ `reasoning_content` est\n"
    "   specifique aux modeles raisonnants configures avec un parser dedie\n"
    "   (ex : DeepSeek R1 lance avec `--enable-reasoning --reasoning-parser\n"
    "   deepseek_r1`). Qwen2.5-0.5B-Instruct n'expose pas ce champ.\n"
    "3. **Verdict** : RECOVERABLE-MACHINE -- pour observer du vrai reasoning\n"
    "   local, il faudrait un modele 7B+ specialise (DeepSeek-R1-Distill-Qwen-7B,\n"
    "   Qwen3-8B-Thinking, etc.).\n"
)


CELL47_FULL = (
    "### Interpretation du benchmark sequentiel\n"
    "\n"
    "Ce test mesure la **vitesse de generation** du endpoint local en mode\n"
    "sequentiel (1 iteration, apres warm-up) :\n"
    "\n"
    "**Résultat observe sur le run c.917** (1 endpoint local, 2026-07-27) :\n"
    "\n"
    "| Endpoint | Statut | Tokens | Vitesse | Observation |\n"
    "|----------|--------|--------|---------|-------------|\n"
    "| **local-mini-v2** (Qwen2.5-0.5B-Instruct, CPU) | OK | 796 | **18.61 tok/s** | 42.78s par requete mono-iteration, throughput CPU bfloat16 (cf sortie cell[44]) |\n"
    "\n"
    "**Analyse des performances** :\n"
    "\n"
    "1. **CPU mono-thread** : Le 0.5B-Instruct sur CPU pur (sans GPU dedie)\n"
    "   atteint 18.61 tok/s, soit ~42s pour 800 tokens. C'est le regime\n"
    "   nominal d'un petit modele sur machine sans GPU NVIDIA.\n"
    "2. **Comparaison indicative** : un 8B quantize 4-bit sur RTX 3090 atteint\n"
    "   typiquement 30-50 tok/s en mono-requete. Le gap reflete la difference\n"
    "   CPU-pure 0.5B vs GPU dedie 8B.\n"
    "3. **Verdict** : RECOVERABLE-MACHINE -- pour observer les chiffres\n"
    "   comparables a ceux annonces dans la litterature (8B @ 30-100 tok/s),\n"
    "   il faudrait un GPU dedie + un modele plus gros.\n"
    "\n"
    "> Sur un **deploiement local complet** (vLLM avec quantization AWQ/GPTQ sur\n"
    "> GPU dedie), un petit modele (8B) atteint typiquement un debit bien superieur\n"
    "> en mono-requete, debit qui s'envole en mode concurrent grace au continuous\n"
    "> batching (voir test suivant).\n"
)


CELL52_FULL = (
    "### Interpretation du test de batching\n"
    "\n"
    "Ce test envoie **25 requêtes simultanees** au endpoint local pour mesurer\n"
    "le debit concurrent :\n"
    "\n"
    "**Résultat observe sur le run c.917** (1 endpoint local, 2026-07-27) :\n"
    "\n"
    "| Endpoint | Succes | Temps total | Tokens cumules | Debit concurrent |\n"
    "|----------|--------|-------------|----------------|-----------------|\n"
    "| **local-mini-v2** (Qwen2.5-0.5B-Instruct, CPU) | **2/25** | 60.48s | 526 | 8.70 tok/s |\n"
    "\n"
    "> Sur l'execution committee, **23 requetes sur 25 ont timeout** : le CPU\n"
    "> mono-thread sature rapidement, les requetes s'enfilent en file d'attente\n"
    "> et ne peuvent pas toutes aboutir dans la fenetre de 60s.\n"
    "\n"
    "**Points pedagogiques** :\n"
    "\n"
    "1. **Scaling concurrent sur CPU = saturation** : En mono-requete, le 0.5B\n"
    "   tient 18.61 tok/s ; en 25 requetes concurrentes, le CPU ne peut pas\n"
    "   paralleliser (un seul forward-pass a la fois), donc le debit global\n"
    "   chute a 8.70 tok/s cumules et la majorite timeout. C'est l'effet\n"
    "   inverse du batching GPU.\n"
    "2. **Continuous batching (local + GPU)** : La cle des performances d'un\n"
    "   **serveur local vLLM** est le \"continuous batching\" -- les requetes\n"
    "   sont traitees en pipeline GPU sans attendre la fin des precedentes.\n"
    "   Sur CPU mono-thread, ce mecanisme n'existe pas, d'ou la saturation.\n"
    "3. **Verdict** : INTRINSIC pour ce run (CPU overload sur 0.5B local),\n"
    "   RECOVERABLE-MACHINE pour la demonstration du continuous batching\n"
    "   (qui necessite un GPU dedie).\n"
    "\n"
    "> Un **deploiement local complet** (serveurs vLLM/Ollama sur GPU dedie)\n"
    "> ajouterait `local-mini` (ZwZ-8B) et `local-medium` (Qwen3.5) avec un\n"
    "> debit concurrent bien superieur grace au batching GPU continu.\n"
)


CELL55_FULL = (
    "### Interpretation du test de parallelisme global\n"
    "\n"
    "Ce test lance **25 requêtes simultanees** sur le endpoint local avec un\n"
    "ordre aleatoire (le code source cell[54] est prevu pour distribuer sur\n"
    "plusieurs endpoints, mais `endpoints[]` ne contient qu'une entree ici) :\n"
    "\n"
    "**Résultat observe sur le run c.917** (1 endpoint local, 2026-07-27) :\n"
    "\n"
    "| Metrique | Valeur |\n"
    "|----------|--------|\n"
    "| Requêtes totales | 25 (1 endpoint) |\n"
    "| Requêtes OK | **0/25** (0%) |\n"
    "| Fenêtre de temps | 60.95s |\n"
    "| Tokens cumules | 0 |\n"
    "| **Debit global** | **0.00 tok/s** |\n"
    "\n"
    "**Detail par endpoint sur l'execution committee** :\n"
    "\n"
    "| Endpoint | Succes | Tokens | Fenêtre | Debit effectif |\n"
    "|----------|--------|--------|---------|----------------|\n"
    "| **local-mini-v2** (Qwen2.5-0.5B-Instruct, CPU) | **0/25** (0%) | 0 | 60.95s | 0.00 tok/s (timeout CPU) |\n"
    "\n"
    "**Leçons cles** :\n"
    "\n"
    "1. **Saturation CPU totale sur 25 requetes** : Le CPU mono-thread ne peut\n"
    "   pas traiter 25 forward-pass en parallele ; les 25 requetes sont mises\n"
    "   en file et aucune ne complete dans la fenetre de 60s. C'est l'effet\n"
    "   extrème du test batching cell[51] : 23/25 timeout deja en cell[51],\n"
    "   ici c'est 25/25.\n"
    "2. **Verdict pedagogique mal preserve** : Le pattern `asyncio.gather`\n"
    "   fonctionne cote client, mais l'infrastructure serveur (CPU vs GPU,\n"
    "   batching ou non) determine ce qu'on observe. Le notebook illustre\n"
    "   ainsi la **portabilite du contrat OpenAI** : un meme client Python\n"
    "   peut pointer vers cloud ou local sans changer de logique metier,\n"
    "   mais les chiffres dependent du backend.\n"
    "3. **Repartition de charge (concept)** : Sur un deploiement multi-endpoints\n"
    "   reel (cloud + vLLM + Ollama), chaque serveur traiterait 25 requetes\n"
    "   concurrentes au lieu de 50 sur un seul, evitant le rate-limiting\n"
    "   d'un seul fournisseur. Ce run ne peut pas le demontrer.\n"
    "4. **Conclusion honnete** : Le notebook **ne pretend pas** mesurer la\n"
    "   performance multi-endpoints sur ce run ; il documente ce qu'un seul\n"
    "   endpoint local saturee sur CPU donne. Pour la mesure multi-endpoints,\n"
    "   voir la sub-issue en cellule 61.\n"
)


# Per-cell prepended blockquote for cells 13/16/28/32/39 (cloud chiffres from PR #8281)
CELL13_PREPEND = (
    "> **Source des chiffres observes** : run anterieur PR #8281 (2026-07-24,\n"
    "> myia-po-2023) sur 2 endpoints cloud (`cloud-gpt5.2` + `openweight-llama4`).\n"
    "> Le run c.917 (2026-07-27, ce notebook) n'a execute que `local-mini-v2`\n"
    "> sur po-2023 ; la sortie `/models` n'est pas rafraichie pour le local.\n"
    "\n"
)

CELL16_PREPEND = (
    "> **Source des chiffres observes** : run anterieur PR #8281 (2026-07-24)\n"
    "> sur 2 endpoints cloud. Le run c.917 n'a pas reexecute cette cellule.\n"
    "\n"
)

CELL28_PREPEND = (
    "> **Source des chiffres observes** : run anterieur PR #8281 (2026-07-24)\n"
    "> sur 2 endpoints cloud. Le run c.917 n'a pas reexecute cette cellule.\n"
    "\n"
)

CELL32_PREPEND = (
    "> **Source des chiffres observes** : run anterieur PR #8281 (2026-07-24)\n"
    "> sur 2 endpoints cloud. Le run c.917 n'a pas reexecute cette cellule\n"
    "> (cell[31] = code SK, source inchangee, outputs = run anterieur).\n"
    "\n"
)

CELL39_PREPEND = (
    "> **Source des chiffres observes** : run anterieur PR #8281 (2026-07-24)\n"
    "> sur 2 endpoints cloud. Le run c.917 n'a pas reexecute cette cellule\n"
    "> (cell[38] = code SK + tools, source inchangee, outputs = run anterieur).\n"
    "\n"
)

CELL61_TAIL = (
    "\n"
    "---\n"
    "\n"
    "## Sub-issue cloud ↔ local\n"
    "\n"
    "Les cellules 35/42/47/52/55 decrivent le run c.917 (2026-07-27, po-2023,\n"
    "1 endpoint local). Les cellules 13/16/28/32/39 citent les chiffres cloud\n"
    "du run anterieur PR #8281 (2026-07-24, myia-po-2023, 2 endpoints cloud).\n"
    "\n"
    "Pour obtenir **la meme comparaison cloud ↔ local sur la meme machine\n"
    "avec les memes chiffres valides**, une sub-issue trackee explicitement\n"
    "le routage vers une lane cloud-capable (po-2024 ou ai-01) qui dispose\n"
    "de la cle OpenAI. Le code source reste inchange (boucle `for ep in\n"
    "endpoints[]` compatible multi-endpoints) ; seule l'execution differe.\n"
    "Reference : `sota-not-workaround.md` Prong A `RECOVERABLE-MACHINE`.\n"
)


PATCHES = [
    (0, 'header'),         # cell[0] - add run-perimeter note before ## Objectifs
    (13, 'prepend', CELL13_PREPEND),
    (16, 'prepend', CELL16_PREPEND),
    (28, 'prepend', CELL28_PREPEND),
    (32, 'prepend', CELL32_PREPEND),
    (35, 'full', CELL35_FULL),
    (39, 'prepend', CELL39_PREPEND),
    (42, 'full', CELL42_FULL),
    (47, 'full', CELL47_FULL),
    (52, 'full', CELL52_FULL),
    (55, 'full', CELL55_FULL),
    (61, 'tail', CELL61_TAIL),
]


def patch_cell0(nb, header):
    cell = nb['cells'][0]
    src = cell['source']
    text = src if isinstance(src, str) else ''.join(src)
    if '## Objectifs' not in text:
        print("ERROR: '## Objectifs' not found in cell[0]")
        sys.exit(1)
    parts = text.split('## Objectifs', 1)
    new_text = parts[0] + header + '## Objectifs' + parts[1]
    _set_cell_source(cell, new_text)


def patch_cell_prepend(nb, idx, prepend):
    cell = nb['cells'][idx]
    src = cell['source']
    text = src if isinstance(src, str) else ''.join(src)
    new_text = prepend + text
    _set_cell_source(cell, new_text)


def patch_cell_full(nb, idx, full_text):
    cell = nb['cells'][idx]
    _set_cell_source(cell, full_text)


def patch_cell_tail(nb, idx, tail_text):
    cell = nb['cells'][idx]
    src = cell['source']
    text = src if isinstance(src, str) else ''.join(src)
    if text.endswith('\n'):
        new_text = text + tail_text
    else:
        new_text = text + '\n' + tail_text
    _set_cell_source(cell, new_text)


def main():
    if not NB.exists():
        print(f"ERROR: {NB} not found")
        sys.exit(1)

    raw = NB.read_bytes()
    nb = json.loads(raw.decode('utf-8'))

    for entry in PATCHES:
        idx = entry[0]
        mode = entry[1]
        if mode == 'header':
            print(f"Patching cell[{idx}] (top header)...")
            patch_cell0(nb, CELL0_HEADER)
        elif mode == 'prepend':
            print(f"Patching cell[{idx}] (prepend source-note)...")
            patch_cell_prepend(nb, idx, entry[2])
        elif mode == 'full':
            print(f"Patching cell[{idx}] (FULL rewrite)...")
            patch_cell_full(nb, idx, entry[2])
        elif mode == 'tail':
            print(f"Patching cell[{idx}] (tail sub-issue)...")
            patch_cell_tail(nb, idx, entry[2])

    # LF-only CR=0 write (L965 ★)
    trailing_nl = raw.endswith(b'\n')
    out = json.dumps(nb, ensure_ascii=False, indent=1).encode('utf-8')
    if trailing_nl and not out.endswith(b'\n'):
        out += b'\n'
    NB.write_bytes(out)

    print()
    print(f"Wrote {NB} ({len(out)} bytes, CR count: {out.count(bytes([13]))})")


if __name__ == '__main__':
    main()