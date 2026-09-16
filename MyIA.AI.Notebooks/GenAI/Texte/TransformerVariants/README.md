# TransformerVariants — les variantes Transformer modernes, ouvertes

Série née de l'epic [#16058](https://github.com/jsboige/CoursIA/issues/16058) : ouvrir la boîte de ce que `transformers.AutoModelForCausalLM` cache quand le modèle est GQA + RoPE + SWA (Mistral, LLaMA-2/3, Qwen), et coder chaque composant from scratch avant de le confronter à l'implémentation industrielle.

Le Transformer canonique (attention multi-tête, PE additif) reste couvert par le notebook d'architecture de la série GenAI/Texte ; cette série ne le duplique pas, elle en part.

## Parcours

| Notebook | Statut | Contenu |
|---|---|---|
| `TV-00a-RoPE-from-scratch.ipynb` | livre | RoPE : rotation par paires de dimensions, invariance de position relative mesuree, contraste avec le PE additif (distance, logit, tache d'inversion entraînée) |
| `TV-00b` — variantes d'attention | livre | MHA vs MQA vs GQA (reduction du KV-cache, facteur 4x confirme) et SWA (fenetre glissante) |
| `TV-00c` — mixture of experts | en revue (PR #16152) | routage top-k, facteur de capacite, perte d'equilibrage |
| `TV-01-Attention-Variants-SOTA.ipynb` | livre | le vrai Mistral-7B v0.1 (GQA 8/32, RoPE theta 10 000 reconstruit depuis les poids, SWA 4096) charge NF4 via `transformers` : KV-cache formule contre mesure (248 contre 256 Mio a T=2048), champ receptif 131 041 > contexte max, prefill/decodage en deux regimes, ppl 7.95 / 1.490 bpc sur WikiText-2, tableau bloc A vs bloc B (item 7) |
| Bloc B — SOTA | en cours | TV-01 livre (attention) ; MoE-SOTA (TV-02) a venir — les memes mesures sur des modeles industriels charges via `transformers` |

## Conventions

- Kernel `python3` (PyTorch + numpy, CPU-compatible) ; aucune dependance a `transformers`/`xformers`/`flash-attn` dans le bloc A (TV-00a/b/c).
- Bloc B (TV-01) : execution GPU CUDA requise (documentee en tete de notebook, ~4 Gio VRAM) ; ajoute `transformers` + `bitsandbytes` + `datasets` — le contrat CPU du bloc A reste preserve pour les TV-00.
- Notebooks en francais, executes de bout en bout avec outputs, 3 exercices stubbes minimum (C.1).
- Chaque affirmation de ce README est une promesse mesuree dans le notebook correspondant, pas un enonce qualitatif.

Voir [#16058](https://github.com/jsboige/CoursIA/issues/16058) pour l'acceptation complete (bloc A from scratch, bloc B SOTA, comparatifs explicites).
