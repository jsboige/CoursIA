# TransformerVariants — les variantes Transformer modernes, ouvertes

Série née de l'epic [#16058](https://github.com/jsboige/CoursIA/issues/16058) : ouvrir la boîte de ce que `transformers.AutoModelForCausalLM` cache quand le modèle est GQA + RoPE + SWA (Mistral, LLaMA-2/3, Qwen), et coder chaque composant from scratch avant de le confronter à l'implémentation industrielle.

Le Transformer canonique (attention multi-tête, PE additif) reste couvert par le notebook d'architecture de la série GenAI/Texte ; cette série ne le duplique pas, elle en part.

## Parcours

| Notebook | Statut | Contenu |
|---|---|---|
| `TV-00a-RoPE-from-scratch.ipynb` | livre | RoPE : rotation par paires de dimensions, invariance de position relative mesuree, contraste avec le PE additif (distance, logit, tache d'inversion entraînée) |
| `TV-00b` — variantes d'attention | a venir | MHA vs MQA vs GQA (reduction du KV-cache) et SWA (fenetre glissante) |
| `TV-00c` — mixture of experts | a venir | routage top-k, facteur de capacite, perte d'equilibrage |
| Bloc B — SOTA | a venir | les memes mesures sur un modele industriel charge via `transformers` |

## Conventions

- Kernel `python3` (PyTorch + numpy, CPU-compatible) ; aucune dependance a `transformers`/`xformers`/`flash-attn` dans le bloc A.
- Notebooks en francais, executes de bout en bout avec outputs, 3 exercices stubbes minimum (C.1).
- Chaque affirmation de ce README est une promesse mesuree dans le notebook correspondant, pas un enonce qualitatif.

Voir [#16058](https://github.com/jsboige/CoursIA/issues/16058) pour l'acceptation complete (bloc A from scratch, bloc B SOTA, comparatifs explicites).
