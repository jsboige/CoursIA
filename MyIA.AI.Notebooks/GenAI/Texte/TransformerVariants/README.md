# TransformerVariants — les variantes Transformer modernes, ouvertes

Série née de l'epic [#16058](https://github.com/jsboige/CoursIA/issues/16058) : ouvrir la boîte de ce que `transformers.AutoModelForCausalLM` cache quand le modèle est GQA + RoPE + SWA (Mistral, LLaMA-2/3, Qwen), et coder chaque composant from scratch avant de le confronter à l'implémentation industrielle.

Le Transformer canonique (attention multi-tête, PE additif) reste couvert par le notebook d'architecture de la série GenAI/Texte ; cette série ne le duplique pas, elle en part.

## Comment lire ce README

- Vous voulez voir chaque composant **from scratch** : suivez le bloc A dans l'ordre (`TV-00a` RoPE, `TV-00b` variantes d'attention, `TV-00d` encodeurs), entièrement CPU et sans `transformers`.
- Vous voulez la **confrontation à l'industrie** : passez au bloc B (`TV-01` attention, `TV-02` MoE), qui charge les vrais modèles et rejoue les mêmes mesures — GPU CUDA requis.
- Vous creusez la **recherche** : `TV-03` (internalisation du CoT) et `TV-04` (DiscoLoop) s'appuient sur les organes du dossier [`tv/`](tv/), que `TV-00d` importe également.

Cette navigation par niveaux suit le principe des séries à plusieurs vitesses décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

## Parcours

| Notebook | Statut | Ce qu'on y apprend |
|---|---|---|
| [TV-00a Python](TV-00a-RoPE-from-scratch-Python.ipynb) · [C#](TV-00a-RoPE-from-scratch-CSharp.ipynb) | livre | RoPE : rotation par paires de dimensions, invariance de position relative mesuree, contraste avec le PE additif (distance, logit, tache d'inversion entraînée) |
| [TV-00b Python](TV-00b-Attention-Variants-from-scratch.ipynb) · [C#](TV-00b-Attention-Variants-from-scratch-CSharp.ipynb) — variantes d'attention | livre | MHA vs MQA vs GQA (reduction du KV-cache, facteur 4x confirme) et SWA (fenetre glissante) |
| `TV-00c` — mixture of experts | livre ailleurs | routage top-k, facteur de capacite, perte d'equilibrage — livre comme [3.4c-MoE-from-scratch](../../../ML/DataScienceWithAgents/03-Deep-Learning/3.4c-MoE-from-scratch.ipynb) dans la serie 03-Deep-Learning (accretion du 3.4, #16151 §5.2) |
| `TV-00d-Encodeurs-from-scratch-Python.ipynb` | livre | les deux familles absentes du bloc A : encodeur seul (BERT, MLM 80/10/10) et encodeur-décodeur (T5, attention croisée) — ablation par position à preuve droite (sujet : 63,7 % bi contre 31,6 % causal) contre contrôle à preuve gauche (verbe : 41,9 % contre 90,0 %), transfert de masque qui s'effondre (43,1 → 24,7 %), seq2seq de normalisation de dates (exact-match 43,2 % glouton, faisceau k=3 42,0 %), alignement appris de l'attention croisée lu position par position |
| `TV-01-Attention-Variants-SOTA-Python.ipynb` | livre | le vrai Mistral-7B v0.1 (GQA 8/32, RoPE theta 10 000 reconstruit depuis les poids, SWA 4096) charge NF4 via `transformers` : KV-cache formule contre mesure (248 contre 256 Mio a T=2048), champ receptif 131 041 > contexte max, prefill/decodage en deux regimes, ppl 7.95 / 1.490 bpc sur WikiText-2, tableau bloc A vs bloc B (item 7) |
| `TV-02-MoE-SOTA.ipynb` | livre | le vrai OLMoE-1B-7B release 0125 (64 experts top-8, 6,9 Md params dont 18,5 % actifs par jeton, bf16 plein — le §1 mesure pourquoi le 4-bit ne s'applique pas) : routeur PLAT demontre (entropie softmax quasi max, gap top-8->top-9 ~4e-5) malgre une charge structuree (entropie 3,89 vs ln 64), capacite du 3.4c rejouee sur la charge reelle (91,5 % servis a c=1,0 — pourquoi dropless), specialisation douce par classe de jetons, tableau 3.4c vs industrie (436 contre 211 LOC, volumes de code relus sur disque a l'execution) |
| Bloc B — SOTA | livre | TV-01 (attention) + TV-02 (MoE) livres — les memes mesures sur des modeles industriels charges via `transformers` |
| `TV-03-Internalisation-CoT-Python.ipynb` | livre | internalisation du raisonnement (Huang et al. 2026, arXiv 2605.28600) sur tache marqueurs multi-sauts : CoT supervise vs answer-only multi-seed, indirection a chaine informative (separation non reproduite — resultat negatif mesure), marche guidee K=2/K=3 (cloturee sans separation positive), organes `tv/model.py` + `tv/task.py` extraits du carnet |
| `TV-04-DiscoLoop-Python.ipynb` | livre | boucles et canaux mixtes (Fu et al. 2026, arXiv 2607.00341) sur l'indirection double (two-hop a entite-pont) : boucle a poids partages egale le profond a 2,9x moins de parametres, DiscoLoop deux-canaux juge NO BEATS a l'echelle jouet (edge -1,99 sigma, DM p < 0.0001), diagnostic decodabilite/alignement du pont dans la direction du papier, realignement sans re-entrainement neutre (deficit situe en amont, dans le stockage du pont, selon les lectures testees), organe `tv/loop.py` |

## Approfondissements

### Autour de TV-00c — le MoE livré ailleurs

| Extension | Notebook | Ce qu'elle ajoute | Prérequis en plus | Outil |
|-----------|----------|-------------------|-------------------|-------|
| TV-00c | [3.4c-MoE-from-scratch](../../../ML/DataScienceWithAgents/03-Deep-Learning/3.4c-MoE-from-scratch.ipynb) | Routage top-k, facteur de capacité, perte d'équilibrage — accrétion du 3.4 dans la série 03-Deep-Learning ([#16151](https://github.com/jsboige/CoursIA/issues/16151) §5.2) | La même architecture Transformer posée en amont | `python3` |

### Autour de TV-03 et TV-04 — les organes de recherche

Les deux carnets de recherche extraient leur moteur dans le dossier partagé [`tv/`](tv/) :
[`tv/model.py`](tv/model.py) (le Transformer jouet), [`tv/task.py`](tv/task.py) (tâches à indirection) et
[`tv/loop.py`](tv/loop.py) (boucles à poids partagés). `TV-00d` importe lui aussi cet organe, et `TV-01`/`TV-02`
empruntent `tv.loc` pour retrouver le dépôt. Le lecteur qui veut reproduire une mesure hors carnet
importe l'organe plutôt que de recopier le modèle.

### Les voisins hors série

En amont, le [3.4-Attention-Transformer-From-Scratch](../../../ML/DataScienceWithAgents/03-Deep-Learning/3.4-Attention-Transformer-From-Scratch.ipynb)
pose l'architecture canonique dont cette série part. En aval, les carnets de production
de la série parente — [10b_Inference_Mechanics](../10b_Inference_Mechanics.ipynb) pour le
prefill/décodage et [11_Quantization](../11_Quantization.ipynb) pour NF4 — approfondissent les
deux régimes que `TV-01` mesure. L'acceptation complète est dans l'epic
[#16058](https://github.com/jsboige/CoursIA/issues/16058).

## Conventions

- Compagnons C# TV-00a/b : kernel .NET 9, TorchSharp-cpu 0.107.0 et CPU mono-thread ; restauration NuGet au premier usage.
- Kernel `python3` (PyTorch + numpy, CPU-compatible) ; aucune dependance a `transformers`/`xformers`/`flash-attn` dans le bloc A (TV-00a/b/c).
- Bloc B : execution GPU CUDA requise (documentee en tete de chaque notebook). TV-01 : NF4 via `bitsandbytes` (~4 Gio VRAM) ; TV-02 : bf16 plein (~12,9 Gio VRAM, le 4-bit ne s'applique pas au MoE — mesure dans le notebook). Ajout de `transformers` + `datasets` — le contrat CPU du bloc A reste preserve pour les TV-00.
- Notebooks en francais, executes de bout en bout avec outputs, 3 exercices stubbes minimum (C.1).
- Chaque affirmation de ce README est une promesse mesuree dans le notebook correspondant, pas un enonce qualitatif.

Voir [#16058](https://github.com/jsboige/CoursIA/issues/16058) pour l'acceptation complete (bloc A from scratch, bloc B SOTA, comparatifs explicites).
