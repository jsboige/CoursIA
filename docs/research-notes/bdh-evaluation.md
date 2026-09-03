# Évaluation BDH (Dragon Hatchling) — verdict partiel c.890

**Grain:** DEEP/research-code — lane `myia-po-2024:CoursIA-2` — prev: MED/slides #14484
**Scope:** cette itération est bornée à la lecture de l'abstract/intro/conclusion (15 pages sur 62) + inspection du dépôt `pathwaycom/bdh`. La micro-reproduction (entraînement 10M params sur 100M tokens) est **hors scope ce cycle** — le repo ne fournit pas de script multi-config sweep, donc l'effort de ré-exécution ≥24h CPU n'est pas justifiable sans scoping préalable (cf § Résiduel).
**Origine:** issue #14489 (user 2026-09-03) — évaluation du sérieux de Pathway et de l'opportunité d'en parler dans le dépôt.
**Sources lues firsthand:** papier arXiv:2509.26507 (62 pages, abstract/intro §1+§8 + scaling §4 + table §8.2), README + `bdh.py` + `train.py` du dépôt `pathwaycom/bdh`, page ARC-AGI leaderboard, page repo GitHub API.

## TL;DR — verdict 3 axes

### Axe A — Sérieux scientifique : **FIDÈLE MAIS À CAVEATS**

- **Auteurs crédibles** : Jan Chorowski (CTO, co-inventeur historique de l'attention avec Bahdanau/Bengio), Adrian Kosowski (CSO, ACM SPAA Best Paper, Inria tenure 23 ans), Łukasz Kaiser (advisor, co-inventeur du Transformer 2017). Le pedigree est authentique.
- **Prétention théorique forte mais cadrée** : BDH reformule l'attention comme dynamique locale de graphe (edge-reweighting). La chaîne de réductions formelles (§2-§3) tient debout au niveau de l'intuition, mais la "correspondance macro-micro" avec le cerveau est une **hypothèse**, pas une démonstration — l'article le dit lui-même (§8.2 : *"plausibly"*).
- **Scaling laws vérifiées empiriquement MAIS pas sur les benchmarks annoncés dans le communiqué produit.** Le papier compare BDH-GPU à **GPTXL** (et non GPT-2) sur une **tâche de traduction**, avec BPTT tronqué 2048 char et 4096 tokens de KV-Cache. Les claims marketing du site Pathway (Sudoku 97.4%, ARC-AGI 29.5%) **ne sont pas dans le papier**.
- **Peer review absent** au 2026-09-03 : aucune soumission NeurIPS/ICLR/ICML visible. Recherche OpenReview : "BDH" ne remonte aucune submission acceptée.

**Verdict A : FIDÈLE** en ce que la science publiée (architecture + scaling translation) est authentique. **DIVERGENCE POSITIVE marketing** pour les claims Sudoku/ARC-AGI : le repo lui-même affiche un disclaimer ("Sudoku Extreme result refers to Pathway's **internal** BDH implementation, not the current open-source repository").

### Axe B — Reproductibilité : **RECOVERABLE-MACHINE (partiel)**

- **Code disponible** : MIT license (vérifié `LICENSE.md`), Python pur, dépendances minimales (`torch`, `numpy`, `requests`).
- **`bdh.py` (5051 octets)** : architecture complète, **lisible et concise** — l'architecture tient en ~150 lignes, ce qui contraste avec nanoGPT-like ~250 lignes.
- **`train.py` (3670 octets)** : **référence, pas sweep**. Une seule configuration (`BDH_CONFIG = bdh.BDHConfig()`), nanoGPT-style, tiny Shakespeare, BLOCK_SIZE=512, BATCH_SIZE=32, MAX_ITERS=3000. **Aucun mécanisme de sweep sur `n` ou `d`** — donc la courbe de scaling 10M→1B params ne peut pas être tracée depuis ce repo.
- **Pas de checkpoints pré-entraînés** : confirmé (issue #14489 §1). HuggingFace / PyTorch Hub ne référencent pas BDH.
- **Pas de seeds publiés** pour les chiffres scaling §4 : la "même configuration" peut diverger run-to-run.
- **Micro-reproduction faisable CPU modeste** sur tiny Shakespeare (3000 itérations), mais cela ne testerait qu'une configuration (~25M params selon §4.1) sans permettre de valider la courbe de scaling.

**Verdict B : RECOVERABLE-MACHINE (GPU recommandé)** — la micro-repro 25M params est faisable (une config, pas sweep). RECOVERABLE-LOCAL seulement si on accepte CPU modeste pour 1 seule configuration. **INTRINSIC pour la courbe de scaling complète** : le repo ne fournit pas le pipeline multi-config requis pour valider les claims de scaling 10M→1B.

### Axe C — Opportunité pédagogique : **À REVENIR si axe B validé, NON ce cycle**

Le papier contient 3 angles théoriquement exploitables pour le dépôt :

1. **Interprétation edge-reweighting ≈ Hebbian learning** : pertinent pour les notebooks ICT-Series (chaîne Cech, edge-reweighting, fast-weights §1.2). **Mais** sans reproduction empirique préalable, l'angle est rhétorique, pas falsifiable.
2. **Scaling laws "rivals GPT2 at same params"** : si la claim tient sur une repro multi-config, c'est un cas d'école ML pour la série ML-Training-Pipeline. **Mais** la repro demande sweep GPU que po-2024 ne peut pas assumer seule (CPU-only per dashboard).
3. **Linear attention positive-sparse** : angle technique pour un notebook Search/ML sur les nouvelles architectures post-Transformer (Mamba, RWKV, xLSTM, Hyena). **Mais** la concurrence est sévère — 4 architectures déjà couvertes ou en cours de sweep ailleurs sur le pool.

**Verdict C : À REVENIR dans 6 mois** — l'angle est réel mais non-prioritaire, et conditionné à (a) repro empirique qui sort du scope c.890, (b) verdict du coordinateur sur les lanes qui porteraient le notebook (probablement po-2026 ML/vision, pas po-2024 audit/finance — j'ai self-pick par R5 responsabilité, pas par lane-match).

## Critères falsifiables pour une PR de suivi (non c.890)

Une éventuelle PR de notebook BDH dans le dépôt devrait satisfaire **simultanément** :

1. **Repro multi-seed** (≥4 seeds parmi {0,1,7,42,99}) sur tiny Shakespeare 25M params, comparée à un nanoGPT-équivalent 25M params publié. Verdict honnête BEATS/NO BEATS/INCONCLUSIVE selon multi-seed + Diebold-Mariano conjonction (`loss_fn="mse"`, seuil `dm_p_median < 0.05`). **Sans cette repro, AUCUNE mention dans le dépôt.**
2. **Vérification ARC-AGI leaderboard firsthand** : pas d'ajout au dépôt tant que la claim ARC-AGI 29.5% n'est pas confirmée sur https://arcprize.org/leaderboard avec score vérifiable et split (public vs semi-private) documenté.
3. **OpenReview search** : si une soumission NeurIPS/ICLR/ICML 2026 apparaît pour BDH/Dragon-Hatchling, attendre la décision peer-review avant de promouvoir dans le dépôt.

## Ce qui est livré ce cycle (c.890)

- Lecture firsthand §1, §4, §8 (15 pages sur 62).
- Inspection `pathwaycom/bdh` : `bdh.py` (architecture), `train.py` (référence), `LICENSE.md` (MIT), README (caveat Sudoku).
- Vérification ARC-AGI leaderboard : **BDH non listé** (WebFetch 2026-09-03 → "No, the page does not mention BDH, Dragon Hatchling, or Pathway").
- Verdict 3 axes documenté ci-dessus.
- Note ajoutée à `docs/research-notes/` (nouveau répertoire, premier fichier).

## Résiduel (à porter par un futur cycle si axe A confirmé par les pairs)

- **Micro-repro multi-config sweep** : GPU-only (RTX 3070 8GB sur po-2026 selon dashboard, ou ai-01). Non faisable po-2024 CPU-only.
- **Lecture intégrale du papier** (47 pages restantes : §2 formalisme BDH, §3 BDH-GPU, §5 emergence of modularity, §A-D appendices) — au cas où la repro confirme la promesse.
- **Note de revue interne** comparant BDH à Mamba/RWKV/xLSTM/Hyena sur les critères du sweep "post-Transformer" déjà amorcé dans le pool ML.
- **Suivi OpenReview** pour soumission NeurIPS/ICLR/ICML 2026 (deadline mai 2026 a passé, donc verdict en attente — checker mi-2026).

## Verdict global

**NE PAS mentionner BDH dans le dépôt à ce stade.** L'axe A est FIDÈLE, mais les axes B (reproductibilité) et C (opportunité) restent conditionnels à une repro empirique que ce cycle n'a pas produite. Issue #14489 peut passer en `candidate-delivered` après confirmation par ai-01 que le présent verdict satisfait l'acceptance.

## Voir aussi

- Issue #14489 — cahier des charges de cette évaluation
- Issue #3801 — EPIC SOTA axe-2 (registre)
- `~/.claude/rules/bibliography-hygiene.md` — règle HARD archivage canonique
- `~/.claude/rules/sota-not-workaround.md` — 5 verdicts SOTA + procédure INTRINSIC 6 axes
- `~/.claude/rules/audit-cross-source-distillation.md` — méthode FIDÈLE/PERTE/DIVERGENCE POSITIVE
- `docs/ml/tsad-benchmark-flaws.md` — précédent d'évaluation critique d'un benchmark ML publié
