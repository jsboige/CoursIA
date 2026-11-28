# 17 — Multi-agent : self-play et information asymétrique

[↑ GameTheory](../README.md) · [Entrée : capstone 17](../GameTheory-17-MultiAgent-RL-Python.ipynb) · [C#](../GameTheory-17-MultiAgent-RL-CSharp.ipynb)

Cette sous-série prolonge le capstone [17 — Apprentissage multi-agent](../GameTheory-17-MultiAgent-RL-Python.ipynb) (self-play, fictitious play, NFSP, PSRO, introduction à AlphaZero) sur deux arcs. Le premier, **17b→17f**, approfondit l'information asymétrique : les modèles fondateurs (Akerlof, Spence, Rothschild–Stiglitz, Wilson–Miyazaki), leurs certificats Lean, la persuasion bayésienne, puis la lecture du marché comme bilan d'espérances. Le second, **17g**, ramène le self-play du capstone vers le framework PettingZoo.

Le carnet 17g occupe la sixième lettre de la chaîne : la descente en sous-série (règle d'accrétion §4ter) évite d'ouvrir un palier 24 orphelin alors que le contenu prolonge directement le self-play du 17.

## Parcours principal — lecture guidée et prérequis

Le fil relie le capstone 17 aux deux arcs de la sous-série. L'arc information asymétrique (17b→17f) demande le palier 11 (types privés) en plus du 17 ; l'arc self-play (17g) ne demande que le capstone 17.

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 17b | [Information asymétrique](GameTheory-17b-Asymmetric-Information-Python.ipynb) | Les modèles fondateurs : Akerlof (marché des citrons), Spence (signal coûteux), Rothschild–Stiglitz (screening), Wilson–Miyazaki | Python | Licence |
| 17c | [Certificat d'Akerlof en Lean](GameTheory-17c-Lean-Lemons-Certificat-Lean.ipynb) | Le certificat du lake `asymmetric_information_lean` exécuté : seuil de pooling exact, monotonie, spirale de prix | Lean | Recherche |
| 17d | [Screening et signaling en Lean](GameTheory-17d-Lean-Screening-Signaling-Lean.ipynb) | Les autres modules du même lake : non-existence de Rothschild–Stiglitz, intervalle séparateur de Spence et minimalité de Riley, Wilson–Miyazaki, pont bayésien | Lean | Recherche |
| 17e | [Persuasion bayésienne](GameTheory-17e-Bayesian-Persuasion-Python.ipynb) · [C#](GameTheory-17e-Bayesian-Persuasion-CSharp.ipynb) | La concavification évaluée par deux méthodes indépendantes (programme linéaire et enveloppe concave) dont l'accord est vérifié, avec un contrôle négatif | Python · C# | Recherche |
| 17f | [Du marché au bilan](GameTheory-17f-Market-to-Balance-Sheet-Python.ipynb) | L'équilibre de marché lu comme un bilan d'espérances : le pont vers la théorie de la décision — capstone de l'arc information asymétrique | Python | Licence |
| 17g | [Self-play vers PettingZoo](GameTheory-17g-SelfPlay-Tabulaire-vers-PettingZoo-Python.ipynb) | Le self-play tabulaire du dilemme du prisonnier (convergence vers Nash (D,D), falsifiable) porté sur PettingZoo (`ParallelEnv`), l'organe multi-agent de la série RL | Python | Recherche |

## Pour aller plus loin

- **Arc information asymétrique** : les formalisations vivent dans le lake [`asymmetric_information_lean`](../asymmetric_information_lean/README.md) ; 17c et 17d en exécutent les certificats.
- **Arc self-play** : 17g s'appuie sur l'organe multi-agent de la [série RL](../../RL/README.md) et sur le capstone 17.

[Retour à GameTheory](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
