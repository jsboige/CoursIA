# Archives — Neurosymbolic-EML (précurseur SL-12, archivé 2026-07-04)

## Contexte de l'archivage

Ces deux notebooks constituaient la **veille #4653** sur l'article *EML Trees Are Universal Approximators*
(Germany, Abdo & Bakarji, arXiv 2606.23179, 22 juin 2026) qui présentait l'Exp-Minus-Log comme
un « continuous analogue of NAND gates ». La conjecture était qu'un substrat continu
*discret-par-construction* servirait de base à un modèle neuro-symbolique interprétable
**par construction** (inverse de la stratégie SAE).

## Statut de la veille #4653 : CLOSE

| Étape | Question | Verdict |
|-------|----------|---------|
| Note-1 (`EML-NAND-Explore.ipynb`) | Un atome EML approxime-t-il NAND sur [0,1]² ? | **INCONCLUSIF** — MSE intégré 0.010 (forme globale OK) mais erreur max 0.253 sur coins booléens (transition continue, pas lecture-unité = booléen strict) |
| Note-1 suite | Arbre EML feed-forward apprend-il parité-3 (XOR 3 bits) ? | **NON-CONFIRMÉ** — exactitude 0.250 (= constant 0.5, minimum trivial) vs MLP équivalent 0.750 |
| Note-2 (`EML-NAND-Compose.ipynb`) | La discipline de composition Table 3 (mélange +, −, ×, /, exp, ln, tanh) franchit-elle la barrière parité-3 ? | **PARTIELLEMENT CONFIRMÉ** (verdict imprimé par la cellule de synthèse, cell[12]) — Architecture A témoin : une exécution, exactitude 0.250 (cell[6]) ; B mixte aléatoire : 10 essais, exactitude max **0.625** (un seul essai à 0.625, les neuf autres à 0.500 ; cell[8]) ; C mixte 2-flux : 10 essais, exactitude max **0.500** (cell[10]). |

**Conclusion Note-2 (verbatim)** : « clore la veille #4653 après cette Note-2 avec verdict documenté ».

## Pourquoi archiver (vs supprimer)

`Consolider != Archiver` (mandat user 2026-04-24, 3-step protocol) : on archive avec **preuve de préservation**, pas de suppression destructive.

### Preuve de conservation de la substance

| Information | Lieu de préservation après archivage |
|-------------|--------------------------------------|
| **Verdict empirique Note-1** (MSE 0.010, exactitude 0.250, θ* retenu) | Cellules code de `EML-NAND-Explore.ipynb` (champs `outputs`) — préservées telles quelles |
| **Verdict empirique Note-2** (architecture A témoin, B et C à 10 essais, table de mixité) | Cellules code de `EML-NAND-Compose.ipynb` (champs `outputs`) — préservées telles quelles |
| **Raison du pivot vers difflogic** | [SL-12-DifferentiableLogicGateNetworks.ipynb](../../SL-12-DifferentiableLogicGateNetworks.ipynb) **cell[1]** (markdown, section « Motivation et contexte historique ») et **cell[19]** (markdown, « Note historique : EML/NAND --> difflogic », id `cell-17`) — cite explicitement la préquelle archivée et la remplace. Les `cell[N]` sont des indices 0-based de `cells` |
| **Référence arXiv** | `EML-NAND-Explore.ipynb` cell[0] — lien `arXiv 2606.23179` préservé |
| **Issue de suivi** | #4653, fermée le 2026-07-02 (`completed`), avant cet archivage |

## Pourquoi la suite logique est SL-12 (difflogic)

`difflogic` (Petersen et al., NeurIPS 2022, [arXiv 2210.08277](https://arxiv.org/abs/2210.08277)) réalise **nativement** ce que la conjecture EML cherchait à atteindre par composition :

- **Chaque neurone = 1 des 16 portes logiques** (AND, OR, NAND, NOR, XOR, XNOR, IMPLIES, ...) apprise par descente de gradient avec relaxation différentiable
- **Discrétisation automatique** : après `eval()`, les poids sont seuillés à 0/1 et la porte est figée — lecture-unité = booléen strict (le contraire exact du verdict EML Note-1)
- **Accuracy MNIST 20×20 de 0,826** mesurée par SL-12 (2000 itérations, CPU, cellule[10] ; le carnet cite environ 90 % pour le papier, avec 5000 itérations et GPU)
- **Inférence rapide, selon la publication** : de l'ordre de 1M images/s sur 1 coeur CPU (valeur citée de Petersen 2022, non mesurée dans SL-12) — versus arbre EML qui ne franchit pas 0.250 sur parité-3

`SL-12` est donc le **successeur mature** de la préquelle `EML-NAND` : la question posée par la veille
est traitée autrement — non pas par composition de primitives `exp − ln` mais
par **apprentissage direct d'une porte logique parmi 16**.

## Restauration (à n'utiliser que si la préquelle redevient utile)

```bash
# Depuis la racine du dépôt :
git mv MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/_archive/2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-Explore.ipynb MyIA.AI.Notebooks/SymbolicAI/Neurosymbolic-EML/
git mv MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/_archive/2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-Compose.ipynb MyIA.AI.Notebooks/SymbolicAI/Neurosymbolic-EML/
# Référencer cette archive comme superseded-by dans la PR de restauration
```

## Métadonnées d'archivage

- **Date d'archivage** : 2026-07-04
- **Superseded-by** : `SL-12-DifferentiableLogicGateNetworks.ipynb` (difflogic)
- **Issue fermée** : #4653
- **PR d'archivage** : (à compléter lors du push)
- **Cycle de l'agent** : C196 (po-2024, partition SymbolicAI/.NET)
- **3-step Consolider** : ANALYZE ✓ → MERGE (référence historique dans `SL-12` cell[19]) → ARCHIVE (ce dossier)