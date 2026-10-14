# ML-Chronos-Foundation (HandsOn Ex18)

**Classe d'actifs :** Actions US (top 10)
**Cloud project ID :** None (local only)

## Description

Modèle de fondation Chronos T5 d'Amazon pour le forecasting de séries temporelles. Rebalance bi-hebdomadaire basée sur la direction des prévisions.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Chronos-Foundation"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.277 |
| CAGR | 7.23% |
| Max Drawdown | 13.5% |
| Modèle | Chronos T5 (Amazon) |
| Rebalance | Biweekly |

## Variante ré-entraînée (exemple 18/02)

`main_finetuned.py` est le port fidèle du livre (section `06 Applied Machine Learning/18
Amazon Chronos Model/02 Fine-Tuned Model/main.py`, dépôt `HandsOnAITradingBook` au commit
`e025f21`) : le ré-entraînement tourne **dans l'algorithme**, au premier rebalancement
trimestriel, puis `ChronosPipeline.predict` fournit les courbes de prévision et SciPy les
poids de Sharpe maximal. Il n'est **pas exécutable en CI** (GPU, `chronos` et `gluonts`
requis) et n'est pas déployé sur QC Cloud.

Le ré-entraînement est donc aussi porté **hors** de l'algorithme, par un harnais
(`finetune/`) qui le rend mesurable sur un GPU local :

- `finetune/run_finetune_chronos.py` — ré-entraîne par graine, puis compare le modèle de
  base et le modèle ré-entraîné hors échantillon ;
- `finetune/chronos_training.py` — le module d'entraînement de `chronos`, **vendorisé**
  depuis le tag `v2.3.2` (Apache-2.0). Le livre importe
  `chronos.scripts.training.train`, module **absent du wheel PyPI** (le fichier vit à la
  racine du dépôt amont) : la copie vendorisée porte son en-tête de provenance, et
  `main_finetuned.py` retombe dessus quand l'import amont échoue.

### Protocole

- **Univers** : `AAPL, MSFT, NVDA, AMZN, GOOGL` — panier fixe de cinq
  méga-capitalisations.
- **Entraînement** : 2016-01-01 → 2021-12-31. **Hors échantillon** : 19 origines
  trimestrielles 2022-01-03 → 2026-07-01 (premier jour de bourse de chaque trimestre
  depuis 2022-01-01), chacune évaluée sur son horizon de prévision de **63 séances**
  (séances de bourse de l'index, origine incluse) — le dernier horizon évalué court du
  2026-07-01 au **2026-09-29** (dernière prévision), et la valorisation du dernier
  rebalancement stratégique porte sur le **2026-09-30**, la séance qui suit la dernière
  prévision (`index[i+63]` du harnais, distincte de la fin d'horizon `index[i+62]`).
- Recette du livre : `context_length` 126 jours, `prediction_length` 63 jours,
  `learning_rate` 1e-5, `adamw_torch_fused`, lot 32, accumulation 2, `tf32` (Ampere), 20
  échantillons de prévision par origine.
- **Erreur** : MAE, MASE (naïf de pas 1 sur la fenêtre réelle) et WQL (quantiles
  0,1 / 0,25 / 0,5 / 0,75 / 0,9), moyenne des cinq séries, par origine trimestrielle
  (19 origines).
- **Significativité** : test de Diebold-Mariano apparié par origine sur la perte MAE. Les
  origines trimestrielles ne se chevauchent pas : aucune correction de Newey-West. La
  p-value est celle de l'approximation normale, libérale à 19 origines — la correction de
  Harvey, Leybourne et Newbold ne ferait que l'élargir.
- **Effet de stratégie** : poids SLSQP du livre (long-only, somme 1, maximisation du
  Sharpe des courbes prévues), rebalancement trimestriel, **5 points de base** de frais sur
  le turnover. Les deux bras jouent **la même** origine, avec la même graine de tirage.
- **Graines** : 1, 2, 3 et 42.

### Écarts au livre, assumés

| Écart | Motif |
|---|---|
| `max_steps` = 300 (le livre : 3) | 3 pas ne ré-entraînent rien ; 3 est un budget de temps d'exécution cloud, pas un choix de méthode |
| `torch_compile` = `False` | le livre compile pour Linux/Ampere ; `torch.compile` n'est pas portable sur ce poste |
| Un ré-entraînement par graine sur 2016-2021, évalué hors échantillon | le livre ré-entraîne à chaque trimestre ; le harnais isole l'effet du ré-entraînement sur une fenêtre fixe, ce qui rend les deux bras comparables |
| Univers fixe de cinq méga-capitalisations | le livre sélectionne les cinq titres les plus liquides au dollar-volume, indisponible hors QC. **Cet univers est Mag7** : aucune revendication de gain n'est portée ici (voir le verdict) |
| Données `yfinance` (clôtures ajustées) | le livre lit l'historique du moteur LEAN ; le harnais tourne hors QC |

### Résultat hors échantillon

| Graine | MAE base | MAE ré-entraîné | MASE base | MASE ré-entraîné | DM (statistique) | DM (p) | Sharpe base | Sharpe ré-entraîné |
|---|---|---|---|---|---|---|---|---|
| 1 | 18,40 | 17,61 | 6,24 | 5,99 | 0,83 | 0,409 | 0,746 | 0,603 |
| 2 | 17,78 | 16,87 | 6,03 | 5,69 | 1,43 | 0,153 | 0,664 | 0,751 |
| 3 | 19,21 | 17,82 | 6,50 | 6,02 | 1,68 | 0,093 | 0,588 | 0,746 |
| 42 | 18,31 | 17,30 | 6,27 | 5,83 | 1,14 | 0,256 | 0,559 | 0,675 |
| **moyenne** | **18,43** | **17,40** | **6,26** | **5,88** | — | — | **0,639** | **0,694** |

WQL moyen : 0,0745 → 0,0732. CAGR moyen : 17,5 % → 18,0 %. Pire baisse moyenne :
−29,1 % → −33,5 %. Le champ `mean_diff` du test est signé `base − ré-entraîné` : une
valeur positive veut dire que le **modèle de base** a la plus grande erreur.

**Précision — `NO BEATS`.** Le modèle ré-entraîné est plus précis sur **les quatre
graines** (MAE moyenne 18,43 → 17,40, soit environ −5,5 %), mais **aucune** graine
n'atteint le seuil de 5 % (p de 0,093 à 0,409). L'effet est donc stable dans son signe et
trop petit pour être distingué du bruit à cette taille d'échantillon (19 origines × 5
séries).

**Stratégie — effet instable, aucun gain revendiqué.** Le Sharpe moyen monte
(0,639 → 0,694) et le CAGR aussi, mais le signe **change selon la graine** (une graine sur
quatre voit le ré-entraîné reculer) et la pire baisse se creuse en moyenne.

**Ce que ces chiffres ne sont pas.** Ils ne se comparent pas au Sharpe 0,277 publié pour
l'exemple 18/01 : celui-ci vient d'un backtest LEAN sur 2015-2026, quand la mesure
ci-dessus vient d'un harnais hors QC, sur une autre fenêtre et un autre univers.

**Le désaccord entre les deux mesures d'erreur mérite d'être dit.** La perte
d'entraînement décroît bien au fil des pas (moyenne 4,83 sur les 300 pas de la dernière
graine, 4,66 au dernier pas), sans que cela se transporte hors échantillon. C'est le
comportement attendu d'un ajustement sur la fenêtre d'entraînement, pour un modèle de
cette taille (`chronos-t5-tiny`) et 300 pas.

### Reproduire la mesure

```bash
# GPU local ; la mesure n'a pas besoin de QC Cloud
python finetune/run_finetune_chronos.py --stage all --seeds 1 2 3 42 \
    --max-steps 300 --run-dir <repertoire-de-sortie>
```

Le harnais écrit un fichier par graine dans `<repertoire-de-sortie>/results/`, plus un
`summary.json` agrégeant les graines. Les copies committées vivent sous
`finetune/measures/` : l'arbre QuantConnect ignore `results/`, et `measures/` est la
convention du dépôt pour les mesures conservées.

## Fichiers

- main.py - Stratégie (v1.0, forecasting Chronos)
- main_finetuned.py - Variante ré-entraînée (exemple 18/02, non exécutable en CI)
- finetune/ - Harnais de mesure hors échantillon (local, hors QC Cloud)

## Références

- Hands-On AI Trading, Section 06, Exemple 18
