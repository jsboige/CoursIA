# RiskKernel — module canonique du noyau de risque déterministe

`risk_kernel.py` porte `RiskKernel`, le noyau de risque déterministe de Steward (arXiv 2610.30557) tel que l'appliquent deux stratégies du dépôt :

| Projet | Lignes | Rééquilibrage | Paramètre |
|---|---|---|---|
| `HAR-RV-Kelly` | six ETF | chaque lundi | `kernel` |
| `Cloud-VolTargeting` | SPY seul (variante v1) | mensuel | `kernel`, plus `reentry` |

Avant l'extraction (#24698), chaque projet portait sa propre copie du noyau dans `main.py`. Les deux copies faisaient la même chose sur tous les chemins que les backtests empruntent ; elles différaient sur des chemins sans effet, par exemple un stop qu'on annule alors qu'aucun n'est posé, ou la liquidation d'une ligne déjà à plat. Le module reprend la version de `HAR-RV-Kelly`, qui gère plusieurs lignes. Les deux stratégies l'importent désormais.

Le projet `DeterministicRiskKernel-QC` (#25221) garde son propre portage, écrit depuis le carnet de recherche, sur dix ETF : il n'est pas concerné par ce module.

## Les trois protections

Le paramètre `kernel` de la stratégie choisit les protections actives. Avec la valeur par défaut, `off`, le noyau ne passe aucun ordre et la stratégie se comporte comme sans lui.

| `kernel` | Plafond d'exposition à 90 % | Stop à 2 ATR(14) | Coupe-circuit à −3 % |
|---|---|---|---|
| `off` (défaut) | non | non | non |
| `cap90` | oui | non | non |
| `kernel_nocb` | oui | oui | non |
| `kernel` | oui | oui | oui |

- **Plafond** : l'exposition brute ne dépasse pas 90 %, sans levier. Les poids cibles sont réduits en proportion.
- **Stop** : chaque ordre d'entrée porte un stop à 2 ATR(14) sous le prix de l'ordre. Une ligne stoppée reste hors marché jusqu'au rééquilibrage suivant.
- **Coupe-circuit** : après une séance close à −3 % ou pire, liquidation à l'ouverture suivante, une séance à plat, puis re-entrée sur les cibles du dernier rééquilibrage. En données journalières la clôture n'est connue qu'après coup : c'est pourquoi la liquidation attend l'ouverture.

## Utilisation dans une stratégie

La stratégie garde ses signaux et son calendrier ; le noyau ne décide que de l'exécution.

```python
from risk_kernel import RiskKernel, check_mode

# dans initialize, APRES avoir enregistre le reequilibrage de la strategie
check_mode(self.kernel)
self.risk = RiskKernel(self, self.kernel, {"SPY": self.symbol("SPY")}, self.symbol("SPY"))

# au reequilibrage
weights = self.risk.cap(weights)
if self.risk.rebalance(weights):
    return              # le noyau a passe les ordres (modes avec stop ou coupe-circuit)
# sinon (off, cap90) : la strategie passe ses ordres comme avant

# a chaque seance close :            self.risk.on_close()
# dans on_order_event(self, event) : self.risk.on_order_event(event)
# en fin de backtest :               for k, v in self.risk.statistics().items(): self.set_runtime_statistic(k, v)
```

Deux contraintes :

- **Ordre de construction.** `RiskKernel` enregistre sa tâche quotidienne du coupe-circuit à sa construction. Il doit être construit après l'enregistrement du rééquilibrage de la stratégie : le jour du rééquilibrage, celui-ci passe alors en premier.
- **Ordre des lignes.** L'ordre du dictionnaire `{ticker: Symbol}` est l'ordre de passage des ordres. Le changer change la séquence des ordres, donc les remplissages.

`reopen_stopped()` est une variante diagnostique : branchée sur un calendrier hebdomadaire (paramètre `reentry=week` de `Cloud-VolTargeting`), elle fait revenir les lignes stoppées sur les cibles du dernier rééquilibrage sans attendre le suivant.

`statistics()` rend six statistiques d'exécution : `Noyau`, `Stops`, `Coupures`, `Ordres invalides`, `Exposition max`, `Seances a plat`. Toutes les valeurs sont des chaînes (`str`), directement utilisables par `set_runtime_statistic`. Pour un calcul ou un tracé numérique, convertir explicitement la valeur concernée ; `Seances a plat` est un rapport textuel sous la forme `nombre/total`.

## Des copies identiques, vérifiées par une garde

QuantConnect n'importe que les fichiers du projet qu'il exécute. Chaque projet qui utilise le noyau porte donc une **copie identique à l'octet** de ce fichier, à côté de son `main.py`. Ce dossier en garde la version canonique.

On aurait pu attacher ce dossier comme bibliothèque de projet QC, comme `SharedPCM`. Ce n'est pas le choix fait ici, pour deux raisons. L'attachement est un geste manuel dans l'éditeur QC, à refaire pour chaque projet consommateur. Et un projet dont la bibliothèque manque compile quand même : l'erreur n'apparaît qu'au lancement du backtest, dans `Initialize()`. Une copie se téléverse avec le projet, et une garde CI vérifie qu'elle n'a pas divergé. Passer à une bibliothèque reste possible plus tard, si le nombre de projets consommateurs le justifie.

La garde `scripts/quantconnect/check_risk_kernel_copies.py` cherche tous les fichiers `risk_kernel.py` sous `projects/` et les compare à la copie canonique (fins de ligne normalisées). Elle signale :

| Code | Cas |
|---|---|
| `COPY_DRIFT` | une copie diffère de la version canonique |
| `COPY_MISSING` | un fichier `.py` importe `risk_kernel` sans copie dans son dossier |
| `CANONICAL_MISSING` | la version canonique est absente |

Elle tourne en CI dans la voie rapide (`risk-kernel-copies-guard`, bloquante) dès qu'un fichier Python sous `projects/` change.

Pour modifier le noyau :

```bash
# 1. editer projects/RiskKernel/risk_kernel.py
# 2. recopier vers chaque projet consommateur
cp MyIA.AI.Notebooks/QuantConnect/projects/RiskKernel/risk_kernel.py MyIA.AI.Notebooks/QuantConnect/projects/HAR-RV-Kelly/
cp MyIA.AI.Notebooks/QuantConnect/projects/RiskKernel/risk_kernel.py MyIA.AI.Notebooks/QuantConnect/projects/Cloud-VolTargeting/
# 3. verifier
python scripts/quantconnect/check_risk_kernel_copies.py
```

Une modification du noyau change les ordres des deux stratégies : elle se mesure par un backtest de chacune, avant et après.

## Mesures

Les résultats du noyau par stratégie (statistiques, coût, lecture) sont dans le README de chaque projet : [HAR-RV-Kelly](../HAR-RV-Kelly/README.md#noyau-de-risque-déterministe-24698), [Cloud-VolTargeting](../Cloud-VolTargeting/README.md#noyau-de-risque-déterministe-24698).

L'extraction ne change aucun ordre. Le 16/11/2026, sur QuantConnect Cloud, le code d'avant (noyau en ligne) et le code extrait ont été lancés avec les mêmes paramètres : HAR-RV-Kelly en `off`, `cap90` et `kernel` (2015-2024), Cloud-VolTargeting en `off`, `kernel` et `kernel` + `reentry=week` (2018-2024). Sur les six paires, les ordres lus par l'API (horodatage, titre, quantité, type, étiquette, prix d'exécution) et les statistiques, y compris celles du noyau, sont identiques.

## Fichiers

| Fichier | Description |
|---|---|
| `risk_kernel.py` | Version canonique du noyau : `RiskKernel`, `check_mode`, constantes `MODES`, `EXPOSURE_CAP`, `STOP_ATR`, `ATR_PERIOD`, `CB_THRESHOLD`, `MIN_WEIGHT` |
