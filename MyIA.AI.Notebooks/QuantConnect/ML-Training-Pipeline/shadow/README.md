# Suivi en ombre des stratégies candidates

Expérience 5c de #18907, outillée par #18923.

Un backtest se refait autant de fois qu'on veut : on finit toujours par trouver la variante qui gagne sur le passé. Le suivi en ombre sépare l'idée de son évaluation. Une candidate est **gelée** à une date D, puis rejouée chaque mois sur des données qui n'existaient pas quand elle a été écrite. Au bout de quelques mois, le CSV montre comment elle s'est comportée hors de l'échantillon qui a servi à la choisir.

## Les trois règles

1. **Geler.** À la date D, la candidate entre dans le registre avec le SHA du commit, ses paramètres, son hypothèse de frais et D. Son code ne change plus.
2. **Rejouer.** Chaque mois, chaque candidate gelée est rejouée de D à la date du passage, avec son code gelé. Une ligne s'ajoute au CSV.
3. **Ne rien retirer.** Une candidate qui perd reste suivie. La modifier crée une **nouvelle** candidate, avec un nouvel identifiant et un nouveau D ; l'ancienne continue d'être rejouée.

L'outil `scripts/shadow_replay.py` rend ces règles mécaniques :

| Règle | Ce qui la fait tenir |
|---|---|
| Geler | chaque entrée du registre porte une empreinte de ses champs ; une entrée modifiée à la main est refusée |
| Rejouer avec le code gelé | le point d'entrée tourne dans un worktree détaché au SHA gelé, dans un processus à part ; le code courant n'est jamais exécuté |
| Ne rien retirer | une ligne du CSV dont la candidate a disparu du registre est refusée ; `freeze` refuse un identifiant déjà pris |
| Un passage par mois | le CSV ne s'écrit qu'en ajout, et refuse un second passage de la même candidate dans le même mois |

Toute commande commence par `validate` : si le registre ou le CSV viole une règle, rien n'est rejoué.

Limite : seul le code est gelé. L'environnement Python (versions de numpy, pandas et des autres bibliothèques) est celui de la machine qui rejoue. Un écart entre deux passages peut donc venir d'une mise à jour de bibliothèque ; le noter dans la PR du passage quand l'environnement a changé.

## Fichiers

| Fichier | Contenu |
|---|---|
| `registry.json` | les candidates gelées (créé par le premier `freeze`) |
| `passes.csv` | une ligne par candidate et par passage, en ajout seul |

Les séries journalières complètes ne vont pas dans le dépôt : `--series-dir` les écrit dans un dossier externe, dont le chemin se cite dans la PR du passage.

Colonnes de `passes.csv` :

| Colonne | Définition |
|---|---|
| `candidate`, `sha`, `frozen_on` | l'identité gelée, recopiée du registre |
| `pass_date` | date du passage |
| `period_end` | dernière séance de la période rejouée |
| `n_days` | nombre de séances, de D à `period_end` |
| `sharpe_net` | moyenne / écart-type (ddof = 1) × √252 des rendements journaliers nets, taux sans risque nul ; vide si l'écart-type est nul |
| `cagr` | produit des (1 + r) à la puissance 1 / années, moins 1 ; années = jours calendaires entre la première et la dernière séance, divisés par 365,25 |
| `max_drawdown` | minimum de équité / maximum courant − 1 |
| `turnover` | rotation journalière moyenne (fraction de l'équité échangée) |
| `fees` | coût de transaction cumulé, en fraction de l'équité de départ |
| `fee_model` | hypothèse de frais recopiée du registre |

Sharpe, CAGR et pire baisse reprennent les définitions du verdict de la 5a (`voltarget_strategy_verdict.py`, #18943) : une candidate suivie en ombre se compare directement à ses chiffres.

## Contrat d'une candidate locale

Le point d'entrée s'écrit `chemin/module.py:fonction`, relatif à la racine du dépôt. La fonction reçoit `start` et `end` (dates ISO) et les paramètres du registre ; elle rend un dictionnaire :

| Clé | Contenu |
|---|---|
| `dates` | les séances, au format ISO |
| `net_returns` | rendements journaliers nets de frais, un par séance |
| `turnover` | rotation journalière, une valeur par séance |
| `fees` | coût cumulé sur la période, en fraction de l'équité de départ |

Les imports voisins du module (`from realized_variance import ...`) sont résolus dans le code gelé.

## Commandes

Depuis `ML-Training-Pipeline/` :

```bash
# Geler une candidate (le SHA est résolu en SHA complet, D vaut aujourd'hui par défaut)
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv \
  freeze --id <identifiant> --kind local --sha <commit> \
  --entrypoint <chemin/module.py:fonction> --params '{"cle": 1}' --fee-model "5bps notional"

# Vérifier registre et CSV
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv validate

# Lister les candidates dues pour le passage du jour
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv due

# Rejouer les candidates locales dues et ajouter leurs lignes
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv \
  replay-local --series-dir <dossier hors dépôt>
```

## Cadence

Un passage par mois, à la première séance du mois. Chaque passage est une PR qui ne touche que `passes.csv`. Elle cite la sortie de `validate` et le dossier des séries.

## Ce qui n'est pas encore là

- **Le rejeu QuantConnect.** Une candidate `qc` se gèle déjà dans le registre (son point d'entrée est l'identifiant du projet QC), et `due` la liste. Mais `replay-local` la saute en le disant. Son rejeu passe par un backtest lancé par le MCP, dates en paramètres, et par la lecture de la courbe d'équité journalière, qui dépend de #18939. Il rendra la même ligne de CSV.
- **Les premières inscriptions et le rythme automatique** sont les étapes 2 et 3 de #18923.
