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
| Rejouer avec le code gelé | candidate locale : le point d'entrée tourne dans un worktree détaché au SHA gelé, dans un processus à part ; candidate QC : `plan-qc` extrait les fichiers du projet au SHA gelé, avec leurs empreintes. Le code courant n'est jamais rejoué |
| Ne rien retirer | une ligne du CSV dont la candidate a disparu du registre est refusée ; `freeze` refuse un identifiant déjà pris |
| Un passage par mois | le CSV ne s'écrit qu'en ajout, et refuse un second passage de la même candidate dans le même mois |

Toute commande commence par `validate` : si le registre ou le CSV viole une règle, rien n'est rejoué.

Limite : seul le code est gelé. L'environnement Python (versions de numpy, pandas et des autres bibliothèques) est celui de la machine qui rejoue, ou la version de LEAN du jour pour une candidate QC. Un écart entre deux passages peut donc venir d'une mise à jour de bibliothèque ou de moteur ; le noter dans la PR du passage quand l'environnement a changé.

## Fichiers

| Fichier | Contenu |
|---|---|
| `registry.json` | les candidates gelées (créé par le premier `freeze`) |
| `passes.csv` | une ligne par candidate et par passage, en ajout seul |
| `qc_example/main.py` | candidate QC d'exemple, qui montre le contrat d'une candidate QuantConnect (pas une candidate à suivre) |

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

## Contrat d'une candidate QuantConnect

Le point d'entrée s'écrit `chemin/du/projet:identifiant`, où le chemin est le dossier du projet dans le dépôt et l'identifiant celui d'un projet QC **dédié au suivi en ombre** : chaque passage y pousse le code gelé et écrase ce qui s'y trouve. Tous les fichiers `.py` du dossier sont poussés, chacun sous la limite de 64 000 caractères d'un fichier de projet QC.

L'algorithme respecte trois règles ; `qc_example/main.py` les montre sur un 60/40 rebalancé chaque mois :

1. **Dates en paramètres.** `start` et `end` (ISO) viennent de `get_parameter`, sans valeur par défaut : un backtest lancé sans eux échoue au lieu de tourner sur une période implicite. Les deux noms sont réservés : un paramètre de registre qui les porte est refusé.
2. **Une clôture par séance, à sa date.** À chaque clôture, la valeur du portefeuille va dans le graphique `shadow`, séries `e0` à `e4` à tour de rôle. Une série unique serait rééchantillonnée par QC sur sa propre grille ; cinq séries entrelacées gardent chaque point à sa séance (#18939).
3. **Les coûts, tracés par la candidate.** Au même moment, `fees` (frais cumulés / valeur de départ) et `turnover` (somme des montants exécutés / valeur du portefeuille au moment de l'exécution). La sortie de `read_backtest` ne porte ni l'un ni l'autre.

`ingest-qc` refuse le passage quand :

- le backtest n'est pas terminé (`completed` différent de `true`), a échoué, ou ne porte pas le nom prévu par le plan ;
- les points d'équité, rangés par date, ne se succèdent pas `e0`, `e1`, … `e4`, `e0` : un point perdu ou en trop casse ce cycle. C'est aussi ce qui arrive si QC tronque ou rééchantillonne une série trop longue ; le passage est alors refusé, jamais calculé sur une courbe incomplète ;
- deux points tombent sur la même séance, ou l'équité sort de [D, date du passage] ;
- le dernier point de `fees` ou de `turnover` n'est pas sur la dernière séance.

Les rendements journaliers sont ceux de la courbe d'équité, frais déjà déduits par QC ; la rotation journalière est la rotation cumulée divisée par le nombre de séances. Les définitions de Sharpe, CAGR et pire baisse sont celles du rejeu local. Le Sharpe de QC, lui, retranche un taux sans risque : les deux ne se comparent pas directement.

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

# Candidate QC : geler, puis préparer le passage (fichiers gelés + plan.json par candidate)
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv \
  freeze --id <identifiant> --kind qc --sha <commit> \
  --entrypoint <chemin/du/projet>:<identifiant QC> --fee-model "modèle de frais par défaut de QC"
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv \
  plan-qc --out-dir <dossier hors dépôt>
```

Entre `plan-qc` et `ingest-qc`, l'opérateur passe par le MCP QuantConnect (l'API QC ne s'appelle que par lui), avec les valeurs de `plan.json` :

1. pousser chaque fichier de `files/` dans le projet `qc_project_id` (`update_file_contents`, ou `create_file` pour un fichier absent du projet) ;
2. compiler (`create_compile`, `read_compile`), puis `create_backtest` avec `backtest_name` et `parameters` ;
3. relire `read_backtest` jusqu'à `completed: true` et enregistrer sa sortie dans `backtest.json`, dans le dossier du plan ;
4. `read_backtest_chart` avec `name` = `chart`, `start` = `chart_start`, `end` = `chart_end`, `count` = `chart_count` et `out_path` = `<dossier du plan>/chart.json`.

```bash
# Relire le passage et ajouter sa ligne
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv \
  ingest-qc --plan-dir <dossier hors dépôt>/<identifiant> --series-dir <dossier hors dépôt>
```

Un backtest à la fois, annoncé sur le tableau de bord de coordination : le quota d'appels QC est partagé par toute la flotte.

## Cadence

Un passage par mois, à la première séance du mois. Chaque passage est une PR qui ne touche que `passes.csv`. Elle cite la sortie de `validate` et le dossier des séries.

## Ce qui n'est pas encore là

- **Les premières inscriptions et le rythme automatique** sont les étapes 2 et 3 de #18923.
