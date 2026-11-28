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
| `league_members.json` | séries de la matrice de corrélation de la ligue (#19821, brique 4) : une variante mesurée par stratégie, avec son issue et sa PR de mesure |

Les séries journalières complètes ne vont pas dans le dépôt : `--series-dir` les écrit dans un dossier externe, dont le chemin se cite dans la PR du passage.

Colonnes de `passes.csv` :

| Colonne | Définition |
|---|---|
| `candidate`, `sha`, `frozen_on` | l'identité gelée, recopiée du registre |
| `pass_date` | date du passage |
| `period_end` | dernière séance clôturée rendue par la candidate pour `end = pass_date` ; bornée par le harnais à `frozen_on ≤ period_end ≤ pass_date`, sans décalage fixe — c'est la donnée disponible qui décide : un passage un lundi s'arrête au vendredi précédent, un passage en semaine peut atteindre la veille |
| `n_days` | nombre de séances de D à `period_end` ; D est fixe au gel et la fenêtre ne se tronque jamais, donc `n_days` ne fait que croître — par blocs d'environ 21 séances par mois, au rythme des jours de semaine des passages (aucune fenêtre n'est sélectionnable) |
| `sharpe_net` | moyenne / écart-type (ddof = 1) × √252 des rendements journaliers nets, taux sans risque nul ; vide si l'écart-type est nul |
| `cagr` | produit des (1 + r) à la puissance 1 / années, moins 1 ; années = jours calendaires entre la première et la dernière séance, divisés par 365,25 |
| `max_drawdown` | minimum de équité / maximum courant − 1 |
| `turnover` | rotation journalière moyenne (fraction de l'équité échangée) |
| `fees` | coût de transaction cumulé, en fraction de l'équité de départ |
| `fee_model` | hypothèse de frais recopiée du registre |

Sharpe, CAGR et pire baisse viennent de `scripts/strategy_metrics.py`, le module que partage aussi le verdict de la 5a (`voltarget_strategy_verdict.py`, #18943) : une candidate suivie en ombre se compare directement à ses chiffres.

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
2. **Une clôture par séance, à sa date.** À chaque clôture, la valeur du portefeuille va dans le graphique `shadow`, séries `e0` à `e4` à tour de rôle. Une série unique serait rééchantillonnée par QC sur sa propre grille ; cinq séries entrelacées gardent chaque point à sa séance (#18939). Une candidate crypto souscrit sans remplissage vers l'avant (`fill_forward=False`) : un passage lancé avant minuit UTC recevrait sinon, à la date du passage, une barre qui répète la clôture de la veille (#24153). Pour les actions, même garde côté candidate : la barre journalière des toutes dernières séances d'un passage n'est pas toujours encore publiée, et Lean la recopie vers l'avant — une candidate qui trace dans `on_data` saute une barre recopiée (`data.bars[spy].is_fill_forward`), sans quoi le passage mesure des séances plates (backtest `273d04de` du 2026-11-20, retiré de #27480 ; garde posée dans `ShortUnprofitableIntl-QC`, #27482). Une candidate gelée avant cette garde, comme `short-intl-v2`, n'en bénéficie pas : pour elle, la même situation est refusée au moment d'`ingest-qc`, sur le graphique `Benchmark` du backtest (voir la liste des refus).
3. **Les coûts, tracés par la candidate.** Au même moment, `fees` (frais cumulés / valeur de départ) et `turnover` (somme des montants exécutés / valeur du portefeuille au moment de l'exécution). `read_backtest` ne rend que les totaux de fin de backtest, pas une valeur par séance.

QC ne garde que dix séries tracées par backtest, tous graphiques confondus, et perd les dernières créées sans erreur. Le contrat en prend sept (`e0..e4`, `fees`, `turnover`) et laisse trois séries libres pour des contrôles ; au-delà, des séries du contrat peuvent disparaître (mesure du 2026-11-10, #24153 : douze séries, `e0` perdue).

`ingest-qc` refuse le passage quand :

- le backtest n'est pas terminé (`completed` différent de `true`), a échoué, ou ne porte pas le nom prévu par le plan ;
- les points d'équité, rangés par date, ne se succèdent pas `e0`, `e1`, … `e4`, `e0` : un point perdu ou en trop casse ce cycle. C'est aussi ce qui arrive si QC tronque ou rééchantillonne une série trop longue ; le passage est alors refusé, jamais calculé sur une courbe incomplète ;
- deux points tombent sur la même séance, ou l'équité sort de [D, date du passage] ;
- le graphique porte plus de points d'équité que le backtest n'a de dates de données (`tradeableDates`) : une barre recopiée par remplissage vers l'avant en est une cause mesurée (#24153) ;
- le dernier point de `fees` ou de `turnover` n'est pas sur la dernière séance ;
- le dossier du plan n'a pas de `benchmark.json`, ou son graphique `Benchmark` s'arrête avant la dernière clôture d'équité : sans ce témoin entier, la publication des dernières séances ne se lit pas ;
- le graphique `Benchmark` vaut 0.0 sur tous ses points et aucun témoin n'est donné. C'est le graphique de tout projet qui fixe le modèle de courtage IB sans appeler `set_benchmark` : mesure du 2026-11-27 sur `fs774`, `splits-lo`, `levetf-base`, `levetf-postfix` et `x775-lev1` ; `halloween-v2`, gelée avant #28893, est dans le même cas. Sans cotation, chaque séance se lirait figée. Le témoin est alors le dossier d'une autre candidate de la même passe (`--witness-dir`), dont le graphique `Benchmark` cote le marché. Son backtest est terminé, porte le nom prévu par son plan et a été lancé au plus tard en même temps que celui de la candidate (champ `created` de `read_backtest`) : une barre publiée quand le témoin l'a lue l'était encore pour la candidate lancée après lui. Les deux contrôles suivants se lisent alors sur le graphique du témoin. Un témoin donné à une candidate qui cote elle-même le marché est refusé : il n'y a qu'une lecture par passage ;
- les barres du benchmark des dernières séances n'étaient pas publiées au passage (à partir de deux séances de suite). Chaque point du graphique `Benchmark` porte la clôture de la séance de la veille, un point par jour de calendrier ; un point de jour de semaine qui répète celui de la veille dit que cette barre n'est pas arrivée et que Lean l'a recopiée. L'équité, elle, ne distingue pas une séance plate d'un portefeuille en liquidités. Une seule séance répétée reste admise : c'est aussi la forme d'un jour de marché fermé la veille du passage (backtest `273d04de`, #27482) ;
- le témoin de ces barres est incomplet. Un jour de semaine sans point autour des dernières séances est une rupture de couverture, pas un week-end : un écart qui ne laisse passer que des samedis et des dimanches garde la suite. De part et d'autre d'un trou, le graphique ne lit que le groupe — clôtures égales, toutes les séances du trou étaient figées ; clôtures différentes, au moins une était publiée, sans dire laquelle. Les séances du trou ne se comptent jamais avec celles d'avant. Le passage est refusé quand un scénario possible atteint deux séances de suite ; un graphique `Benchmark` qui s'arrête avant la date du passage laisse de même sa dernière séance sans lecture.

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
4. `read_backtest_chart` avec `name` = `chart`, `start` = `chart_start`, `end` = `chart_end`, `count` = `chart_count` et `out_path` = `<dossier du plan>/chart.json` ;
5. la même lecture avec `name` = `benchmark_chart` (le graphique `Benchmark` du backtest) et `out_path` = `<dossier du plan>/benchmark.json`.

```bash
# Relire le passage et ajouter sa ligne
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv \
  ingest-qc --plan-dir <dossier hors dépôt>/<identifiant> --series-dir <dossier hors dépôt>
```

Une candidate dont le graphique `Benchmark` vaut 0.0 partout se rejoue **après** une candidate de la même passe qui cote le marché. Son passage se relit avec le dossier de celle-ci en témoin :

```bash
python scripts/shadow_replay.py --registry shadow/registry.json --csv shadow/passes.csv \
  ingest-qc --plan-dir <dossier hors dépôt>/<identifiant> \
  --witness-dir <dossier hors dépôt>/<témoin> --series-dir <dossier hors dépôt>
```

Un backtest à la fois, annoncé sur le tableau de bord de coordination : le quota d'appels QC est partagé par toute la flotte.

## Points d'entrée disponibles

| Point d'entrée | Ce qu'il rejoue | Paramètres |
|---|---|---|
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/shadow_inverse_vol.py:inverse_vol` | la règle à inverse de la volatilité du harnais papier, sur SPY, QQQ, IEF et GLD, telle que l'expérience #19072 l'a mesurée ; rendements d'un investisseur en euros | `convention` : `"U"` (volatilité des cours en dollars) ou `"F"` (volatilité des cours convertis en euros) ; `target` : la cible de `inverse_vol_weights` (0,025 dans le verdict de #19072) |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/shadow_etf_rotation.py:etf_rotation` | la rotation mensuelle par momentum entre six poches d'actions UCITS cotées en euros, pré-inscrite dans #28992, avec repli sur une ligne d'attente monétaire | `top` : nombre de poches choisies (2) ; `look` et `skip` : fenêtre du momentum en fins de mois (9 et 1) ; `band` : écart de poids qui déclenche un ordre (0,02) ; `fee` : frais par unité de poids échangée (0,001) |

Fonctionnement de `inverse_vol` :

- il importe `inverse_vol_currency.py` (règle du harnais, conversion en euros, simulation) au lieu de le recopier : une candidate gelée rejoue le code qui a produit le verdict de #19072 ;
- le portefeuille reste en liquidités jusqu'à la première séance à partir de D. Sa clôture porte l'allocation d'ouverture et ses frais ; viennent ensuite les dernières séances des mois terminés ;
- les séances rejouées vont de D inclus à la date du passage exclue : la séance du jour peut être encore ouverte quand le passage tourne ;
- fenêtre de volatilité, plafond par ligne, bande et frais sont ceux de #19072 ;
- les cours (Yahoo, ajustés des dividendes) sont téléchargés à chaque passage dans un dossier temporaire.

Fonctionnement de `etf_rotation` :

- à chaque fin de mois, il classe six poches d'actions cotées à Paris (petites capitalisations de la zone euro, valeur, qualité, croissance, émergents, Japon) par leur momentum 9-1, le rendement de la fin de mois t-9 à la fin de mois t-1 ;
- les deux premières reçoivent chacune la moitié. Une poche choisie dont le momentum n'est pas strictement positif laisse sa moitié à la ligne d'attente (taux au jour le jour en euros) ;
- ouverture, fenêtre et calendrier des rotations sont ceux d'`inverse_vol` ; une ligne n'est retraitée que si son écart au poids cible atteint la bande ;
- le calendrier est celui des séances communes aux six poches, et la ligne d'attente, cotée sur une autre place, y est reportée à sa dernière clôture ;
- une poche sans ses neuf fins de mois d'historique arrête le passage en erreur : la règle ne se replie jamais sur moins de poches.

## Corrélation hebdomadaire de la ligue

`scripts/league_correlation.py` corrèle les courbes de capital déjà mesurées sur QC Cloud, lues dans les traces (`chart.json`, graphique `shadow`), sans relancer de backtest. Chaque série devient une suite de rendements hebdomadaires arrêtés au vendredi, pour que les séries crypto, qui ont des points le week-end, se comparent aux séries actions. Chaque paire reçoit une corrélation de Pearson sur ses semaines communes et un intervalle par bootstrap circulaire par blocs apparié. Le protocole est écrit dans #20083.

```bash
python scripts/league_correlation.py --traces-root <dossier des traces> --against spy --json matrice.json
```

`--against` rapporte chaque série à un membre et la place par rapport au seuil de 0,7 de la règle d'entrée du panier, sans décider de l'entrée. La colonne « Investies » donne la part de semaines où la stratégie n'était pas en liquide : une corrélation proche de zéro se lit sur ces seules semaines.

Le cœur actions n'a pas de trace QC : c'est la règle de volatilité inverse du harnais paper (#19072). `scripts/league_core_series.py` calcule sa série hors QC, par le point d'entrée de l'ombre, et l'écrit dans `series.csv` ; le membre `core-equity` la lit avec `"kind": "local"`. La règle y est tenue sur un compte en USD, comme les autres membres : compté en euros, le cœur porterait le change EUR/USD sur sa liquidité, et sa corrélation aux autres membres baisserait de 0,19 en moyenne (#20365).

```bash
python scripts/league_core_series.py --out <traces>/20365-league-core/core-equity \
    --closes-dir <traces>/20365-league-core/closes
```

## Cadence

Un passage par mois, à la première séance du mois. Chaque passage est une PR qui ne touche que `passes.csv`. Elle cite la sortie de `validate` et le dossier des séries.

## Ce qui n'est pas encore là

- **Les candidates dues** : `btc-voltarget-v2` a eu son premier passage accepté le 2026-11-15 (`passes.csv`). Le premier passage de `short-intl-v2` reste dû : celui du 2026-11-20 a été retiré de #27480 — les barres journalières des dernières séances n'étaient pas encore publiées et le backtest mesurait des séances plates ; la garde est posée côté candidate (règle 2, #27482) et côté harnais (`ingest-qc` refuse un passage dont les barres du benchmark n'étaient pas publiées) ; le passage se refait une fois les séances publiées. `drk-kernel` et `halloween`, gelées le 2026-11-08, sont hors contrat (dates lues par défaut, ni `fees` ni `turnover`, projet de la mesure publiée au point d'entrée) : la correction est livrée sur `main` (#27482), leur gel en `drk-kernel-v2` et `halloween-v2` sur un projet dédié est fait (2026-11-22, SHA `fc56eec4cc09`) ; leur premier passage est dû au prochain passage mensuel (fenêtre nulle le jour du gel). Un passage QC demande le MCP QuantConnect, absent de plusieurs sièges : sur un siège sans MCP, les candidates QC restent dues.
- **Le rythme automatique** (étape 3 de #18923) : le décideur existe (`scripts/shadow_schedule.py`), aucun déclencheur planifié ne l'appelle — la cadence est encore tenue à la main.

Un passage pris en cours de mois plutôt qu'à la première séance ne fausse pas la lecture : la fenêtre hors échantillon ne fait que s'allonger de D à la date du passage, et `due` ne l'ouvre qu'une fois par mois et par candidate.
