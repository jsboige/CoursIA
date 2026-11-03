> REFERENCE — vivante — dernière révision 2026-10-30

# Exécuter un carnet QuantBook et rapporter ses sorties

Un carnet QuantBook (`qb = QuantBook()`, `qb.History(...)`) ne s'exécute que dans un noyau LEAN Research. Les sorties committées doivent être celles de ce noyau (règle C.2 et procédure « Exécution Quantbooks » de [procedures-recurrentes.md](../reference/procedures-recurrentes.md)). Elles ne se reconstruisent pas à la main et ne viennent pas d'une substitution de source de données.

Plusieurs lanes ont buté sur le même point : faire tourner le carnet sur QC Cloud, puis récupérer un fichier `.ipynb` qui contient ses sorties. Cette page recense les routes essayées, avec la date et la source de chaque mesure, puis l'étape commune qui ramène les sorties dans la branche.

## Choisir une route

| Route | Noyau | Données | Sorties dans le fichier récupéré | Coût | Usage |
|---|---|---|---|---|---|
| **A** — LEAN Research local (Docker) | machine de la lane | dossier `data/` local | oui (`nbconvert --inplace`) | aucun | les titres du carnet sont couverts par les données locales |
| **B** — exécution directe dans l'IDE QC Cloud | serveur Research QC | toutes les données QC | oui, après un enregistrement explicite (24/10/2026) ; perdues le 30/09/2026 (#18623) | minutes de nœud incluses | **route par défaut** pour un carnet à committer |
| **C** — exécuteur côté noyau | serveur Research QC | toutes les données QC | rendues comme valeur d'une cellule | minutes de nœud incluses | quand « Run All » ne persiste pas les sorties |
| **D** — Research Assistant | serveur Research QC | toutes les données QC | non persistées le 16/05/2026 (#1177) | environ 800 à 1200 QCC par session (estimation, #1195) | explorer, déboguer, reconstruire un carnet |

Les routes se combinent. L'assistant (D) corrige le code d'un carnet qui ne tourne pas ; la route B l'exécute ensuite pour produire les sorties à committer.

## Route A — LEAN Research local

Organe : [`scripts/notebook_tools/qc_quantbook_execute.py`](../../scripts/notebook_tools/qc_quantbook_execute.py) (recette validée le 2026-05-10).

```bash
python scripts/notebook_tools/qc_quantbook_execute.py <dossier_projet_lean> \
    --notebook research.ipynb --port 8889 --timeout 600
```

- Le carnet doit vivre dans un dossier de projet LEAN (à côté de `main.py`), lui-même sous un espace de travail qui contient `lean.json` et `data/`.
- Étape 0 : l'organe extrait les titres demandés (`AddEquity`, `AddForex`, `AddCrypto`) et s'arrête si leurs données locales sont périmées ou dégénérées (#8734). Provisionner l'univers d'abord : section « Provisionnement reproductible des data LEAN locales » de [quantconnect.md](quantconnect.md) (#8627, #8737, #8742).
- Couverture mesurée le 2026-10-23 (#22122) : actions US journalières oui ; en crypto, seul BTCUSD journalier est présent. Le téléchargement d'actions depuis QC est bloqué par l'abonnement Security Master.
- Le `lean` trouvé sur le `PATH` peut être le prouveur Lean 4 installé par elan. Épingler l'outil QC avec la variable `LEAN_CLI` (chemin du `lean.exe` installé par pip).
- Sous Git Bash, préfixer par `MSYS_NO_PATHCONV=1` les commandes qui passent un chemin conteneur (`/Lean/...`).
- Précédents : #8401, #9515, #22019, #22122.

## Route B — exécution directe dans l'IDE QC Cloud

Mesurée le 2026-10-24 sur `research_m12_har_rv_j.ipynb` (PR #22412).

1. **Fermer l'onglet du carnet dans l'IDE QC**, puis envoyer le carnet en texte clair dans le projet QC (MCP `update_file_contents`). Un onglet resté ouvert réécrit sa copie par-dessus l'envoi : recharger et relire le fichier avant d'exécuter.
2. Ouvrir le carnet. **Select Kernel** → « QuantConnect Research Server Collection » → `Foundation-Py-Default`.
3. **Run All**, puis attendre que le bouton « Interrupt » disparaisse.
4. **Enregistrer explicitement** (Ctrl+S). Le 2026-09-30, #18623 avait mesuré des sorties perdues après « Run All » ; le 2026-10-24, l'enregistrement explicite les a gardées.
5. Récupérer le fichier. L'API de fichiers ne rend pas les sorties (voir « Routes refusées »). La lecture passe par le point de lecture de fichiers de l'IDE, depuis la page de l'IDE ouverte dans Playwright :
   - dans le cadre de l'éditeur, relever la requête de ressource de l'IDE (`/vscode-remote-resource?path=...`) ;
   - ne changer que le paramètre `path` (`/home/lean-user/workspace/project/<fichier>`), puis lire avec `fetch(..., {cache: "no-store"})` depuis ce même cadre ;
   - enregistrer le contenu dans un dossier ignoré par git, par un téléchargement du navigateur (`waitForEvent("download")`, puis `saveAs`).

   La requête porte un jeton de session : il reste dans le contexte du navigateur, ne s'imprime pas, ne se recopie ni dans un fichier, ni dans un commentaire, ni dans un journal. Même règle pour le fichier d'espace de travail de l'IDE, qui contient un jeton d'utilisateur QC : ne pas le lire.
6. Ramener les sorties dans la branche avec `merge_executed_outputs.py` (section suivante). Il refuse un fichier dont une cellule de code n'a pas d'`execution_count` : c'est le contrôle de l'étape 4.

## Route C — exécuteur côté noyau

Utile quand le fichier enregistré revient sans sorties. Une cellule unique, en texte clair, exécutée dans le noyau QC :

- lit le carnet cible dans le dossier du noyau ;
- vérifie son empreinte (section suivante) avant d'exécuter quoi que ce soit ;
- exécute les cellules de code une par une dans un espace de noms partagé, en capturant stdout et stderr (et l'affichage riche si l'on passe par `IPython.utils.capture.capture_output`) ;
- rend le résultat comme valeur de la cellule, que l'IDE persiste.

Les sorties capturées se remettent au format nbformat dans un carnet exécuté, que `merge_executed_outputs.py` fusionne ensuite comme en route B, contrôle d'empreinte compris. Mesurée le 2026-10-24 sur `research_m11ef_ensemble.ipynb` (PR #22412, sorties texte seulement). Variante de #18623 : un exécuteur par websocket (protocole Jupyter v1) qui écrit un `*_executed.ipynb`, lu ensuite par `GET /files/`.

Une capture limitée à stdout et stderr perd les figures : pour un carnet qui en trace, préférer la route B, ou capturer l'affichage riche.

## Route D — Research Assistant

Accès et précautions : section « QC Cloud Assistants » de [quantconnect.md](quantconnect.md) et [QC_CLOUD_ASSISTANTS_WORKFLOW.md](../../MyIA.AI.Notebooks/QuantConnect/docs/QC_CLOUD_ASSISTANTS_WORKFLOW.md).

- **Ce qu'il fait bien.** Le 2026-05-16, il a reconstruit un carnet d'apprentissage automatique (une centaine de variables, plusieurs modèles) et corrigé seul les colonnes `NaN`, les longueurs incohérentes et les paramètres d'`adfuller` (#1195, déploiement A-8ad2fb).
- **Ce qu'il ne fait pas.** Le même jour, sur un autre déploiement (A-e22ad0, #1177), il a exécuté les cellules 0 à 5 avec de vraies sorties, mais les sorties n'ont pas été persistées dans le fichier `.ipynb`. Il a aussi modifié les cellules au lieu de seulement les exécuter, et la session a expiré au bout d'une quinzaine de minutes (« No Coding Session Available »).
- **Ses métriques ne se reprennent pas telles quelles.** Il annonçait un Sharpe de 3,50 ; la revalidation du cluster a donné 0,971, sans frais de transaction ni walk-forward dans son calcul (#1195).
- **Coût.** Il consomme des crédits QC. Annoncer le déploiement sur le dashboard et relever le solde de crédits avant de le lancer.

Enchaînement recommandé : l'assistant corrige le carnet dans le projet QC ; la lane relit la source corrigée (MCP `read_file`), la reporte dans la branche, puis l'exécute par la route B. Si l'assistant a laissé un fichier avec ses sorties, `merge_executed_outputs.py` le dit : il refuse un carnet incomplet.

## Ramener les sorties dans la branche

Organe : [`scripts/notebook_tools/merge_executed_outputs.py`](../../scripts/notebook_tools/merge_executed_outputs.py).

```bash
# empreinte du code, avant l'envoi puis après la récupération
python scripts/notebook_tools/merge_executed_outputs.py --fingerprint <carnet_branche> <carnet_recupere>

# copie des sorties, cellule de code par cellule de code
python scripts/notebook_tools/merge_executed_outputs.py <carnet_branche> <carnet_recupere> --dry-run
python scripts/notebook_tools/merge_executed_outputs.py <carnet_branche> <carnet_recupere>
```

- **Empreinte** : sha256 des sources des cellules de code jointes par un saut de ligne, 16 premiers caractères hexadécimaux. Le markdown n'y entre pas : on peut réécrire l'interprétation après l'exécution sans la changer.
- **Refus** : sources de code différentes ou nombre de cellules de code différent (exit 1) ; carnet récupéré incomplet, c'est-à-dire une cellule de code sans `execution_count` ou une sortie `error` (exit 2, levable par `--allow-incomplete` quand l'erreur fait partie de la démonstration).
- **Ce que l'outil copie** : `outputs` et `execution_count`, rien d'autre. Le markdown, les métadonnées et la mise en forme JSON du carnet de la branche sont conservés.
- **Ce n'est pas une retouche de sortie** au sens de la règle 6 de [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) : l'outil transporte les sorties produites par le noyau, et refuse si le code exécuté n'est pas celui de la branche. Une sortie à corriger se corrige dans le code, puis le carnet repasse par la route choisie.

## Contrôles avant la PR

- L'empreinte du carnet de la branche est celle du carnet exécuté.
- `execution_count` consécutifs, aucune sortie `error` non voulue.
- `python scripts/notebook_tools/validate_pr_notebooks.py github/main <carnets>` passe.
- Les ratchets de sortie et de source (`check_output_failure_text`, `check_output_collapse`, `check_source_collapse`) excluent les chemins `/research/` par construction (`EXCLUDE_MARKERS`, [check_output_failure_text.py:118](../../scripts/notebook_tools/check_output_failure_text.py#L118)). Pour un carnet de `QuantConnect/research/`, mesurer à la main, cellule par cellule contre `main`, la longueur des sources et des sorties, et l'écrire dans le body.
- Le body nomme la route, la date d'exécution, le noyau et les empreintes.

## Routes refusées

| Route | Motif | Source |
|---|---|---|
| API de fichiers QC (MCP `read_file`, `POST /api/v2/files/read`) pour récupérer les sorties | rend le carnet avec `execution_count` mais `outputs: []` ; elle reste valable pour lire une source | #1177 |
| Export par l'Object Store | refusé dans cet environnement | mesure du 2026-10-24 (PR #22412) |
| Envoyer à QC un exécuteur dont la source est compressée ou encodée | contraire aux conditions d'utilisation de QuantConnect ; tout ce qui est envoyé à QC est en texte clair | refus du 2026-10-24 |
| Remplacer `qb.History` par yfinance, ou reconstruire les sorties localement | les sorties ne sont plus celles du carnet (règle C.2) | clôture de #1177 (2026-05-27) |
| Retoucher une sortie à la main | falsifie la preuve d'exécution | règle 6 de [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) |

## Pièges mesurés

- **Nœud de recherche R1-4 (1 CPU, 4 Go) et données minute.** Huit sessions sans qu'une seule cellule s'exécute : la poignée de main du noyau ne se termine pas (#4132, 2026-07-01). Verdict `INTRINSIC` pour ce nœud. La question de recherche a été tranchée par une exécution locale sur les données QC téléchargées (#4255, #4452).
- **Sauts de ligne échappés deux fois.** Une source envoyée avec des `\n` littéraux au lieu de vrais sauts de ligne lève des `SyntaxError` dans le noyau (#1177). Relire le fichier dans l'IDE après l'envoi.
- **Fenêtre de données glissante.** `qb.History(..., timedelta(days=N))` change de période à chaque exécution : figer des bornes `datetime` et imprimer la première et la dernière barre de chaque série (PR #22412).
- **Barres sans échange.** En crypto horaire, le serveur QC comble les heures sans échange en répétant la dernière clôture, à volume nul ; une suspension de cotation y devient un saut de prix isolé. Filtrer les barres à volume nul et les rendements qui enjambent un trou (PR #22412).
- **Fuseau des bornes.** Les bornes passées à `qb.History` semblent lues dans le fuseau du QuantBook (New York) alors que l'index des séries est en UTC (constat de la PR #22412, non vérifié à la source). Imprimer les dates des barres plutôt que de supposer l'alignement.

## Voir aussi

- [quantconnect.md](quantconnect.md) — MCP, provisionnement des données, assistants
- [QC_CLOUD_ASSISTANTS_WORKFLOW.md](../../MyIA.AI.Notebooks/QuantConnect/docs/QC_CLOUD_ASSISTANTS_WORKFLOW.md) — assistants, coûts, matrice de délégation
- #1177 (tentatives de mai 2026), #1195 (assistants), #4132 (nœud R1-4), #18623 (exécution par websocket), #21836 (re-exécution des carnets de recherche)
