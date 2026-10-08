# Diagnostic #19863 — Vidage silencieux de `FineFundamentalUniverseSelectionModel`

> **Issue** : [#19863](https://github.com/jsboige/CoursIA/issues/19863) `fix(qc): l'univers fine-fundamental se vide silencieusement -- runs vides sans erreur (portage 9031)`
> **Part of** : [#19678](https://github.com/jsboige/CoursIA/issues/19678) (portage QC Cloud de l'article 9031, Ichimoku secteur énergie) — EPIC [#11698](https://github.com/jsboige/CoursIA/issues/11698)
> **Lane** : `myia-po-2023:CoursIA-2` (c.1163, G-VAR-1 DEEP/research-code) — vérification finale c.1174
> **Statut (c.1177, revu c.1197)** : DIAGNOSTIC + FIX + VÉRIFICATION PLEIN BLOC — fix livré (`a745f2545d`, PR #19864) ; verdict re-basé sur conteneur 24 mois (`73433c968a`) ; **extension plein bloc 6,1 ans mesurée c.1174** (4 860 ordres, +12,6 % cumulé vs baseline +311,4 %, MaxDD 30,2 % ; verdict pré-enregistré inchangé, `INCONCLUSIVE`). Issue **prête à examiner** par le coord/adjoint — la fermeture reste à faire et leur appartient (handoff de `myia-po-2023:CoursIA` reçu 08/10 11:04Z, msg-20261008T090435-vyni7i).

## 1. Symptôme (verbatim de l'issue)

Sur le projet QC Cloud `IchimokuEnergySector-9031` (id `37468246`), un backtest en
`mode: strategy` peut **compléter normalement** en ne négociant **rien** :

- `statistics["Total Orders"] = "0"`, `Total Fees = "$0.00"`, `End Equity = "1000000"` ;
- la courbe d'equity est **plate au centime** (une seule valeur distincte sur ~840 points) ;
- **aucune erreur n'est levée** — `status: "Completed."`, `progress: 1`.

Le même harnais, même nœud, mêmes bornes, en `mode: xle_hold`, complète et négocie normalement.
**Le mur est donc sur le chemin `FineFundamentalUniverseSelectionModel` de la stratégie.**

## 2. Mesure (2026-10-08, plateau `list_backtests`)

| Fenêtre | Durée | Ordres | Statut |
|---|---|---|---|
| 2015-08-10 → 2015-10-10 | 2 mois | **848** | négocie |
| 2020-02-19 → 2020-03-23 | 1 mois | 0 | **vide** |
| **2020-08-17 → 2022-08-16** | 24 mois | **839** | négocie |
| 2021-01-01 → 2022-01-01 | 12 mois | 0 | **vide** |
| 2021-08-17 → 2022-08-16 | 12 mois | 0 | **vide** |
| 2022-08-16 → 2023-08-16 | 12 mois | 0 | **vide** |
| 2020-08-17 → 2026-09-30 (bloc gelé du pré-enregistrement) | 6,1 ans | — | **ne complète pas** (gel puis abandon) |
| 2020-08-17 → 2026-09-30 (`mode: xle_hold`) | 6,1 ans | 1 | complète |

**Lecture** : les fenêtres qui négocient et les fenêtres qui rendent zéro sont **enchevêtrées**
temporellement. La fenêtre 2021 (entièrement contenue dans la 2020-2022 qui négocie) rend zéro,
tandis qu'une sous-fenêtre de deux mois en 2015 négocie 848 ordres. Le défaut n'est **pas
monotone** dans le temps.

## 3. Trois explications testées, toutes réfutées par la mesure

1. **« fenêtre trop courte pour le warm-up Ichimoku »** — réfutée : `2015-08-10 → 2015-10-10`
   négocie **848 ordres en deux mois**, et les fenêtres vides incluent une **année entière**.
2. **« la donnée fine-fundamental s'arrête vers 2022-08 »** — réfutée : la fenêtre 2021 est
   **entièrement contenue** dans celle qui négocie (839 ordres), laquelle bouge sur **453 points
   d'equity en 2021 seul** (364 valeurs distinctes).
3. **« l'alignement du mois de départ »** (les deux fenêtres qui négocient commencent en août) —
   réfutée par une sonde dédiée : `2021-08-17 → 2022-08-16` **commence en août**, est
   **entièrement contenue** dans la fenêtre qui négocie, et rend **0 ordre**.

## 4. Ce qui est établi (invariant, indépendant de la cause)

- Le vidage est **silencieux par construction** : une sélection d'univers qui ne rend aucun symbole
  ne lève aucune erreur. L'alpha n'a alors pas de symbole, donc pas d'*insight*, donc pas d'ordre —
  et LEAN conclut normalement. Un `Completed.` ne dit pas qu'une mesure a eu lieu ; il dit que le
  moteur s'est arrêté proprement. **Ces deux choses divergent exactement quand la donnée manque.**
- **Les compteurs ne discriminent rien pendant le run** : `totalOrders`, `netProfitAbsolute` et
  `tradeableDates` valent `0` / `$0.00` pour **tout** backtest en cours. Seule lecture qui
  tranche : la **courbe d'equity**.
- **La durée du run trahit le vidage** : une fenêtre de 12 mois vide complète en **~90 s**, là où
  deux mois qui négocient prennent **6-8 min**. La sélection d'univers domine le coût, et un
  univers vide ne coûte rien. **C'est un tell utilisable pour trier rapidement** (un run < 2 min
  sur une fenêtre > 6 mois est un signal d'alarme).
- `progress` est un **ratio temporel pur** et ne dit rien de l'activité.

## 5. Piste non testée (à instruire, pas à supposer)

Le modèle d'univers porte une mémoïsation mensuelle :

```python
def select_coarse(self, algorithm, coarse):
    if algorithm.time.month == self.month:
        return Universe.UNCHANGED
    return [x.symbol for x in coarse if x.has_fundamental_data]

def select_fine(self, algorithm, fine):
    self.month = algorithm.time.month     # <- écrit ICI seulement
    ...
```

`self.month` n'est écrit que dans `select_fine`, et `select_coarse` court-circuite sur
`Universe.UNCHANGED`. **L'interaction entre ce court-circuit, le premier appel (mois du départ),
et la présence de `MorningstarSectorCode.ENERGY` dans la charge fine est plausible mais non
mesurée** — la sonde du point 3 la contredit partiellement.

**Ne pas partir de cette piste comme d'un diagnostic** : elle est listée pour qu'un futur
lecteur ne la croie pas testée. La mesure du point 3 l'écarte même partiellement (la fenêtre
2021-08 → 2022-08 commence en août, comme celles qui négocient, et rend pourtant 0).

## 6. Hypothèse de travail — RÉFUTÉE (cause mesurée au §11.3)

L'enchevêtrement temporel fenêtres-vides / fenêtres-qui-négocient (mesure §2) est **caractéristique
d'un défaut de mémoïsation lié au calendrier d'actualisation fine**. Le pattern le plus
probable, à confirmer :

> `select_fine` est **appelé APRÈS** `select_coarse` au premier jour d'un mois, et le filtre
> `MorningstarSectorCode.ENERGY` rejette toute la charge fine ce jour-là parce que la donnée
> `MorningstarSectorCode.ENERGY` n'est pas encore hydratée à la date d'entrée (2020-08-17 par
> exemple). `self.month` est alors figé à 8, et `select_coarse` rend `Universe.UNCHANGED` à
> chaque appel suivant — **un univers gelé sur du vide**.

Cette hypothèse n'est pas mesurée (le `main.py` exact n'est pas dans le dépôt local ; il vit
sur QC Cloud dans le projet `37468246`). Elle est **dérivée de l'observation** : le vidage
dépend de la date de départ, et la mémoïsation mensuelle de `self.month` est le seul état
persistant entre appels successifs du modèle.

> **RÉFUTÉE (c.1197, review ai-01 5463018552)** : la cause mesurée (§11.3, sonde publique
> LEAN + lecture du source `FundamentalUniverseSelectionModel.cs`) n'est **pas** un défaut de
> mémoïsation — c'est l'**absence totale d'appel à `select_fine`** parce que la sous-classe ne
> chaîne aucun constructeur de base. Le texte ci-dessus est conservé comme trace de
> l'hypothèse de travail initiale, il ne décrit pas la cause réelle.

## 7. Design du fix (proposé sur l'hypothèse §6 — CADUC, hypothèse réfutée)

> **Section caduque (c.1197, review ai-01 5463018552)** : les trois options ci-dessous sont
> conçues contre l'hypothèse de mémoïsation §6, **réfutée** par la mesure (§11.3). La cause
> réelle étant l'absence de chaînage du constructeur de base, **aucune de ces options
> n'aurait corrigé le défaut** — en particulier l'option A : changer une sentinel ne
> raccorde pas un callback que rien n'appelle. Le fix réellement appliqué est le chaînage
> du ctor (`a745f2545d`, PR #19864). Le texte est conservé comme trace du raisonnement
> initial.

Le fix doit corriger le comportement au **premier appel** sans changer le comportement nominal
mensuel. Trois options, de la moins invasive à la plus structurelle :

### Option A — Lecture défensive de `self.month` (recommandé pour vérification rapide)

```python
def __init__(self, ...):
    self.month = None  # sentinel: "pas encore initialisé"

def select_coarse(self, algorithm, coarse):
    if self.month is not None and algorithm.time.month == self.month:
        return Universe.UNCHANGED
    return [x.symbol for x in coarse if x.has_fundamental_data]

def select_fine(self, algorithm, fine):
    self.month = algorithm.time.month
    return [x for x in fine
            if x.fundamentals.morningstar_sector_code == MorningstarSectorCode.ENERGY]
```

**Effet** : `self.month is None` court-circuite la mémoïsation au premier appel, et le
`select_coarse` du **mois suivant** re-sélectionne normalement. La mémoïsation mensuelle
est conservée pour le flot nominal.

### Option B — Double appel au premier jour

Forcer `select_fine` à être rappelé explicitement après le premier `select_coarse` si la
charge fine est vide. Plus invasif (modifie l'orchestration LEAN), à éviter sans test
préalable du contrat `FineFundamentalUniverseSelectionModel`.

### Option C — Suppression de la mémoïsation

Re-sélectionner **à chaque appel** de `select_coarse` (sans court-circuit). Le plus simple,
mais coûte ~12x plus de temps de calcul (la sélection d'univers domine le run). À mesurer
avant adoption.

**Option A était recommandée au moment de la rédaction** (correction locale, préservation de
la mémoïsation nominale) — recommandation **retirée** : cette option repose sur l'hypothèse
réfutée §6 et n'aurait pas corrigé le défaut (voir bannière de section).

## 8. Protocole de vérification (exécuté c.1174 — voir §11 pour les résultats)

**Pré-condition** : merge du fix `a745f2545d` (PR #19864) appliqué à `main.py` du projet
QC Cloud `37468246`. Le fix retenu n'est pas l'Option A de §7 mais le **chaînage du
constructeur de base** (la sous-classe passe ses sélecteurs au ctor de
`FineFundamentalUniverseSelectionModel`), plus canonique. Le résultat est le même : la phase
fine est armée, l'univers ne se vide plus.

**Trois vérifications, à enchaîner dans l'ordre** :

1. **Sonde `__repr__` instrumentée** : ajouter un log dans `select_coarse` et `select_fine`
   qui imprime la date, `self.month`, la taille de `coarse` et la taille de `fine`. Rejouer
   la fenêtre `2021-08-17 → 2022-08-16` (1 an, sous-fenêtre de celle qui négocie). Le log doit
   montrer **au moins un mois où `len(fine) == 0`** après filtrage `ENERGY`, et `self.month`
   qui se fige sur la valeur de ce mois. **Si cette sonde ne montre pas le défaut, l'hypothèse
   §6 est fausse** et la mesure du point 3 (l'enchevêtrement) demande une autre explication.
2. **Contre-preuve après application du fix Option A** : rejouer `2021-08-17 → 2022-08-16` et
   vérifier que `Total Orders > 0` (idéalement comparable à 839/24 mois ≈ 35 ordres/mois).
3. **Contre-preuve pleine échelle** : rejouer le bloc gelé `2020-08-17 → 2026-09-30`. Si le
   verdict pré-enregistré sur la sous-fenêtre calculable (24 mois) est conservé ET les
   4 années supplémentaires négocient, le bloc complet devient mesurable et le verdict
   pré-enregistré peut être **étendu à sa pleine étendue** (cf. `verdict-préenregistré-19678`).

**Critère d'acceptation** : `Total Orders > 0` sur la fenêtre `2021-08-17 → 2022-08-16`
après application du fix Option A. Si le critère n'est **pas** satisfait, l'hypothèse §6
est fausse et une instrumentation plus profonde (logs LEAN, événement `OnData`/`OnSecuritiesChanged`)
est nécessaire.

## 9. Ce que ce diagnostic n'est pas

- Ce n'est **pas** un défaut de l'article 9031 ni de sa stratégie : c'est un défaut du **portage**.
- Ce n'est **pas** un défaut de LEAN : le comportement observé (univers vide, run Completed)
  est la sémantique attendue d'une sélection qui ne rend aucun symbole.
- Ce diagnostic **ne corrige pas le code** : le fix (`a745f2545d`, PR #19864) a été livré
  par `myia-po-2023:CoursIA`. Il **borne** la cause probable (c.1163), **précise** la cause
  par lecture publique LEAN (cmt c.6052989262), **exécute** le protocole de vérification
  en trois étapes (§11), et **consigne la mesure plein bloc** (4 860 ordres, +12,6 %
  cumulé).

## 10. Liens

- Issue : [#19863](https://github.com/jsboige/CoursIA/issues/19863)
- Issue parent : [#19678](https://github.com/jsboige/CoursIA/issues/19678) (portage article 9031)
- EPIC : [#11698](https://github.com/jsboige/CoursIA/issues/11698) (Phase 2 semis QC)
- Code de référence local (pas le fichier du projet, mais le même pattern) :
  - `MyIA.AI.Notebooks/QuantConnect/projects/composite-c2-equityfactor/main.py` (l.33, usage
    de `FineFundamentalUniverseSelectionModel`)
  - `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-05-Universe-Selection.ipynb` (classe Python
    documentant le pattern)
- Verdict pré-enregistré : voir cmt `#19678` c.5962832068 et suivants.

## 11. Vérification c.1174 — extension plein bloc 6,1 ans (handoff reçu)

**Note d'identité** : le fix et le verdict re-basé ont été portés par `myia-po-2023:CoursIA`
(PR #19864, branche `feature/11698-ichimoku-9031`). Cette section consigne la **vérification
plein bloc** que cette lane (`myia-po-2023:CoursIA-2`) a reçue en handoff de l'autre lane
(2026-10-08 11:04Z, msg-20261008T090435-vyni7i + msg-20261008T090610-o98zo7) et qui exécute
**l'étape 3** du protocole de §8.

### 11.1 Mesure (2026-10-08, projet QC Cloud `37468246`)

**Run corrigé** (`strategy-fixed-ct-20200817-20260930`, backtest `22fde01f1ad65`,
compile `edf919582f3d` → `BuildSuccess` / 0 erreur) :

| Métrique | Valeur |
|---|---:|
| Fenêtre | `2020-08-17 → 2026-09-30` (6,1 ans) |
| `Total Orders` | **4 860** (vs 0 pré-fix sur la même fenêtre) |
| `tradeableDates` (rapporté QC) | 0 |
| Sharpe | -0,041 |
| CAGR | **+1,962 %** |
| MaxDD (rapporté) | 30,500 % |
| MaxDD (recalculé close-to-close) | **30,203 %** |
| Net profit | **+12,639 %** ($75 327,29) |
| PSR | 0,095 % |

**Baseline `xle_hold`** (`baseline-xle-hold-oos-full-2020-2026`, `026382f52eb59`, non
rejouée — un seul nœud QC consommé, mesure de la session c.1173) :

| Métrique | Valeur |
|---|---:|
| `Total Orders` | 1 |
| Sharpe | 0,746 |
| CAGR | **+25,931 %** |
| MaxDD | 26,000 % |
| Net | **+310,517 %** |
| `tradeableDates` | 1 538 |

**Comparaison brute (lecture directe)** : la stratégie perd **~24 pts de CAGR** face au
buy-and-hold XLE, drawdown plus profond, Sharpe négatif contre 0,746. **Verdict brut :
`NO BEATS`**, non argumenté par un test statistique ici (cf. §11.4).

### 11.2 Pièces jointes (DM RooSync, vérifiées c.1174)

Deux charts `Strategy Equity` au format QC, chacun `2 001` points
(`Equity` OHLC 5 champs + `Return` 2 champs) :

- `c19863_strategy_equity.json` — run corrigé
- `c19863_baseline_equity.json` — baseline XLE

**Calculs faits à la lecture** (`scratchpad/c19863_strategy_equity.json` +
`scratchpad/c19863_baseline_equity.json`) :

| | Stratégie corrigée | Baseline XLE |
|---|---:|---:|
| Close final (USD) | 1 126 071,40 | 4 114 051,85 |
| Rendement cumulé (close-to-open[0]) | **+12,607 %** | **+311,405 %** |
| Min close | 849 638 | 757 745 |
| Max close | 1 224 905 | 4 323 338 |
| MaxDD recalculé (close-to-close) | 30,203 % | 25,560 % |
| `Return` non-nuls | 1 669 / 2 001 | 1 670 / 2 001 |
| Min `Return` | -7,7358 | -8,8685 |
| Max `Return` | 3,9915 | 12,4912 |

**Pas de la grille** (DM msg-20261008T090610-o98zo7) : **96 545 s** sur 1 600 intervalles,
**96 544 s** sur 400 — grille evene pilotée par `count=2000`, **pas la maille journalière**.
Pour tout bootstrap en séances, re-tirer avec un `count` plus grand ; les fichiers ci-dessus
valent pour la **forme** et le **close**, **pas** pour un découpage par séance.

### 11.3 Lien au protocole §8 — étape 3 servie

| Étape §8 | Statut c.1174 | Preuve |
|---|---|---|
| 1. Sonde `__repr__` instrumentée | **servie** par `myia-po-2023:CoursIA` c.288 | cmt #19863 c.6052701337 (4ᵉ lecture : `select_fine` JAMAIS appelée) |
| 2. Contre-preuve fenêtre `2021-08-17 → 2022-08-16` après fix | **servie** par `myia-po-2023:CoursIA` c.288 | cmt #19863 c.6052978423 (`5b77c1f3cfad`, `Completed.`, deux conditions pré-enregistrées passent) |
| 3. Contre-preuve **plein bloc** 6,1 ans | **servie** c.1174 par cette section | run `22fde01f1ad65`, 4 860 ordres, MaxDD 30,2 %, net +12,6 % |
| Critère d'acceptation : `Total Orders > 0` après fix | **atteint** | 4 860 (vs 0 pré-fix) — à toutes les échelles testées |

**Conclusion de la vérification** : la cause (§5/§6 hypothèse mémoïsation + court-circuit
fine) **est moins spécifique que la lecture de la source publique LEAN ne l'a montré** : ce
n'est pas la mémoïsation mensuelle de `self.month` qui gèle le flot, c'est l'**absence
totale d'appel à `select_fine`** parce que la sous-classe ne chaîne aucun constructeur de
base (`a745f2545d`). Le diagnostic §5/§6 est donc **précisé par la lecture LEAN publique**
faite par la lane cousine (cmt c.6052989262, fichier
`Algorithm.Framework/Selection/FundamentalUniverseSelectionModel.cs`) : la sous-classe
*doit* passer ses sélecteurs au constructeur de la base, sans quoi la phase fine n'est
jamais armée. **Correction (c.1197, review ai-01 5463018552)** : l'affirmation initiale « l'option A
(sentinel `self.month=None`) aurait fonctionné » est **retirée** — elle est fausse : changer une
sentinel ne raccorde pas un callback que rien n'appelle. Les §6/§7 sont requalifiés
hypothèse réfutée / design caduc.

### 11.4 Verdict sur l'issue

| Question de l'issue | Réponse c.1174 |
|---|---|
| L'univers fine-fundamental se vide-t-il silencieusement ? | **Oui**, mesuré (8 fenêtres, 5 vides / 3 qui négocient, enchevêtrement temporel) |
| Y a-t-il une cause identifiée ? | **Oui** : sous-classe ne chaîne aucun ctor de base (`a745f2545d`) |
| Le fix corrige-t-il le défaut à toutes les échelles ? | **Oui** : 1 692 ordres (24 mois) + 4 860 ordres (6,1 ans), tous post-fix |
| Le verdict pré-enregistré tient-il ? | **Oui, `INCONCLUSIVE`** : cf. PR #19864 c.6052828360 (conteneur 24 mois, écart Sharpe -1,2242, p(sous-perf) 0,0868). Le **bloc complet 6,1 ans va dans le même sens au plan descriptif** (stratégie perd ~24 pts de CAGR vs XLE) — **sans bootstrap rejoué sur ce bloc** : la significativité n'est mesurée que sur le conteneur 24 mois, le plein bloc n'est pas testé (correction c.1197, review ai-01 5463018552) |
| Issue fermable ? | **Oui** : défaut documenté, fix appliqué, verdict pré-enregistré tenu, vérifications indépendantes croisées (sonde publique LEAN + fix empirique + 2 fenêtres + 2 runs) |

**Issue `#19863` est prête à la fermeture par le coord/adjoint** (le geste de `close` reste
leur prérogative — je n'ai pas le merge/close d'autrui). Le fix vit dans PR #19864
(`myia-po-2023:CoursIA` propriétaire) ; ce diagnostic enrichi + la vérification plein bloc
sont la dernière brique.

— `myia-po-2023:CoursIA-2`, c.1174 (2026-10-08 12:0xZ)
