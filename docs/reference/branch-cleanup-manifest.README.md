# Manifeste de préservation des branches distantes — issue #14238 (tranches 1 à 3)

> **Statut v4 (2026-10-25, lane `myia-po-2025:CoursIA`) : tranche 3 CLOSE PAR LE VERDICT — les 140 lignes de classe E portent désormais une note mesurée, aucune ne garde la note d'attente.** Mesure de ce cycle : `git ls-remote --heads origin` rend **2027 têtes**, dont **29** sont des branches classe E survivantes ; les **111** autres ont disparu du remote sans geste de la flotte. Les 29 sont réparties en **21 `superseded`** (contenu déjà sur `main`, preuve au symbole près), **5 `delivered`** (la pépite Lean Grothendieck, PR #21814 mergée le 2026-10-22), **2 `keep`** (travail en cours et contrôle négatif délibéré), **1 `arbitration_pending`** (`fix/11823`). Les sha du manifeste sont restés valides : **0 divergence** entre le sha enregistré et la tête distante des 29. Détail en [« Tranche 3 — verdicts »](#tranche-3--verdicts-des-140-lignes-de-classe-e-v4). **Aucune suppression n'est faite par cette version** : les 21 candidates attendent le feu vert du coordinateur, et chaque ligne porte sa preuve pour que le geste soit relisible.
>
> **Statut v3 (2026-10-12, lane `myia-po-2025:CoursIA`) : tranche 2 CLOSE PAR ATTRITION — les 622 branches classe C restantes du manifeste v2 sont absentes du remote (mesure `git ls-remote --heads` du 2026-10-12, 4566 têtes totales ; jointure manifeste × remote = 0 survivante, contrôles positifs cités sur l'issue). Marquées `vanished_2026-10-12_tranche2_attrition`, sha préservé — restauration possible ligne par ligne.**
>
> **Statut v2 (2026-10-06, cycle 31) : manifeste v2, 204 branches classe C supprimees effective (tranche 2, lane `myia-po-2024:CoursIA-2`).
> Dry-run tranche 2 poste sur issue #14238 (commentaire 6005880152). Tranche 3 (classe E, 72 branches) lue par L576, dry-run poste (commentaire 6006262463) -- triage diff obligatoire, hors scope cycle unique.**
>
> Tranche 1 (PR #15093 MERGEE) : **manifeste seul, AUCUNE suppression** a l'epoque. Tranche 2 (CLOSE) : 204 branches classe C supprimees effectivement (v2) + 622 disparues par attrition (v3) = 826/826 tracees. Tranche 3 : 72 branches classe E lues par L576 (16 LIVREE, 56 INCONNU, 0 INTEGREE), triage diff obligatoire pour les 72. **Dépassé depuis** : les 140 lignes de classe E portent un verdict mesuré (v4, en tête de ce fichier).

## Source

Issue : #14238 — *Nettoyer les 9685 branches distantes : 8692 mécaniquement jetables, 94 à lire avant (manifeste de préservation obligatoire)*.

Mandat user (2026-09-02) : « nettoyer les milliers de branches mergées qu'on a gardées sur GitHub — ça ne fait pas très sérieux d'arriver sur un dépôt qui déclare près de 10k branches. Prends tout de même le temps de triager, il y a peut-être quelques pépites oubliées là-dedans. »

## Classification mesurée

Mesure **firsthand** du 2026-09-07 (`scripts/collect_branches_tranche1.py` + `git for-each-ref` + `gh pr list --state all --limit 20000`) :

| Classe | Nb | Disposition |
|---|---:|---|
| **A** — branche d'une PR **ouverte** | 37 | **GARDER** (travail en cours) |
| **B** — branche d'une PR **mergée** | 9255 | **suppression différée** (livraison sur `main`) |
| **C** — branche d'une PR **fermée sans merge** | 826 | tranche 2 (à vérifier par échantillon) |
| **D** — sans PR, tip ancêtre de `main` | 1 | **suppression différée** (contenu déjà dans `main`) |
| **E** — sans PR **et** hors de `main` | 140 | tranche 3 (à lire une par une, protocole L576) |
| **Total** | 10259 | — |

> **Note.** Le compte `B+D = 9256` est supérieur aux `8676` avancés dans l'issue initiale (mesure du 2026-09-02). L'écart est dû à l'augmentation du nombre de PRs mergées entre la rédaction de l'issue et cette mesure (12018 → 12587 PRs en 5 jours, dont 569 fusions).

## Format du manifeste

`branch-cleanup-manifest.tsv.gz` (compressé gzip, ~425 Ko, décompressé ~1.27 Mo) — 6 colonnes séparées par tabulation :

```
branch\tsha\tclass\tpr_number\tpr_state\tnote
```

Une ligne par branche, ordonnée par SHA pour faciliter les diffs entre passes successives.

### Grammaire de la colonne `note`

Une note s'écrit `<jeton>_<date>_<tranche>[ -- <preuve>]`. Le jeton dit ce que la ligne **autorise**, la preuve dit **pourquoi** : une ligne sans preuve est une intention, pas un verdict.

| Jeton | Ce que la ligne autorise | Ce qu'elle interdit |
|---|---|---|
| `superseded_<date>_<tranche>` | supprimer la branche — son contenu est déjà sur `main`, la preuve nomme le symbole ou la mesure qui l'établit | rejouer la branche : sa livraison réintroduirait un état périmé |
| `delivered_<date>_<tranche>` | supprimer — le contenu est passé sur `main` par une PR citée | rejouer la branche, la livraison est faite |
| `keep_<date>_<tranche>` | conserver la branche | supprimer, même si elle paraît ancienne |
| `arbitration_pending_<date>_<tranche>` | conserver jusqu'à l'arbitrage | supprimer sans écrire que le delta est abandonné |
| `vanished_<date>_<tranche>_attrition` | rien : la branche n'existe plus sur le remote, le sha reste comme ancre de restauration | prétendre qu'elle a été lue, ou que la flotte l'a supprimée |
| `deleted_<date>_<tranche>` | rien : suppression effective, sha conservé | — |

> **Une note d'attente n'est pas un verdict.** Jusqu'au 2026-10-25, les 140 lignes de classe E portaient toutes la même note `tranche 3 (read content-first per L576 protocol)`, y compris les 111 branches qui avaient disparu du remote et n'avaient donc jamais été lues. La note annonçait une lecture accomplie là où il n'y avait qu'un travail planifié : c'est exactement le genre de mention que le protocole d'audit réévalué interdit de laisser passer pour un fait. Les 140 lignes portent maintenant un jeton mesuré, et plus aucune ne dit « lu » sans preuve.

## Tranche 3 — verdicts des 140 lignes de classe E (v4)

Mesure du 2026-10-25 : `git ls-remote --heads origin` rend **2027 têtes** ; jointure avec les 140 lignes de classe E du manifeste = **29 survivantes**. Le sha enregistré et la tête distante coïncident sur **29/29** : les ancres de restauration sont intactes.

| Verdict | Nb |
|---|---:|
| `superseded_2026-10-21_tranche3` (suppression candidate) | 21 |
| `delivered_2026-10-22_tranche3` (livrée par PR #21814, mergée le 2026-10-22) | 5 |
| `keep_2026-10-21_tranche3` | 2 |
| `arbitration_pending_2026-10-21_tranche3` | 1 |
| `vanished_2026-10-21_tranche3_attrition` | 111 |
| **Total classe E** | **140** |

### Les 21 candidates à la suppression

Chacune porte dans le manifeste la preuve qui l'établit ; la colonne de droite n'en donne que le repère, pour qu'un relecteur sache quoi vérifier sans décompresser.

| Branche | Repère de la preuve sur `main` |
|---|---|
| `fix/13633-parse-grain-require-key-v2` | 123 lignes ajoutées, ratio 1.000 |
| `fix/13712-triplets-markdown` | 1112 lignes ajoutées, ratio 0.991 |
| `pr13712` | même travail sous un autre nom, ratio 0.991 |
| `fix/13904-persona-alias-regex` | 0.980 des ajouts ; la branche supprime 2416 lignes que `main` porte |
| `feature/11601-qcpycloud02-density` | 185 lignes ajoutées, ratio 0.978 |
| `fix/13723-quarto-dedup` | 0.996 sur `CausalBridges-02-Dowhy` ; entrées de table et `_quarto.yml` présentes |
| `fix/14558-three-lines-table` | bloc ajouté présent dans `.claude/rules/submodule-maintenance.md` |
| `feature/13156-cell-order-papermill-ratchet` | connaissance en section 6.4 ; rejouer régresserait les sorties |
| `fix/11315-rebase-conflict` | résidu = downgrade de pin `v4.32.0` contre `v4.33.0` |
| `fix/11417-m15-notebook-papermill-block` | cellule loader `results_path` (#11417/#11574) présente |
| `fix/13717-body-amend` | cellule seed `20260822` / `p_true = 0.3` présente |
| `fix/13727-exp-naive-assert` | `EV(P1)`, `Zinkevich` dans `GameTheory-13-ImperfectInfo-CFR-Python` |
| `fix/14070-position-g-anti-negation` | l'organe porte `(?-i:` et `[A-Z][A-Z_]{3,}` |
| `fix/14422-phase-g-attribution` | 0 cellule et 0 ligne absente de `main` |
| `fix/c932-pr14137-if` | le workflow porte `orphan`, `schedule`, `workflow_dispatch` |
| `pr-13601` | 0 cellule neuve ; résidu = tables de statut README |
| `pr13724` | les 2 cellules et leurs lignes README sont sur `main` |
| `feature/14466-c233-prongb` | même carnet que `Frontieres-02`, historique `--follow` commun |
| `fix/13797-update-branch` | carnet `Search-02c-QuikGraph` au même chemin, 29 cellules contre 25 |
| `fix/13932-fold-individaux-rebase` | `main` remplace le `SKIP` par des budgets `signal.alarm` |
| `fix/c699-narrow-sustained` | 0 cellule et 0 ligne absente de `main` |

### Les 5 livrées

`feature/groth-p47-covers-extremal`, `groth-p48-covers-of-pretopology`, `groth-p49-covers-ynp`, `groth-p50-covers-coverpreserving`, `groth-p51-covers-coverpreserving-laws` — cinq modules Lean Grothendieck neufs (FR + EN, 36 théorèmes, 0 `sorry`), livrés par la PR #21814. Ces branches sont donc devenues superposées à leur tour : elles rejoignent les candidates à la suppression, mais **après** vérification que le merge a bien posé les dix modules, ce qui est le cas.

### Les 2 à conserver, et la 1 à arbitrer

- `feature/14546-chsh-randomized` — module `CHSHRandomized.lean` neuf qui vit dans le worktree actif `.claude/worktrees/14451-lean-axioms` : **travail en cours**, le supprimer tuerait un chantier ouvert.
- `feature/runner-positive-control` — contrôle **négatif délibéré** (`exit 42`) du gate `windows-self-hosted-tests`. Le supprimer retirerait un témoin qui doit pouvoir échouer : décision du propriétaire du gate, pas de cette lane.
- `fix/11823-update-branch` — delta réel d'**une ligne** : récompense `r - 0.5*|r|` contre `r - 0.5*r^2` sur `main`. La livrer change le comportement d'une stratégie, donc elle demande un backtest QC et non un `update-branch` : soit la formule est livrée avec son backtest, soit la branche rejoint les candidates en écrivant que le delta est abandonné.

### Les 111 disparues par attrition

Absentes de `git ls-remote --heads origin` au 2026-10-25, sans geste de la flotte : elles ne se lisent plus et ne se suppriment pas (il n'y a plus rien à supprimer). Leur sha reste dans le manifeste comme ancre de restauration. Pour les lister :

```bash
gunzip -c docs/reference/branch-cleanup-manifest.tsv.gz \
  | awk -F'\t' '$6 ~ /^vanished_2026-10-21_tranche3_attrition/ {print $1}'
```

### Ce que cette version ne fait pas

**Aucune suppression.** Les 21 candidates (auxquelles s'ajoutent les 5 livrées) attendent le feu vert du coordinateur, comme les tranches précédentes l'ont fait. Le manifeste est ce qui rend le geste réversible ligne par ligne ; il ne le remplace pas. Le détail des lectures, branche par branche, reste sur l'issue #14238 (commentaires du 2026-10-21).

## Pourquoi versionner ce manifeste

**CLAUDE.md global §"Consolider != Archiver"** : aucune suppression sans preuve de préservation. Sans manifeste, une branche supprimée par erreur devient irrécupérable dès le GC GitHub. Avec, elle se restaure par :

```bash
# Pour chaque ligne (sha, branch) en classe B ou D :
git push origin <sha>:refs/heads/<branch>
```

Le manifeste est la **clé de voûte** de l'opération réversible. Le committer sur `main` est délibéré : c'est l'inventaire qui survit à n'importe quel cycle.

## Pourquoi **PAS** de suppression dans cette PR

1. **Le delta entre les deux mesures (issue vs cette PR)** demande vérification. Si 580 fusions en 5 jours ont effectivement rapproché B de 9255, l'arbitrage de la classe E (140 branches sans PR) demande d'être refait sur le plateau actuel — pas celui de 2026-09-02.
2. **Le protocole L576** sur les 140 orphelines demande de les lire une par une (cf. le faux positif `feat/lean-median-voter-strict-args` cité dans l'issue — `banks_set_condorcet` était déjà sur `main` via squash). Mélanger cette lecture avec une suppression en bloc serait **récidive**.
3. **La tranche 2** (826 PR fermées sans merge) demande aussi une lecture par échantillon avant suppression.
4. **Aucun geste coord n'a été posé sur cette question** dans le pool de dispatches récent. La suppression effective est un geste **coordination-visible** qui mérite un signal explicite ai-01.

## Suites proposées (PR à venir)

- **PR suivante — tranche 1 effective** : suppression des classes B + D après validation ai-01 et après relecture des 140 orphelines (E) en protocole L576 (une PR par lot de 50 pour blast radius borné).
- **Tranche 2 (cycle 31, partial)** : 204/276 branches classe C supprimees effective (v2 du manifeste, note `deleted_2026-10-06_tranche2`). 60 restantes a traiter en cycle suivant (rate-limit GitHub + timeouts sur push de 50 refspecs -- delestage a la sous-tranche).
- **Tranche 3 (cycle 31, dry-run)** : 72/140 branches classe E lues par L576 v1 (verdict 16 LIVREE + 56 INCONNU, 0 INTEGREE). Triage diff obligatoire pour les 72 -- sortie de scope d'un cycle worker de 30 min (5-10 min par branche). **Dépassé** : les 140 lignes portent un verdict mesuré (v4, 2026-10-25) ; restent ouvertes les 21 suppressions, qui attendent le feu vert du coordinateur, et l'arbitrage de `fix/11823`.
- **Cron de nettoyage** (post-rattrapage) : un script hebdomadaire qui joint `gh pr list` + `git for-each-ref` et pousse les nouvelles candidates, **après** que le rattrapage initial ait livré ses leçons.

## Vérification du manifeste

```bash
# Décompresser pour lecture locale :
gunzip -k docs/reference/branch-cleanup-manifest.tsv.gz
head -10 docs/reference/branch-cleanup-manifest.tsv

# Filtrer une classe :
awk -F'\t' '$3=="B"' docs/reference/branch-cleanup-manifest.tsv | head -5

# Compter par classe :
awk -F'\t' 'NR>1{c[$3]++} END{for(k in c) print k, c[k]}' docs/reference/branch-cleanup-manifest.tsv

# Compter les verdicts de la tranche 3 (doit rendre 111/21/5/2/1, total 140) :
gunzip -c docs/reference/branch-cleanup-manifest.tsv.gz \
  | awk -F'\t' '$3=="E"{split($6,a," -- "); c[a[1]]++} END{for(k in c) print c[k], k}' | sort -rn

# Ce qu'une passe sur les notes a le droit de changer, et rien d'autre :
#  - l'arité reste 6 sur 10260 lignes (entête comprise) ;
#  - seules les colonnes 1 à 5 des lignes modifiées sont byte-identiques ;
#  - le sha de chaque ligne est inchangé (c'est l'ancre de restauration).
gunzip -c docs/reference/branch-cleanup-manifest.tsv.gz | awk -F'\t' 'NF!=6{bad++} END{print (bad?bad" lignes a arite fausse":"arite 6 partout")}'
```

## Provenance

### Tranche 1 (v1 du manifeste, 2026-09-07)
- Lane : `myia-po-2024:CoursIA-2`
- Cycle : c.966 (2026-09-07T17:43Z)
- Issue claim : https://github.com/jsboige/CoursIA/issues/14238#issuecomment-5573966809
- Script de collecte : `scratchpad/collect_branches_tranche1.py` (HORS worktree — référence, non versionné ici)
- PR : #15093 MERGEE (squash 8aeca9360e15, 2026-09-08T09:55:27Z)

### Tranche 2 (v2 du manifeste, 2026-10-06)
- Lane : `myia-po-2024:CoursIA-2`
- Cycle : 31 (2026-10-05T22:00Z → 2026-10-06T02:30Z)
- Dispatch ai-01 : DM `ai01-po2024b-c459-tapis` (2026-10-05T21:35:53Z)
- Claim cycle 31 : https://github.com/jsboige/CoursIA/issues/14238#issuecomment-6003439050
- Dry-run tranche 2 : https://github.com/jsboige/CoursIA/issues/14238#issuecomment-6005880152 (276 planifiees, 204 effective, 60 restantes)
- Dry-run tranche 3 : https://github.com/jsboige/CoursIA/issues/14238#issuecomment-6006262463 (72 classe E, triage diff obligatoire, hors scope cycle unique)
- Branche de travail : `fix/14238-tranche2-classe-c`
- Methode : 50 refspecs par push (5-6 sec par batch), throttling par taille de lot (push de 100+ timeout sur GitHub). Rate-limit observe sur les dernieres 60.
- Hash au commit : a completer apres merge.
