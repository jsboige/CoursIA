# Manifeste de préservation des branches distantes — issue #14238 (tranches 1 à 3)

> **Statut v4 (2026-10-25, lane `myia-po-2025:CoursIA`) : tranche 3 CLOSE PAR LE VERDICT — les lignes de classe E portent désormais une note mesurée, aucune ne garde la note d'attente.** Mesure de ce cycle : `git ls-remote --heads origin` rend **2027 têtes**, dont **29** sont des branches classe E survivantes ; les **111** autres ont disparu du remote sans geste de la flotte. Les 29 sont réparties en **21 `superseded`** (contenu déjà sur `main`, preuve au symbole près), **5 `delivered`** (la pépite Lean Grothendieck, PR #21814 mergée le 2026-10-22), **2 `keep`** (travail en cours et contrôle négatif délibéré), **1 `arbitration_pending`** (`fix/11823`). Les sha du manifeste sont restés valides : **0 divergence** entre le sha enregistré et la tête distante des 29. Détail en [« Tranche 3 — verdicts »](#tranche-3--verdicts-des-lignes-de-classe-e-v4). **Aucune suppression n'est faite par cette version** : les 21 candidates attendaient le feu vert du coordinateur, et chaque ligne porte sa preuve pour que le geste soit relisible. *(Compteurs datés du 2026-10-25, donc périmés : le feu vert est venu, la suppression a été faite le 2026-10-25 sur bundle vérifié — voir les correctifs ci-dessous.)*
>
> **Correctif mesuré le 2026-10-27 (lane `myia-po-2025:CoursIA`) : les cinq branches `delivered` ont disparu du remote depuis le verdict — le partage courant est 24 présentes / 116 absentes, pas 29 / 111.** `groth-p47-covers-extremal`, `groth-p48-covers-of-pretopology`, `groth-p49-covers-ynp`, `groth-p50-covers-coverpreserving` et `groth-p51-covers-coverpreserving-laws` rendent `404` sur `repos/jsboige/CoursIA/branches/<nom>` **et** sont absentes de `git ls-remote --heads origin` (deux instruments indépendants) : la PR #21814 a supprimé sa branche source au merge du 2026-10-22. Le jeton `delivered_2026-10-22_tranche3` reste l'état **de la tranche** — il documente une décision de lecture, et le réécrire effacerait la trace de ce qui a été jugé ; mais pour le partage **d'aujourd'hui**, ces cinq lignes se lisent avec les disparues. Conséquence sur la mesure de restauration : « sha enregistré = tête distante » a été vérifié sur les 29 branches alors présentes, et porte aujourd'hui sur les 24 encore joignables — les cinq autres n'ont plus de tête à comparer, pas une tête divergente.
>
> **Re-mesure complète du 2026-10-27 (lane `myia-po-2025:CoursIA`) : 3 présentes / 137 absentes.** Le correctif ci-dessus avait corrigé les cinq `delivered` par soustraction (29 − 5 = 24) ; cette fois la jointure a été **rejouée en entier** contre `git ls-remote --heads origin`, et elle donne **3** branches de classe E encore joignables. L'écart avec 24 n'est pas une erreur du correctif précédent : les **21 `superseded`** ont été **supprimées le 2026-10-25**, après le feu vert du coordinateur et **sur sauvegarde préalable** — bundle `C:\Backups\coursia-superseded21-20261025.bundle`, sha256 `72547159d696b45c44da197ca88c3938496a4758f1703d9ddc80011df7120253`, `git bundle verify` OK, les 21 refs à leur tête (commentaire `[BUNDLE]` du 2026-10-25T16:22:44Z sur l'issue #14238). Les 21 noms absents sous le jeton `superseded` sont exactement ceux du bundle. Restent joignables les **2 `keep`** et l'**1 `arbitration_pending`**, dont le sha enregistré égale toujours la tête distante (`feature/14546-chsh-randomized`, `feature/runner-positive-control`, `fix/11823-update-branch`). Les jetons ne sont pas réécrits : ils datent une décision de lecture, pas un état courant. Conséquence pour la restauration : sur les 137 branches sans tête distante, on restaure par le `<sha>` conservé ou par le bundle, jamais par un nom de branche.
>
> **Statut v3 (2026-10-12, lane `myia-po-2025:CoursIA`) : tranche 2 CLOSE PAR ATTRITION — les 622 branches classe C restantes du manifeste v2 sont absentes du remote (mesure `git ls-remote --heads` du 2026-10-12, 4566 têtes totales ; jointure manifeste × remote = 0 survivante, contrôles positifs cités sur l'issue). Marquées `vanished_2026-10-12_tranche2_attrition`, sha préservé — restauration possible ligne par ligne.**
>
> **Statut v2 (2026-10-06, cycle 31) : manifeste v2, 204 branches classe C supprimees effective (tranche 2, lane `myia-po-2024:CoursIA-2`).
> Dry-run tranche 2 poste sur issue #14238 (commentaire 6005880152). Tranche 3 (classe E, 72 branches) lue par L576, dry-run poste (commentaire 6006262463) -- triage diff obligatoire, hors scope cycle unique.**
>
> Tranche 1 (PR #15093 MERGEE) : **manifeste seul, AUCUNE suppression** a l'epoque. Tranche 2 (CLOSE) : 204 branches classe C supprimees effectivement (v2) + 622 disparues par attrition (v3) = 826/826 tracees. Tranche 3 : 72 branches classe E lues par L576 (16 LIVREE, 56 INCONNU, 0 INTEGREE), triage diff obligatoire pour les 72. **Dépassé depuis** : les lignes de classe E portent un verdict mesuré (v4, en tête de ce fichier).

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

> **Une note d'attente n'est pas un verdict.** Jusqu'au 2026-10-25, les lignes de classe E portaient toutes la même note `tranche 3 (read content-first per L576 protocol)`, y compris les 111 branches qui avaient disparu du remote et n'avaient donc jamais été lues. La note annonçait une lecture accomplie là où il n'y avait qu'un travail planifié : c'est exactement le genre de mention que le protocole d'audit réévalué interdit de laisser passer pour un fait. Elles portent maintenant un jeton mesuré, et plus aucune ne dit « lu » sans preuve.

## Tranche 3 — verdicts des lignes de classe E (v4)

Mesure du 2026-10-25 : `git ls-remote --heads origin` rend **2027 têtes** ; jointure avec les lignes de classe E du manifeste = **29 survivantes**. Le sha enregistré et la tête distante coïncident sur **29/29** : les ancres de restauration sont intactes.

**Re-mesure du 2026-10-27 : 24 survivantes, 5 disparues depuis.** Les cinq branches du jeton `delivered` ont été supprimées du remote par le merge de leur propre PR (source branch supprimée le 2026-10-22) : `404` sur les deux instruments, cf. correctif en tête de document. Le tableau ci-dessous reste l'état **de la tranche** — les jetons ne sont pas réécrits — et la jointure courante se lit `3 présentes / 137 absentes` — rejeu complet du 2026-10-27, cf. correctif en tête : entre-temps les 21 `superseded` ont elles aussi quitté le remote, supprimées le 2026-10-25 après feu vert et sur bundle vérifié. La comparaison sha ↔ tête distante porte aujourd'hui sur les 3 joignables.

| Verdict | Nb |
|---|---:|
| `superseded_2026-10-21_tranche3` (suppression candidate) | 21 |
| `delivered_2026-10-22_tranche3` (livrée par PR #21814, mergée le 2026-10-22) | 5 |
| `keep_2026-10-21_tranche3` | 2 |
| `arbitration_pending_2026-10-21_tranche3` | 1 |
| `vanished_2026-10-21_tranche3_attrition` | 111 |
| **Total classe E** | **140** |

### Les 21 candidates à la suppression

Chacune porte dans le manifeste la preuve qui l'établit ; la colonne de droite n'en donne que le repère, pour qu'un relecteur sache quoi vérifier sans décompresser. Les mesures chiffrées de chaque repère (ajouts, suppressions, part déjà présente sur `main`, cellules) sont dans [`branch-cleanup-manifest.verdicts.json`](branch-cleanup-manifest.verdicts.json), relevées le 2026-10-25 contre `main` : la présente table ne porte que le prédicat, le chiffre reste falsifiable dans son fichier de données.

| Branche | Repère de la preuve sur `main` |
|---|---|
| `fix/13633-parse-grain-require-key-v2` | contenu intégralement présent (part sur `main` 1.000) |
| `fix/13712-triplets-markdown` | contenu presque intégralement présent (part sur `main` 0.991) |
| `pr13712` | même travail sous un autre nom (part sur `main` 0.991) |
| `fix/13904-persona-alias-regex` | ajouts présents (part sur `main` 0.980) ; la branche supprime encore du contenu que `main` porte |
| `feature/11601-qcpycloud02-density` | contenu présent (part sur `main` 0.978) |
| `fix/13723-quarto-dedup` | contenu présent sur `CausalBridges-02-Dowhy` (part sur `main` 0.996) ; entrées de table et `_quarto.yml` présentes |
| `fix/14558-three-lines-table` | bloc ajouté présent dans `.claude/rules/submodule-maintenance.md` |
| `feature/13156-cell-order-papermill-ratchet` | connaissance en section 6.4 ; rejouer régresserait les sorties |
| `fix/11315-rebase-conflict` | résidu = downgrade de pin `v4.32.0` contre `v4.33.0` |
| `fix/11417-m15-notebook-papermill-block` | cellule loader `results_path` (#11417/#11574) présente |
| `fix/13717-body-amend` | cellule seed `20260822` / `p_true = 0.3` présente |
| `fix/13727-exp-naive-assert` | `EV(P1)`, `Zinkevich` dans `GameTheory-13-ImperfectInfo-CFR-Python` |
| `fix/14070-position-g-anti-negation` | l'organe porte `(?-i:` et `[A-Z][A-Z_]{3,}` |
| `fix/14422-phase-g-attribution` | aucune cellule ni ligne absente de `main` |
| `fix/c932-pr14137-if` | le workflow porte `orphan`, `schedule`, `workflow_dispatch` |
| `pr-13601` | aucune cellule neuve ; résidu = tables de statut README |
| `pr13724` | les cellules ajoutées et leurs lignes README sont sur `main` |
| `feature/14466-c233-prongb` | même carnet que `Frontieres-02`, historique `--follow` commun |
| `fix/13797-update-branch` | carnet `Search-02c-QuikGraph` au même chemin ; contenu de la branche inclus dans celui de `main` |
| `fix/13932-fold-individaux-rebase` | `main` remplace le `SKIP` par des budgets `signal.alarm` |
| `fix/c699-narrow-sustained` | aucune cellule ni ligne absente de `main` |

### Les 5 livrées

`feature/groth-p47-covers-extremal`, `groth-p48-covers-of-pretopology`, `groth-p49-covers-ynp`, `groth-p50-covers-coverpreserving`, `groth-p51-covers-coverpreserving-laws` — cinq modules Lean Grothendieck neufs (FR + EN, 36 théorèmes, 0 `sorry`), livrés par la PR #21814. Ces branches sont donc devenues superposées à leur tour : elles rejoignent les candidates à la suppression, mais **après** vérification que le merge a bien posé les dix modules, ce qui est le cas.

### Les 2 à conserver, et la 1 à arbitrer

- `feature/14546-chsh-randomized` — module `CHSHRandomized.lean` neuf qui vit dans le worktree actif `.claude/worktrees/14451-lean-axioms` : **travail en cours**, le supprimer tuerait un chantier ouvert.
- `feature/runner-positive-control` — contrôle **négatif délibéré** (`exit 42`) du gate `windows-self-hosted-tests`. Le supprimer retirerait un témoin qui doit pouvoir échouer : décision du propriétaire du gate, pas de cette lane.
- `fix/11823-update-branch` — delta **re-mesuré le 2026-10-27** (la formule de cette ligne n'était qu'une lecture, pas une mesure). Le delta fonctionnel est bien **une expression dans une seule cellule de code** : `reward = portfolio_return - 0.5 * (portfolio_return ** 2)` devient `... - 0.5 * abs(portfolio_return)`. Les cellules touchées sont cette expression, la cellule de code qui la porte, la prose et l'énoncé d'exercice qui doivent la décrire, une cellule de navigation et deux `***` → `---` sans effet. Deux mesures changent la décision. (a) La cellule de navigation porte encore `QC-Py-Cloud-04` et renvoie à `Cloud-04-MeanReversion` / `Cloud-05-MLP-Forecasting`, alors que `main` a renommé ce carnet en `QC-Py-Cloud-10` et le fait voisiner `Cloud-09-OptionWheel` (#14082) : livrer la branche telle quelle **annulerait ce renommage**, elle doit d'abord être rebasée sur le nouveau chemin. (b) L'écart n'est pas cosmétique : pour `|r| < 1`, la branche vaut `r - 0.5*|r|` contre `r - 0.5*r^2` sur `main`, soit `0,5*|r|*(1-|r|)` de récompense en moins — à `|r| = 1 %`, elle ne garde que 50,3 % de celle de `main` (0,005 contre 0,00995). Le signal d'entraînement change, donc la livraison demande un backtest QC et non un `update-branch` : soit la formule est livrée avec son backtest, soit la branche rejoint les candidates en écrivant que le delta est abandonné.

### Les disparues par attrition (111 au verdict ; 137 absentes à la re-mesure du 2026-10-27)

Absentes de `git ls-remote --heads origin` au 2026-10-25, sans geste de la flotte : elles ne se lisent plus et ne se suppriment pas (il n'y a plus rien à supprimer). Leur sha reste dans le manifeste comme ancre de restauration.

S'y ajoutent depuis le 2026-10-27 les cinq branches du jeton `delivered` (`groth-p47-covers-extremal` à `groth-p51-covers-coverpreserving-laws`), retirées du remote par le merge de #21814. Elles ne relèvent pas de l'attrition mais du même résultat opérationnel : plus de tête distante à comparer, plus rien à supprimer. Leur jeton n'est pas réécrit — il date une décision de lecture, pas un état courant.

Pour les lister :

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
- **Tranche 3 (cycle 31, dry-run)** : 72/140 branches classe E lues par L576 v1 (verdict 16 LIVREE + 56 INCONNU, 0 INTEGREE). Triage diff obligatoire pour les 72 -- hors du périmètre d'un cycle worker, le triage par branche dépassant son budget. **Dépassé** : les lignes de classe E portent un verdict mesuré (v4, 2026-10-25) ; les 21 suppressions ont été faites le 2026-10-25 sur bundle vérifié, et il reste l'arbitrage de `fix/11823`.
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
#  - l'arité reste celle d'origine (entête comprise) ;
#  - seules les colonnes 1 à 5 des lignes modifiées sont byte-identiques ;
#  - le sha de chaque ligne est inchangé (c'est l'ancre de restauration).
gunzip -c docs/reference/branch-cleanup-manifest.tsv.gz | awk -F'\t' 'NF!=6{bad++} END{print (bad?bad" lignes a arite fausse":"arite 6 partout")}'

# Re-lire ce que la PR PUBLIE, et non le fichier du disque : sans ce contrôle,
# une recompression locale ratée passerait inaperçue (NanoClaw, #22509).
gh api "repos/jsboige/CoursIA/contents/docs/reference/branch-cleanup-manifest.tsv.gz?ref=<sha-de-la-tete>" \
  --jq .content | base64 -d | gunzip \
  | awk -F'\t' 'NF!=6{bad++} END{print (bad?bad" lignes a arite fausse":"arite 6 partout")}'

# Jointure manifeste x têtes distantes -- d'où viennent les compteurs du statut v4
# et des correctifs. Le résultat dépend de l'INSTANT de la mesure : la citer.
gunzip -c docs/reference/branch-cleanup-manifest.tsv.gz \
  | awk -F'\t' '$3=="E"{print $1}' | sort -u > /tmp/e.txt
git ls-remote --heads origin | sed 's#.*refs/heads/##' | sort -u > /tmp/heads.txt
echo "présentes: $(comm -12 /tmp/e.txt /tmp/heads.txt | wc -l)"; echo "absentes: $(comm -23 /tmp/e.txt /tmp/heads.txt | wc -l)"
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
