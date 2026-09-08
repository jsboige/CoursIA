# Manifeste de préservation des branches distantes — issue #14238 (tranche 1)

> **Statut : manifeste versionné, AUCUNE suppression effectuée dans cette PR.**
> La suppression des branches listées en classe **B** et **D** est différée jusqu'à validation explicite par ai-01 et confirmation que le pipeline de restauration est en place.

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
- **Tranche 2** : relecture échantillon des 826 PR fermées sans merge, suppression par lot.
- **Tranche 3** : 140 orphelines, protocole L576 complet, 3 issues acceptables par branche (déjà livré / ouvrir PR / périmé).
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
```

## Provenance

- Lane : `myia-po-2024:CoursIA-2`
- Cycle : c.966 (2026-09-07T17:43Z)
- Issue claim : https://github.com/jsboige/CoursIA/issues/14238#issuecomment-5573966809
- Script de collecte : `scratchpad/collect_branches_tranche1.py` (HORS worktree — référence, non versionné ici)
- Hash au commit : à compléter après merge
