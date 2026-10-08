# Manifeste de préservation des branches distantes — issue #14238 (tranches 1+2)

> **Statut v2 (2026-10-06, cycle 31) : manifeste v2, 204 branches classe C supprimees effective (tranche 2, lane `myia-po-2024:CoursIA-2`).
> Dry-run tranche 2 poste sur issue #14238 (commentaire 6005880152). Tranche 3 (classe E, 72 branches) lue par L576, dry-run poste (commentaire 6006262463) -- triage diff obligatoire, hors scope cycle unique.**
>
> Tranche 1 (PR #15093 MERGEE) : **manifeste seul, AUCUNE suppression** a l'epoque. Tranche 2 (PR en cours) : suppression effective des 204 premieres branches classe C validees par echantillon. Tranche 3 : 72 branches classe E lues par L576 (16 LIVREE, 56 INCONNU, 0 INTEGREE), triage diff obligatoire pour les 72.

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
- **Tranche 2 (cycle 31, partial)** : 204/276 branches classe C supprimees effective (v2 du manifeste, note `deleted_2026-10-06_tranche2`). 60 restantes a traiter en cycle suivant (rate-limit GitHub + timeouts sur push de 50 refspecs -- delestage a la sous-tranche).
- **Tranche 3 (cycle 31, dry-run)** : 72/140 branches classe E lues par L576 v1 (verdict 16 LIVREE + 56 INCONNU, 0 INTEGREE). Triage diff obligatoire pour les 72 -- sortie de scope d'un cycle worker de 30 min (5-10 min par branche).
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
