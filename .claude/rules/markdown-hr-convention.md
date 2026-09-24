---
paths: MyIA.AI.Notebooks/**/*.ipynb
---

# Séparateur hr en cellule markdown — ne pas substituer silencieusement `---` par `***`

S'applique à **tous les agents** qui éditent des notebooks pédagogiques (`MyIA.AI.Notebooks/**/*.ipynb`). Source : issue **#14683** (3 enrichissements consécutifs substitution silencieuse, NanoClaw 3ᵉ escalade).

## Règle

Dans une cellule markdown, le séparateur horizontal (`<hr>`) est rendu **à l'identique** par les trois notations Markdown :

| Notation | Rendu |
|---|---|
| `---` | `<hr>` |
| `***` | `<hr>` |
| `* * *` | `<hr>` |
| `___` | `<hr>` |

**Aucune substitution silencieuse n'est autorisée** entre ces notations dans une PR d'enrichissement (notebook-enricher, iterative-builder, et toute main humaine). Si une cellule existante porte `---` et qu'une raison valable impose de passer à `***` :

1. **Déclarer la substitution dans le body de la PR** (section `### Sweep` ou `### Modifications non triviales`), avec :
   - le nombre de cellules touchées ;
   - le motif (collision front-matter YAML/Quarto, normalisation typographique, etc.) ;
   - la preuve mesurée (sortie de `grep -c '^---$'` avant/après sur le notebook).
2. **Ne pas l'inclure dans une PR qui s'annonce comme « byte-identique à main »** au titre de C.3 (cf [anti-regression.md](anti-regression.md)).

## Pourquoi cette règle

Mesure **re-corrigée first-hand sur l'ensemble du corpus (c.806, 2026-09-24)** sur 1406 notebooks :

- Cellules avec `---` seul : 256
- Cellules avec `***` (incl. `* * *`) : 3154
- Ratio : **1 : 12.3** en faveur de `***`, ce qui traduit une **préférence éditoriale nette** dans le dépôt, **pas** une obligation de rendu. (Mesure antérieure c.763 : 54:326 sur 200 notebooks → l'écart avec la mesure complète vient de l'échantillonnage ; la mesure re-corrigée sur le corpus entier fait foi.)

Le `Quarto Pages Deploy` (`.github/workflows/quarto-pages-deploy.yml`) traite les quatre notations sans casse sur `main`. Le motif Quarto/YAML front-matter **n'est pas établi** (les 256 cellules `---` restantes en production ne déclenchent aucun rouge CI). Une PR d'enrichissement qui substitue `---` → `***` sans déclarer la modification commet deux fautes :

1. **Claim C.3 rendu faux** : « cellules non modifiées restent byte-identiques à main » devient inexact pour N+ cellules (N ≥ 17 confirmé sur #14643).
2. **Pattern `reecriture-non-annoncee`** traqué par le dépôt (#14113/#14119), indépendamment de la bénignité du geste.

## Voies licites

Une PR d'enrichissement peut **toujours** :

- Ajouter de nouvelles cellules markdown portant `***` (préférence éditoriale du dépôt, ratio 12:1 mesuré).
- Laisser intactes les cellules existantes, quelle que soit leur notation.
- **Déclarer** un sweep de normalisation comme dans la voie (a) du ticket #14683 (PR dédiée narrow scope 1:1, partition par famille — même véhicule que #14209), avec son motif et sa preuve.

## Détection — garde automatisée active

La garde est portée par **`scripts/ci/check_hr_substitution.py`** (créée c.806, post-#17428) :

- Parse le diff unifié d'une PR (`gh pr diff <N>`) ou de la working tree (`--self`).
- Détecte les 4 notations CommonMark (`---`, `***`, `* * *`, `___`) en `+` ou `-` **uniquement** dans les fichiers `.ipynb` sous `MyIA.AI.Notebooks/`.
- Regroupe par fichier et signale les **substitutions silencieuses** (au moins une ligne `+` ET une ligne `-` du même fichier, sans mention dans le body de la PR).
- Heuristique de déclaration dans le body : chemin du fichier (relatif ou basename) **+** compteur (N ajouté/removed ou +X/−X) **+** mot-clé (`substitut`, `sweep`, `hr`, `notat`, `---`, `***`).
- Verdict `exit 1` = `SILENT_SUBSTITUTION_DETECTED` ; `exit 0` = aucune substitution silencieuse (ou PR le déclare).

```bash
python scripts/ci/check_hr_substitution.py <PR_NUMBER>
python scripts/ci/check_hr_substitution.py --self        # working tree only
python scripts/ci/check_hr_substitution.py --json       # sortie machine
```

**Remarque** : une version antérieure de cette règle mentionnait un label `reecriture-non-annoncee` sans workflow dédié. **Elle est obsolète depuis c.806** : la garde est désormais outillée via `scripts/ci/check_hr_substitution.py`, à câbler dans `.github/workflows/always-on-guards.yml` ou un workflow dédié `hr-substitution-guard.yml` (PR de câblage à venir). La détection **n'est plus** à la diligence du seul reviewer — NanoClaw trace les substitutions non déclarées, et la garde les bloque en CI.

## Interdits

- **Pas de substitution `---` → `***` silencieuse** dans une PR d'enrichissement qui s'annonce byte-identique (C.3).
- **Pas de motif Quarto supposé sans preuve** : la voie (a) du ticket #14683 l'exigeait explicitement (« établi, pas supposé »).
- **Pas de sweep one-shot global** qui toucherait l'ensemble du dépôt en une seule PR (cf #14209 — partition par famille, véhicule dédié).

## Voir aussi

- [notebook-conventions.md](notebook-conventions.md) — C.1 stubs, C.2 outputs, C.3 byte-identity
- [anti-regression.md](anti-regression.md) — pas de réécriture non déclarée
- [consecutive-code-cells.md](consecutive-code-cells.md) — pattern sibling sur cellules code consécutives
- issue **#14683** — ticket d'origine
