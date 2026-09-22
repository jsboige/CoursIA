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

Mesure first-hand sur 200 premiers notebooks de `MyIA.AI.Notebooks/` (c.763) :

- Cellules avec `---` seul : 54
- Cellules avec `***` (incl. `* * *`) : 326
- Ratio : ~6:1 en faveur de `***`, ce qui traduit une **préférence éditoriale existante** dans le dépôt, **pas** une obligation de rendu.

Le `Quarto Pages Deploy` (`.github/workflows/quarto-pages-deploy.yml`) traite les deux notations sans casse sur `main`. Le motif Quarto/YAML front-matter **n'est pas établi** (les 54 cellules `---` restantes en production ne déclenchent aucun rouge CI). Une PR d'enrichissement qui substitue `---` → `***` sans déclarer la modification commet deux fautes :

1. **Claim C.3 rendu faux** : « cellules non modifiées restent byte-identiques à main » devient inexact pour 17+ cellules (mesure #14643).
2. **Pattern `reecriture-non-annoncee`** traqué par le dépôt (#14113/#14119), indépendamment de la bénignité du geste.

## Voies licites

Une PR d'enrichissement peut **toujours** :

- Ajouter de nouvelles cellules markdown portant `***` (préférence éditoriale du dépôt).
- Laisser intactes les cellules existantes, quelle que soit leur notation.
- **Déclarer** un sweep de normalisation comme dans la voie (a) du ticket #14683 (PR dédiée narrow scope 1:1, partition par famille — même véhicule que #14209), avec son motif et sa preuve.

## Détection

- `git diff` filtré sur `^[-+](---|\*\*\*)$` dans les fichiers `.ipynb` montre les substitutions brutes.
- Le label `reecriture-non-annoncee` (workflow `reecriture-non-annoncee.yml`) se déclenche quand une PR touche un notebook sans déclarer la modification.

## Interdits

- **Pas de substitution `---` → `***` silencieuse** dans une PR d'enrichissement qui s'annonce byte-identique (C.3).
- **Pas de motif Quarto supposé sans preuve** : la voie (a) du ticket #14683 l'exigeait explicitement (« établi, pas supposé »).
- **Pas de sweep one-shot global** qui toucherait l'ensemble du dépôt en une seule PR (cf #14209 — partition par famille, véhicule dédié).

## Voir aussi

- [notebook-conventions.md](notebook-conventions.md) — C.1 stubs, C.2 outputs, C.3 byte-identity
- [anti-regression.md](anti-regression.md) — pas de réécriture non déclarée
- [consecutive-code-cells.md](consecutive-code-cells.md) — pattern sibling sur cellules code consécutives
- issue **#14683** — ticket d'origine
