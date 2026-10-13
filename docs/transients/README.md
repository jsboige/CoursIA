# Rapports transients (`docs/transients/`)

Lane des documents **transients** de la documentation CoursIA : comptes rendus, audits datés, instantanés d'état — des documents qui portent une valeur de preuve à leur date de production et qui n'ont pas leur place dans l'arbre pérenne.

Lane ouverte par #14623. L'organe qui vérifie la convention est [`scripts/check_docs_transients_lane.py`](../../scripts/check_docs_transients_lane.py).

> **Pourquoi `transients/`, et ni `reports/` ni `rapports/`.** `.gitignore` écarte **récursivement** les deux noms, chacun pour une raison de fond : ligne 711, `reports/` — rapports de notation ECE contenant des données personnelles étudiantes (« never commit ») ; ligne 784, `rapports/` — « Reports and temporary assets (use RooSync dashboard instead) ». Un fichier déposé sous un `reports/` ou un `rapports/` quelconque est **ignoré par git sans le dire** : la lane aurait un contenu que personne ne peut committer. Le nom retenu décrit donc la **propriété** qui définit la lane — la transience — et non le type de document, précisément pour ne pas heurter ces deux règles ; il ne s'agit pas de percer des garde-fous (protection de données personnelles, doctrine « les rapports vont au dashboard ») mais de nommer autrement ce que #14623 demande de déposer dans l'arbre.
>
> **Mesurer un nom avant de le choisir.** `git check-ignore -v docs/<nom>/` — avec le **slash final** : sur un chemin inexistant sans slash, git interroge un *fichier*, et une règle `nom/` ne répond pas (faux « libre » mesuré sur `docs/rapports` à la création de cette lane). Puis `git add` réellement, seul instrument qui tranche.

## Trois catégories, trois destinations

| Catégorie | Ce que c'est | Où ça vit | Ce qui en sort |
|---|---|---|---|
| **Pérenne** | Doc vivante : référence, procédure, règle, état d'une série | `docs/reference/`, `docs/<thème>/` | Reste ; se met à jour sur place |
| **Transiente** | Rapport, audit, instantané daté — une mesure, à sa date | **`docs/transients/`** (cette lane) | Sort par distillation (ci-dessous) |
| **Archive** | Contenu conservé pour mémoire, inactif | `docs/archive/` | **Stock à résorber**, pas une destination |

`docs/archive/` **n'est pas** la destination d'un rapport de cette lane : y déposer un transient de plus agrandit le stock que #14623 existe pour réduire. Un rapport ne rejoint `docs/archive/` que lorsque sa distillation est faite et qu'il ne reste qu'un document inerte à conserver pour mémoire.

## Convention — nom et en-tête

Un fichier de cette lane porte :

1. **un nom préfixé par sa date de production** : `<YYYY-MM-DD>-<slug>.md`. La forme est déjà employée dans l'arbre (cf. `docs/ledgers/`) — cette lane la codifie, elle ne l'invente pas ;
2. **en tête**, la ligne d'en-tête gelée :

```
> RAPPORT — <date de production> — <périmètre> — figé
```

Exemple :

```
> RAPPORT — 2026-09-29 — audit des filtres de chemin des workflows — figé
```

Le mot `figé` est le marqueur du contrat : un document qui le porte est un instantané, il ne se met pas à jour sur place. S'il doit vivre et évoluer, c'est qu'il est pérenne — il change alors de lane plutôt que d'en-tête.

## Née ici, sort par distillation

Un rapport ne s'accumule pas. Quand sa conclusion est durable, elle est **distillée** dans le document pérenne qui la porte (règle, référence, procédure, README de série), et ce document **cite** le rapport. Une fois la distillation faite, le rapport a fini son office : il peut être archivé ou retiré. La lane est un **transit**, pas un stock.

## Sortie d'archive (`docs/archive/`)

L'archive est un **stock à résorber, pas une destination** (tranche 2 de #14623). Elle ne grandit plus par dépôt de rapports neufs ; elle se résorbe par trois voies, chacune appuyée sur une preuve citée dans la PR :

| Voie | Quand | Preuve exigée dans la PR |
|---|---|---|
| **Distillation** | le contenu durable d'un document archivé sert un document vivant | le diff du document pérenne enrichi, plus le chemin de l'original archivé — qui **reste en place** : l'archive ne réécrit pas l'histoire, elle se résorbe morceau par morceau |
| **Restauration** | un document archivé s'avère mal classé : c'est une référence pérenne | la citation de l'en-tête ou du contenu qui fonde le caractère pérenne — établie sur **lecture complète** du fichier, jamais sur le titre (leçon de la re-vérification #14623 : « état d'une série » est pérenne par la table des catégories elle-même) |
| **Retrait** | contenu intégralement absorbé ou dupliqué ailleurs | preuve de préservation : diff vide contre le document survivant, ou contenu byte-identique cité |

**Entrée : un rapport daté neuf ne rejoint plus `docs/archive/`.** La destination d'un rapport daté est cette lane, `docs/transients/` (nom daté + en-tête gelé). Déplacer un document **existant** vers l'archive reste légitime — c'est une reclasse, pas une création. La distinction est mécanique : l'organe signale toute **création** (statut `A` du diff ; les renames `R` sont des reclasses) sous `docs/archive/` portant la signature transiente — nom daté `<YYYY-MM-DD>-…` ou en-tête gelé en tête :

```bash
python scripts/check_docs_transients_lane.py --base origin/main
```

La garde CI [docs-transients-guard](../../.github/workflows/docs-transients-guard.yml) applique ce contrôle à chaque PR touchant `docs/**/*.md`.

## Vérification

```bash
python scripts/check_docs_transients_lane.py                          # CONFORME (0) / VIOLATION (1)
python scripts/check_docs_transients_lane.py --json                   # verdict machine
python scripts/check_docs_transients_lane.py --base origin/main       # + contrôle d'entrée d'archive
python -m pytest scripts/tests/test_check_docs_transients_lane.py -q
```

L'organe vérifie les **trois sens** du contrat :

- **dans la lane** — chaque `*.md` (sauf ce README) est daté et porte l'en-tête gelé, dont la date concorde avec celle du nom ;
- **hors de la lane** — aucun fichier de `docs/` (hors `docs/archive/` et cette lane) ne porte l'en-tête `> RAPPORT —` en tête de document : un transient égaré dans l'arbre pérenne est exactement la dérive que cette lane existe pour rendre visible ;
- **entrée d'archive** (avec `--base <ref>`) — aucune **création** de rapport daté sous `docs/archive/` dans le diff `<ref>...HEAD` : les reclasses (renames) restent permises, les créations portant la signature transiente sont signalées. Un échec du `git diff` sous-jacent est lui-même un finding (`GIT_DIFF_FAILED`), jamais un acquittement silencieux.

## État

Lane ouverte le 2026-09-29, **vide à dessein**. Le premier peuplement vient de la re-vérification des fichiers listés par #14623, qui a mesuré que la majorité d'entre eux ne sont **pas** des transients — références citées par le harnais, artefact régénéré par la CI, fichier sous PR ouverte — et ne se déplacent donc pas ici.

## Hors périmètre

- réparation des liens de `docs/archive/` (#13748) ;
- refonte de l'index `docs/README.md` (#13748) ;
- convention `_archive/` du code (#13749).