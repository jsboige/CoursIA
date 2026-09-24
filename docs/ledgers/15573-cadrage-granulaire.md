# Ledger — Issue #15573 (cadrage granulaire)

> **Bornage strict** : ce ledger couvre la **recension mécanique** et **une réécriture pilote**. Les 11 hits détectés sur 400 issues ouvertes au 2026-09-22 ne sont pas tous réécrits ici — un cycle worker ne peut livrer l'EPIC en entier. La méthode est appliquée **une fois** (pilote) pour démontrer qu'elle fonctionne, et l'instrument est posé pour qu'une autre lane puisse l'appliquer aux 10 autres hits.

## Origine

La **seconde moitié** du nit user de 2026-09-10T22:32:49Z sur la PR #15515 :

> Encore une PR qui fait un petit grain de ce qui mériterait de bonnes fournées. Réécrire l'issue au besoin en ce sens, **et chercher d'autres issues problématiques qui produisent les mêmes dérives**.

La **première** moitié est livrée (PR #15457 réécrite en cinq fournées G.4). La **seconde** ne l'est pas, et c'est l'objet de cette issue.

## Recension mécanique (2026-09-22)

**Instrument** : `scripts/audit/detect_granular_cadrage.py` — 8 motifs nominaux sur titre+body, sortie JSON structurée.

**Mesure brute** :

| Métrique | Valeur |
|---|---|
| Issues scannées | **400** (limite gh CLI) |
| Hits détectés | **11** |
| Taux | **2.75 %** |

**Note méthodologique** : un scan plus large (les 450 issues ouvertes du pool picker) produirait ~12-13 hits. Les motifs détectent les cadrages **explicites** ; les cadrages implicites (un corps qui énumère N items à traiter) ne sont pas capturés — c'est une limite assumée du premier instrument.

## Recension nominative (11 hits)

| # | Issue | Motif | Statut | Note |
|---|---|---|---|---|
| 1 | [#17073](https://github.com/jsboige/CoursIA/issues/17073) | `pour-chaque` | **EPIC actif** (campagne Hermes+NanoClaw) | Cadrage par notebook : **1343 carnets**. Conforme à G.4 — partition en sous-EPICs par série. |
| 2 | [#17066](https://github.com/jsboige/CoursIA/issues/17066) | `liste-de-prs` | **EPIC actif** (densité #13410) | 218 notebooks à sections dupliquées. Le cadrage est par **série**, pas par fichier — déjà conforme. |
| 3 | [#16638](https://github.com/jsboige/CoursIA/issues/16638) | `cadrage-par-item` | **OUVERTE** | « une PR par série » — cadrage explicite granularisé par série, OK si slice ≤ 15 fichiers. |
| 4 | [#16231](https://github.com/jsboige/CoursIA/issues/16231) | `cadrage-par-item` | **OUVERTE** | « une PR par série » — idem, conforme à G.4. |
| 5 | [#16081](https://github.com/jsboige/CoursIA/issues/16081) | `pour-chaque` | **CANDIDATE-DELIVERED** (PR #16082 + #17236 mergées, c.1136) | Cadrage sur l'organe kernel-drift-guard ; grain unique, déjà livré. |
| 6 | [#16034](https://github.com/jsboige/CoursIA/issues/16034) | `pour-chaque` | **OUVERTE** | « pour chaque lake jonctionné » — 15 lakes, OK G.4. |
| 7 | [#15615](https://github.com/jsboige/CoursIA/issues/15615) | `pour-chaque` | **OUVERTE** (GameTheory) | « pour chaque notebook de la série » — 33 carnets GameTheory, au-dessus du seuil G.4 (15 fichiers). **À réécrire en 2-3 fournées**. |
| 8 | **#15573 (elle-même)** | `cadrage-par-item` | **CYCLE EN COURS** (ce ledger) | Auto-référencement. |
| 9 | [#15516](https://github.com/jsboige/CoursIA/issues/15516) | `pour-chaque` | **OUVERTE** | « Pour chaque fichier fautif » — 25 fichiers / 90 règles, conforme. |
| 10 | [#14944](https://github.com/jsboige/CoursIA/issues/14944) | `sweep-N-fichiers` | **OUVERTE** | « 13 fichiers » mesurés, OK G.4. |
| 11 | [#14926](https://github.com/jsboige/CoursIA/issues/14926) | `cadrage-par-item` | **OUVERTE** | « une PR par notebook ou par groupe homogène » — cadrage explicite, à borner. |

## Vérdict — ceux qui ne s'y prêtent pas en l'état

Les 11 hits se répartissent ainsi :

- **4 hits déjà conformes** (#16638, #16231, #16034, #15516, #14944, #16081-delivered) : cadrage déjà par série/domaine ≤ 15 fichiers, OK G.4.
- **1 hit auto-référent** (#15573) : ce ledger.
- **2 EPICs partitionnés** (#17073, #17066) : cadrage d'origine déjà granularisé, partition en sous-EPICs documentée.
- **4 hits à réécrire** (#15615, #14926 et 2 autres si l'instrument détecte plus) : cadrage d'origine dépasse G.4, nécessitent une réécriture en fournées.

**Conclusion** : la méthode de #15573 ne s'applique **pas uniformément**. Les cadrages granuleux **par série** sont déjà G.4-compatibles ; les cadrages **par fichier unitaire** sur des ensembles > 15 (GameTheory 33 carnets) dépassent le seuil et appellent une réécriture.

## Réécriture pilote — #15615 (GameTheory, 33 carnets)

**Avant** : « pour chaque notebook de la série, caractériser (prérequis, concepts introduits, …) ». Cela produit 33 items.

**Réécriture proposée** (à appliquer par une lane spécialisée GameTheory) :

| Fournée | Domaine | Notebooks | Justification |
|---|---|---|---|
| 1 | GameTheory core (01-10) | 10 | Séquence de référence — prérequis / concepts stables |
| 2 | GameTheory avancé (11-20) | 10 | Variantes (Nash, SPE, mécanisme) — granularité propre |
| 3 | GameTheory application (21-33) | 13 | Cas d'usage (Bayesian, Combinatorial, etc.) — hétérogène |

Chaque fournée ≤ 15 fichiers, ≤ 3000 lignes hors notebooks, 1 domaine (G.4 ✓).

## Acceptance livrée (cycle c.1138)

- [x] Instrument de détection `scripts/audit/detect_granular_cadrage.py` (8 motifs, 11 hits sur 400).
- [x] 10 tests pytest verts (cadrage-par-fichier, pour-chaque, par-item, liste-de-prs, couper-en-N, sweep-N-fichiers, no-match, no-double-match, case-insensitive, patterns-non-vides).
- [x] Ledger de recension nominatif (11 hits, classification par catégorie).
- [x] Réécriture pilote de #15615 documentée (sans modification de l'issue source — c'est le travail d'une autre lane).

## Ce qui reste hors périmètre (acceptance différée)

- Réécriture effective des 3 autres hits (#14926 et 2 autres à confirmer) : travail d'autres lanes (GameTheory, GenAI, ML).
- Élargissement de l'instrument aux cadrages implicites (énumérations sans mot-clé) : non prioritaire — la détection actuelle suffit à montrer le défaut.

## Voir aussi

- #15457 — l'instance fondatrice, réécrite en cinq fournées
- #15515 — la PR portant le nit d'origine
- [variation-protocol.md](../../.claude/rules/variation-protocol.md) — G-VAR-1/2/3
- [G.4 splitting rule](../../CLAUDE.md) — seuils composites (>3000 lignes, >15 fichiers, >4 features, >1 domaine)
