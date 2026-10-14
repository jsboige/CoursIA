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
| 7 | [#15615](https://github.com/jsboige/CoursIA/issues/15615) | `pour-chaque` | **RÉÉCRITE (2026-10-03)** | « pour chaque notebook de la série » — **114 carnets** mesurés sur main (blocs 01-25 + accrétions). Body réécrit avec préfixe daté : audit en 4 fournées (A 01-05 ×33, B 06-10 ×30, C 11-15 ×25, D 16-25 ×26). |
| 8 | **#15573 (elle-même)** | `cadrage-par-item` | **CYCLE EN COURS** (ce ledger) | Auto-référencement. |
| 9 | [#15516](https://github.com/jsboige/CoursIA/issues/15516) | `pour-chaque` | **OUVERTE** | « Pour chaque fichier fautif » — 25 fichiers / 90 règles, conforme. |
| 10 | [#14944](https://github.com/jsboige/CoursIA/issues/14944) | `sweep-N-fichiers` | **OUVERTE** | « 13 fichiers » mesurés, OK G.4. |
| 11 | [#14926](https://github.com/jsboige/CoursIA/issues/14926) | `cadrage-par-item` | **OUVERTE** | « une PR par notebook ou par groupe homogène » — cadrage explicite, à borner. |

## Vérdict — ceux qui ne s'y prêtent pas en l'état

Les 11 hits se répartissent ainsi :

- **4 hits déjà conformes** (#16638, #16231, #16034, #15516, #14944, #16081-delivered) : cadrage déjà par série/domaine ≤ 15 fichiers, OK G.4.
- **1 hit auto-référent** (#15573) : ce ledger.
- **2 EPICs partitionnés** (#17073, #17066) : cadrage d'origine déjà granularisé, partition en sous-EPICs documentée.
- **Hits réécrits** : #18058 (2026-09-29, PR #18382) · #15615 (2026-10-03, ce ledger). **Reste à réécrire** : #14926 (et d'autres si l'instrument en détecte) — cadrage d'origine dépasse G.4, nécessitent une réécriture en fournées.

**Conclusion** : la méthode de #15573 ne s'applique **pas uniformément**. Les cadrages granuleux **par série** sont déjà G.4-compatibles ; les cadrages **par fichier unitaire** sur des ensembles > 15 (GameTheory 33 carnets) dépassent le seuil et appellent une réécriture.

## Réécriture pilote — #15615 (GameTheory)

**Avant** : « pour chaque notebook de la série, caractériser (prérequis, concepts introduits, …) ». La recension du 2026-09-22 comptait 33 carnets ; la mesure du 2026-10-03 en trouve **114** sur main (tous numérotés, blocs 01-25 + accrétions lettrées ; blocs denses : 06×12, 15×10, 03×8, 04×8).

**Réécriture APPLIQUÉE le 2026-10-03** au body de [#15615](https://github.com/jsboige/CoursIA/issues/15615) (préfixe daté, historique conservé) — l'audit de gradation se livre en 4 fournées :

| Fournée | Blocs | Carnets (mesuré) | Thèmes dominants (titres) |
|---|---|---|---|
| A | 01-05 | 33 | forme normale, Nash, premières preuves Lean |
| B | 06-10 | 30 | combinatoire, évolution, répétés, extensifs, Stackelberg |
| C | 11-15 | 25 | jeux coopératifs, bayésiens |
| D | 16-25 | 26 | design de mécanismes, bayésien appliqué, open-source |

Une fournée = un sous-tableau de gradation posté en commentaire de l'issue = un grain MED livrable indépendamment ; l'ordre cible (scope 2) se consolide après les 4 fournées. Les scopes 2 et 3 du body d'origine sont inchangés.

## Acceptance livrée (cycle c.1138)

- [x] Instrument de détection `scripts/audit/detect_granular_cadrage.py` (8 motifs, 11 hits sur 400).
- [x] 10 tests pytest verts (cadrage-par-fichier, pour-chaque, par-item, liste-de-prs, couper-en-N, sweep-N-fichiers, no-match, no-double-match, case-insensitive, patterns-non-vides).
- [x] Ledger de recension nominatif (11 hits, classification par catégorie).
- [x] Réécriture pilote de #15615 documentée (sans modification de l'issue source — c'est le travail d'une autre lane).

## Ce qui reste hors périmètre (acceptance différée)

- Réécriture effective de #14926 (dernier hit ouvert de la recension du 2026-09-22) : cadrage « une PR par notebook ou par groupe homogène » à borner — domaine claudish.
- **Exécution des fournées A-D de #15615** : la réécriture pose le cadrage, les sous-tableaux de gradation restent à produire par une lane spécialisée GameTheory.
- Élargissement de l'instrument aux cadrages implicites (énumérations sans mot-clé) : non prioritaire — la détection actuelle suffit à montrer le défaut.

## Voir aussi

- #15457 — l'instance fondatrice, réécrite en cinq fournées
- #15515 — la PR portant le nit d'origine
- [variation-protocol.md](../../.claude/rules/variation-protocol.md) — G-VAR-1/2/3
- [G.4 splitting rule](../../CLAUDE.md) — seuils composites (>3000 lignes, >15 fichiers, >4 features, >1 domaine)

## Entrée #18058 — première réécriture APPLIQUÉE (lane myia-po-2023:CoursIA, 2026-09-29)

**Hit** : `cadrage-par-item` — « Une PR par notebook ou par série » (§ Comment prendre une tranche).

**Mesure du plateau au geste** : 8 PRs sous #18058 en 2 jours — 3 mono-notebook (MGS-07c #18097 MERGED, MGS-07d #18092 OPEN, PT_08 #18069 OPEN) contre 3 tranches batchées conformes (RAG 05 #18088, 01-3 #18074, SK-01 #18101, toutes MERGED). La lecture unitaire prévaut sur le « ou par série » — demi-défaut #15457 : l'option fournée existait mais n'était pas prescrite.

**Réécriture appliquée** : bullet remplacé par « Fournées par famille d'abord — 2 à 4 PRs au total, jamais une PR par notebook », avec l'exception mono-PR (ré-exécution > ~30 min ou claim conflictuel) et les modèles livrés cités. Préfixe daté posé sur le body (le lecteur voit ce qui a changé, historique conservé).

**Hit #17550 dispositionné sans réécriture** (même cycle) : le plateau s'est auto-corrigé — 9 mono-PRs revertées puis fermées par ai-01 « le reste consolidé en une seule PR » (po-2025:CoursIA-2) ; il ne reste que #18255 (tranche 15/16, dossier adjoint). Réécrire maintenant serait du churn sur une issue presque résolue.
