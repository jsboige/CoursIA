# Chantier 1 — tranche A7 : relecture froide — statuations (ops 2, 6), verdict catalogue, quatrième loi

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2023:CoursIA` · **date de mesure** 2026-10-12
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (op 1) · [A3](12204-ict-chantier-1-a3.md) (ops 3, 9) · [A4](12204-ict-chantier-1-a4.md) (op 4) · [A5](12204-ict-chantier-1-a5.md) (ops 2, 6, 10) · [A6](12204-ict-chantier-1-a6.md) (statuation 11-13 + file d'attente) · [audit froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md) (les 14 opérations, trois axes)

## Ce que cette tranche fait

Le grain A7 demandait : *« Relecture froide : la table est-elle un catalogue ? La vérification a-t-elle fait apparaître une quatrième loi ? »* Les tranches précédentes y ont en outre déposé des dossiers explicites — la réconciliation du 2026-10-04 : *« A7, quand il statuera, trouvera deux dossiers de plus sur son bureau »* (promotions ops 2 et 6). Cette tranche statue donc sur trois choses : (a) les deux dossiers, (b) le verdict catalogue, (c) la quatrième loi. Elle relit l'intégralité des ledgers du chantier et re-mesure firsthand les deux artefacts décisifs des statuations.

## Statuation 1 — Opération 6 « Réparer localement sous garantie » : PROMUE TABLE

Les deux attestations in-repo, indépendantes par le domaine :

| Attestation | Substrat | Témoin |
|---|---|---|
| Paire `GameTheory-13b/13c` (A5, exécutées) | jeux (safe subgame solving) | contre-témoin du raffinement naïf, garantie contrôlée |
| `Search/Part1-Foundations/Search-03f-Reparer-Localement-Sous-Garantie-Python.ipynb` (#19013) | recherche de chemin (LPA*) | garantie transportée, localité payée juste |

**Re-mesures firsthand de ce cycle** (une statuation ne s'appuie pas sur la mesure d'un autre sans relire — G.1) :

- Search-03f : **cellules code toutes exécutées avec sorties, 0 erreur** (lecture JSON du carnet) ; témoins présents (`8/8` concordances ×2, `12 expansions` ×7, `garantie` ×25) ;
- **Indépendance par construction confirmée : 0 occurrence de `Sandholm`/`Kroer` dans Search-03f** (grep insensible à la casse) — le carnet ne cite pas le cadre théorique dont l'attestation jumelle est issue ; l'indépendance n'est pas une allégation de la réconciliation, elle est mesurée dans le texte de l'artefact.

**Verdict : l'op 6 rejoint la TABLE.** Deux endroits du dépôt (`GameTheory/`, `Search/`), témoins mesurés, indépendance par construction. La réserve de la réconciliation (même source Sandholm) est levée par l'attestation qui ne la mentionne pas.

## Statuation 2 — Opération 2 « Abstraire à dette bornée » : reste en FILE D'ATTENTE

Les deux candidates recensées par la réconciliation : Kroer-Sandholm (théorie **externe**) + GT-19 (locale, mesurée). Re-mesure firsthand : GT-19 porte **5 occurrences de `Sandholm`/`Kroer`** — il cite sa source théorique, comme la réconciliation l'avait établi.

**Motif de non-promotion — le critère §1, pas la qualité de GT-19.** Le critère d'admission demande « deux attestations dans des endroits indépendants **du dépôt** ». Kroer-Sandholm n'est pas un endroit du dépôt : c'est une source théorique externe, exactement le statut qui avait fait descendre l'op 2 à l'audit froid (« externe tant que sa distillation n'a pas atterri »). La distillation #12208 (CLOSE) a livré GT-19 — qui devient la **première** attestation in-repo, pas la seconde. Compter (théorie externe, instantiation locale qui la cite) pour deux attestations indépendantes rééditerait le double comptage déjà refusé sur l'op 12 (A6) et la non-indépendance par le stimulus refusée sur l'op 3 (c.1308 : Infer-20, même chantier/jour/lane — ici, la dépendance est même plus forte : GT-19 cite explicitement sa source).

**Voie de promotion** (inchangée depuis A5) : une seconde instantiation in-repo sur autre série (Search, par exemple) qui abstrait à perte bornée **mesurée** sans citer Kroer-Sandholm — le patron exact de l'op 6 vient d'en faire la démonstration.

## Verdict 1 — La table est-elle un catalogue ?

**Oui au sens du garde-fou §1 — et ce verdict est une réussite, pas un échec.** Le garde-fou disait : *« une simple bibliothèque de transformations, même très riche, reste encore un CATALOGUE »*. La table n'est pas une *simple* bibliothèque, pour trois raisons mesurées :

1. **Des lois relient les opérations.** Les lois I-III couvrent 5 opérations (I : 5↔7 ; II : 1↔7 ; III : 13↔12) en **2 composantes connexes** — {1, 5, 7} et {12, 13}. Un catalogue n'a pas de graphe.
2. **Le critère d'admission fait tomber autant qu'il fait monter.** Bilan mesuré du chantier : 4 descentes (audit froid), 2 promotions refusées pour double comptage ou non-indépendance (op 12 en A6, op 2 ci-dessus), 1 rétrogradation de provenance corrigée à la volée (A6, correctif grep). Un inventaire qui ne dégrade jamais s'auto-certifie — celui-ci dégrade.
3. **Les dettes se sont précisées par la vérification** (§Dette unifiée ci-dessous). Un catalogue a des cases vides ; une table attestée a des dettes dont on sait ce que serait la levée.

**Le verrou du grade A tient, inchangé.** Les lois ne **composent pas entre elles** : on ne sait pas enchaîner I puis II pour prédire quelque chose ; pas d'adjonctions, d'unités, d'identités triangulaires. Le body le disait (« ce n'est pas un grade A ») — sept tranches plus tard, c'est toujours vrai, et c'est précisément le statut que la consigne d'origine assignait : prouver qu'on peut tenir un inventaire honnête **avant** de prétendre remplir les strates 6 et 7.

## Verdict 2 — La vérification a-t-elle fait apparaître une quatrième loi ?

**Oui — d'un type différent des trois premières, et c'est dit tel quel.**

Les lois I-III sont des lois de **composition** : elles relient deux opérations entre elles. La régularité apparue dans la vérification relie les **attestations** d'une même opération — les deux rives, preuve et mesure :

> **LOI IV — la mesure met au prix les hypothèses de la preuve.** Quand une opération est attestée sur les deux rives, l'attestation empirique ne se contente pas de confirmer : elle chiffre la borne, valide la reconstruction, exécute l'inclusion — ou **réfute une hypothèse du théorème**. Un théorème à hypothèses non mesurées est une attestation à moitié prix.

**Occurrences recensées** (toutes déjà mesurées par les tranches, croisées ce cycle) :

| Opération | Rive formelle | Rive mesure | Ce que la mesure fait au prix |
|---|---|---|---|
| 11 — Descendre sous budget | `Descent.lean` (terminaison sous **3 hypothèses**) | Search-11d (c.1208) | **réfute `hnostall`** (100 % blocage hors cible à budget généreux), mesure la dissociation budget/blocage |
| 9 — Élargir l'espace | `Admissibility.lean:50` (`P_reel ⊆ P_relache`) | SW-14 | **exécute** l'élargissement, témoin = diff de triplets + delta d'inférences |
| 14 — Agréger un collectif | `Shapley.lean:614-634` (Möbius sorry-free) | SC-06 | **valide la reconstruction** par exécution (écart 5.55e-17 entre deux voies) |
| point fixe | `argumentation_lean` (Knaster-Tarski) | Tweety-07a C# | **exécute le lfp** et imprime le témoin (`{a, c}`) |
| 1 — Recoordonner | `Life.lean` (kernel-décidable après recoordination) | MGS-21 / Sudoku-13 | **mesure la cause** (200/200 candidats R1 hors espace ; trois formes, trois destins) |
| 6 — Réparer sous garantie | Sandholm (théorie externe) | 13b/13c + Search-03f | **contrôle la garantie** (8/8 concordances, contre-témoin du naïf) |

L'occurrence fondatrice est l'op 11 : la mesure n'y confirme pas le théorème, elle **corrige** son domaine de validité — c'est le seul point du chantier où l'empirique a renvoyé le formel à ses hypothèses. Les autres occurrences pontées font au moins chiffrer.

**Réserve de type, écrite** : la Loi IV est une loi d'**admission**, pas de composition — elle renforce le critère §1 (la promotion d'une opération pontée exige la mesure des hypothèses, pas seulement la preuve), elle n'ajoute pas d'arête au graphe des opérations. Elle est **adoptée** ici parce que six occurrences indépendantes la portent et qu'elle codifie une pratique que la table a déjà tenue de fait (toutes ses opérations pontées l'ont satisfaite avant d'être nommées) — réversible au §4 comme toute décision de la table.

**Observation de structure au passage** : les 4 entrées TABLE sans pont preuve/mesure sont précisément les ops 8, 10, 12, 13 — la rive formelle elle-même (8), et les trois opérations dont les lois sont les plus combinatoires (10, et 12/13 reliées par la Loi III). Les lois de composition vivent côté empirique ; la loi d'admission vit sur le pont. La table le porte comme indice, pas comme conclusion.

## La dette unifiée — ce que la relecture ajoute

A2 reformulait la dette de l'op 1 : « nos trois attestations sont trois post-mortems » — la bonne représentation trouvée **après** l'échec, jamais dérivée. A4 reformulait celle de l'op 4 : côté Hashlife **la preuve décide des bords**, côté ICT-15d l'expérimentateur décide **sans théorie**. La relecture froide unifie : c'est **une seule dette**, pas deux —

> **« Qui décide ? »** — du changement de représentation (op 1), des bords du recouvrement (op 4). Dans le régime formel, un théorème décide (`padCenter2_margin_ge_jumpReach` ; la recoordination kernel-décidable). Dans le régime empirique, l'invariance se **teste**, elle ne se **dérive** pas. La levée de cette dette — une théorie qui choisirait la représentation ou les bords **avant** de payer l'échec — est la première chose qu'exigerait le passage du catalogue au grade A.

## État final de la table (après statuations)

**TABLE (12 entrées)** : 1, 4, **6** *(promue ce cycle)*, 7, 8, 9, 10, 11, 12, 13, 14, `point fixe`.
**FILE D'ATTENTE (6 entrées)** : 2 *(première attestation in-repo posée : GT-19 ; seconde = instantiation sans citation de la source)*, 3, 5, `institutionnaliser`, `inhiber`, `réviser une croyance`.
**Lois** : I, II, III (composition) + IV (adoption, type admission).

Les grains restants du chantier sont tous de type A5-final : des **secondes attestations de contenu** (ops 2, 3, 5) — créables dans d'autres séries sur le patron op 6/op 12, multi-heures chacun.

## Honnêteté méthodologique

- **Re-mesuré firsthand ce cycle** : Search-03f (comptes mécaniques + 0 mention Sandholm), GT-19 (5 mentions), claim CLEAR sur l'issue, absence de PR ouverte sur `docs/ledgers/12204-*`.
- **Croisé, pas re-mesuré** : les six occurrences de la Loi IV vivent dans leurs ledgers d'origine avec leurs preuves citées — la relecture les agrège, elle ne répète pas leurs expériences. Les verdicts d'ops 12/13/11/`point fixe` sont ceux d'A6, relus et acceptés.
- Cette tranche **statue** sur des dossiers préparés par d'autres lanes (po-2025, po-2026, po-2027, po-2024, ai-01) — la relecture froide était le seul grain conçu pour ça : son auteur n'a pas participé aux tranches qu'il juge.

## Références

- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · claim : [issuecomment-6120275820](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6120275820)
- Précédent de non-indépendance par le stimulus : tranche c.1308 du [ledger audit-froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md) (op 3, Infer-20)
- Refus de double comptage : [A6 §Op 12](12204-ict-chantier-1-a6.md)
