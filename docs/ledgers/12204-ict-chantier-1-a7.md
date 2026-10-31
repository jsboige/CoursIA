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
- **Indépendance par construction confirmée : 0 occurrence de `Sandholm`/`Kroer` dans Search-03f** (grep insensible à la casse) — le carnet ne cite pas le cadre théorique dont l'attestation jumelle est issue ; l'indépendance n'est pas une allégation de la réconciliation, elle est mesurée dans le texte de l'artefact. *(Requalifié le 2026-10-21 : ce grep est un **indice documentaire**, pas une preuve — un carnet peut implémenter une abstraction issue de la même littérature sans la nommer ; voir §Correctif du 2026-10-21, la preuve d'origine y est refondée sur éléments positifs.)*

**Verdict : l'op 6 rejoint la TABLE.** Deux endroits du dépôt (`GameTheory/`, `Search/`), témoins mesurés, indépendance par construction. La réserve de la réconciliation (même source Sandholm) est levée par l'attestation qui ne la mentionne pas. *(Requalifiée le 2026-10-21 : la réserve est levée par la preuve positive d'origine — littérature et algorithme distincts —, non par l'omission ; voir §Correctif. Le verdict TABLE est maintenu sur ces nouveaux motifs.)*

## Statuation 2 — Opération 2 « Abstraire à dette bornée » : reste en FILE D'ATTENTE

Les deux candidates recensées par la réconciliation : Kroer-Sandholm (théorie **externe**) + GT-19 (locale, mesurée). Re-mesure firsthand : GT-19 porte **5 occurrences de `Sandholm`/`Kroer`** — il cite sa source théorique, comme la réconciliation l'avait établi.

**Motif de non-promotion — le critère §1, pas la qualité de GT-19.** Le critère d'admission demande « deux attestations dans des endroits indépendants **du dépôt** ». Kroer-Sandholm n'est pas un endroit du dépôt : c'est une source théorique externe, exactement le statut qui avait fait descendre l'op 2 à l'audit froid (« externe tant que sa distillation n'a pas atterri »). La distillation #12208 (CLOSE) a livré GT-19 — qui devient la **première** attestation in-repo, pas la seconde. Compter (théorie externe, instantiation locale qui la cite) pour deux attestations indépendantes rééditerait le double comptage déjà refusé sur l'op 12 (A6) et la non-indépendance par le stimulus refusée sur l'op 3 (c.1308 : Infer-20, même chantier/jour/lane — ici, la dépendance est même plus forte : GT-19 cite explicitement sa source).

**Voie de promotion** (inchangée depuis A5) : une seconde instantiation in-repo sur autre série (Search, par exemple) qui abstrait à perte bornée **mesurée** sans citer Kroer-Sandholm — le patron exact de l'op 6 vient d'en faire la démonstration. *(Correctif 2026-10-21 : la voie est refondée sur l'**origine**, pas l'omission — voir §Correctif : « sans citer Kroer-Sandholm » n'est ni nécessaire ni suffisant ; ce qui porte la promotion est une origine documentairement établie, littérature propre citée et algorithme distinct du cadre.)*

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
**FILE D'ATTENTE (6 entrées)** : 2 *(première attestation in-repo posée : GT-19 ; seconde = instantiation d'origine documentairement établie — correctif 2026-10-21)*, 3, 5, `institutionnaliser`, `inhiber`, `réviser une croyance`.
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

## Correctif du 2026-10-21 — la preuve d'indépendance requalifiée (revue externe, dispatch ai-01)

**Provenance.** Une revue externe, confirmée par le coordinateur ([commentaire 6321883534](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6321883534), DM c2205-astra-12204), relève que la Statuation 1 traitait l'**absence de citation comme une preuve d'indépendance** : « 0 occurrence de Sandholm/Kroer [...] l'indépendance est mesurée dans le texte de l'artefact », « la réserve [...] est levée par l'attestation qui ne la mentionne pas », et la voie de promotion de l'op 2 en faisait un critère (« sans citer Kroer-Sandholm »). Le reproche est fondé : **un grep négatif mesure ce que le carnet écrit, pas d'où vient son algorithme** — et posé en critère, il récompense l'attestation qui tait sa source. Ce correctif requalifie, refonde et re-statue ; les formulations d'origine restent visibles ci-dessus, annotées.

**Le test documentaire exécuté ce cycle** (ce qui testerait *vraiment* l'indépendance, exécuté sur Search-03f) :

| Axe | Mesure firsthand | Résultat |
|---|---|---|
| **Références du carnet** | cellule 0 + cellule 7 : « LPA\* (Koenig & Likhachev, 2002) » ; cellule Référence (46) : « Sven Koenig & Maxim Likhachev, *D\* Lite*, AAAI 2002 » | ancrage **positif** dans la littérature *recherche incrémentale*, distincte de la littérature jeux |
| **Algorithme implémenté** | cellule 8 : signature LPA\* complète ($g$, $rhs$, file d'incohérences $U$, clés $k=(k_1,k_2)$) ; exercice 3 : clause d'arrêt $k_{top} \geq key(goal)$ | la machinerie **Koenig-Likhachev authentique**, pas une transposition du *safe subgame solving* (attestation jumelle : contrainte d'adversaire, GT-13b/13c) |
| **Historique de création** | issue #19013, créée 2026-10-03, lane `myia-po-2027:CoursIA`, body : « Seconde attestation de l'opération 6 [...] suivant le patron des précédentes promotions » | **stimulus partagé** (commissionné par le chantier) ; lane, série et littérature distinctes de la première attestation |

**Nouvelle statuation de l'op 6 — TABLE maintenue, motifs refondés.** L'indépendance ne repose plus sur l'omission mais sur **trois éléments positifs** : littérature propre citée dans le carnet (Koenig & Likhachev), algorithme identifiable et distinct du cadre Sandholm, substrat et série distincts. Le grep « 0 Sandholm/Kroer » devient ce qu'il est : un **indice documentaire** cohérent avec ces éléments, jamais une preuve à lui seul. **Résiduel écrit** : le stimulus est partagé (les deux attestations existent pour témoigner de l'op 6) — le précédent op 3 (c.1308, Infer-20) avait refusé l'indépendance pour *même chantier/jour/lane* ; ici chantier partagé mais lane, série, littérature et machinerie algorithmique distinctes. L'indépendance est établie **au niveau documentaire que le dépôt permet** : la source de l'abstraction « réparer sous garantie » est la littérature LPA\*, pas une dérivation du cadre Sandholm silencieusement copiée.

**Voie de promotion de l'op 2 — refondée sur l'origine.** La seconde attestation exigée n'est plus « une instantiation qui ne cite pas Kroer-Sandholm » mais : *une instantiation in-repo sur autre série dont l'**origine** est documentairement établie* — (i) littérature propre citée dans la cellule références, (ii) algorithme implémenté identifiable et distinct du cadre Kroer-Sandholm, (iii) perte bornée **mesurée**. L'absence de citation n'est ni nécessaire ni suffisante : un carnet qui tait sa source ne gagne pas l'indépendance ; un carnet qui cite une *autre* littérature la documente.

**Propagation traitée.** La formulation défectueuse avait essaimé : (a) [A8](12204-ict-chantier-1-a8.md) §op 6 avait posé comme condition de falsifiabilité « l'apparition d'une citation Sandholm/Kroer dans Search-03f » — requalifiée par annotation (une future citation bibliographique ne changerait pas l'origine de l'algorithme ; la falsification pertinente reste la violation de la garantie, condition (a)) ; (b) [A9](12204-ict-chantier-1-a9.md) a exécuté l'ancienne voie (« construite sans citation de Kroer-Sandholm ») pour proposer la promotion de l'op 2 — annoté : le dossier A9 **contient déjà** la preuve positive d'origine (sources d'hommage Culberson & Schaeffer 1998, Holte et al. 2005 — lignée *pattern databases*, distincte de la littérature jeux) ; la statuation qui jugera ce dossier doit peser l'origine sur ces éléments, non sur le contraste de grep.

**Re-mesuré firsthand ce correctif** : citations Koenig/Likhachev de Search-03f (cellules 0, 7, 46), signature algorithmique de la cellule 8, historique #19013 (createdAt/lane/body), propagation A8 §op 6 et A9 (lectures entières des deux ledgers).
