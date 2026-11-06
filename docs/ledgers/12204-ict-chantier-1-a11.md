# Chantier 1 — tranche A11 : statuation des opérations 3 « Quotienter/fibrer » et 5 « Recoller » au format d'admission, et examen du dossier « réviser une croyance »

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2028:CoursIA` · **date de mesure** 2026-11-02
**Base** : `60cad4a59386` (`origin/main`)
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (op 1) · [A3](12204-ict-chantier-1-a3.md) (ops 3, 9) · [A4](12204-ict-chantier-1-a4.md) (op 4) · [A5](12204-ict-chantier-1-a5.md) (ops 2, 6, 10) · [A6](12204-ict-chantier-1-a6.md) (statuation 11-13 + file d'attente) · [A7](12204-ict-chantier-1-a7.md) (statuations ops 2, 6, quatrième loi + Correctif du 2026-10-21) · [A8](12204-ict-chantier-1-a8.md) (conditions de rétrogradation) · [A9](12204-ict-chantier-1-a9.md) (seconde attestation op 2) · [A10](12204-ict-chantier-1-a10.md) (statuation op 2)

## Ce que cette tranche fait

A10 laissait les ops 3 et 5 en FILE D'ATTENTE avec leurs **secondes attestations livrées et fondues** (#19109 → Search-03b, #19112 → Search-03f, mergées le 05/10) et la statuation « pas encore faite ». Cette tranche est cette statuation : elle re-mesure les deux dossiers firsthand sur `main` courant, départage la question de localisation laissée ouverte (le commit `62691e121`/#22127 annonce une « fusion 03g » qui ne concerne **pas** le témoin op 3 — voir §Départage), pèse l'origine des secondes attestations sur les trois axes du Correctif A7, et statue au format d'admission à trois champs fixé par l'arbitrage du 2026-10-14 et [A8](12204-ict-chantier-1-a8.md). Elle examine en outre le dossier `réviser une croyance`, dont l'annotation de file (« Tweety, non branché ») datait d'A6 (27/09) et prédate la livraison de GT-13e (#20215, 10/10).

## Départage préalable — où vivent les témoins après les fusions

Deux événements de nommage coexistent et se confondent facilement :

- **#19109 (04/10)** a livré `Search-03g-Quotienter-Fibrer-Python.ipynb` ; le carnet dédié a été **retiré au profit du logement dans Search-03b** (cf A10 l.51 et la file d'attente du body). Aucun fichier `Search-03g-Quotienter` n'existe plus sur `main` (mesuré : `git ls-files` Part1-Foundations → 03, 03b, 03c, 03d, 03e, 03f seulement).
- **#22127 (commit `62691e121`)** annonce « 03g fusionne » : il concerne un **second** 03g génération **mémoire bornée** (#22125), fusionné dans Search-03f — pas le témoin op 3.

**Mesure firsthand de ce cycle** (empreintes des témoins dans les carnets committés) : le contenu op 3 (quotient d'occupation `S_B`, règle de chaîne, dette Ruzsa) vit dans **Search-03b** (cellules 26-38) ; le contenu op 5 (recollement, σ, colle) vit dans **Search-03f** (cellules 19-40 et 70). La lecture d'A10 est confirmée ; l'apparent conflit avec `62691e121` est résolu par généalogie.

## Re-mesures firsthand de ce cycle

Une statuation ne s'appuie pas sur la mesure d'un autre sans relire (G.1). Toutes les mesures ci-dessous sont exécutées le 2026-11-02 sur `origin/main` (`60cad4a59386`), lecture JSON des carnets committés.

**État d'exécution** :

| Témoin | Cellules code | `execution_count` null | Erreurs |
|---|---|---|---|
| `Search/Part1-Foundations/Search-03b-PatternDatabases.ipynb` | 24 | 0 | 0 |
| `Search/Part1-Foundations/Search-03f-Reparer-Localement-Sous-Garantie-Python.ipynb` | 31 | 0 | 0 |
| `SymbolicAI/Lean/ANALYSE/ANALYSE-04-PFR-Primitives-Python.ipynb` | 11 | 0 | 0 |
| `GameTheory/GameTheory-13e-Revision-Croyances-Adversaire-Python.ipynb` | 13 | 0 | 0 |

Les empreintes numériques des témoins ont été vérifiées **dans les sorties committées** (pas seulement en source) :

- **Op 3, Search-03b** : règle de chaîne `15.8842 = 6.3923 + 9.4919` et contrôle Monte-Carlo 200 000 tirages (cell. 29) ; `I(X_A;X_B | S_B) = 0` exactement contre `2.070389` bits marginaux (cell. 31) ; contre-témoin profils de lignes `1.582975` bit avec hiérarchie assertée (cell. 33) ; dette Ruzsa `81/81` par structure (Z_9) contre `80/84` par contingence (puzzle, 4 fibres à successeurs multiples — cell. 37).
- **Op 5, Search-03f** : tables de couverture avec portails du triple chevauchement `(3,4)`, `(3,6)` (cell. 21-23) ; composition σ = π_AB∘π_BC∘π_CA = ((3,4) (3,6)) ≠ id avec compatibilité par paires vérifiée et non-recollabilité exhaustive 0/24 (cell. 25-34) ; **témoin exploitable Loi I** : marche de méidentification exécutée pas à pas — position réelle (3,4), colle croyante (3,6), l'agent traverse son but au pas 1, finit en (4,2), optimum réel 1 pas (cell. 32, sortie intégrale) ; **réparation mesurée** : π_AB corrigée bijection OK, σ recomposée = identité assertée, « Numerotations globales coherentes apres reparation : 24 / 24 », univalence des trois chaînes de consultation assertée (cell. 34).

**L'origine des secondes attestations pesée sur les trois axes du Correctif A7** :

*Op 3 — seconde attestation Search-03b :*

| Axe | Mesure firsthand (2026-11-02) | Verdict |
|---|---|---|
| (i) Littérature propre citée | `Culberson` ×6, `Felner` ×19, `Edelkamp` ×4, `Korf` ×21 — lignée pattern databases, distincte de la littérature PFR | **réuni** |
| (ii) Algorithme identifiable et distinct du cadre de la première attestation | Quotient d'occupation `S_B` du puzzle glissant, inférence conditionnelle mesurée sur énumération exhaustive (60 480 états) — machinerie pattern-databases, pas une transposition des primitives additives de Ruzsa d'ANALYSE-04 | **réuni** |
| (iii) Témoin **mesuré** | `I(X_A;X_B \| S_B) = 0` exact (sortie committée) + règle de chaîne vérifiée à 1.8e-15 + contre-témoin hiérarchisé | **réuni** |

*Op 5 — seconde attestation Search-03f :*

| Axe | Mesure firsthand (2026-11-02) | Verdict |
|---|---|---|
| (i) Littérature propre citée | `Koenig` ×3, `LPA` ×55 — lignée recherche incrémentale (LPA*), distincte du cadre de dualité prix/tickets de de Finetti | **réuni** |
| (ii) Algorithme identifiable et distinct du cadre de la première attestation | Composition de numérotations de portails entre zones (σ = π_AB∘π_BC∘π_CA, univalence, colle multivaluée) — mécanique de cohérence de patchwork spatial, pas une transposition de l'inclusion-exclusion des prix | **réuni** |
| (iii) Témoin **mesuré** | σ ≠ id imprimé pendant compatibilité par paires ; 0/24 exhaustif ; marche de méidentification exécutée ; réparation 24/24 + univalence assertée | **réuni** |

**Indices documentaires (non-critères, cohérents)** : Search-03b cite `Tao` ×2 et `Ruzsa` ×10 — nommer la littérature de la première attestation lorsqu'on mesure la dette Ruzsa en comparaison est l'honnêteté du carnet, pas un défaut d'indépendance (même statut que GT-19 citant Kroer-Sandholm en A10 ; le Correctif A7 interdit de lire un grep négatif comme preuve, il n'érige pas le grep positif en disqualification). Le résiduel de stimulus partagé (les deux carnets op 3 existent pour témoigner de l'opération) est le même que celui jugé non disqualifiant pour l'op 2 en A10 et l'op 6 en A8.

## Statuation — Opération 3 « Quotienter/fibrer » : PROMUE TABLE

**Attestation 1** — `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE/ANALYSE-04-PFR-Primitives-Python.ipynb` (primitives PFR, miroir Python de Lean-21b ; PR #12252, 2026-08-22, exécutée intégralement : aucune cellule à `execution_count` null, aucune erreur) : distance de Ruzsa `d[X;Y] = H(X−Y) − ½·(H(X)+H(Y))` exécutable avec tests de limite — translation `d = 0`, cas dégénéré `d = 1.5`, dépendance à la loi de groupe mesurée (Z/4Z vs Klein : `0.5` vs `0.0` sur mêmes distributions), inégalité triangulaire avec égalité exacte et saturation sans colinéarité (cell. 2, 4, 7).

**Attestation 2** — `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03b-PatternDatabases.ipynb` (quotient d'occupation du puzzle glissant ; PR #19109 livrée en 03g puis fondue dans 03b, mergée le 05/10, exécutée intégralement : aucune cellule à `execution_count` null, aucune erreur) : règle de chaîne `H(X) = H(S_B) + H(X|S_B)` à `15.8842 = 6.3923 + 9.4919` (1.8e-15), témoin `I(X_A;X_B | S_B) = 0` exact contre `2.070389` marginaux, contre-témoin `1.582975` hiérarchisé, dette Ruzsa `81/81` structure vs `80/84` contingence. **Origine documentairement établie** sur les trois axes ci-dessus.

**Condition de rétrogradation** (exécutable, falsifiable, sans critère d'omission) :

- **(a) Violation mesurée du témoin** : une re-exécution de Search-03b (ou d'un carnet jumeau sur un autre terrain) où `I(X_A;X_B | S_B) > 0` sous le quotient d'occupation — le quotient cesserait d'expliquer toute l'interaction d'exclusion, et c'est le témoin nul qui a porté la promotion qui tomberait. *Exécutable : re-exécuter le carnet en cherchant un terrain dont l'interaction d'exclusion ne se factorise pas par l'occupation.*
- **(b) Perte d'un témoin** : retrait du dépôt, effondrement de sortie (ratchet collapse) ou `sorry`-ification d'ANALYSE-04 ou de Search-03b — l'admission retombe à une attestation et l'op 3 repart en file d'attente, au mécanisme §1 du body.

**Ni l'apparition ni la disparition d'une citation bibliographique** dans l'un des carnets n'est une condition (Correctif A7).

## Statuation — Opération 5 « Recoller » : PROMUE TABLE

**Attestation 1** — `MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean/Coherence/DutchBook.lean` (+ `Coherence/Basic.lean`, issue #4050, Lean-formel, 0 `sorry`) : direction constructive du théorème de cohérence de de Finetti — si les prix violent l'inclusion-exclusion (`δ = q(A∪B) + q(A∩B) − q(A) − q(B) ≠ 0`), un Dutch Book explicite existe (mises `(1, 1, −1, −1)`, perte δ indépendante de l'état) ; la cohérence locale des prix force le recollement en une mesure additive. La réciproque (séparation d'hyperplans) est documentée **ouverte** dans l'en-tête du fichier — cadrage honnête, non `sorry`-backed.

**Attestation 2** — `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03f-Reparer-Localement-Sous-Garantie-Python.ipynb` (composition de numérotations de portails entre zones ; PR #19112 livrée en 03h puis fondue dans 03f, mergée le 05/10, exécutée intégralement : aucune cellule à `execution_count` null, aucune erreur) : compatibilité par paires (contrat faible) vérifiée pendant que σ = ((3,4) (3,6)) ≠ id ; non-recollabilité exhaustive 0/24 ; colle multivaluée (1 vs 3) ; témoin exploitable Loi I (méidentification marchée, but traversé au pas 1) ; réparation mesurée (bijection, σ = id, 24/24, univalence assertée, exactitude BFS). **Origine documentairement établie** sur les trois axes ci-dessus (lignée LPA*/Koenig).

**Condition de rétrogradation** :

- **(a) Violation mesurée de la garantie de recollement** : une re-exécution de Search-03f (ou d'un jumeau sur autre terrain) où soit la réparation échoue à ses propres assertions (24/24 → N < 24, univalence rompue — la colle réparée ne recolle pas), soit la composition σ devient l'identité **sans** réparation sur le banc incompatible (0/24 → N > 0 recollables — le contre-exemple qui porte la loi cesserait d'en être un). *Exécutable : re-exécuter le carnet sur des terrains à triple chevauchement plus denses.*
- **(b) Perte d'un témoin** : retrait, `sorry`-ification ou régression de preuve de `DutchBook.lean`/`Basic.lean`, ou ratchet collapse de Search-03f — retour en file d'attente au mécanisme §1.

## Non-attestation examinée et non comptée

`MyIA.AI.Notebooks/Probas/Applications/Quotients-Fibres-Recollement-Python.ipynb` (titre repéré par grep ce cycle — vocabulaire op 3/op 5 complet, garde-fou Ruzsa) a été mesuré avant tout décompte : son Temps 4 (« Composer deux transports et mesurer l'écart », l'opération op 5) rend la sortie **« Temps 4 NON TENTE : Q non operationnel au temps 3 »** — le critère de Finetti n'est pas atteint au niveau de finesse 1D, et l'Exercice 3 qui construirait le cas atteignable est un **stub étudiant** (« Exercice 3 a completer »). Son quotient (Temps 3) échoue de même. Ce carnet atteste la **mesure honnête d'un échec** (biais plug-in de l'information mutuelle, #23064/#23559) — même famille de statut qu'Infer-20 pour l'op 3 : examiné, mesuré, **non compté**. Il ne pèse ni pour ni contre les promotions ci-dessus.

## Dossier « réviser une croyance » — annotation fausse à sa naissance ; deux attestations mesurées, admission proposée (décision ai-01)

La file d'attente du body porte l'annotation « Tweety, non branché » depuis A6 (2026-09-27). **Première version de ce ledger (02/11) : elle était tenue pour exacte à sa date, sur la mesure « aucun carnet Tweety de révision sur `main` ». Cette mesure était FAUSSE** — corrigée le 04/11 sur signalement du dossier d'adjoint (c.6618976519, myia-po-2025:CoursIA-2) : le grep A11 avait raté la série. `Tweety-04-Belief-Revision-Python.ipynb` existe depuis le **2026-01-21** (`c88b4230aa`), son jumeau `Tweety-04-Belief-Revision-CSharp.ipynb` depuis le **2026-07-02** (`e33b7c2e37`, #4984, « AGM belief revision .NET native (IKVM) ») — tous deux **antérieurs à A6**, donc l'annotation était fausse dès sa naissance, et l'audit-froid (2026-08-24) les avait tout autant manqués.

**Mesure firsthand du Tweety-04 (04/11, `main` courant)** — Python : `execution_count` non nul sur toutes les cellules code, 0 erreur ; cell. 6 (`278b5928`) imports CrMas vérifiés (`CrMasSimpleRevisionOperator`, `CrMasArgumentativeRevisionOperator`, `LeviMultipleBaseRevisionOperator`, `KernelContractionOperator`, `RandomIncisionFunction`) ; cell. 10 (`1c9fda5e`) **révision réellement exécutée** sur base contradictoire `{A2:q, A3:!q, A1:p, A3:!r, A2:(p=>r)}` avec nouvelles infos `{!p (A2), s (A3)}` : opérateur **Levi** → `[A2:!p, A3:s, A2:q, A1:p, A3:!r]` (la newinfo entre, la croyance de l'agent le plus credible est rétablie), **Simple** → base inchangée (refus), **Argumentatif** → résultat committé. Jumeau CSharp : toutes les cellules exécutées, résultats Levi committés ; son incision « aléatoire » mesurée fausse + 2 erreurs théoriques ont été **corrigées et re-exécutées** le 30/10 (#22971).

**Mesure firsthand de ce cycle** — `GameTheory-13e-Revision-Croyances-Adversaire-Python.ipynb` (exécutée intégralement : aucune cellule à `execution_count` null, aucune erreur) : banc AGM complet — énumération des noyaux d'une base de croyances avec contrôle croisé Z3 (`assert_and_track`, core = noyau, cell. 11), incision sous ordre d'enracinement **mesuré** (valeur prédictive des atomes sur histoire tenue à part), révision B * φ, contrôles négatifs (évidence cohérente → expansion pure), **témoin** : 200 tours contre le vrai type t8 — `revise : +450.0`, `reset : −15.0`, `refus : −765.0` (le changement d'avis minimal vaut +465, le refus d'évidence coûte 1215, cell. 20), et **batterie** : 20 bases aléatoires, 7 postulats AGM (succès, inclusion, vacuité, cohérence, extensionnalité, sous-expansion, super-expansion) **20/20 chacun** (cell. 23).

**Statuation corrigée (04/11)** : l'opération `réviser une croyance` porte désormais **deux attestations** mesurées firsthand — **Tweety-04** (1re chronologiquement, depuis 01/21 : substrat JVM/Tweety CrMas, révision multi-agents à ordre de crédibilité, opérateurs Levi/Simple/Argumentatif exécutés) et **GT-13e** (#20215, 10/10 : substrat Python/GameTheory, AGM par noyaux et incision sous enracinement mesuré, batterie 7 postulats 20/20 — mesure du § précédent, inchangée). Les deux substrats sont **distincts** (crédibilité multi-agents vs postulats AGM), l'indépendance des attestations est réelle. **Condition de rétrogradation proposée** : (a) une re-exécution où les opérateurs Tweety-04 divergent des sorties committées (imports CrMas cassés, résultats Levi/Simple/Argumentatif non reproduits) ou où la batterie AGM de GT-13e tombe sous 20/20 ; (b) perte d'un des deux témoins (retrait ou sorry-ification de Tweety-04 ou de GT-13e). **L'entrée en TABLE est proposée à la décision du coordinateur** — l'existence des deux témoins ne vaut pas admission automatique (dossier d'adjoint c.6618976519) : l'évaluation contre le contrat est faite ci-dessus, la promotion reste un acte ai-01. Jusqu'à décision, l'opération reste listée en FILE D'ATTENTE avec l'annotation : *« deux attestations mesurées (Tweety-04, GT-13e) ; admission proposée — décision coordinateur »*.

## État de la table après A11

- **TABLE (15 entrées)** : ops **1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14** + `point fixe`.
- **FILE D'ATTENTE** : `institutionnaliser` (DAO seulement) · `inhiber` (pas de banc) · `réviser une croyance` (deux attestations mesurées : Tweety-04 + GT-13e ; admission proposée — décision coordinateur, correction du 04/11).

La table numérotée du premier jet (§2 du body) est complète **et entièrement instruite** : les dix opérations d'origine sont toutes en TABLE, aucune ne reste en instruction ailleurs. Les trois entrées restantes de la file sont des opérations non numérotées du premier jet, dont une désormais dotée de **deux** attestations en attente de la décision d'admission.

## Ce que cette tranche ne fait pas

- Elle ne modifie **ni** le ledger A10 **ni** les ledgers A2-A9 ni la table maîtresse labellisée ([audit-froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md)) : les promotions vivent dans ce ledger, le body de l'EPIC en rend compte.
- Elle **ne statue pas** sur `institutionnaliser` ni `inhiber` (aucune attestation nouvelle mesurée ce cycle) ni sur la **Loi I** de la section 3 du body, dont le décompte d'attestations (de Finetti + lecture Brown-Sandholm requalifiée en Tombée 3) serait à reprendre séparément si le corps des lois doit être resynchronisé — la marche de méidentification de Search-03f y est un **témoin exploitable supplémentaire**, cité par la livraison #19112, mais cette resynchronisation n'est pas un effet automatique de la statuation op 5.
- Elle n'étend pas les conditions de rétrogradation aux 13 entrées existantes : celles d'[A8](12204-ict-chantier-1-a8.md) restent la référence ; les conditions ci-dessus équipent **les deux entrées nouvelles**.
- Elle ne compte pas le carnet Probas `Quotients-Fibres-Recollement` comme attestation (motif mesuré ci-dessus).

## Effet demandé sur le body de l'EPIC

1. Case **A11** dans la liste des grains §4 (format des cases A2-A10).
2. Mise à jour de l'état de la table : ops 3 et 5 : file d'attente → **TABLE** ; la file d'attente se réduit aux trois entrées non numérotées.
3. Annotation de `réviser une croyance` remplacée (« Tweety, non branché » → « deux attestations mesurées (Tweety-04, GT-13e) ; admission proposée — décision coordinateur »).
4. Renvois au présent ledger pour les deux conditions de rétrogradation.

## Références

- Livraisons des secondes attestations : [#19109 [DELIVERED] op 3, c.5980587552](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-5980587552) et [#19112 [DELIVERED] op 5, c.5981067379](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-5981067379) — commentaires du 04/10.
- Arbitrage coordinateur (format d'admission à trois champs) : [issuecomment-6179879158](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6179879158)
- Voie de promotion refondée sur l'origine : [A7 §Correctif du 2026-10-21](12204-ict-chantier-1-a7.md#correctif-du-2026-10-21--la-preuve-dindépendance-requalifiée-revue-externe-dispatch-ai-01)
- Conditions de rétrogradation : [A8](12204-ict-chantier-1-a8.md) · Statuation op 2 (précédent de forme) : [A10](12204-ict-chantier-1-a10.md)
- Premières attestations : ANALYSE-04/#12252 (op 3, Tombée 4 de l'audit-froid) · `decision_theory_lean/Coherence/DutchBook.lean`/#4050 (op 5, Tombée 3)
- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · claim de tranche : c.6565508951 (02/11)
