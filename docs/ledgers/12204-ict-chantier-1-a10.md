# Chantier 1 — tranche A10 : statuation de la promotion op 2 « Abstraire à dette bornée » au format admission

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2027:CoursIA` · **date de mesure** 2026-10-23
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (op 1) · [A3](12204-ict-chantier-1-a3.md) (ops 3, 9) · [A4](12204-ict-chantier-1-a4.md) (op 4) · [A5](12204-ict-chantier-1-a5.md) (ops 2, 6, 10) · [A6](12204-ict-chantier-1-a6.md) (statuation 11-13 + file d'attente) · [A7](12204-ict-chantier-1-a7.md) (statuations ops 2, 6, quatrième loi + Correctif du 2026-10-21) · [A8](12204-ict-chantier-1-a8.md) (conditions de rétrogradation) · [A9](12204-ict-chantier-1-a9.md) (seconde attestation op 2, dossier de promotion)

## Ce que cette tranche fait

A9 avait laissé l'op 2 en FILE D'ATTENTE avec verdict **promotion PROPOSÉE** et la statuation formelle « revient à la relecture du chantier » — geste conditionné par le bloc d'état du 2026-10-22 au merge de #21861 (Correctif A7 inclus), aujourd'hui mergée. Cette tranche est cette relecture : elle pèse le dossier A9 sur la voie **refondée sur l'origine** (Correctif A7), re-mesure les deux témoins firsthand, et statue au format d'admission à trois champs fixé par l'arbitrage du 2026-10-14 et [A8](12204-ict-chantier-1-a8.md) : **deux attestations + condition de rétrogradation**.

## Re-mesures firsthand de ce cycle

Une statuation ne s'appuie pas sur la mesure d'un autre sans relire (G.1). Toutes les mesures ci-dessous sont exécutées ce jour sur `origin/main` (`73d951e5648e`), lecture JSON des carnets committés.

**État d'exécution** :

| Témoin | Cellules code | `execution_count` null | Erreurs |
|---|---|---|---|
| `GameTheory-19-Abstraction-a-Dette-Python.ipynb` | 7 | 0 | 0 |
| `Search/Part5-Frontieres/Frontieres-11-Abstraction-Dette-ShortestPath-Python.ipynb` | 12 | 0 | 0 |

**L'origine pesée sur les trois éléments du Correctif A7** (le contraste de grep n'est pas un critère — il est cité ci-dessous comme indice documentaire, avec les chiffres du jour) :

| Axe | Mesure firsthand (2026-10-23) | Verdict |
|---|---|---|
| (i) Littérature propre citée | Frontieres-11 : `Culberson` ×2, `Holte` ×3, « pattern database » ×2 (lignée Culberson & Schaeffer 1998 / Holte et al. 2005, distincte de la littérature jeux) | **réuni** |
| (ii) Algorithme identifiable et distinct du cadre Kroer-Sandholm | Frontieres-11 : bornage **admissible** par partition en provinces k (`admissible` ×9 dans le carnet), agrégation min des traversées — machinerie pattern-databases, pas une transposition de la fusion d'états jeux de GT-19 | **réuni** |
| (iii) Perte bornée **mesurée** | Lignes imprimées du carnet exécuté : « Borne min (k=6), 200 requetes longues : 0 violation(s) » + « 200 requetes courtes : 0 violation(s) » (= **0/400** contre l'oracle Dijkstra) ; contre-témoin « Borne moyenne (k=3), 200 requetes courtes : **5 violation(s)** » ; « Bracket certifie sans oracle : [39.0, 138] -- l'optimum (130) doit y vivre » ; « Dette : releve 138 - optimum 130 = **8** » | **réuni** |

**Indice documentaire (non-critère, cohérent)** : `Sandholm` ×14 + `Kroer` ×9 dans GT-19 (le premier témoin **cite** son cadre — c'est son honnêteté, pas un défaut) contre 0 + 0 dans Frontieres-11. Mesure du jour, supérieure au « 5 occurrences » relaté par A9 (qui comptait plus étroitement) ; le sens du contraste est inchangé.

**Première attestation re-lue** (GT-19, livrée par A5/#18118) : « Exploitabilite = 1.9091 > 0 : la strategie retransportee n'est PAS un equilibre de G » (la dette rendue **visible et chiffrée**), chaîne « P6 raffine P4 : OK » / « P3 raffine P2 : OK », courbe de dette imprimée « solve exact + retransport + exploitability dans G ». La loi « le relèvement transporte une garantie » y est attestée en son sens **négatif mesurable** : la garantie est un chiffre qui peut être lu, pas une allégation.

## Statuation — Opération 2 « Abstraire à dette bornée » : PROMUE TABLE

**Au format d'admission à trois champs** :

**Attestation 1** — `MyIA.AI.Notebooks/GameTheory/GameTheory-19-Abstraction-a-Dette-Python.ipynb` (jeux à somme nulle, fusion d'états ; PR #18118/A5, exécutée) : courbe de dette mesurée P6→P2, exploitabilité du retransporté chiffrée (1.9091), garantie transportée lue comme un nombre.

**Attestation 2** — `MyIA.AI.Notebooks/Search/Part5-Frontieres/Frontieres-11-Abstraction-Dette-ShortestPath-Python.ipynb` (recherche de chemin, partition en provinces k ; PR #20931/A9, exécutée) : borne admissible auditée 0/400 contre oracle, contre-témoin agrégation moyenne 5/200 courtes, bracket sans oracle [39.0, 138] contenant l'optimum 130, dette chiffrée 8. **Origine documentairement établie** sur les trois axes ci-dessus (littérature pattern databases citée, algorithme distinct, perte mesurée) — l'indépendance tient sur ces éléments positifs, conformément au Correctif A7 ; le résiduel de stimulus partagé (les deux carnets existent pour témoigner de l'op 2) est le même que celui écrit pour l'op 6, jugé alors non disqualifiant au niveau documentaire que le dépôt permet.

**Condition de rétrogradation** (exécutable, falsifiable, sans critère d'omission — la falsification pertinente est la violation de la garantie) :

- **(a) Violation mesurée de la borne** : une re-exécution de Frontieres-11 (ou un carnet jumeau sur un autre graphe) où une requête **violée** apparaît sous la borne déclarée admissible — i.e. le contre-témoin « agrégation moyenne » change de statut : ce n'est plus le contre-exemple pédagogique mais un défaut de la borne min elle-même (0/400 → N > 0 sur la même famille). Réfuterait la loi « le relèvement transporte une garantie » sur le témoin qui l'a fait entrer. *Exécutable : re-exécuter le carnet avec un graphe adversarial cherchant la requête qui ment sous la borne min.*
- **(b) Perte d'un témoin** : retrait du dépôt ou effondrement de sortie (ratchet collapse) de l'un des deux carnets — l'admission retombe à une seule attestation et l'op 2 repart en file d'attente, au mécanisme §1 du body.

**Ni l'apparition ni la disparition d'une citation bibliographique** dans l'un des carnets n'est une condition : une future mention Kroer-Sandholm dans Frontieres-11 ne changerait pas l'origine de son algorithme (Correctif A7, requalification du même geste sur l'op 6 en A8).

## État de la table après A10

- **TABLE (13 entrées)** : ops **1, 2, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14** + `point fixe`.
- **FILE D'ATTENTE** : ops 3 et 5 (secondes attestations livrées et fondues — #19109 « op 3 Quotienter/Fibrer loge dans Search-03b » et #19112 « op 5 recoller loge dans Search-03f », mergées le 05/10, [DELIVERED] c.5980587552/c.5981067379 ; carnets dédiés 03g/03h retirés au profit du logement dans 03b/03f — statuation pas encore faite) · `institutionnaliser` (DAO seulement) · `inhiber` (pas de banc) · `réviser une croyance` (Tweety, non branché).

La table numérotée est **complète pour les dix opérations du premier jet** (§2 du body) : les quatre absentes du premier jet (11-14) avaient été promues par A6, il ne manquait que l'op 2 — c'est fait. Ce qui reste en file d'attente numérotée (3, 5) sont des promotions en cours d'instruction ailleurs, pas des dossiers dormants de ce chantier.

## Ce que cette tranche ne fait pas

- Elle ne statue **ni** sur l'op 3 **ni** sur l'op 5 : leurs secondes attestations sont portées par le claim `myia-ai-01:CoursIA-2` au fil de l'EPIC (10-15) ; statuer dessus maintenant serait juger des dossiers non encore livrés.
- Elle ne modifie **pas** la table maîtresse labellisée ([audit-froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md)) ni les ledgers A2-A9 : la promotion vit dans ce ledger, le body de l'EPIC en rend compte (effet demandé ci-dessous).
- Elle n'étend **pas** la condition de rétrogradation aux 12 entrées existantes : celles d'[A8](12204-ict-chantier-1-a8.md) restent la référence ; la condition ci-dessus équipe **l'entrée nouvelle**.

## Effet demandé sur le body de l'EPIC

1. Case **A10** dans la liste des grains §4 (format des cases A2-A8).
2. Mise à jour de l'état de la table (op 2 : file d'attente → TABLE) et de la ligne file d'attente.
3. Renvoi au présent ledger pour la condition de rétrogradation de l'op 2.

## Références

- Arbitrage coordinateur (format d'admission à trois champs) : [issuecomment-6179879158](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6179879158)
- Voie de promotion refondée sur l'origine : [A7 §Correctif du 2026-10-21](12204-ict-chantier-1-a7.md#correctif-du-2026-10-21--la-preuve-dindépendance-requalifiée-revue-externe-dispatch-ai-01)
- Dossier de promotion : [A9](12204-ict-chantier-1-a9.md) · Conditions de rétrogradation : [A8](12204-ict-chantier-1-a8.md)
- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · claim de tranche : [issuecomment-6375401202](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6375401202)
