# Ledger de l'acceptance 2 de l'EPIC #16473

> **Suivi des rattachements nominatifs** demandés par l'acceptance 2 du corps de l'EPIC #16473 (« Consolidation globale du dépôt — parapluie anti-entropie, axes A-F »).
>
> **Acceptance 2 (verbatim)** : « chaque sous-grain listé en §A-F reçoit, dans les 14 jours suivant la création de cette Epic, soit (a) un `Part of #<chapeau>` + une inscription dans le body chapeau, soit (b) un refus motivé par écrit. Aucune issue A-F ne reste orpheline sans justification écrite. »
>
> **Origine** : `scripts/audit_consolidation_orphans.py --fetch` (organe livré par PR #16504, MERGED 2026-09-17). **Mesure live 2026-10-05** : 399 scannées / 29 rattachées / 370 orphelines.
>
> **Lane d'origine** : **myia-po-2024:CoursIA-2** — claim initial `c.5988917609` (1320 chars) + claim suivi `c.5988930369` (2579 chars), tous deux OK longueur/PAYLOAD-TRAP.

## Convention d'écriture

Chaque ligne suit le format (TSV avec tabs comme séparateurs) :

```text
date_cycle<TAB>#issue<TAB>chaperon_proposé<TAB>axe<TAB>statut<TAB>preuve<TAB>note
```

- **date_cycle** : ISO 8601 UTC (`YYYY-MM-DDTHH:MMZ`)
- **#issue** : numéro GitHub
- **chaperon_proposé** : `#5081` (renum), `#4362` (Lean), `#13737` (structurel), `#9535` (ménage), `#16473` (parapluie), ou `REFUS_MOTIVÉ` si refus
- **axe** : `A`/`B`/`C`/`D`/`E`/`F` selon l'EPIC
- **statut** : `PROPOSÉ` (à commenter), `COMMENTÉ` (commentaire `Part of #X` posté sur l'issue), `REFUSÉ` (refus motivé posté), `REJETÉ_PAR_PORTEUR` (le porteur a contesté le rattachement)
- **preuve** : URL du commentaire ou de la PR, ou note de cycle
- **note** : rationale du rattachement, contexte

## Lots

### Lot 1 — axe B (doublons/jumeaux/consolidation notebooks), 56 orphelines

Mesure 2026-10-05 : 56 orphelines sur l'axe B (vs 64 hier 2026-10-04 — régression de 8 unités sur 24h, à monitorer).

**11 cibles prioritaires identifiées** dans le claim suivi `c.5988930369` :
- doublons détectés par ratchets CI : #16121, #16040, #16111, #15962, #14624, #18039
- jumeaux/collisions : #18725 (claim ma lane), #18683 (claim ai-01), #19116 (claim ai-01), #18646 (ouvert à chacune)
- nomenclature : #16231 (claim multi-lane, chantier C ma lane)

**Stratégie de commentaire** : commentaire `Part of #13737` (chaperon structurel) sur les orphelines SANS claim actif, **pas d'immixtion** dans celles avec claim tiers. Le coordinateur tranche en cas de désaccord.

#### Sous-lot 1.1 — orphelines sans claim tiers (à commenter)

L'audit 2026-10-05T05:50Z liste 56 orphelines axe B ; la plupart portent un claim tiers actif (po-2024, po-2026, po-2027, po-2023, ai-01). Les commentaires `Part of #<chaperon>` posés par ma lane seraient **des immixtions** dans le périmètre d'autres lanes — la règle R0 de coordination (cf `CLAUDE.md` §A) demande de **demander, pas appliquer** quand un geste touche le périmètre d'une autre lane.

**Décision** : pour ce cycle, **pas de commentaire nominatif direct** sur les orphelines à claim tiers. Préparer un dossier de proposition que l'adversaire (po-2025:CoursIA adjoint) et le coordinateur (ai-01) tranchent. Les commentaires nominatifs seront posés **après validation de l'adversaire/coordinateur**, ou par les porteurs eux-mêmes.

#### Statut émission commentaires nominatifs

```text
date_cycle | #issue | chaperon | axe | statut | preuve | note
2026-10-05T06:00Z | #16473 | #16473 | B | PROPOSÉ | c.5988917609 + c.5988930369 | Claim initial + suivi postés sur l'EPIC parapluie. Aucun commentaire nominatif émis sur les sous-grains axe B ce cycle (immixtion). Stratégie validée par coordination avec adjoint à venir.
2026-10-05T06:10Z | PR#19232 | — | B | OUVERT | https://github.com/jsboige/CoursIA/pull/19232 | Ledger de suivi acceptance 2 lot 1 (axe B) — ouvert par ma lane pour matérialiser la stratégie sans commentaires nominatifs. À reviewer par l'adjoint (po-2025:CoursIA) et le coordinateur (ai-01) avant émission des commentaires sur les sous-grains à claim tiers.
```

### Lots 2-5 — axes A, C, D, E, F

À servir aux cycles suivants, dans l'ordre dedie par l'adversaire/coordinateur après livraison du lot 1.

## Suites à donner

1. **Cycle prochain** : créer un sous-grain concret dans `scripts/audit_consolidation_orphans.py` (extension `--suggest-rattachement` qui propose automatiquement un chaperon par heuristique : mots-clés `lean|mathlib` → #4362, `renum|nommage|kernel` → #5081, `doublon|twin|duplicate|collision` → #13737, `arch|ménage|nettoyage` → #9535, `consolidation|parapluie|entropie` → #16473). PR séparée.
2. **Après cette PR** : commentaires nominatifs émis par les porteurs eux-mêmes, ou par l'adversaire après validation — pas par ma lane en mode worker.
3. **Liaison #13906** : tracker l'organe `scripts/epic_body_staleness.py` ; réécrire ce ledger à chaque livraison de l'organe (cf EPIC #16473 §F).

## Références

- EPIC #16473 — body chapeau : https://github.com/jsboige/CoursIA/issues/16473
- Claim initial : c.5988917609 (1320 chars)
- Claim suivi : c.5988930369 (2579 chars)
- PR organe : #16504 (MERGED 2026-09-17)
- Audit dernier : `python scripts/audit_consolidation_orphans.py --fetch` au 2026-10-05T05:4xZ → 399/29/370

---

Co-Authored-By: Claude Haiku 4.5 (1M context) <noreply@anthropic.com>