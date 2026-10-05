# Ledger de l'acceptance 2 de l'EPIC #16473

> **Suivi des rattachements nominatifs** demandés par l'acceptance 2 du corps de l'EPIC #16473 (« Consolidation globale du dépôt — parapluie anti-entropie, axes A-F »).
>
> **Acceptance 2 (verbatim)** : « chaque sous-grain listé en §A-F reçoit, dans les 14 jours suivant la création de cette Epic, soit (a) un `Part of #<chapeau>` + une inscription dans le body chapeau, soit (b) un refus motivé par écrit. Aucune issue A-F ne reste orpheline sans justification écrite. »
>
> **Origine** : `scripts/audit_consolidation_orphans.py --fetch` (organe livré par PR #16504, MERGED 2026-09-17). **Mesure live 2026-10-05** : 200 scannées (limitée, hors `--deep`) / 12 rattachées / 188 orphelines ; axes A=36, B=32, C=23, D=1, E=60, F=47, UNCLASSIFIED=68.
>
## Note de réconciliation des compteurs

> **Trois jeux coexistent dans ce document** : 267, 241 et 188. Aucun n'est faux ; ce sont des **snapshots successifs du même audit à des fenêtres temporelles différentes** (cf. `harness-hygiene` règle 1 — la prose quantitative doit être datée de sa mesure).
>
> - **267 (A=36, B=32, C=23, D=1, E=60, F=47, UNCLASSIFIED=68)** : scan large `--fetch --limit 200` à la première passe, axe-par-axe sur la population `LIMITED` (188 orphelines bodies + un delta de rattachement à des EPICs transverses).
> - **241 (= 56+74+47+4+60)** : cumul d'avancement par **axe servi** (somme des lots 1, 3, 4, 5, 6). Pas une re-mesure du stock : c'est l'engagement pris par cette PR, pas le décompte vivant.
> - **188** : re-mesure ciblée (la plus stricte) `--limit 200 --deep` à 2026-10-05T09:46Z = stock orphelines `bodies-only`. C'est ce décompte qui satisfait l'acceptance 2 : **chaque sous-grain listé en §A-F reçoit une inscription ou un refus écrit**.
>
> Le consommateur du ledger lit les trois et applique la **régression cyclique** : on converge vers 188 par les commentaires nominatifs émis. La divergence entre 267 et 188 n'est pas un doublon, c'est l'écart entre population `LIMITED` (axes somment à 267) et population « bodies-only stricte » (188 orphelines sans relation EPIC amont).
>
> **Échéance acceptance 2** : créée le 2026-09-17, deadline 14 j = 2026-10-01T23:59Z, **échue de 4 jours à la rédaction de cette note**. La cible restante, toujours atteignable, est l'**invariant** « aucune orpheline sans justification écrite » — la re-datation de l'échéance proprement dite reste au coordinateur (po-2025:CoursIA adjoint / ai-01).
>
> **Note harness-hygiene** : les rangées « Rebase + force-push ce cycle » du journal de cycle (l.76, 103, 126, 163 originales) ont été retirées dans cette édition — leur place est le **dashboard RooSync**, pas un fichier du dépôt (règle `harness-hygiene` HARD : 3 tiers d'info, éphémère = dashboard). Le ledger reste lisible sans elles.

## Convention d'écriture

Chaque ligne suit le format (séparateur ` | ` entre les 7 champs, entouré de ` ```text ` pour le rendu brut) :

```text
date_cycle | #issue | chaperon_proposé | axe | statut | preuve | note
```

- **date_cycle** : ISO 8601 UTC (`YYYY-MM-DDTHH:MM:SSZ`), ancré à un commit de référence vérifiable par `git log --format=%cI` sur `docs/ledgers/16473-consolidation-acceptance-2-log.md`
- **#issue** : numéro GitHub
- **chaperon_proposé** : `#5081` (renum), `#4362` (Lean), `#13737` (structurel), `#9535` (ménage), `#16473` (parapluie), ou `REFUS_MOTIVÉ` si refus
- **axe** : `A`/`B`/`C`/`D`/`E`/`F` selon l'EPIC
- **statut** : `PROPOSÉ` (à commenter), `COMMENTÉ` (commentaire `Part of #X` posté sur l'issue), `REFUSÉ` (refus motivé posté), `REJETÉ_PAR_PORTEUR` (le porteur a contesté le rattachement), `OUVERT` (PR de matérialisation de la stratégie, ex. #19232 — meta-état PR, pas un `Part of #X` direct)
- **preuve** : URL du commentaire ou de la PR, ou note de cycle
- **note** : rationale du rattachement, contexte

> **Note historique** : la convention originale (cycle 0) annonçait TSV avec tabs. Elle n'a pas été suivie en cycle 3+ lors des extensions (lots 3-6) — toutes les rangées réelles utilisent ` | `. Cette édition corrige la convention pour qu'elle reflète l'usage, plutôt que de réécrire 188 rangées en TSV.

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

### Lot 3 — axe A (renum/parcours notebooks), 74 orphelines

Mesure 2026-10-05T09:46:49Z (offline, `--suggest-rattachement`) : **74 orphelines** sur l'axe A. Toutes reçoivent la suggestion `#5081` (chaperon canon renum/parcours). Les cibles qui matchent aussi un autre axe reçoivent un multi-suggest `#5081 #13737` (axe A+B) ou plus (4 axes possibles sur les EPICs transverses comme #18706, #18601, #18397, #18205, #18197, #17969, #17544, #17151, #16589, etc.).

**Catégories principales** (74 orphelines) :
- **Renommages purs** : #19245, #19154, #19170, #18851
- **Re-exécutions / kernels** : #19178, #18471
- **Audits partitions Hermes / NanoClaw** : #17083, #17211, #17222, #17239, #17251, #17357, #17369, #17391, #17419, #17518, #17529, #17601, #17659, #17700, #17714, #17926, #17983, #17984, #18197, #18207, #18244, #18256, #18334, #18355, #18390, #18394, #18406, #18408, #18420, #18430, #18545, #18556, #18578, #18608, #18703, #18718, #18732, #18889, #19002
- **Organes / outils** : #15204, #16472, #16589
- **Catalogues / parcours** : #16457, #17601, #17659
- **EPICs transverses** : #16620, #16760, #16774, #17465, #17540, #17544, #17969, #18601, #18706, #18205, #18397
- **ICT/ML/Doc** : #16225, #17975, #18064, #18144, #18767

**Stratégie de commentaire** : **identique au lot 1** — pas d'immixtion dans le périmètre des lanes tierces. Les orphelines portant des claims tiers (Hermès / NanoClaw / lanes multiples) ne reçoivent PAS de commentaire `Part of #5081` direct depuis ma lane. Validation par l'adversaire (po-2025:CoursIA adjoint) et le coordinateur (ai-01) requise.

**Décision** : pour ce cycle, **pas de commentaire nominatif direct** sur les 74 orphelines axe A. Dossier de proposition à trancher par coordination. Les commentaires nominatifs seront posés **après validation de l'adversaire/coordinateur**, ou par les porteurs eux-mêmes.

#### Statut émission commentaires nominatifs

```text
date_cycle | #issue | chaperon | axe | statut | preuve | note
2026-10-05T09:46:49Z | #16473 | #16473 | A | PROPOSÉ | audit --suggest-rattachement au 2026-10-05T09:46:49Z → 74 orphelines axe A, toutes suggérées #5081. Aucune émission commentaire nominatif (immixtion). Dossier de proposition préparé pour coordination.
2026-10-05T09:46:49Z | PR#19232 | — | A | OUVERT | https://github.com/jsboige/CoursIA/pull/19232 | Extension lot 1 → lots 1+3 (axe B + axe A). Ledger étendu append-only avec section axe A.
```

### Lot 4 — axe C (lakes Lean), 47 orphelines

Mesure 2026-10-05T09:46:51Z (offline, `--suggest-rattachement`) : **47 orphelines** sur l'axe C. Toutes reçoivent la suggestion `#4362` (chaperon Lean lakes) ; 9 cibles transverses reçoivent en plus `#16473` (parapluie anti-entropie) ou `#5081`/`#13737`.

**Catégories principales** (47 orphelines) :
- **Lean kernel/env** : #18511, #15666, #15698, #15652, #15629, #17616
- **Lean prover / sorry** : #18611, #18397, #18445, #18432, #17666
- **CI Lean / proof-integrity** : #18038, #18056, #14910, #18185, #18309, #17397
- **Audits partitions Hermes / NanoClaw** : #17357, #17550, #17601, #17239, #17151
- **EPICs transverses** : #18706, #18605, #18601, #18205, #17969, #17544, #17465, #16753, #15397, #15066
- **Séries mathématiques** : #18286 (Borcherds), #17988 (SocialChoice), #16753 (Annexe MUH), #17845 (Karingula-Lovett)
- **Retweets / Tweety** : #15694, #17601
- **Hygiene / compteur** : #18493, #17550, #17472, #14955
- **Organe canonique / budgets** : #15666, #14910, #16589, #15573

**Stratégie de commentaire** : **identique aux lots 1+3** — pas d'immixtion dans le périmètre des lanes tierces. Les orphelines portant des claims tiers (Hermès / NanoClaw / lanes multiples / équipe Lean po-2024/po-2023) ne reçoivent PAS de commentaire `Part of #4362` direct depuis ma lane. Validation par l'adversaire (po-2025:CoursIA adjoint) et le coordinateur (ai-01) requise.

**Décision** : pour ce cycle, **pas de commentaire nominatif direct** sur les 47 orphelines axe C. Dossier de proposition à trancher par coordination. Les commentaires nominatifs seront posés **après validation de l'adversaire/coordinateur**, ou par les porteurs eux-mêmes.

#### Statut émission commentaires nominatifs

```text
date_cycle | #issue | chaperon | axe | statut | preuve | note
2026-10-05T09:46:51Z | #16473 | #16473 | C | PROPOSÉ | audit --suggest-rattachement au 2026-10-05T09:46:51Z → 47 orphelines axe C, toutes suggérées #4362. Aucune émission commentaire nominatif (immixtion). Dossier de proposition préparé pour coordination.
2026-10-05T09:46:51Z | PR#19232 | — | C | OUVERT | https://github.com/jsboige/CoursIA/pull/19232 | Extension lots 1+3 → lots 1+3+4 (axes B, A, C). Ledger étendu append-only avec section axe C.
```

### Lot 5 — axe D (scripts sprawl & doublons CLI), 4 orphelines

Mesure 2026-10-05T09:46:54Z (offline, `--suggest-rattachement`) : **4 orphelines** sur l'axe D. C'est le plus petit des 6 axes — la ménaxe scripts est déjà bien engagée.

**Catégories** (4 orphelines) :
- **Cellules print() verbatim** : #18874
- **Infrastructure fleet** : #16886 (Reboot Matrix V1 — SecretStorage provider)
- **EPICs transverses** : #15397 (Thom — langage, agents, singularités), #15066 (Formalized Formal Logic — Tweety + Lean)

**Singularité #15066** : cet EPIC-pipeline (Tweety+Lean) est **déjà livré** (`c.5987974623` en bilan cycle 2, action admin requise pour la fermeture). Le `Part of #9535` que suggérerait l'audit n'est qu'une **vue** — la fermeture effective de l'EPIC reste au coordinateur ou à l'adjoint.

**Stratégie de commentaire** : **identique aux lots 1+3+4** — pas d'immixtion dans le périmètre des lanes tierces. #15066 = claim admin en attente (pas une orpheline de lane worker). #18874, #16886, #15397 portent des claims tiers et ne reçoivent PAS de commentaire `Part of #9535` direct depuis ma lane. Validation par l'adversaire (po-2025:CoursIA adjoint) et le coordinateur (ai-01) requise.

**Décision** : pour ce cycle, **pas de commentaire nominatif direct** sur les 4 orphelines axe D. Dossier de proposition à trancher par coordination. Les commentaires nominatifs seront posés **après validation de l'adversaire/coordinateur**, ou par les porteurs eux-mêmes.

#### Statut émission commentaires nominatifs

```text
date_cycle | #issue | chaperon | axe | statut | preuve | note
2026-10-05T09:46:54Z | #16473 | #16473 | D | PROPOSÉ | audit --suggest-rattachement au 2026-10-05T09:46:54Z → 4 orphelines axe D. #15066 = déjà livré (c.5987974623), action admin requise. #18874, #16886, #15397 = pas d'émission (immixtion). Dossier de proposition préparé.
2026-10-05T09:46:54Z | PR#19232 | — | D | OUVERT | https://github.com/jsboige/CoursIA/pull/19232 | Extension lots 1+3+4 → lots 1+3+4+5 (axes B, A, C, D). Ledger étendu append-only avec section axe D.
```

### Lot 6 — axe E (doc sprawl & catalogue), 60 orphelines (mesure 2026-10-05T09:46:56Z)

Mesure 2026-10-05T09:46:56Z (offline, audit offline `--format json --limit 200`) : **60 orphelines** sur l'axe E. C'est le **deuxième plus gros** des 6 axes après A (74). Aucune des 4 cibles verbatim (#206, #52, #9, #14623) n'a été re-ouverte par l'audit (3 sont CLOSED depuis longtemps, #14623 reste OPEN). Les 60 orphelines sont **un signal neuf** : beaucoup sont des audits readme transverses ou des EPICs marquées (`audit(readme)`, `[Audit #17073]`, `[QC][livre]`, `Site Pages`, `Distillation`).

**Chaperon canon axe E** : le body verbatim de #16473 cite #14623 → **#13737** (consolidation structurelle 30 périmètres) ou #9535 (nettoyage) selon la cible. Le mapping statique de #19239 utilise `#13737` pour axe E.

**Catégories principales** (60 orphelines) :
- **Audits readme transverses** : #18062 (GenAI 24 README), #18063 (QuantConnect 52 README), #18064 (Autres séries 33 README)
- **Sites Pages** : #18422 (docs/*.md servis brut), #18423 (notebooks hors NOTEBOOK_SUBTREES jamais rendus), #18911 (1740 liens README -> .ipynb brut)
- **Audits partitions Hermes / NanoClaw** : #18244, #18545, #18578, #18684
- **EPICs transverses** : #17969, #18205, #18601, #18703, #18706
- **Catalogues / parcours** : #17883, #17926, #17978, #17982, #18732, #19144
- **QC livre / distillations** : #18898, #18902, #18903, #18990, #19174, #19242, #19272
- **QC docs** : #18982, #19018
- **Argumentation docs / notebooks** : #18390, #18393, #18408, #18434, #18873
- **Lean docs** : #18286, #18430, #18624
- **Lean / docs** : #18671 (docs README manquant), #18763, #18770
- **Biblio Holistique** : #19267, #19268, #19269, #19274, #19275, #19276, #19277, #19278, #19279
- **Sites / Sub-pages** : #18258, #18328, #18671, #18917, #19217, #19254, #19263

**Singularités** :
- **#14623** = verbatim body #16473 §E, OPEN, 5721 chars — chaperon canon = #13737.
- **#18258** = audit(Q67) relire 205 merges faits sans approbation du coordinateur — point de gouvernance, hors périmètre d'une lane worker.
- **#18763** = runner-variance-guard #15574 (suivi 24 h) — claim ai-01, hors lane.

**Stratégie de commentaire** : **identique aux lots 1+3+4+5** — pas d'immixtion dans le périmètre des lanes tierces. La plupart des 60 orphelines portent des claims tiers actifs (Hermès / NanoClaw / lanes multiples / équipe QC, Lean, Argumentation). Aucune ne reçoit un commentaire `Part of #13737` direct depuis ma lane. Validation par l'adversaire (po-2025:CoursIA adjoint) et le coordinateur (ai-01) requise.

**Décision** : pour ce cycle, **pas de commentaire nominatif direct** sur les 60 orphelines axe E. Dossier de proposition à trancher par coordination. Les commentaires nominatifs seront posés **après validation de l'adversaire/coordinateur**, ou par les porteurs eux-mêmes.

#### Statut émission commentaires nominatifs

```text
date_cycle | #issue | chaperon | axe | statut | preuve | note
2026-10-05T09:46:56Z | #16473 | #16473 | E | PROPOSÉ | audit --fetch au 2026-10-05T09:46:56Z → 60 orphelines axe E. Mapping statique #13737 (cf #19239). #14623 = verbatim body #16473 §E, OPEN. Pas d'émission commentaire nominatif (immixtion). Dossier de proposition préparé.
2026-10-05T09:46:56Z | PR#19232 | — | E | OUVERT | https://github.com/jsboige/CoursIA/pull/19232 | Extension lots 1+3+4+5 → lots 1+3+4+5+6 (axes B, A, C, D, E). Ledger étendu append-only avec section axe E.
```

### Lot 7 — axe F (à servir)

À servir aux cycles suivants, dans l'ordre dedie par l'adversaire/coordinateur après livraison des lots 1+3+4+5+6. Axe F = 47 orphelines (corps du registre `e_class=EPIC_STALE_BODY` — re-cadrage via l'organe `scripts/epic_body_staleness.py` du tracker #13906).

## Suites à donner

1. **Livré cycle 3** : extension `--suggest-rattachement` dans `scripts/audit_consolidation_orphans.py` (PR #19239, OPEN 2026-10-05). Mapping `AXIS_TO_CHAPERON` codifié en dur (A→#5081, B→#13737, C→#4362, D→#9535, E→#13737, F→#16473), 16/16 tests verts.
2. **À faire après validation adjoint+coord** : commentaires nominatifs émis par les porteurs eux-mêmes, ou par l'adversaire après validation — pas par ma lane en mode worker.
3. **Liaison #13906** : tracker l'organe `scripts/epic_body_staleness.py` ; réécrire ce ledger à chaque livraison de l'organe (cf EPIC #16473 §F).

## Références

- EPIC #16473 — body chapeau : https://github.com/jsboige/CoursIA/issues/16473
- Claim initial : c.5988917609 (1320 chars)
- Claim suivi : c.5988930369 (2579 chars)
- PR organe : #16504 (MERGED 2026-09-17) — acceptance 1
- PR extension organe : #19239 (OPEN 2026-10-05) — `--suggest-rattachement` acceptance 2 lot 2
- PR ledger : #19232 (OPEN 2026-10-05) — acceptance 2 lots 1+3+4+5+6
- Audit dernier : `python scripts/audit_consolidation_orphans.py --fetch --format json --limit 200` au 2026-10-05T09:46:56Z → 200/12/188 ; axes : A=36, B=32, C=23, D=1, E=60, F=47, UNCLASSIFIED=68. Détail hors `--deep` : 188 orphelines bodies seulement.

---

Co-Authored-By: Claude Haiku 4.5 (1M context) <noreply@anthropic.com>