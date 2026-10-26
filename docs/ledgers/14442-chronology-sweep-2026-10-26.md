# Sweep — chronologie de livraison Git dans les carnets GameTheory (issue #14442)

**Date** : 2026-10-26 · **Lane** : myia-po-2028:CoursIA-2 · **Organe** : `scripts/notebook_tools/audit_workflow_chronology.py`

## Ce que ce ledger documente

L'issue #14442 (défaut 3) demande que le **sweep** des introductions et conclusions de
carnets GameTheory qui justifient leur contenu par la **chronologie de livraison** Git
(renvois à un EPIC / une PR / le fait d'avoir été « livré ») soit **documenté avec une
classification contextuelle et les cas analogues nommés**. Ce ledger est ce document.

Il ne supprime rien : il **mesure**, **classe** et **nomme**. La dé-chronologisation
elle-même est livrée **carnet par carnet** (un PR par tranche) ; la PR associée à ce ledger
livre la première — GT-20, le reliquat nommé par le coordinateur le 25/10.

## Méthode

1. **Détection** — `audit_workflow_chronology.py` parcourt les cellules markdown de la série
   et signale chaque marqueur de chronologie de livraison, avec l'index de cellule et le
   texte matché. Marqueurs : `EPIC #N`, `PR #N`, `Issue #N`, un numéro de PR/issue en
   parenthèse `(#NNNN)`, et le past-participe « livré » accolé à un numéro / à « sur main ».
2. **Classification contextuelle** — chaque occurrence est **relue dans son contexte**
   (l'issue interdit le fix regex global) et rangée dans l'une de deux classes :

| Classe | Définition | Geste |
|---|---|---|
| **PROVENANCE_UTILE** | le numéro cite une **source** pour un fait / verdict / décision (« Verdict SOTA-OK (#10459) », « parité lib-vs-lib (issue #10382) », « prouvé dans PR #1320 »). Il nomme *d'où vient* l'information. | **conserver** — le retirer perdrait la provenance |
| **CHRONOLOGIE_GIT_A_RETIRER** | le numéro / le « livré » justifie **l'existence / la livraison** du contenu (« Carnet livré par l'issue #20379 », « livré sur main par #13350, commit … », « DISPATCH ai-01, PR #15175, MERGED <ts> »). Il raconte *quand / comment c'est été construit*. | **retirer / reformuler** — ce récit vit dans git, les PR et les issues, pas dans le carnet |

Un pointeur de carnet **sans** numéro (« voir GT-3b », « les murs de GT-3b ») n'est **pas**
signalé : c'est un renvoi pédagogique vers un carnet voisin, pas une chronologie. De même
« promesse livrée à Colonne » (prose française courante) ne matche pas.

## Mesure (série GameTheory, 2026-10-26)

- **50 carnets** portent au moins un marqueur ; **106 marqueurs** au total.
- Répartition par type : `pr_paren` 42 · `issue` 25 · `epic` 20 · `pr` 17 · `livre` 2.
- **La majorité des 106 est PROVENANCE_UTILE** (verdicts SOTA, parités lib-vs-lib,
  « prouvé dans PR #N ») : ces renvois **restent**. La tranche réellement à
  dé-chronologiser est la sous-classe CHRONOLOGIE_GIT_A_RETIRER, nommée ci-dessous. C'est
  précisément pourquoi l'organe signale le candidat mais ne supprime pas : un balayage
  « supprimer tout `#NNNN` » effacerait la provenance.

## Cas analogues nommés (classe CHRONOLOGIE_GIT_A_RETIRER)

Ces carnets portent, dans une introduction ou une conclusion, un **récit de livraison**
qui se dé-chronologise (retirer le « livré par l'issue / la PR / sur main, commit », le
« DISPATCH ai-01 … MERGED <ts> », le « ai-01 dans la review PR #N ») tout en **gardant**
la source et les résultats. Ils forment le backlog de tranches de #14442 :

| Carnet | Cellule(s) | Récit de livraison à retirer |
|---|---|---|
| **GT-20** (livré par la PR associée) | 36 | « l'EPIC #12205 prescrit », « GT-3b (#12213) », « GT-3b livré (#12253) », « GOL-06 … (#12286) » |
| GT-06k FairBot-Loeb | 0, 1, 34 | « Carnet livré par l'issue #20379 », « PR #15923 » |
| GT-13d Optimistic-CFR | 1 | « livré sur main par #13350, commit … » |
| GT-06j Bounded-Proofs | 31 | « DISPATCH ai-01, EPIC #15062, PR #15175, MERGED 2026-09-09… » |
| GT-03d Le-Joueur-LLM | 5, 25 | « ai-01 dans la review PR #12295 », « Substrat EPITA (#12254) » |
| GT-13c Safe-Subgame (C#) | 20 | « issue #13468, PR #13480, épilogue en conclusion » |
| GT-11b BayesianGamesExt | 42 | « side-track sur l'issue #4251 (Part of #4038) » |
| GT-09b Commitment-Stackelberg | 24 | « les open games (issue #12212, en cours de livraison) » |
| SocialChoice/10 | 13 | « la PR #21632, encore ouverte à la date » |

Le **GT-20** est le reliquat que le coordinateur a nommé le 25/10 comme seul actionnable à
l'instant ; les deux autres reliquats de l'issue (GenAI/Texte/10e — GPU + embargo, et
2.14b-XAI — figé par la PR ouverte #21413) sortent du périmètre GameTheory de ce sweep.

## Portée de la PR associée

- **livré** : l'organe de détection + ce sweep documenté + la dé-chronologisation de
  **GT-20** (cellule 36 : les 4 renvois de livraison retirés ; la source bibliographique
  Robinson & Goforth 1978, les pointeurs de provenance GT-3b / GOL-06 et les chiffres
  structurels 75 / 576 / 5625 / diamètre 12 / géodésiques 16-2-236 544 conservés).
- **non livré ici** : les 9 autres carnets du tableau (tranches de suivi de #14442) et le
  défaut 2 de l'issue (déplacer l'annexe hors de GT-04). L'issue reste ouverte ; la PR est
  `See #14442`.

## Reprise

```bash
python scripts/notebook_tools/audit_workflow_chronology.py MyIA.AI.Notebooks/GameTheory   # exit 1 si marqueur
```

Après chaque tranche, re-passer l'organe sur le carnet touché : il doit rendre **0 marqueur**
dans les cellules de livraison, sans avoir touché les renvois de provenance.
