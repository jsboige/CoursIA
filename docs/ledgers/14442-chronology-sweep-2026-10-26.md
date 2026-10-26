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
   parenthèse `(#NNNN` (parenthèse fermante facultative), et le past-participe « livré »
   accolé à un numéro / à « sur main ».
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

**Deux mesures, à lire ensemble** — la seconde corrige la première.

| | Carnets | `pr_paren` | `issue` | `epic` | `pr` | `livre` | Total |
|---|---|---|---|---|---|---|---|
| **Patron initial** `\(#\d{4,5}\)` | 50 | 42 | 25 | 20 | 17 | 2 | **106** |
| **Patron corrigé** `\(#\d{4,5}\b` | 50 | **47** | 25 | 20 | 17 | 2 | **111** |

- La mesure du sweep est celle du **patron corrigé** : **50 carnets / 111 marqueurs**
  (base `bf1f9c20`), **49 carnets / 107 marqueurs** au head de la tranche
  (`pr_paren` 44 · `issue` 25 · `epic` 19 · `pr` 17 · `livre` 2) — le delta est
  exactement les 4 marqueurs de GT-20 retirés par la tranche.
- **Pourquoi le total a grandi (+5)** : le patron initial exigeait la parenthèse
  **fermante**. Un renvoi suivi d'un commentaire — « (#15399, clos COMPLETED) »,
  « (#10382, axe 5) » — ou non fermé passait sous le radar. La cécité a été mesurée
  (rejeu de l'organe au base et au head, 5 occurrences muettes au base, 4 au head) et
  corrigée dans l'organe lui-même ; les 5 occurrences révélées sont **nommées** dans le
  tableau ci-dessous. Un sweep conduit avec un organe aveugle sur une classe de forme
  ne prouve pas l'exhaustivité de la mesure : c'est la leçon que porte cette révision.
- **La majorité des 111 est PROVENANCE_UTILE** (verdicts SOTA, parités lib-vs-lib,
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

### Les 4 occurrences révélées par la correction du patron

Elles n'étaient **pas** visibles au premier sweep : le patron exigeait la parenthèse
fermante. Relevées au head de la tranche, relues dans leur contexte, et classées :

| Carnet | Cellule | Renvoi | Classe | Geste |
|---|---|---|---|---|
| **GT-16g** Populations-Othman-Sandholm | 0 | « le pilote `GameTheory-16e-…` **(#15399, clos COMPLETED)** » | **CHRONOLOGIE_GIT_A_RETIRER** | « clos COMPLETED » est l'**état de livraison** de la PR au moment de l'écriture : inaudible pour un apprenant. Le pointeur vers le carnet 16e (pédagogique) se garde ; le numéro et l'état se retirent. |
| GT-16g | 0 | « La formalisation Lean de la Proposition 6 **(#12343, §1.1 du 16e)** » | PROVENANCE_UTILE | Le numéro **localise** la source de la formalisation (avec sa section) : c'est un renvoi de provenance, pas un récit de livraison. **Conserver.** |
| SocialChoice/01-Arrow (C#) | 31 | « **Pont industriel** (#10382, axe 5) » | PROVENANCE_UTILE | Le numéro nomme la **décision** (l'axe 5 de l'issue) dont le pont est issu. **Conserver.** |
| SocialChoice/04-Computational-Aggregation (C#) | 36 | « **Recette du pont** (#10382, axe 5 PythonNet) » | PROVENANCE_UTILE | Idem — même issue, même axe, même fonction de provenance. **Conserver.** |

Conséquence : la cécité ne cachait **qu'un seul** récit de livraison (GT-16g), mais elle
cachait aussi **trois** renvois de provenance — dont la suppression aurait été une
**régression de contenu**. C'est la mesure qui justifie la règle « l'organe signale,
la lecture classe » : un organe qui classifies lui-même aurait supprimé les trois.

Le **GT-20** est le reliquat que le coordinateur a nommé le 25/10 comme seul actionnable à
l'instant ; les deux autres reliquats de l'issue (GenAI/Texte/10e — GPU + embargo, et
2.14b-XAI — figé par la PR ouverte #21413) sortent du périmètre GameTheory de ce sweep.

## Portée de la PR associée

- **livré** : l'organe de détection (+ la correction de son patron `pr_paren`) + ce sweep
  documenté + la dé-chronologisation de **GT-20** (cellule 36 : les 4 renvois de livraison
  retirés ; la source bibliographique Robinson & Goforth 1978, les pointeurs de provenance
  GT-3b / GOL-06 et les chiffres structurels 75 / 576 / 5625 / diamètre 12 / géodésiques
  16-2-236 544 conservés).
- **non livré ici** : les 9 autres carnets du tableau (tranches de suivi de #14442), la
  dé-chronologisation de **GT-16g** (seule occurrence CHRONOLOGIE_GIT_A_RETIRER révélée
  par la correction du patron, dans l'issue de suivi nommée) et le défaut 2 de l'issue
  (déplacer l'annexe hors de GT-04). L'issue reste ouverte ; la PR est `See #14442`.

## Reprise

```bash
python scripts/notebook_tools/audit_workflow_chronology.py MyIA.AI.Notebooks/GameTheory   # exit 1 si marqueur
```

**Le critère de reprise est « 0 marqueur de la classe CHRONOLOGIE_GIT_A_RETIRER », pas
« 0 marqueur ».** La version initiale de cette section exigeait « 0 marqueur » dans les
cellules de livraison — un critère **inatteignable et faux** : l'organe rend des
*candidats* de classe CHRONOLOGIE **et** de classe PROVENANCE, et un carnet dont la
prose est irréprochable conserve légitimement des renvois de provenance
(« Verdict SOTA-OK (#10459) », « Pont industriel (#10382, axe 5) »). Sur les carnets
cités dans le tableau ci-dessus, « 0 marqueur » rend 0 pendant qu'il reste des
renvois à conserver — et une consigne de reprise qui rend 0 sur un carnet non traité
apprend à la lane qu'elle n'a rien à faire. Le critère est donc **la lecture** : re-passer
l'organe sur le carnet touché, **classer** chaque occurrence qu'il rend, et n'exiger
**0 que sur la classe CHRONOLOGIE_GIT_A_RETIRER**. C'est aussi ce que l'issue demande
(interdiction du fix regex global) et ce que fait l'organe.

