# Contrat du cycle de merge — ce qui se rend, dans quel ordre, sous quel nom

S'applique aux **trois roles** qui produisent les merges du depot : le coordinateur `myia-ai-01:CoursIA`, le titulaire `myia-po-2025:CoursIA-2`, le secretaire `myia-po-2026:CoursIA-3`. Source : mandat user 2026-09-22 — « on a souvent des regressions car les bonnes pratiques ne sont pas cristallisees avant d'etre oubliees, c'est peut-etre le bon moment de mettre les choses en dur ».

Les **mecanismes** du gate (codes de sortie, empreinte, `[ADJOINT PREFLIGHT]`) vivent dans les skills `coordinate` / `coordinate-adjoint` et dans [coordinator-discipline.md](coordinator-discipline.md). Cette regle ne les repete pas : elle fixe les **quatre gestes** dont l'oubli a un cout mesure, et que rien n'empechait d'oublier.

## Regle 1 — un lot se rend NOMINATIVEMENT, jamais en compte (HARD)

Un lot de PRs pre-machees se rend en **citant chaque PR**. Un cumul (« 56 OK B.0 frais », « la file est prete ») n'est pas une livraison : c'est une affirmation que le destinataire doit re-etablir a l'aveugle, et cette re-decouverte **perime** les dossiers qu'elle traverse.

Mesure du 2026-09-22, trois lots reels sur le meme cycle :

| Format rendu | Conversion en merge |
|---|---:|
| liste **nominative** (PRs citees une a une) | **10/10 — 100 %** |
| **cumul** non nomme | **15/53 — 28 %** |
| auto-tire par le coordinateur | **2/54 — 4 %** |

Le travail sous-jacent etait **le meme** dans les trois cas. L'ecart vient entierement du format du rendu. **C'est le levier de debit le plus rentable mesure a ce jour**, avant toute optimisation de quota ou de cout d'appel.

Corollaire : un lot se rend **au fil de l'eau**, jamais en barriere. Chaque dossier pret remonte seul ; attendre d'avoir le lot complet ajoute de la peremption sans ajouter d'information.

## Regle 2 — le dossier se pose EN DERNIER (HARD)

Toute ecriture tierce sur les surfaces de discussion **posterieure** au dossier le perime. Auditer une PR, y repondre, y poster un constat : chacun de ces gestes invalide une attestation deja ecrite — **y compris la sienne propre**.

L'ordre est donc : lire, ecrire tout ce qu'on a a ecrire, **puis** attester. Mesure du 2026-09-22 : **12 des 32** refus `rc=1` du cycle portaient `discussion changed after dossier` — un dossier juste, tue par une ecriture qui a suivi.

La piece jumelle vit dans [git-workflow.md](git-workflow.md) : **la branche est gelee entre le dossier et le merge**. Un dossier a besoin d'une branche silencieuse, sinon le travail de prevalidation est detruit par le travail de reparation, indefiniment.

## Regle 3 — `BLOCKED` vaut autant que `READY`, et ne se maquille jamais (HARD)

Un dossier `verdict: BLOCKED` est une **livraison complete**, pas un echec : il laisse le coordinateur dispatcher depuis un motif atteste **sans ouvrir les surfaces**, donc sans les perimer.

**N'ecrire jamais `READY` pour rendre son travail visible.** Un `b0: clear` faux a deja ete mesure sur une PR portant 3 findings HIGH ouverts. Le verdict decrit l'etat de la PR, jamais l'effort fourni.

Symetrique cote coordinateur : un `BLOCKED` se dispatche **depuis son motif**, il ne se re-audite pas. Et quand la cause est d'**infrastructure** (parc de runners, `main` rouge, minuteur `DWELL`), l'attester en la **nommant** — renvoyer la PR a son auteur pour reparation lui demande de reparer ce qui n'est pas chez lui.

## Regle 4 — un levier se rend AVEC sa portee (HARD)

Toute amelioration proposee ou livree nomme, dans la **meme phrase**, ce qu'elle **ne** traite **pas**. Un levier rendu sans sa portee laisse croire que le probleme est traite, et ferme l'enquete sur la cause dominante.

Cas fondateur : le double fetch des check-runs du gate (#17390) reduit le cout **par appel**. La cause dominante mesuree de la consommation est la **peremption** — des dossiers produits puis jamais consommes. Rendre le premier sans nommer la seconde aurait fait passer un gain marginal pour une solution.

Corollaire, porte par [[a-correct-fix-can-perime-the-whole-fleet-at-once]] : un changement **juste** de l'ensemble des champs qui composent une **empreinte** perime **toutes** les attestations en vol d'un coup. Son livrable est une **issue** avec sa fenetre et son controle positif, pas un commit de passage.

## Partition des emetteurs — pas d'auto-attestation

Le gate compare la lane du dossier au tag `Grain:` de la PR : une lane ne peut pas attester ce qu'elle porte. La partition d'un gisement se fait donc **par lane porteuse**, et se declare au moment du dispatch.

Le login GitHub etant partage, le champ `lane` est une **declaration fail-closed**, pas une preuve d'identite. Ce que le gate exige est que la prevalidation soit **tierce**, pas qu'elle vienne d'une lane nommee.

## Mesures et incidents

Chiffres, distribution des refus par motif, et le detail du cycle qui fonde ces quatre regles : [docs/reference/merge-cycle-measures.md](../../docs/reference/merge-cycle-measures.md).

## Voir aussi

- [coordinator-discipline.md](coordinator-discipline.md) — mecanique du gate et des roles
- [git-workflow.md](git-workflow.md) — gel de branche, `update-branch` et peremption du dossier
- [pr-review-discipline.md](pr-review-discipline.md) — §B.0, emission des marqueurs de reserve
- [harness-hygiene.md](harness-hygiene.md) — les 3 tiers : pourquoi le detail est en `docs/`
