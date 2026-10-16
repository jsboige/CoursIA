# Chantier 1 — tranche A8 : conditions de rétrogradation pour chaque entrée de la TABLE

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2027:CoursIA` · **date de mesure** 2026-10-15
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) · [A3](12204-ict-chantier-1-a3.md) · [A4](12204-ict-chantier-1-a4.md) · [A5](12204-ict-chantier-1-a5.md) · [A6](12204-ict-chantier-1-a6.md) · [A7](12204-ict-chantier-1-a7.md) · [audit froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md)

## Ce que cette tranche fait

L'arbitrage coordinateur du 2026-10-14 ([issuecomment-6179879158](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6179879158)) retient la recommandation d'analyse externe : **toute admission dans la table nomme ses deux témoins et ce qui la ferait redescendre**. Le chantier rétrograde déjà — mais toujours après coup, à la relecture. A8 rétro-équipe chaque entrée actuelle de sa **condition de rétrogradation** : l'observation précise, exécutable sur le dépôt, qui la renverrait en file d'attente. Une entrée pour laquelle aucune condition ne se formule est signalée comme **non falsifiable sous sa forme actuelle**.

Une condition n'est pas une revocation : c'est le prix d'entrée payable à tout moment. Le mécanisme historique (faire tomber autant que faire monter, §1 du body) reste la seule voie de sortie — A8 le rend **exécutable à l'avance** au lieu de le laisser à la relecture suivante.

## Table des conditions (12 entrées TABLE, état post-A7)

| # | Opération | Attestations (rappel) | Condition de rétrogradation — observation précise et exécutable |
|---|---|---|---|
| 1 | **Recoordonner** | Sudoku-13 (SMT après deux impasses) · `conway_lean`/`Life.lean` (recoordination kernel-décidable) · MGS-21 (R2 dominant par mesure) | Une quatrième instance, de famille distincte, où la **même** recoordonnerie est tentée avant et après mesure **sans changement de destin** (forme d'émission indifférente au résultat) — réfuterait la loi « la forme décide du destin » sur laquelle l'opération repose. Exécutable : un carnet A/B sur un problème nouveau, même contrainte sous deux formes, deux exécutions, destin identique mesuré. |
| 4 | **Décomposer localement** | Hashlife (`padCenter2_margin_ge_jumpReach`, bords décidés par la preuve) · ICT-15d (jouet, partition avouée) · EPITA (orchestration, identification restaurée) | Une preuve de recouvrement où les **bords ne peuvent pas être définis avant les sections** (dépendance circulaire bords ↔ sections exhibée) — réfuterait la loi « les bords doivent être définis avant les sections ». Exécutable : un contre-exemple formel ou un carnet où toute tentative de pré-définition des bords échoue par circularité mesurée. |
| 6 | **Réparer localement sous garantie** | GT-13b/13c (safe subgame solving, garantie contrôlée) · Search-03f (LPA*, 8/8 concordances, **0 mention Sandholm/Kroer** mesuré) | (a) Une instance où la garantie transportée de Search-03f est **violée** (coût LPA* > coût A* from scratch sur une séquence de changements) ; (b) ou l'apparition d'une citation Sandholm/Kroer dans Search-03f, cassant l'indépendance par construction. Exécutable : re-exécution du carnet avec une séquence adversariale cherchant la violation, ou `grep -i "sandholm\|kroer"` retournant non vide. |
| 7 | **Engendrer un témoin** | Sudoku-13 (générateur Z3, grille produite) · `conway_lean` (certification de motifs, synthèse hors Lean) · GT-16b (générateur/vérificateur séparés, témoin d'impossibilité) | Une instance où le **générateur est le vérificateur** (le moteur qui produit le témoin est le même que celui qui le valide, sans séparation) et où cette confusion n'est **pas** détectée par le pipeline — réfuterait la loi « le générateur n'est pas le vérificateur ». Exécutable : audit d'un carnet où la même fonction produit et valide, sans témoin indépendant. |
| 8 | **Certifier** | 18/22 lakes à 0 sorry réel (mesuré P3, instrument canonique) · Lean-22b (gate `fail_on_sorry`) | `distinct_code_sorry` remontant au-dessus de la mesure P3 sur un lake précédemment à 0, **sans** que la remontée soit traceable à une dette assumée (PR `debt`/`regression-accepted` avec sign-off) — réfuterait l'affirmation « le dépôt sait certifier » en montrant que la certification recule sans décision. Exécutable : `python scripts/lean/count_code_sorry.py --json` à chaque cycle, comparaison à la mesure de référence. |
| 9 | **Élargir l'espace** | `planning_lean/Planning/Admissibility.lean:50` (`relaxed_plan_admissible` = `P_reel ⊆ P_relache`) · SW-14 (extension η, diff de triplets + verdict SHACL) | Une instance d'élargissement où `P_reel ⊄ P_relache` (l'extension **perd** de l'atteignable réel — la monotonie est violée) — réfuterait la loi de monotonie de l'atteignabilité. Exécutable : un carnet où une extension de vocabulaire/primitives rend un état précédemment atteignable inatteignable, mesuré. |
| 10 | **Concevoir la règle** | GT-16b (AMD, `M* = argmax J(M)`) · GT-20 (Stackelberg) · SC-27 (smart contracts, témoin d'impossibilité) | Une instance où l'optimisation dans `M` **fait apparaître une coordonnée hors de `M`** (le mécanisme optimal exhibé requiert une action, un joueur ou une règle qui n'était pas dans l'espace de conception déclaré) — réfuterait la dette écrite (« optimiser dans M n'est pas faire apparaître une coordonnée hors de M ») en montrant qu'elle est violée en pratique sans être détectée. Exécutable : un carnet où la solution optimale trouvée utilise une primitive absente de la déclaration d'espace. |
| 11 | **Descendre sous budget** | `mimo_lean/Descent.lean` (`descent_flips_le_barrier` l.110, terminaison l.144, sorry-free) · Search-11d (60 exécutions, 0 violation hstrict/hbarrier/plafond, `hnostall` réfutée) | Une réintroduction de `hnostall` comme hypothèse **non mesurée** dans une future formalisation de descente (le théorème ré-admis sans que sa troisième hypothèse soit testée empiriquement) — réfuterait la Loi IV appliquée à cette opération. Exécutable : grep d'une future preuve de descente cherchant `hnostall` ou équivalent non testé. |
| 12 | **Composer des regards** | GT-21 (jeux 2×2, play/coplay) · Search-12a (gridworld pondéré, paire incompatible exhibée, associativité 92 triples) | Une instance où la composition play-forward/coplay-backward **violet l'associativité** sur un domaine fini où elle était attendue (parenthésage changeant le résultat mesuré) — réfuterait la loi « composition associative ». Exécutable : énumération de triples sur un domaine nouveau, comptage des violations d'associativité > 0. |
| 13 | **Traverser un mur** | GT-24 (jeux 2×2, 0/576 raccourcis, chemin certifié minimal) · GT-20c (3×2, 15,0 % raccourcis — **réfute le 0/576** sur ce substrat) | La condition est **déjà partiellement rencontrée** : GT-20c a réfuté la généralisation du 0/576. Ce qui maintient l'entrée en TABLE est la **validité restreinte** (le 0/576 tient sur le 2×2 fermé). Rétrogradation complète si : une formalisation Lean du 3×2 (aucun fichier `.lean` ne cite encore ce substrat, mesuré ce cycle) **confirme** le raccourci tout en montrant que le témoin « chemin minimal certifié » de GT-24 était **mal construit** (pas seulement non généralisable) — réfuterait la première attestation elle-même, pas seulement sa portée. Exécutable : lake `Chemins3x2` ou équivalent prouvant que le certificat GT-24 est incorrect sur son propre domaine. |
| 14 | **Agréger un collectif** | `Shapley.lean:614-634` (Möbius sorry-free) · SC-06 (miroir Python, écart 5.55e-17 sur 16 coalitions) | Une divergence mesurée entre le calcul Lean et le calcul Python de la reconstruction de Möbius sur une instance commune (écart > ε de représentation flottante) — réfuterait la validation croisée qui est la forme exacte du pont preuve/mesure. Exécutable : exécuter les deux voies sur une instance nouvelle, comparer. |
| — | **`point fixe`** | `argumentation_lean` (Knaster-Tarski, `Characteristic.lean`) · Tweety-07a C# (lfp de la fonction caractéristique ADF, témoin `{a,c}` imprimé, ligne 647) | Une instance où le lfp calculé par Tweety-07a **diffère** du lfp théorique de Knaster-Tarski sur le même opérateur (les deux moteurs donnent des points fixes distincts pour la même fonction caractéristique) — réfuterait la correspondance mesurée entre les deux substrats. Exécutable : carnet calculant le lfp des deux côtés sur un ADF commun, comparaison des ensembles. |

## Entrées non falsifiables sous leur forme actuelle

**Aucune entrée de la TABLE n'est non falsifiable.** Chaque condition ci-dessus est une observation précise, exécutable sur le dépôt (carnet, grep, mesure d'écart, re-exécution). C'est le critère §1 qui rend cela possible : une opération n'entre que si son témoin a une forme connue — et une forme de témoin connue est précisément ce qui rend une condition de sortie formulable.

La **Loi IV** (admission) n'est pas une entrée de la table et ne porte pas de condition propre : elle est une propriété du critère d'admission, pas une opération. Sa rétrogradation éventuelle serait celle du critère lui-même (une admission sans mesure des hypothèses qui se révèle meilleure qu'une admission avec) — hors scope de cette tranche.

## Ce que cette tranche ne fait pas

- Elle ne **statue** sur aucune promotion ni descente : les 12 entrées restent où A7 les a laissées. A8 équipe, il ne juge pas.
- Elle ne **modifie pas** la table maîtresse ([audit-froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md)) : les conditions vivent ici, et le body de l'EPIC renvoie à ce fichier (effet demandé ci-dessous).
- Elle ne **prétend pas** que les conditions sont exhaustives : une relecture ultérieure peut en ajouter sans invalider celles-ci. Le format est un plancher, pas un plafond.

## Effet demandé sur le body de l'EPIC

Ajouter après la section §4 (grains), avant §4bis, une case :

```markdown
- [x] **A8** — *(livré : [`docs/ledgers/12204-ict-chantier-1-a8.md`](../blob/main/docs/ledgers/12204-ict-chantier-1-a8.md), PR #20814 — conditions de rétrogradation rétro-équipées sur les 12 entrées TABLE ; aucune non falsifiable ; format d'admission à trois champs désormais requis : deux attestations + condition de sortie)*
```

Et dans le §1 (critère d'admission), une phrase : « Depuis A8 (2026-10-15), toute promotion écrit aussi sa **condition de rétrogradation** — l'observation qui la renverrait en file. Une entrée sans condition formulable est signalée non falsifiable. »

## Honnêteté méthodologique

- **Re-mesuré firsthand ce cycle** : existence des artefacts de chaque attestation (12/12 présents sur `main`), sorry count courant (`distinct_code_sorry` = 12, répartis : game_theory_lean 1, decision_theory_lean 2, conway_lean 1, knot_lean 8 — la mesure P3 de l'audit froid est la référence historique, la valeur courante est celle du jour), absence de fichiers `.lean` citant le substrat 3×2 (condition op 13 vérifiée réelle), contenu de Search-03b et Search-03f vérifié (les renommages de #19109/#19112 ont logé les ops 3 et 5 dans des carnets existants — les conditions de ces ops, quand elles seront promues, viseront les vrais fichiers).
- **Croisé, pas re-mesuré** : les formes de témoins sont celles des tranches d'origine (A2-A7 + audit-froid), relues et acceptées. Les conditions sont écrites à partir des **lois et dettes déjà formulées** par le chantier — A8 n'invente pas de critères nouveaux, il rend exécutables ceux que les tranches ont déjà tenus.
- La condition de l'op 13 est la seule qui soit **déjà partiellement rencontrée** (GT-20c a réfuté la généralisation) : elle est écrite comme telle, avec la distinction validité-restreinte vs réfutation-de-l'attestation.

## Références

- Arbitrage coordinateur (format d'admission à trois champs) : [issuecomment-6179879158](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6179879158)
- Table finale (post-A7) : [A7 §État final](12204-ict-chantier-1-a7.md)
- Table maîtresse labellisée : [audit-froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md)
- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · claim : [issuecomment-6179879158](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6179879158) (dispatch ai-01)
