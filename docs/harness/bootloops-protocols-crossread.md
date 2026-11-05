# Lecture croisée — les 12 protocoles BootLoops contre notre harnais

**Ce que c'est.** Une lecture comparée, protocole par protocole, des douze `skills` publiés par l'organisation GitHub `BootLoops-ai` contre les règles que ce dépôt applique déjà. Elle répond à quatre questions pour chacun : *que font-ils*, *avons-nous un équivalent*, *que faudrait-il adopter*, *que refusons-nous et pourquoi*.

**Ce que ce n'est pas.** Ni une adoption, ni une revendication de supériorité dans un sens ou dans l'autre. **Ce document n'ajoute aucune obligation** : il ne modifie ni `CLAUDE.md`, ni `.claude/rules/**`. Toute adoption qui ajouterait une obligation relèverait de la gouvernance du §A de `CLAUDE.md` — une PR par protocole, avec sign-off user.

Vient de la veine V2 de #20428 (distillation Schwartz / BootLoops), qui en nomme le livrable : « une lecture croisée pérenne `docs/harness/` (ce qu'ils ont / ce que nous avons / ce qu'on adopte / ce qu'on refuse et pourquoi) ».

## Provenance, et ce qui a été lu

| Point | Valeur mesurée |
|---|---|
| Dépôt | `https://github.com/BootLoops-ai/skills` |
| Tête lue | `ca892277dcf0468d995f0036f3bd6d753a8afe7d`, commit du 2026-10-01 |
| Licence | MIT (`LICENSE`) pour le code ; **CC BY 4.0** (`LICENSE-CONTENT`) pour la prose et les `*.md` |
| Fichiers lus | les **12** `skills/<nom>/SKILL.md`, téléchargés à la source et lus intégralement (~186 Ko cumulés) |
| Non lu | le paquet `bootloops` (intégrales certifiées) et `kira` (fork IBP, GPL-3.0). Cette lecture porte sur les **protocoles**, pas sur le code |

**Règle d'attribution appliquée.** Chaque affirmation ci-dessous s'appuie sur la checklist du protocole, citée verbatim entre guillemets et en anglais (la source est en anglais). Aucun extrait n'est paraphrasé en français entre guillemets — une reformulation traduite présentée comme une citation serait une fabrication. Aucun code n'est copié : la licence du contenu impose l'attribution, celle de `kira` interdit la copie.

## Les douze, et où nous nous situons

Verdicts : **DEJA** = nous l'avons, parfois sous un autre nom ; **ECART** = ils nomment quelque chose que nous n'avons pas nommé ; **PARTIEL** = nous couvrons une partie, pas la propriété qui fait la valeur du protocole.

| # | Protocole BootLoops | Notre équivalent mesuré | Verdict |
|---|---|---|---|
| 1 | `acceptance-gate` — ce qu'un résultat calculé doit satisfaire avant de s'appeler « fait » | H.1-H.4 (validation réelle), B.0 (aucun nit non levé), G.2 (métriques honnêtes) | **ECART** sur le contrôle négatif |
| 2 | `constant-recognition` — reconnaître des digits haute précision comme une constante close (PSLQ, LLL) | rien de nommé ; C.5 et G.2 en couvrent la motivation | **PARTIEL** |
| 3 | `independence-bookkeeping` — garder le second chemin réellement indépendant | G.1 (vérifier un claim contre la source), H.4 (merge non complaisant) | **ECART** sur le registre de contact |
| 4 | `lit-review` — revue de littérature dont l'exhaustivité est falsifiable | `bibliography-hygiene` (archivage), pas la revue | **ECART** |
| 5 | `planted-truth` — le pipeline doit d'abord récupérer une vérité plantée | anti-régression : « un motif de détection se valide par ses faux négatifs » | **DEJA**, avec une différence de forme |
| 6 | `prose-lint` — linter d'intégrité de la prose scientifique | C.5 (prose quantitative) + `check_prose_quantitative_claims.py` | **DEJA**, périmètre plus étroit chez nous |
| 7 | `prove-protocol` — protocole multi-agents de preuve et de réfutation | harnais prover `agent_tests/prover/` (#1453), comptage `count_code_sorry.py` | **PARTIEL** |
| 8 | `reading-contract` — n'asserter que ce que le document dit, avec localisateur | G.1 + SDDD (triple ancrage) | **DEJA**, localisateur moins formalisé |
| 9 | `ref-check` — vérification bibliographique champ par champ | `bibliography-hygiene` (identité en première page) | **PARTIEL** |
| 10 | `referee-sim` — simuler la meilleure objection de chaque audience | `pr-review-discipline` (critères A–I), pas la simulation | **ECART** |
| 11 | `timing-discipline` — mesurer avant de lancer, projeter par écrit | « Productivité opérations longues » (HARD 2026-05-11) | **ECART** sur la projection écrite |
| 12 | `tool-stewardship` — consulter l'index avant d'écrire, documenter après | « Catalogue agents / skills / scripts — USAGE MANDATÉ » + `organ-first-implementation` | **DEJA** |

## Les écarts qui valent une décision

Cinq écarts seulement sont substantiels. Les autres sont des nuances de forme ou relèvent du métier de la physique.

### E1 — Le contrôle négatif daté, dans `acceptance-gate`

Ce qui manque chez nous n'est pas l'exigence de preuve — H.1 à H.4 la portent — mais **le contrôle qui doit échouer** :

> "- [ ] Positive control passed; negative control failed, visibly, at the expected digit."

Un contrôle positif prouve que le chemin fonctionne ; un contrôle négatif prouve que le contrôle **sait** échouer. La même checklist ferme la porte de sortie :

> "Verdict is CLOSED only if every box above is checked; otherwise OPEN, with what remains stated."

Notre culture écrit déjà cela à un endroit — « un motif de détection se valide par ses faux négatifs » (`.claude/rules/anti-regression.md`), où la leçon fondatrice est un détecteur qui sous-comptait en silence. Mais la règle vit dans le comptage des `sorry`, pas comme condition générale de clôture d'un résultat.

**Ce qu'on gagnerait** : un verdict binaire reproductible au lieu de la prose « validé », et la fin des « DONE » partiels que G.3 interdit déjà mais que rien ne mesure.

### E2 — Le registre de contact, dans `independence-bookkeeping`

La règle est en une ligne, et c'est une règle à sens unique :

> "- [ ] The certifying reference is disjoint from the claim: not in its contact history, not produced by the code under test."

et son test :

> "- [ ] The counterfactual test passes: had the reference differed, the result could not have come out different."

Notre G.1 exige de vérifier un claim **contre la source**. Elle ne dit rien de la **contamination** : un oracle qui a servi à régler un paramètre ne peut plus certifier le résultat de ce réglage. C'est exactement le défaut que l'on rencontre quand un détecteur est calibré sur le corpus qu'il audite ensuite, et que l'audit rend un vert de complaisance.

**Ce qu'on gagnerait** : nommer *qui a nourri quoi* avant de certifier, et un test simple à poser sur chaque dossier de validation.

### E3 — La projection écrite avant le lancement, dans `timing-discipline`

> "- [ ] Projection written down with one-line provenance before launch."

Notre règle « Productivité opérations longues » dit de **lancer en arrière-plan et de ne pas attendre passivement**. Elle ne dit pas de **projeter** avant. La différence est mesurable : une projection écrite rend vérifiable le fait qu'un run a dérivé, et le protocole y ajoute l'unité de progrès réel :

> "- [ ] Real-progress unit defined, with where it accumulates and the expected rate; monitoring watches it, not the log."

**Ce qu'on gagnerait** : de quoi distinguer un run long d'un run bloqué sans lire un log intégral.

### E4 — Le lecteur adverse et le contexte neuf, dans `referee-sim`

> "- [ ] The pass ran in a fresh context."

Notre review se fait en contexte partagé, et la discipline B.0 mesure les **verdicts**, pas la fraîcheur du regard. Le protocole demande d'énumérer les audiences, de générer leur meilleure objection **et de vérifier que la réponse est là où l'objecteur la cherchera**. C'est plus exigeant que « répondre à la remarque » : une réponse enterrée au fond d'un long dossier ne compte pas.

**Ce qu'on gagnerait** : une raison mécanique de faire reviewer par un agent qui n'a pas écrit le livrable — ce que la délégation bornée de `model-delegation.md` (déléguer le read-heavy vérifiable, garder la décision et le cross-check G.1) rend possible, sans le fonder sur un protocole.

### E5 — Le registre de lecture, dans `lit-review`

> "- [ ] Every P3+ work read full-text with a verbatim quote and location, or explicitly flagged FULL-TEXT-UNREAD with its grade marked as a ceiling."

Notre `bibliography-hygiene` est solide sur l'**archivage** — identité vérifiée, une seule copie, lecture avant attribution, chemin cité. Elle ne produit pas de **registre** qui rende l'exhaustivité falsifiable : on ne peut pas aujourd'hui distinguer « j'ai lu 14 références » de « j'en ai survolé 3 et cité 14 ».

## Ce que nous refusons, et pourquoi

**Nous n'adoptons pas les douze.** Deux règles du harnais s'y opposent explicitement, et ce sont de bonnes règles :

- **« Fixing Prompts and Rules — No Pendulum »** (`~/.claude/CLAUDE.md`) : ajouter une obligation pour corriger un défaut observé est l'échec-pendule. Un protocole importé sans le défaut mesuré qu'il corrige **chez nous** est exactement cela.
- **« Harnais maigre »** (`roo-extensions#3657`) : le harnais est déjà payé à chaque requête. Douze protocoles de plus, ce sont douze sections de plus dans un contexte qui n'en peut plus.

**Ce que nous refusons nommément** :

| Protocole | Motif du refus |
|---|---|
| `prose-lint` | Notre C.5 est **mécanisé** (`check_prose_quantitative_claims.py`, bloquant sur lignes ajoutées). Importer une liste de vocabulaire banni en prose humaine serait un recul : leur linter s'applique à la main, le nôtre rougit. |
| `prove-protocol` | Le métier du prover est chez nous et il est instrumenté (#1453, `count_code_sorry.py`, `LeanVerifier.check_axioms`). Ce qui manque au prover est **mesuré** ailleurs et se corrige en code, pas en protocole. |
| `constant-recognition` | Ne concerne aucune série du dépôt aujourd'hui. À reprendre le jour où une série physique manipule PSLQ pour de bon — pas avant. |
| `tool-stewardship` | Nous avons déjà « USAGE MANDATÉ » et `organ-first-implementation`, et nous les appliquons. Le protocole est plus long, pas plus fort. |
| `planted-truth` | Déjà là sous la forme du faux négatif. La différence est de forme : chez nous c'est une leçon, chez eux une batterie déclarée **avant** d'ouvrir les données réelles. C'est E1 qui porte le gain, pas une duplication. |

## Ce qu'on propose d'adopter

Trois, pas cinq, et **un par PR**, chacun sous sign-off user puisqu'il ajoute une obligation :

1. **`acceptance-gate` → la condition de clôture d'un résultat** (E1). Un verdict `CLOSED`/`OPEN` avec cases, dont le contrôle négatif. Candidat naturel : `.claude/rules/verify-before-claiming.md`, qui porte déjà la règle voisine.
2. **`independence-bookkeeping` → le registre de contact dans les dossiers de validation** (E2). Candidat : `CLAUDE.md` §B.0 (« Aucun nit non levé ne survit à un merge »), ou une section de `prevalidation-dossier-order-detail.md` qui décrit déjà la forme du dossier.
3. **`timing-discipline` → la projection écrite des runs longs** (E3). Candidat : la section « Productivité opérations longues » de `CLAUDE.md`, qui gagne une ligne et une mesure.

E4 et E5 sont **notés, pas proposés** : ils demandent un instrument (un reviewer en contexte neuf, un registre de lecture lisible par un organe) avant de pouvoir devenir une règle. Une règle sans instrument ne mord pas — c'est la leçon que ce dépôt a déjà payée plusieurs fois.

## Ce que la lecture a appris sur nous

Un point, et il est désagréable : **sur douze protocoles, nous en avons déjà quatre en substance, et aucun des quatre n'est nommé comme un protocole.** « Un détecteur se valide par ses faux négatifs » et « le catalogue est la source, pas la mémoire » vivent dans des documents de règles au milieu d'autres choses. Ce qui nous manque n'est souvent pas la discipline — c'est qu'elle ne soit pas **énoncée une fois, à un endroit, sous un nom qu'un agent peut citer**.

C'est aussi l'explication des cinq écarts : ils ne portent pas sur la rigueur, mais sur des **artefacts datés** — une projection écrite, un registre de contact, une batterie de contrôles déclarée avant. Un artefact se relit ; une bonne intention se perd à la compaction.

## Voir aussi

- #20428 — la distillation qui porte cette veine (V2), et ses points de décision
- `.claude/rules/anti-regression.md` — « un motif de détection se valide par ses faux négatifs »
- `.claude/rules/verify-before-claiming.md` · `.claude/rules/pr-review-discipline.md` — H.1-H.4, B.0, G.1
- `.claude/rules/bibliography-hygiene.md` — archivage et lecture avant attribution
- `~/.claude/CLAUDE.md` — « No Pendulum » et « Harnais maigre » (roo-extensions#3657)
