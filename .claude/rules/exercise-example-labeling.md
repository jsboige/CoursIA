# Labeling Exemple / Exercice — content-based, STOP au flip-flop

S'applique a **tous les agents de-leak** (po-2023, po-2024, po-2025, po-2026, ai-01) sur les notebooks pedagogiques.

**Source** : mandat user 2026-05-20 (cours EPITA-IS live). Apres une frenesie de relabels contradictoires entre agents (le "pendule"), le user a impose une regle unique pour arreter le chaos. Broadcast dashboard workspace CoursIA 2026-05-20T09:25Z.

## Principe (HARD)

Un notebook pedagogique DOIT contenir des **Exemples** (resolus) ET des **Exercices** (non resolus). Les deux **COHABITENT**. Quand un exercice est resolu/soumis il devient un exemple, et de nouveaux exercices sont ajoutes a la suite. Ne jamais "purger" l'un au profit de l'autre.

## Classification PAR CONTENU, pas par titre (HARD)

- Cellule code = **solution complete fonctionnelle** => c'est un **EXEMPLE**. Label "Exemple" / "Exemple guide". **NE JAMAIS stubber, NE JAMAIS relabeler en Exercice.**
- Cellule code = **stub** (squelette / `# TODO` / "a completer" / `print("...a completer")` / `pass` / `return None`) => c'est un **EXERCICE**. Garder en stub. **NE JAMAIS remplir la solution.**

## Seul vrai leak a corriger (les 2 seuls cas)

1. Titre "**Exercice**" + cellule code = solution complete => **stubber le code** (garder le titre Exercice, conserver `# TODO`/`# Indice`/`# Etape N`).
2. Titre "**Exemple**" + cellule code = stub vide => **relabeler le titre en Exercice**.

Tout le reste est deja dans l'etat cible : ne pas toucher.

## Interdits (= la source du chaos)

- **find-replace aveugle** de titres "Exercice" <-> "Exemple" (= gaming du leak-scanner, incidents #1214 / #1336).
- **resoudre un stub d'exercice** (remplir la solution).
- **transformer un exemple resolu en exercice** (stubber un worked-example).
- **reverter des relabels deja valides** (cf #1343 ferme comme redondant).

## Reference validee user (etat CIBLE)

`SW-2-CSharp` : cell42 et cell45 = **Exemples guides** (solutions correctes, GARDEES) + cell48 = **Exercice** stub. C'est l'etat correct. **Ne PAS toucher.**

## Rappel C.1 (notebook-conventions)

Le stub d'exercice n'utilise **jamais** `raise NotImplementedError` / `assert False` / `1/0`. Patterns corrects : `pass`, `print("Exercice a completer")`, `return None`, `result = None  # TODO etudiant`. Le notebook doit s'executer de bout en bout meme exercices non completes.

## Incidents de reference

- **#1214** (commit a9d8ff8b) "fix(leaks): relabel SemanticWeb instructor solutions as Exemple guide (16->0 HIGH)" : find-replace AVEUGLE `Exercice` -> `Exemple guide` sur 7 notebooks SW pour faire passer le leak-scanner SANS de-leaker. A corrompu la prose. Gaming du detecteur, pas une correction. Reverte/corrige via #1339.
- **#1336** : rootcause de #1214 documente.
- **#1343** : revert redondant ferme (ne pas re-reverter des relabels deja valides).
- **EPIC #1344** : Planners de-leak (convention appliquee : stub = objectif + squelette, PAS verbatim/solution).

## Voir aussi

- [.claude/rules/anti-regression.md](anti-regression.md) — ne pas stripper une cellule `# Solution` / `# Exemple resolu` demonstrative.
- [.claude/rules/notebook-conventions.md](notebook-conventions.md) — C.1 stubs sans erreur volontaire, C.2 outputs.
- CLAUDE.md section C — regles notebooks 2026-04-26.
