---
paths: MyIA.AI.Notebooks/**/*.ipynb
---

# Labeling Exemple / Exercice — content-based, STOP au flip-flop

S'applique a **tous les agents de-leak** (po-2023, po-2024, po-2025, po-2026, ai-01) sur les notebooks pedagogiques.

**Source** : mandat user 2026-05-20 (cours EPITA-IS live). Apres une frenesie de relabels contradictoires entre agents (le "pendule"), le user a impose une regle unique pour arreter le chaos. Broadcast dashboard workspace CoursIA 2026-05-20T09:25Z.

**Amendement user 2026-09-07** (arbitrage #15042, signale par l'audit Astra #3) : le remede du cas 1 devient la **digestion**, pas le stub. Verbatim : « La regle devrait demander la digestion en exemple guide et la proposition d'un nouvel exercice en cas de leak (ou de soumission legitime). »

## Principe (HARD)

Un notebook pedagogique DOIT contenir des **Exemples** (resolus) ET des **Exercices** (non resolus). Les deux **COHABITENT**. Quand un exercice est resolu/soumis il devient un exemple, et de nouveaux exercices sont ajoutes a la suite. Ne jamais "purger" l'un au profit de l'autre.

## Classification PAR CONTENU, pas par titre (HARD)

- Cellule code = **solution complete fonctionnelle** => c'est un **EXEMPLE**. Label "Exemple" / "Exemple guide". **NE JAMAIS stubber, NE JAMAIS relabeler en Exercice.**
- Cellule code = **stub** (squelette / `# TODO` / "a completer" / `print("...a completer")` / `pass` / `return None`) => c'est un **EXERCICE**. Garder en stub. **NE JAMAIS remplir la solution.**

## Les 2 seuls cas a corriger

1. Titre "**Exercice**" + cellule code = solution complete => **digerer** (procedure ci-dessous). **Ne PAS stubber le code.**
2. Titre "**Exemple**" + cellule code = stub vide => **relabeler le titre en Exercice**.

Tout le reste est deja dans l'etat cible : ne pas toucher.

## Digestion (remede du cas 1, HARD)

Trois gestes, dans cet ordre, et **le premier est une conservation** :

1. **Retitrer** la section en "Exemple guide" — le contenu decide du label (section precedente), donc c'est le titre qui est faux, jamais le code.
2. **Conserver le code tel quel, avec son attribution s'il en porte une** (nom de groupe, d'etudiant, numero de PR de rendu). Une resolution attribuee est un livrable pedagogique, pas une fuite.
3. **Ajouter a la suite un nouvel exercice non resolu** qui mesure quelque chose de neuf — pas une reformulation du meme enonce. Sans ce troisieme geste, le notebook perd une activite et la digestion appauvrit le catalogue.

**La cause d'origine ne change pas le geste.** Une solution d'instructeur laissee en place (leak) et un rendu d'etudiant merge (soumission legitime) se digerent **de la meme facon** : le notebook ne garde aucune trace de la difference, et un agent qui rencontre le resultat ne peut pas la reconstituer.

**Un "Exemple guide" est TERMINAL.** Il ne redeclenche ni le cas 1 (son titre n'est plus "Exercice") ni le cas 2 (son code n'est pas un stub). Ne pas inventer un cas 3 pour le re-traiter : c'est l'etat cible, pas une etape.

**Precedent dans le depot** : `Texte/4_Function_Calling.ipynb` c45/c52, "EXEMPLE CORRIGE — Assistant de Planification Multi-Outils" — resolution conservee et titree, exercices maintenus a cote.

**Pourquoi ce remede et pas le stub** : le protocole de TP (correction user 2026-09-07, EPIC #15035) veut que **chaque groupe rende au moins un exercice corrige, different d'une session a l'autre**. La digestion est le mecanisme qui rend ce cycle soutenable — le catalogue s'enrichit d'un exemple attribue et d'un exercice neuf a chaque rendu. Stubber la resolution effacerait le travail etudiant que ce cycle produit, et [anti-regression.md](anti-regression.md) le classe deja en regression de contenu.

## Interdits (= la source du chaos)

- **find-replace aveugle** de titres "Exercice" <-> "Exemple" (= gaming du leak-scanner, incidents #1214 / #1336).
- **resoudre un stub d'exercice** (remplir la solution).
- **transformer un exemple resolu en exercice** (stubber un worked-example).
- **stubber une resolution attribuee** a un groupe ou a un etudiant — c'est le cas 1 mal traite, et ce que l'amendement 2026-09-07 ferme.
- **digerer a moitie** : retitrer sans ajouter le nouvel exercice laisse le notebook avec une activite de moins.
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
- **#15042** : la regle prescrivait deux gestes opposes sur le meme objet — "NE JAMAIS stubber" (classification par contenu) contre "stubber le code" (cas 1). Signale par l'audit Astra #3 sur `RAG-et-Memoire-Semantique/05-Stockage-Vectoriel.ipynb` c30/c32/c34. Tranche par le user le 2026-09-07 en faveur de la digestion.

## Voir aussi

- [.claude/rules/anti-regression.md](anti-regression.md) — ne pas stripper une cellule `# Solution` / `# Exemple resolu` demonstrative.
- [.claude/rules/notebook-conventions.md](notebook-conventions.md) — C.1 stubs sans erreur volontaire, C.2 outputs.
- [.claude/rules/three-exercises-per-notebook.md](three-exercises-per-notebook.md) — le nouvel exercice ajoute par la digestion compte dans ce plancher.
- CLAUDE.md section C — regles notebooks 2026-04-26.
