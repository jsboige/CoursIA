# Doctrine des lakes Lean — le site suit le consommateur

> REFERENCE — vivante — dernière révision 2026-11-11

**Statut** : validée par le user le 2026-11-02, en réponse au plan de consolidation du coordinateur (EPIC #4362, issue pilote #24183). Verbatim : « a) Je valide b) OK poure redescendre c) On le garde avec la notice qui doit exister, et on documente la comparaison des preuves comme tu as proposé ».

Ce document dit **où vit un lake**, **quand deux lakes fusionnent**, et **comment deux preuves d'un même résultat coexistent**. Il ne dit rien de l'harmonisation des révisions Mathlib ni des jonctions, qui restent l'objet de #4362.

## Pourquoi une doctrine

Deux mouvements se sont croisés sans se connaître :

- **La mutualisation** (#4362, #4365, de juin à août 2026). On regroupait des lakes dans des lakes-hubs pour deux raisons : le disque (un checkout Mathlib de plusieurs Go par lake) et la CI (un workflow par lake). C'est ainsi que `game_theory_lean` a absorbé stable_marriage, cooperative_games, social_choice et repeated_games.
- **La redescente en sous-séries** (#17545, depuis septembre 2026). Chaque lake rejoint les carnets qui le citent, pour la lisibilité.

Ces deux raisons de la mutualisation sont tombées :

- **Disque** : `scripts/lean/setup_shared_mathlib.ps1` partage `.lake/packages` par jonction dès que le couple (toolchain, rev Mathlib) coïncide. Les mesures par machine sont dans les blocs « État mesuré » de #4362 et dans `docs/lean/junctions-*.md`. L'emplacement d'un lake n'y change rien.
- **CI** : `.github/workflows/lean-ci-matrix.yml` sert les 33 lakes listés dans `scripts/lean/ci_lakes.json`. Un lake ne coûte plus un workflow, il coûte une entrée de matrice.

Le regroupement a pourtant continué par inertie. Résultat mesuré dans GameTheory le 2026-11-02 : un hub, huit lakes, une coquille, et les théorèmes d'Arrow et de Sen prouvés deux fois dans deux lakes qui s'ignoraient (#24183). `decision_theory_lean` avait fait l'aller-retour : remonté à la racine de Probas le 23/06, redescendu le 02/10.

## Les quatre règles

**R1 — Le site suit le consommateur.** Un lake vit dans le dossier de la (sous-)série dont les carnets l'importent. Quand plusieurs séries le citent, il vit chez celle qui porte son théorème phare, et les autres renvoient vers lui.

**R2 — Le partage ne passe plus par la fusion.** Le disque se partage par jonction Mathlib, à condition que le lake soit dans le groupe (toolchain, rev) canonique. La CI se partage par une entrée dans `ci_lakes.json`. Économiser du disque ou des jobs **n'est plus un motif de fusion**.

**R3 — On ne fusionne que par les imports.** Deux lakes fusionnent quand l'un importe l'autre, ou quand ils redéfinissent les mêmes objets (même `Preference`, même `SWF`). Une théorie distincte reste un lake distinct : la clause anti-god-lake de #4365 est maintenue.

**R4 — Un résultat a une maison canonique ; un doublon se déclare.** Deux preuves d'un même résultat peuvent coexister si elles sont **déclarées** comme preuves alternatives : renvoi croisé dans les deux docstrings, et note de comparaison (axiomes atteints, longueur, généralité, ce que chaque stratégie enseigne). Un doublon non déclaré est un défaut. Quand une preuve dérive d'un code tiers, sa notice d'attribution vit **à côté du code**, pas dans un dossier qui ne le contient plus.

## Précondition et exceptions

La doctrine suppose la convergence Mathlib : un lake hors du groupe canonique perd la jonction, donc le partage de disque de R2. Les exceptions sont **nommées**, jamais tacites. Exemple en vigueur : le lake de Peters (`GameTheory/SocialChoice/social_choice_lean_peters`), sur v4.32.1, verdict INTRINSIC de #7081.

## Appliquer la doctrine

| Geste | Ce qui est exigé |
|---|---|
| **Écrire un théorème** | `git grep` du résultat (nom et énoncé) dans les **autres** lakes d'abord. S'il existe, la première sortie est d'y renvoyer, la seconde de le prouver autrement **en le déclarant** (R4). Leçon de #23022, qui n'offrait que « porter » ou « documenter ». |
| **Créer un lake** | Dossier de la sous-série consommatrice (R1). Toolchain et rev du groupe canonique, entrée dans `ci_lakes.json`, jonction posée. |
| **Déplacer un lake** | Une PR par déplacement, avec preuve de préservation : théorèmes conservés, `python scripts/lean/count_code_sorry.py --json` inchangé, `lake build SUCCESS` après le déplacement, renvois des carnets et chemin de `ci_lakes.json` mis à jour. La notice d'attribution suit le code. Anti-régression : `.claude/rules/anti-regression.md`. |
| **Fusionner deux lakes** | Seulement au titre de R3. Le body de la PR cite la mesure : les imports croisés, ou les objets redéfinis des deux côtés. |
| **Garder deux preuves** | Renvois croisés dans les docstrings et note de comparaison publiée (R4). La maison canonique est nommée. Quand la question des droits se pose, elle tranche : la preuve sans dette de licence est canonique. |

## Organes

- `scripts/lean/lean_material_map.py` : la carte des lakes et de leurs consommateurs. L'inventaire de conformité y ajoutera deux colonnes, « site = consommateur » et « doublons déclarés ».
- L'organe de détection des doublons de théorèmes entre lakes (#24183, tranche T0) fera rougir un doublon non déclaré. Contrôle positif : Arrow et Sen.
- `scripts/lean/ci_lakes.json` et `lean-ci-matrix.yml` portent la CI ; `scripts/lean/setup_shared_mathlib.ps1` porte les jonctions.

## Historique

- #4362 : EPIC harmoniser, mutualiser, regrouper. Le levier « regrouper » est retiré le 2026-11-02 et remplacé par R1-R4.
- #4365 : regroupement GameTheory (fermée le 2026-08-14). Renversée le 2026-11-02 pour `game_theory_lean`, dont les libs redescendent dans leurs sous-séries.
- #17545 : redescente des lakes en sous-séries.
- #24183 : pilote GameTheory (organe T0, comparaison des deux preuves d'Arrow et de Sen, `lean_game_defs` contre `lean_game_defs_ext`, redescente et carte des lakes).
