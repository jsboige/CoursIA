---
paths: "{**/*.lean,scripts/lean/**}"
---

# Doctrine des lakes Lean — le site suit le consommateur

Référence complète : [lean-lakes-doctrine.md](../../docs/reference/lean-lakes-doctrine.md) (validée par le user le 2026-11-02, EPIC #4362). Cette règle n'ajoute rien à la doctrine : elle la charge quand la session touche un lake, plutôt que de la répéter dans la surface auto-chargée de `CLAUDE.md`.

## Les quatre règles

- **R1 — Le site suit le consommateur.** Un lake vit dans le dossier de la (sous-)série dont les carnets l'importent. Quand plusieurs séries le citent, il vit chez celle qui porte son théorème phare, et les autres renvoient vers lui.
- **R2 — Le partage ne passe plus par la fusion.** Le disque se partage par jonction Mathlib (`scripts/lean/setup_shared_mathlib.ps1`, groupe (toolchain, rev) canonique), la CI par une entrée de `scripts/lean/ci_lakes.json`. Économiser du disque ou des jobs **n'est plus un motif de fusion**.
- **R3 — On ne fusionne que par les imports.** Deux lakes fusionnent quand l'un importe l'autre, ou quand ils redéfinissent les mêmes objets (même `Preference`, même `SWF`). Une théorie distincte reste un lake distinct : la clause anti-god-lake est maintenue.
- **R4 — Un résultat a une maison canonique ; un doublon se déclare.** Deux preuves d'un même résultat coexistent si elles sont déclarées comme preuves alternatives : renvois croisés dans les deux docstrings, et note de comparaison (axiomes atteints, longueur, généralité, ce que chaque stratégie enseigne). Un doublon non déclaré est un défaut ; la notice d'attribution d'un code tiers vit à côté du code.

## Avant d'écrire un théorème

`git grep` du résultat (nom et énoncé) dans les **autres** lakes d'abord. S'il existe : la première sortie est d'y renvoyer, la seconde de le prouver autrement **en le déclarant** (R4).

## Geste et preuve attendue

| Geste | Ce qui est exigé |
|---|---|
| Créer un lake | Dossier de la sous-série consommatrice (R1), toolchain et rev du groupe canonique, entrée dans `ci_lakes.json`, jonction posée |
| Déplacer un lake | Une PR par déplacement : théorèmes conservés, `python scripts/lean/count_code_sorry.py --json` inchangé, `lake build` vert après le déplacement, renvois des carnets et chemin de `ci_lakes.json` à jour ; la notice d'attribution suit le code |
| Fusionner deux lakes | Seulement au titre de R3 ; le body de la PR cite la mesure — imports croisés, ou objets redéfinis des deux côtés |
| Garder deux preuves | Renvois croisés dans les docstrings et note de comparaison (R4) ; la maison canonique est nommée |

La doctrine suppose la convergence Mathlib : un lake hors du groupe canonique perd la jonction. Les exceptions sont **nommées**, jamais tacites (exemple en vigueur : `GameTheory/SocialChoice/social_choice_lean_peters`, v4.32.1, verdict INTRINSIC de #7081).

Organes : `scripts/lean/lean_material_map.py` porte la carte des lakes et de leurs consommateurs ; l'inventaire de conformité y ajoute « site = consommateur » et « doublons déclarés ».