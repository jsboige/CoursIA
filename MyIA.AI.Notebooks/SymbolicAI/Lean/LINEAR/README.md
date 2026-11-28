# Sous-série LINEAR — l'algèbre linéaire d'Axler en marches Lean

Sous-série (11ᵉ, schéma canonique) de la série [SymbolicAI/Lean](../README.md), née de l'Epic
Origami [#24838](https://github.com/jsboige/CoursIA/issues/24838) (Fille 3.1 : les marches `.lean`,
Fille 3.2 : les carnets) : le socle d'algèbre linéaire exigé par `Lean-12` (sensibilité) et
`Lean-13` (Kochen-Specker/CHSH) — produits scalaires sur ℂ compris — avant que le capstone
`Lean-11c-Escalier-Algebre-Lineaire.ipynb` ne referme l'ascension dans la série principale.

Le plan des neuf carnets suit l'ordre d'Axler (*Linear Algebra Done Right*, 4e éd., déterminants
rejetés au dernier chapitre) :
[commentaire c.6928287873 de #24838](https://github.com/jsboige/CoursIA/issues/24838#issuecomment-6928287873).

## Parcours principal

| Carnet | Statut | Ce qu'on y apprend |
|---|---|---|
| [LINEAR-01-Espaces-Vectoriels-Lean.ipynb](LINEAR-01-Espaces-Vectoriels-Lean.ipynb) | présent | La marche 1 en carnets : espaces vectoriels, sommes, sommes directes (Axler 1.31-1.45), dimension finie, bases, critères de bonne taille et Grassmann (2.19-2.43) — **exécuté nativement** (kernel `lean4-wsl-linear`, lac [`linear_lean`](linear_lean/README.md)) ; exercices 1B.1-1B.2 résolus, quatre sorry-cibles documentées (empreinte honnête affichée) |
| [LINEAR-02-Applications-Lineaires-Lean.ipynb](LINEAR-02-Applications-Lineaires-Lean.ipynb) | présent | La marche 2 en carnets : espace des applications linéaires, composition, noyau/image, théorème du rang (3.21), inversibilité et isomorphismes — **exécuté nativement** (kernel `lean4-wsl-linear`) |

## Comment lire ce README

Les deux carnets présents se lisent **dans l'ordre** : LINEAR-01 pose le vocabulaire (espace vectoriel, somme directe, dimension, base) que LINEAR-02 réutilise tel quel pour les applications linéaires et le théorème du rang. Chacun s'exécute nativement, sans Python : le kernel `lean4-wsl-linear` et le lac [`linear_lean`](linear_lean/README.md) suffisent, et les sorties du compilateur Lean sont la preuve.

Les sept carnets restants (Fille 3.2, sur le compagnon amont `rkirov/linear-algebra-done-right-lean`,
Apache-2.0 avec attribution dans chaque carnet consommateur) sont **prévus, non écrits** : `LINEAR-03-Polynomes` (ch. 4),
`LINEAR-04-Valeurs-Propres` (ch. 5), `LINEAR-05-Produit-Scalaire` (ch. 6),
`LINEAR-06-Operateurs-Produit-Scalaire` (ch. 7), `LINEAR-07-Operateurs-Complexes` (ch. 8,
théorème spectral), `LINEAR-08-Formes-Canoniques` (ch. 9), `LINEAR-09-Trace-Determinant` (ch. 10,
en dernier — choix d'Axler assumé). Ils ne sont pas liés ici : un lien vers un carnet
inexistant est un lien mort.

Cette sous-série est le **prérequis** de `Lean-12` (sensibilité) et `Lean-13` (Kochen-Specker/CHSH) : le produit scalaire sur ℂ, qui n'arrive qu'au carnet prévu 05, est précisément ce qui manque pour les deux carnets amont. La montée reste donc incomplète tant que le chapitre 6 d'Axler n'est pas portage.

## Source, licence, archivage

- **Source unique** : Axler, *Linear Algebra Done Right*, 4e éd., Springer 2024, **CC BY-NC 4.0**,
  version du 30 octobre 2026 — copie archivée au gisement partagé
  `G:\Mon Drive\MyIA\IA\Bibliographie IA\Pedagogie-Proves\` (règle `bibliography-hygiene`).
- **Aucune ligne recopiée** des compagnons (`rkirov/linear-algebra-done-right-lean`, Apache-2.0
  déclaré dans son README amont ; `blanketism/Axler-Solutions`, sans licence déclarée) : consultés
  uniquement pour comparer les progressions, jamais vendus. Les carnets LINEAR-03 à 09 qui
  consommeront le compagnon amont porteront son attribution Apache-2.0 dans leur en-tête.
- Le lac [`linear_lean/`](linear_lean/README.md) distille l'ordre d'Axler, pas son texte :
  les définitions sont portées par les organes natifs de Mathlib, déclarés et cités.
- Les **exercices** du lac sont des sorry-cibles documentées (mandat user 2026-11-03) :
  baseline CI `4` (`exercice_1B_3`, `2A_13`, `2C_12`, `2C_13`), comptée par
  `scripts/lean/count_code_sorry.py`. Les carnets affichent l'empreinte honnête —
  `sorryAx` sur les cibles, axiomes standards sur les théorèmes du texte.
