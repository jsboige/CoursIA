# Dimension recherche — `R0` … `R3`

L'axe recherche ne dit **pas** ce qu'un carnet est difficile à faire : il dit
ce que le carnet **produit au-delà** de l'enseignement de la technique.

C'est un axe séparé, et il doit le rester : un carnet `D2` peut toucher un
problème ouvert, un carnet `D4` peut n'être qu'une technique établie bien
outillée.

## Le défaut que cet axe corrige

Jusqu'ici, le catalogue marquait un carnet « recherche » à partir de son
**chemin** :

```python
# generate_catalog.py -- _is_research_path
RESEARCH_DIR_KEYWORDS = {"research", "archive", "_archive", "_archives", "examples", "partner-course"}
```

Un carnet est donc « recherche » parce qu'il est **dans un dossier nommé
`research`** — jamais parce que son contenu pose une question. C'est
exactement le genre de qualification que l'EPIC [#24993](https://github.com/jsboige/CoursIA/issues/24993)
veut remplacer par une qualification **déclarée et justifiée**.

## Les quatre niveaux

| Niveau | Ce que le carnet produit | Critère de décision |
|---|---|---|
| `R0` | **Transmission** : il enseigne une technique établie. | Aucun protocole de mesure propre, aucune comparaison contrôlée, aucune question posée. |
| `R1` | **Outillage** : il construit un **instrument** — un jeu d'or annoté, un corpus, une métrique, un banc, un protocole — réutilisable par d'autres carnets. | Le produit est une **mesure** que l'on peut réutiliser ; le verdict, lui, est connu d'avance. |
| `R2` | **Exploration** : il pose une **question de mesure falsifiable** et y répond par une comparaison contrôlée (témoin, ablation, balayage) **dont le verdict n'est pas connu d'avance**. | On ne sait pas à l'avance ce que la mesure va dire ; le carnet le dit. |
| `R3` | **Front** : il affronte une **question ouverte**, ou un état de l'art non stabilisé — aucun témoin ne tranche, et le carnet assume de ne pas trancher. | Le carnet **n'a pas** de verdict. |

### `R1` et `R2` — le discriminant tient en une question

> *Le verdict était-il connu avant la mesure ?*

- S'il l'était (un témoin qui doit concorder, une méthode dont on connaît le
  comportement théorique), le carnet est `R1` : il **vérifie**, il outille.
- S'il ne l'était pas (le carnet ne sait pas à l'avance quelle famille de
  caractéristiques porte le modèle, ni si la régularisation fera ce que la théorie
  annonce), le carnet est `R2` : il **explore**.

C'est cette question, et non la présence d'un tableau de chiffres, qui
distingue les deux.

### `R3` est un cas particulier, et il est rare

`R3` ne veut pas dire « le carnet est difficile » ni « il utilise un algorithme
récent ». Il veut dire que **la question reste ouverte à la fin du carnet**.
Un carnet `R2` qui trouve son verdict reste `R2` — il a tranché. Un carnet qui
constate un résultat inattendu **et l'explique** reste `R2` ; il ne devient pas
`R3` parce que le résultat a surpris.

## Ce qui n'est pas un signal de recherche

| Signal | Pourquoi il ne suffit pas |
|---|---|
| Le chemin du carnet (`research/`, `examples/`) | c'est le défaut que cet axe remplace |
| Un mot-clé dans le markdown (`paradoxe`, `contre-intuitif`) | [#24292](https://github.com/jsboige/CoursIA/issues/24292) : 39 carnets touchés, **aucun** vrai cas — un cours de décision doit contenir des paradoxes *enseignés* |
| Un tableau de résultats | un témoin qui concorde est une vérification (`R1`), pas une exploration |
| Un algorithme « de pointe » | `word2vec` est un algorithme de 2013 ; ce qui compte est la question posée, pas la fraîcheur du modèle |
| La densité pédagogique ([#13410](https://github.com/jsboige/CoursIA/issues/13410)) | elle mesure ce qui est **donné**, pas ce qui est **découvert** |

## La qualification est déclarée, pas calculée

Chaque valeur `R` porte **une ligne de justification** qui cite la section du
carnet qui la fonde. L'organe
(`scripts/notebook_tools/curriculum_qualification.py`) refuse une entrée sans
justification, mais **ne calcule jamais** la valeur : un axe qui se déduirait
d'un scan serait un axe que le prochain scan invaliderait.

La série pilote (`NLP`) ne contient **aucun `R3`** : elle enseigne des
techniques établies (TAL, n-grammes, CRF, PCFG, HMM, IR, plongements,
classement de texte). Son composant « recherche » est de l'**exploration
contrôlée** (`R2`) et de l'**outillage** (`R1`), pas du front.

## Voir aussi

- [echelle-difficulte.md](echelle-difficulte.md) — l'autre axe.
- [manifest.json](manifest.json) — la donnée.
- [pilot-nlp.md](pilot-nlp.md) — la série pilote.
- [README.md](README.md) — l'organisation du répertoire et l'organe.
