# Provenance — GameTheory-15e Coalition Power SMT

## Source étudiante

| Champ | Valeur |
|---|---|
| Auteurs | Ilias Kalalou et Kaelan Grall |
| Dépôt | [jsboige/2026-Epita-Intelligence-Symbolique](https://github.com/jsboige/2026-Epita-Intelligence-Symbolique) |
| Projet | [`T1-PouvoirCoalition-IliasKalalou-KaelanGrall/`](https://github.com/jsboige/2026-Epita-Intelligence-Symbolique/tree/main/T1-PouvoirCoalition-IliasKalalou-KaelanGrall) |
| PR source | [#30](https://github.com/jsboige/2026-Epita-Intelligence-Symbolique/pull/30) |
| Commit étudiant final | [`5b22a9d787af2a2316764fe162cb5457fa546b46`](https://github.com/jsboige/2026-Epita-Intelligence-Symbolique/commit/5b22a9d787af2a2316764fe162cb5457fa546b46) |
| Commit de merge | [`34b3e1e3261a26d3f21396d148e122f8c1855260`](https://github.com/jsboige/2026-Epita-Intelligence-Symbolique/commit/34b3e1e3261a26d3f21396d148e122f8c1855260) |
| Licence source | MIT — `LICENSE` à la racine du dépôt source |
| Reproduction fraîche | 2026-09-06 : 135/135 tests T1 verts, suite isolée avec `PYTHONPATH` sur le dossier du projet |

## Geste intellectuel préservé

Ilias Kalalou et Kaelan Grall demandent si le pouvoir réel d'un acteur dans un vote se confond avec son poids nominal. Leur projet compare Shapley-Shubik, Banzhaf et Deegan-Packel, calcule les pivots et coalitions gagnantes minimales, puis confronte une énumération Python à un encodage SMT/Z3.

La soutenance permet une attribution plus précise :

- **Ilias Kalalou** présente la question de départ, les jeux pondérés, l'analyse de l'Assemblée nationale, les blocs et contre-factuels, un vote de censure réel et l'application ;
- **Kaelan Grall** présente les trois indices, l'encodage booléen Z3, l'énumération par clauses de blocage, la matrice d'axiomes, les contre-factuels de modes de scrutin, l'architecture et les limites.

Leur concession orale est conservée : les preuves SMT sont bornées à un nombre de joueurs fixé et les groupes politiques sont modélisés comme des acteurs unitaires.

## Sources croisées

La distillation a été confrontée à cinq surfaces :

1. code et historique Git complets du projet T1 sur `main` ;
2. PR étudiante #30 et son diff complet ;
3. revue professorale historique `EPITA-2026-IS-Review.md` ;
4. segment exact de soutenance, environ 00:34:06–00:49:10 ;
5. corpus CoursIA `GameTheory-15`, `15b`, `15c`, leurs modules Python et le module Lean `game_theory_lean/CooperativeGames/Shapley.lean`.

La revue historique utilise le mot « CEGIS ». Le code et la soutenance montrent plutôt du **bounded model checking** et de l'**énumération de modèles avec clauses de blocage** : aucune boucle candidat → contre-exemple → raffinement n'est présente. Le notebook CoursIA n'emploie donc pas le terme CEGIS.

## Transformation éditoriale CoursIA

Le notebook est une réécriture pédagogique autonome, pas une copie du paquet étudiant. CoursIA :

- resserre le parcours sur une seule lane scientifique : calcul indépendant ↔ SMT borné ↔ preuve Lean générale ;
- ajoute une hiérarchie explicite des garanties ;
- transforme les composants du projet en exemples progressifs exécutables dans un seul notebook ;
- ajoute trois exercices stubbés ;
- conserve un contrefactuel politique où une seule modification — l'agrégation des groupes de gauche — varie ;
- distingue explicitement les explications éditoriales postérieures de ce que les étudiants ont eux-mêmes soutenu.

Le théorème général d'unicité de Shapley et la formulation « calcul versus preuve » ont été explicités par l'enseignant pendant l'oral puis ancrés dans le corpus Lean de CoursIA. Ils ne sont pas attribués rétroactivement à Ilias Kalalou ou Kaelan Grall.

## Données politiques

Les effectifs de la XVIIe législature repris dans l'exemple proviennent de la table du projet étudiant, qui cite la page officielle des groupes de l'Assemblée nationale :

- [Assemblée nationale — Les groupes politiques](https://www.assemblee-nationale.fr/dyn/les-groupes-politiques)

Il s'agit d'effectifs stabilisés à l'automne 2024. Cette date fait partie du modèle : les effectifs parlementaires évoluent.

## Références scientifiques

- Shapley, L. S. & Shubik, M. (1954). *A Method for Evaluating the Distribution of Power in a Committee System*.
- Banzhaf, J. F. (1965). *Weighted Voting Doesn't Work: A Mathematical Analysis*.
- Deegan, J. & Packel, E. W. (1978). *A New Index of Power for Simple n-Person Games*.
- Dubey, P. & Shapley, L. S. (1979). *Mathematical Properties of the Banzhaf Power Index*.
- Tang, Y. & Lin, F. (2009). *Computer-aided Proofs of Arrow's and Other Impossibility Theorems* — référence méthodologique citée par le projet pour les preuves bornées.
- de Moura, L. & Bjørner, N. (2008). *Z3: An Efficient SMT Solver*.

## Limites et niveau de garantie

- L'énumération Python calcule exactement une instance finie, mais son coût est exponentiel.
- L'accord Python/Z3 est une cross-validation différentielle sur les jeux exécutés, pas une preuve universelle.
- `UNSAT` vaut pour l'espace et le nombre de joueurs encodés.
- Un modèle `SAT` suffit à réfuter une propriété universelle quand ses contraintes correspondent bien au domaine annoncé.
- La preuve Lean générale est un artefact distinct, vérifié par le noyau Lean dans CoursIA.
- Les groupes politiques sont supposés unitaires ; abstentions, dissidences et plausibilité des alliances sont hors modèle.
- Un vote réel unique ne mesure pas une fréquence de pivot.
- Les indices sont descriptifs dans leur modèle et ne constituent aucune recommandation politique.
