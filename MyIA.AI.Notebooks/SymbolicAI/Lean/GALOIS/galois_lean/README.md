# Problème inverse de Galois — M₂₃ groupe de Galois sur ℚ

Lake `galois_lean` : couche de preuve pour le notebook **[Lean-22](../GALOIS-01-Probleme-Inverse-M23-Python.ipynb)** (problème inverse de Galois), autour du groupe sporadique de Mathieu M₂₃.

## Contexte

Le préprint [arXiv:2608.08538](https://arxiv.org/abs/2608.08538) (Poonen et al., 9 août 2026) établit que **M₂₃ est un groupe de Galois sur ℚ** — clôture d'un programme de 40 ans. Le user a demandé de vérifier si la formalisation Lean était accessible avec notre bagage.

Deux énoncés, soigneusement distingués dans le notebook :

| Énoncé | Statut |
|--------|--------|
| M₂₃ est un groupe simple d'ordre 10 200 960 | **prouvé** (Lean, sorry-free) |
| M₂₃ est un **groupe de Galois sur ℚ** | **cité, non formalisé** (préprint ; Belyi absent de Mathlib) |

## Ce que ce lake contient

- **`Galois/M23Lean4Web.lean`** (fichier volumineux) : version single-file Lean4Web de la preuve M₂₃, *vendored* depuis l'amont [`KitaKen1/finite-simple-groups-lean`](https://github.com/KitaKen1/finite-simple-groups-lean) (Apache-2.0). Démontre `Sporadic.card_M23 : Nat.card M23 = 10200960` et `Sporadic.simple_M23 : IsSimpleGroup M23` par une **chaîne de stabilisateurs à certificats** (Schreier–Sims matérialisé) — pas `native_decide`, pas `sorry`. La simplicité passe par le stabilisateur de point (M₂₂ embarqué) + un certificat de conjugaison excluant le cas régulier d'ordre 23.
- **`Galois.lean`** : agrégateur racine — importe les **cinq** modules du lake (`Galois.M23Lean4Web` plus les deux paires FR/EN `AdicCompletionLocalRing` et `LowerRamificationGroup`), donc un point d'entrée unique qui porte la couche M₂₃ *et* la couche adic-complétion.
- **`Galois/*_en.lean`** : siblings i18n (#4980) de la couche adic-complétion — `AdicCompletionLocalRing_en` et `LowerRamificationGroup_en`. Le module vendu `M23Lean4Web` reste hors i18n (lib tierce, cf `lean-i18n`).

Le `lean_lib Galois` porte ``globs := #[`Galois.*]`` comme `@[default_target]`, ce qui auto-découvre tous les sous-modules — dont les siblings `_en`. **Forme bare-lib : historique, plus utilisable.** Elle avait été adoptée quand la forme glob déclenchait un quirk de trace *job-computation* de lake v4.31.0-rc1 (« some modules have bad imports ») ; le commentaire du `lakefile.lean` consigne que la forme glob est vérifiée SUCCESS à v4.33.0. Surtout, `check_en_built` (`scripts/lean/check_i18n_siblings.py`) ne lit que les `roots`/`globs` : un miroir `_en` importé depuis la racine serait signalé UNBUILT par la CI `lean-i18n-drift` alors même que `lake build` le compile.

## État

- **Toolchain** : `leanprover/lean4:v4.33.0` à la tête courante (cf `lean-toolchain`, qui fait foi ; migration v4.32.1 → v4.33.0 posée par `26f6bc44ee`, #14953 — `git log --follow` sur `lean-toolchain` désigne ce commit, pas le renommage `88edc37b4d` qui n'a que déplacé le fichier). Historique : `v4.31.0-rc1` → v4.32.1 (#11325/#11256), puis v4.33.0. La preuve amont `M23Lean4Web.lean` reste pinned à sa version d'origine — un bump toolchain ne touche pas le vendored.
- **Mathlib** : `db584cd6d46c92f209a44c0f1c829460d327499d` (v4.33.0), en accord entre `lakefile.lean:10-11` et `lake-manifest.json` — les deux fichiers qui font foi. Les revs `d568c8c` (pin v4.31.0-rc1) et du bump 4.32.1 sont **historiques** ; aucun ne décrit l'état courant.
- **Sorry** : **0** (mode `real`, comptage Lean-aware) — 0 `sorry` tactique, 0 `native_decide`, 0 `axiom` déclaré
- **Axiomes** : `#print axioms Sporadic.card_M23` / `simple_M23` → `{propext, Classical.choice, Quot.sound}` = whitelist §B
- **Build** : matrice `lean-ci-matrix.yml` (job `galois_lean`) depuis la suppression du wrapper `lean-galois.yml` (`145808a50d`, #23011 — #13751 item 4). Dernier run **SUCCESS** connu : 2026-10-31T18:36:51Z sur `88edc37b4d`, au pin v4.33.0 (le lake y était déjà migré par `26f6bc44ee`) — c'était le **dernier run du wrapper**, avant la migration du 2026-11-01 ; aucun fichier du lake n'a changé sur `main` depuis, le job matrice n'a donc pas encore tourné sur ce lake (`git log 145808a50d..origin/main -- …/galois_lean/` est vide). Le chiffre de 1324 jobs reste **historique** : il date du pin v4.31.0-rc1 et n'a pas été re-mesuré depuis.
- **Dépendances** : Mathlib 4 uniquement — 8 imports, dont 7 `Mathlib.GroupTheory.*` et `Mathlib.Algebra.Group.Subgroup.Finite` (`M23Lean4Web.lean:32-39`)

## Pourquoi réutiliser l'amont plutôt que réécrire

Per `sota-not-workaround` : refaire une échelle de petits groupes à côté d'une preuve M₂₃ déjà faite (sorry-free, Apache-2.0) serait la **réimplémentation-jouet** interdite. On réutilise l'amont avec attribution. La partie *from-scratch* du lake (notebook Lean-22) porte sur la **pédagogie du problème inverse de Galois** (vérification indépendante du polynôme de degré 23 via sympy, système de Steiner S(4,7,23), vocabulaire SGA1), pas sur la réémergence de la preuve de groupe.

## Attribution

- Amont : Copyright (c) 2026 Kenta. — licence Apache-2.0. Chaque fichier dérivé préserve l'en-tête amont + la note *« AI usage: Developed with assistance from Claude Code (Fable 5, 1M context, high reasoning) »*.
- Le notebook Lean-22 documente explicitement que l'identification `23T5 = M23` (groupe de Galois) requiert Magma propriétaire et n'est **pas** reproduite — seule la vérification du polynôme (degré, irréductibilité, discriminant) est exécutable en sympy.

## Voir aussi

- [GROTH-02-Tribut-Python](../../GROTH/GROTH-02-Tribut-Python.ipynb) — hommage comparable (prouve ce qu'il annonce)
- `grothendieck_lean` — angle SGA1 (π₁ étale, existence de Riemann) pour le chaînon-pont vers la réalisation galoisienne
- EPIC i18n #4980 : siblings `_en` **livrés** pour la couche adic-complétion (`AdicCompletionLocalRing_en`, `LowerRamificationGroup_en`) ; le module vendu `M23Lean4Web` en est exclu par la règle (lib tierce).
