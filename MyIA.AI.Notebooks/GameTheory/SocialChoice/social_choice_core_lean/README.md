# social_choice_core_lean

Maison canonique du **choix social formalisé** de CoursIA. Issue #24183 (tranche T3,
2026-11-08) : la lib `SocialChoice` descend du hub `game_theory_lean` vers
`GameTheory/SocialChoice/social_choice_core_lean`, à côté des carnets qui la citent
doctrine R1 — « le site d'un lake suit les carnets qui l'utilisent », validée par le
user le 2026-11-02.

## Contenu (modules FR/EN + umbrella)

| Module | Ce qu'il porte |
|---|---|
| `Basic` / `Framework` | Préférences, profils, fonctions de bien-être social (socle `Finset`/Mathlib) |
| `Arrow` | Théorème d'impossibilité d'Arrow — **preuve alternative déclarée** (port d'`asouther4/lean-social-choice`, Geanakoplos 2005 par pivot) |
| `Sen` | Théorème d'impossibilité de Sen (libéralisme minimal + Pareto) |
| `AMD` | Résultats d'existence type Arrow–Milgrom–Dummett |
| `Groves` | Mécanismes de Groves (incitations à révéler) |
| `MechanismDesign` | 32 théorèmes de design de mécanismes |
| `Voting` | Méthodes de vote et propriétés (21-22 théorèmes) |
| `SortedListCounting` | Combinatoire de comptage ordonné (lemmes techniques) |

Total mesuré au déplacement : **149 théorèmes, 178 définitions, 0 `sorry`** (CERTIFIED,
empreinte des blobs `d23a3651…` inchangée au `git mv`, 21 renommages R100).

## La preuve canonique d'Arrow vit ailleurs

Ce lake porte le **port d'asouther4** (preuve alternative déclarée, sans licence amont —
voir `NOTICE.md`). La **preuve canonique indépendante** (coalitions décisives, Lean core,
`Fin n`) vit dans `lean_game_defs/SocialChoice.lean`. La comparaison des deux
stratégies — axiomes atteints, longueur, généralité, ce que chacune enseigne — est
dans le carnet `../01b-Lean-SocialChoice-Formal.ipynb`.

## CI

Entrée `socialchoicecore` dans `scripts/lean/ci_lakes.json` : sorry-baseline 0,
`axiom-fail-on-sorry`, Mathlib au pin du hub d'origine (`db584cd6`).
