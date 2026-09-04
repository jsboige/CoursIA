# Ledger #12204 — Chantier 1 ICT, tranche audit-froid : trois labels par opération, quatre entrées tombées

**Statut** : tranche de l'EPIC #12204 « Chantier 1 — La table des opérations ». Provisionnée par le steering ai-01 du 2026-08-22T20:54Z (« audit froid : faire tomber les entrées qui ne survivent pas »), protocole fixé par la revue extérieure du 2026-08-22 en commentaire d'issue.

**Lane** : `myia-po-2025:CoursIA` (claim paths-scoped, [issuecomment-5383064486](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-5383064486)).
**Date** : 2026-08-23. **Base** : `origin/main` `1d021b4fe`.

## Le protocole — trois labels orthogonaux

Repris de la revue extérieure (commentaire #12204, 2026-08-22) :

| axe | valeurs | ce qu'il mesure |
|---|---|---|
| **provenance** | `RAPPORTE` / `FIRSTHAND` | ai-je lu la source, ou une lecture de la source ? |
| **attestation** | `1 attestation` / `2+ attestations` | le seuil d'admission de l'EPIC (§1 du body) |
| **force** | `empirique` / `exhaustif` / `Lean-formel` | ce que vaut la preuve, pas ce qu'elle couvre |

Une opération `FIRSTHAND / 1 attestation / exhaustif` et une opération `RAPPORTE / 2+ attestations / empirique` ne sont pas comparables sur un axe unique.

## La table labellisée — 14 opérations

Labels établis à partir : (a) des vérifications A3 firsthand ([`12204-ict-chantier-1-a3.md`](12204-ict-chantier-1-a3.md), po-2026) ; (b) des mesures de ce cycle (§Preuves ci-dessous) ; (c) du corps de la revue extérieure pour les quatre contestées. `RAPPORTE` partout où ce cycle n'a pas relu la source firsthand — c'est le sens même du label.

| # | Opération | provenance | attestation | force | Verdict |
|---|---|---|---|---|---|
| 1 | Recoordonner | FIRSTHAND (A2, #13956) | 2+ (Sudoku-13, `conway_lean`, MGS-21) — les trois tiennent | empirique avec cause mesurée + Lean-formel kernel-décidable | **TABLE** — confirmée. Dette reformulée : les trois attestations sont des post-mortems — une théorie du « bon » changement choisirait la représentation avant de payer l'échec ([A2](12204-ict-chantier-1-a2.md)) |
| 2 | Abstraire à dette bornée | RAPPORTE | **1** (Kroer-Sandholm externe) | n/a | **⬇ FILE D'ATTENTE** — voir §Tombée 1 |
| 3 | Quotienter / fibrer | FIRSTHAND (A3 + ce cycle) | **1 locale** (Lean-21b) | empirique-notebook | **⬇ FILE D'ATTENTE** — voir §Tombée 4 |
| 4 | Décomposer localement | RAPPORTE | 2+ (ICT-15d jouet, Hashlife, EPITA) | empirique | **TABLE** avec dette ouverte (qui décide des bords) — grain A4 |
| 5 | Recoller | RAPPORTE | **1 + 1 lecture** | Lean-formel (de Finetti) | **⬇ FILE D'ATTENTE** — voir §Tombée 3 |
| 6 | Réparer localement sous garantie | RAPPORTE | **1** (Sandholm seul) | n/a | **⬇ FILE D'ATTENTE** — voir §Tombée 2 |
| 7 | Engendrer un témoin | FIRSTHAND (ce cycle) | 2+ (Sudoku-13, `conway_lean`, GT-16b #12259) | empirique + Lean-formel | **TABLE** — la mieux attestée du dépôt. GT-25 #12395 (translateur Life) renforcera la ligne quand elle quittera la file CI — non comptée tant qu'OPEN |
| 8 | Certifier | FIRSTHAND (ce cycle) | 2+ (22 lakes) | Lean-formel | **TABLE** — 18/22 lakes à 0 sorry réel (mesuré §P3) |
| 9 | Élargir l'espace | FIRSTHAND (A3) | **2** (`planning_lean` Admissibility.lean:50 + SW-14 #12263) | Lean-formel + empirique | **TABLE** — promotion mesurée §Tombées (gain) |
| 10 | Concevoir la règle | FIRSTHAND (ce cycle) | 2+ (GT-16b #12259, GT-20 #12303, SC-27 #12265) | empirique | **TABLE** — le mécanisme comme variable, trois familles |
| 11 | Descendre sous budget | RAPPORTE | 1 (à confirmer) | n/a | en constitution — statuer en A6 |
| 12 | Composer des regards | FIRSTHAND (ce cycle) | 2+ (GT-21 #12245 + Loi III) | empirique-notebook | en constitution — **candidate forte**, voir §Gain |
| 13 | Traverser un mur | RAPPORTE | 1 (GT-24 #12364, 576/576) | empirique | en constitution — statuer en A6 |
| 14 | Agréger un collectif | RAPPORTE | 1 (Shapley `game_theory_lean`) | Lean-formel | en constitution — statuer en A6 |

## Les quatre tombées (décisions de la revue extérieure, appliquées)

**Tombée 1 — Op 2 « Abstraire à dette bornée » → FILE D'ATTENTE.**
Soutenue surtout par Kroer-Sandholm, **externe** tant que sa distillation (#12208) n'a pas atterri (vérifié ce cycle : #12208 OPEN, non mergée). `MechanismDesign.lean` n'est pas une seconde attestation de *bounded abstraction* : il atteste un mécanisme (op 10), pas une borne d'abstraction. → `RAPPORTE / 1 attestation`.

**Tombée 2 — Op 6 « Réparer localement sous garantie » → FILE D'ATTENTE.**
Une seule famille (Sandholm). Le critère §1 de l'EPIC est mécanique : une attestation ⇒ file d'attente, pas la table.

**Tombée 3 — Op 5 « Recoller » → FILE D'ATTENTE (1 attestation + 1 lecture).**
La mention « mauvais recollement → déviation adversariale » (Brown-Sandholm) est **notre lecture structurelle** du safe subgame solving, pas un théorème Čech ni une attestation. C'est le défaut exact qui a coulé la première tentative ICT-15d : nommer le cadre mathématique avant de posséder les transports. La ligne reste dans la table comme **lecture**, étiquetée comme telle. De Finetti reste la seule attestation (1).

**Tombée 4 — Op 3 « Quotienter / fibrer » → FILE D'ATTENTE.**
A3 a établi firsthand que `teorth/pfr` est **externe au dépôt** (find + grep : 0). Ce cycle vérifie que la contrepartie locale est arrivée : **Lean-21b MERGED** (#12252, 2026-08-22T12:57Z, « 3 primitives PFR + tests de limite »). C'est une vraie attestation locale — mais **une seule** : parler de « primitive transversale » exige un **second substrat**. → `FIRSTHAND / 1 attestation locale / empirique-notebook`.

## Deux gains de mesure (le froid fait tomber ET remonter)

**Gain 1 — Op 9 « Élargir l'espace » passe à 2 attestations.**
A3 (firsthand, po-2026) : `planning_lean/Planning/Admissibility.lean:50` — `relaxed_plan_admissible : reaches π s g → reachesR π s g` = `P_reel ⊆ P_relache` exactement. Ce cycle : **SW-14-Python-Coup-Ontologique** (#12263 MERGED) exécute l'élargissement du vocabulaire OWL (extension η) avec témoin = diff de triplets + verdict SHACL + delta d'inférences. Deux substrats indépendants (Lean/planning vs Python/ontologie), même loi de monotonie. L'op 9 est la première opération **promue par la mesure** de cette Epic.

**Gain 2 — Loi III « les deux espèces de flèches » gagne sa seconde attestation.**
Le body dit : « attestée une fois » (transformation vs morphisme, swap ordinal). **GT-21-Deux-Espèces-de-Flèches** (#12245 MERGED, notebook vérifié sur le disque ce cycle) pose le théorème fini transformation-vs-morphisme. La Loi III passe à 2 attestations ; le verdict de grade §3 du body (« deux lois attestées deux fois, une une fois ») devient **trois lois attestées deux fois** — sans changer la conclusion (toujours pas un grade A).

**Contrepartie — Loi I « obstruction abstraite → témoin exploitable » retombe à 1 attestation.**
Elle citait de Finetti **et** Brown-Sandholm comme deux attestations. La Tombée 3 requalifie Brown-Sandholm en lecture structurelle → la Loi I n'a plus que de Finetti (1). Le grade §3 doit être révisé en conséquence : **Loi I : 1 · Loi II : 2 · Loi III : 2**.

## Preuves de ce cycle (firsthand, reproductibles)

**P1 — #12208 (distillation Kroer-Sandholm) non atterrie** : `gh pr list --state all --search 12208` → aucune PR de livraison ; issue ouverte.

**P2 — Lean-21b merged** : `gh pr view 12252` → `MERGED 2026-08-22T12:57:43Z`, fichier `Lean-21b-PFR-Primitives-Transportables.ipynb`.

**P3 — sorry réels sur les lakes** (instrument canonique, base worktree `1d021b4fe`) :

```text
$ python scripts/lean/count_code_sorry.py --json
lakes porteurs de sorry reel: 4/22
  game_theory_lean: 1 · decision_theory_lean: 2 · conway_lean: 1 · knot_lean: 13
```

→ 18/22 lakes à 0 sorry réel : l'op 8 « Certifier » est attestée au pluriel, la dette est concentrée (knot_lean porte 13/17).

**P4 — GT-21 sur le disque** : `GameTheory-21-Deux-Especes-de-Fleches.ipynb` présent (livré #12245, merged — commit `c7bc85f2d` tête de main à la base du worktree).

**P5 — SW-14 sur le disque, exécuté** : 5/5 cellules code `execution_count 1..5`, outputs présents (vérifié ce cycle lors de la fermeture #12234).

**P6 — GT-16b AMD lu ce cycle** : générateur / vérificateur séparé / témoin d'impossibilité — op 10 attestée, avec la réserve de cohérence DSIC consignée sur #12211 (issuecomment-5383043049).

## Honnêteté méthodologique

- Les labels `FIRSTHAND` ci-dessus renvoient aux preuves P1-P6 ou à A3 ; tout le reste est `RAPPORTE` (issu du body de l'EPIC ou de la revue, non relu ce cycle). Les tranches A2/A4 restent le chemin pour convertir les `RAPPORTE` restants.
- Cette tranche **applique** des décisions déjà tranchées par la revue extérieure pour les 4 tombées ; elle **mesure** les 2 gains et la contrepartie Loi I. Elle ne crée aucune règle nouvelle (cf `audit-cross-source-distillation` règle 2 : grain au cas par cas).
- `RAPPORTE` n'est pas un déshonneur : c'est l'état honnête d'une table dont la fonction première (§6 du body) est précisément de distinguer le vérifié du rapporté.

## Effet demandé sur le body de l'EPIC

Le body §2 doit refléter : op 2, 5, 6 → file d'attente ; op 3 → file d'attente (1 attestation locale) ; mention Brown-Sandholm (op 5) → lecture structurelle ; §3 verdict de grade → Loi I : 1 · Loi II : 2 · Loi III : 2. L'édition du body est posée en commentaire de livraison sur l'issue (l'EPIC reste la source de vérité ; ce ledger en est la preuve).

## Références

- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · tranches : A3 ([ledger](12204-ict-chantier-1-a3.md), PR #12293) · audit-froid (ce fichier)
- Revue extérieure (protocole + 4 contestations) : commentaire #12204 du 2026-08-22
- Steering : ai-01 2026-08-22T20:54Z ([DISPATCH→inbox] dashboard workspace-CoursIA)
- Précédent de format : [`3801-sota-axe2.md`](3801-sota-axe2.md)
