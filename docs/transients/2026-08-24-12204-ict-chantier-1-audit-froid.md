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
| 2 | Abstraire à dette bornée | FIRSTHAND (réconciliation 04/10) | **2 candidates** (Kroer-Sandholm externe + GT-19 #12267 locale mesurée, enregistrée §Tranche réconciliation 04/10) | empirique-notebook (source théorique externe) | en constitution — 2ᵉ attestation candidate enregistrée ; promotion à statuer par A7 (indépendance par le stimulus à trancher, précédent op 3 c.1308 : GT-19 cite Kroer-Sandholm et naît du même voyage de digestion #12229) |
| 3 | Quotienter / fibrer | FIRSTHAND (A3 + ce cycle) | **1 locale** (Lean-21b) | empirique-notebook | **⬇ FILE D'ATTENTE** — voir §Tombée 4 |
| 4 | Décomposer localement | FIRSTHAND (A4, #14453) | 2+ recensées : Hashlife (Lean-formel, non-jouet) + ICT-15d (empirique jouet, partition avouée) + EPITA (empirique, identification restaurée) | Lean-formel + empirique | **TABLE** — confirmée. Dette reformulée en bipartition : la preuve décide des bords côté Hashlife (`padCenter2_margin_ge_jumpReach`), l'expérimentateur les choisit sans théorie côté ICT-15d ([A4](12204-ict-chantier-1-a4.md)) |
| 5 | Recoller | RAPPORTE | **1 + 1 lecture** | Lean-formel (de Finetti) | **⬇ FILE D'ATTENTE** — voir §Tombée 3 |
| 6 | Réparer localement sous garantie | FIRSTHAND (réconciliation 04/10) | **2** (Sandholm externe + Search-03f #19013 MERGED 2026-10-04, convention op 7 remplie — comptée dès merge) | empirique-notebook, substrat indépendant | en constitution — 2ᵉ attestation livrée (LPA\*, 0 mention de Sandholm : indépendance par construction) ; promotion TABLE à statuer par la revue (§Tranche réconciliation 04/10) |
| 7 | Engendrer un témoin | FIRSTHAND (ce cycle) | 2+ (Sudoku-13, `conway_lean`, GT-16b #12259) | empirique + Lean-formel | **TABLE** — la mieux attestée du dépôt. GT-25 #12395 (translateur Life) renforcera la ligne quand elle quittera la file CI — non comptée tant qu'OPEN |
| 8 | Certifier | FIRSTHAND (ce cycle) | 2+ (22 lakes) | Lean-formel | **TABLE** — 18/22 lakes à 0 sorry réel (mesuré §P3) |
| 9 | Élargir l'espace | FIRSTHAND (A3) | **2** (`planning_lean` Admissibility.lean:50 + SW-14 #12263) | Lean-formel + empirique | **TABLE** — promotion mesurée §Tombées (gain) |
| 10 | Concevoir la règle | FIRSTHAND (ce cycle) | 2+ (GT-16b #12259, GT-20 #12303, SC-27 #12265) | empirique | **TABLE** — le mécanisme comme variable, trois familles |
| 11 | Descendre sous budget | FIRSTHAND (A6 + c.1208) | **1 + 1 en instance** (`mimo_lean/Descent.lean` — thèse op 11 explicite, sorry-free ; Search-11d #16392 — comptée dès merge, convention op 7) | Lean-formel + empirique | en constitution — 2ᵉ attestation livrée sur substrat indépendant (c.1208) ; promotion TABLE à statuer par A7 |
| 12 | Composer des regards | FIRSTHAND (ce cycle + A6) | **2 directes** (GT-21 #12245 jeux 2×2 + Search-12a #16426 gridworld pondéré — comptée dès merge, convention op 7) | empirique-notebook ×2, substrats indépendants | en constitution — 2ᵉ attestation directe livrée ; promotion TABLE à statuer par la revue (witness form connu : paire incompatible exhibée, Search-12a §5) |
| 13 | Traverser un mur | FIRSTHAND (A6 + c.1216) | **2 directes** (GT-24 #12364 MERGED + Search-13a #16438 pavage hexagonal chemins certifiés — comptée dès merge, convention op 7) | empirique-notebook ×2, substrats indépendants | en constitution — 2ᵉ attestation directe livrée ; promotion TABLE à statuer par la revue (witness form connu : distinction épaisseur m_path / largeur m + test négatif morphisme/percement, Search-13a §8) |
| 14 | Agréger un collectif | FIRSTHAND (A6 + ce cycle) | **2** (`Shapley.lean:614-634` Möbius/Harsanyi sorry-free + SC-06 Python exécuté, PR ce cycle) | Lean-formel + empirique | **TABLE** — promotion mesurée §Gain 3 (même pattern que l'op 9) ; GaleShapley reste exclu (appariement ≠ agrégation) |

## Les quatre tombées (décisions de la revue extérieure, appliquées)

**Tombée 1 — Op 2 « Abstraire à dette bornée » → FILE D'ATTENTE.**
Soutenue surtout par Kroer-Sandholm, **externe** tant que sa distillation (#12208) n'a pas atterri (vérifié ce cycle : #12208 OPEN, non mergée). `MechanismDesign.lean` n'est pas une seconde attestation de *bounded abstraction* : il atteste un mécanisme (op 10), pas une borne d'abstraction. → `RAPPORTE / 1 attestation`.

**Tombée 2 — Op 6 « Réparer localement sous garantie » → FILE D'ATTENTE.**
Une seule famille (Sandholm). Le critère §1 de l'EPIC est mécanique : une attestation ⇒ file d'attente, pas la table.

**Tombée 3 — Op 5 « Recoller » → FILE D'ATTENTE (1 attestation + 1 lecture).**
La mention « mauvais recollement → déviation adversariale » (Brown-Sandholm) est **notre lecture structurelle** du safe subgame solving, pas un théorème Čech ni une attestation. C'est le défaut exact qui a coulé la première tentative ICT-15d : nommer le cadre mathématique avant de posséder les transports. La ligne reste dans la table comme **lecture**, étiquetée comme telle. De Finetti reste la seule attestation (1).

**Tombée 4 — Op 3 « Quotienter / fibrer » → FILE D'ATTENTE.**
A3 a établi firsthand que `teorth/pfr` est **externe au dépôt** (find + grep : 0). Ce cycle vérifie que la contrepartie locale est arrivée : **Lean-21b MERGED** (#12252, 2026-08-22T12:57Z, « 3 primitives PFR + tests de limite »). C'est une vraie attestation locale — mais **une seule** : parler de « primitive transversale » exige un **second substrat**. → `FIRSTHAND / 1 attestation locale / empirique-notebook`.

## Trois gains de mesure (le froid fait tomber ET remonter)

**Gain 1 — Op 9 « Élargir l'espace » passe à 2 attestations.**
A3 (firsthand, po-2026) : `planning_lean/Planning/Admissibility.lean:50` — `relaxed_plan_admissible : reaches π s g → reachesR π s g` = `P_reel ⊆ P_relache` exactement. Ce cycle : **SW-14-Python-Coup-Ontologique** (#12263 MERGED) exécute l'élargissement du vocabulaire OWL (extension η) avec témoin = diff de triplets + verdict SHACL + delta d'inférences. Deux substrats indépendants (Lean/planning vs Python/ontologie), même loi de monotonie. L'op 9 est la première opération **promue par la mesure** de cette Epic.

**Gain 2 — Loi III « les deux espèces de flèches » gagne sa seconde attestation.**
Le body dit : « attestée une fois » (transformation vs morphisme, swap ordinal). **GT-21-Deux-Espèces-de-Flèches** (#12245 MERGED, notebook vérifié sur le disque ce cycle) pose le théorème fini transformation-vs-morphisme. La Loi III passe à 2 attestations ; le verdict de grade §3 du body (« deux lois attestées deux fois, une une fois ») devient **trois lois attestées deux fois** — sans changer la conclusion (toujours pas un grade A).

**Contrepartie — Loi I « obstruction abstraite → témoin exploitable » retombe à 1 attestation.**
Elle citait de Finetti **et** Brown-Sandholm comme deux attestations. La Tombée 3 requalifie Brown-Sandholm en lecture structurelle → la Loi I n'a plus que de Finetti (1). Le grade §3 doit être révisé en conséquence : **Loi I : 1 · Loi II : 2 · Loi III : 2**.

**Gain 3 — Op 14 « Agréger un collectif » passe à 2 attestations.**
La 1ʳᵉ (A6) : `Shapley.lean:614-634` — `Mobius.mobiusCoeff` / `Mobius.mobiusReconstruction`, l'inversion de Möbius sur le treillis des coalitions, sorry-free (0 `sorry` réel mesuré : l'unique occurrence du mot dans le fichier est de la prose, ligne 1260). Cette livraison : **SC-06 — Möbius, agrégation, pouvoir, manipulation** (`MyIA.AI.Notebooks/GameTheory/SocialChoice/06-Mobius-Aggregation-Pouvoir-Manipulation.ipynb`, PR ce cycle) exécute le miroir Python exact de ces deux définitions — reconstruction vérifiée par exécution sur les 16 coalitions de `[6;4,3,2,1]` (le re-test `[8;5,4,3,2,1]` est posé en exercice, non exécuté) — puis dérive la valeur de Shapley par les dividendes **et** par énumération des 24 ordres d'entree (deux voies indépendantes, écart 5.55e-17), mesure l'écart poids/pouvoir (Banzhaf ; dummy du Luxembourg, Conseil 1958) et instancie le témoin de Gibbard-Satterthwaite sur un Borda à électeurs pondérés. Deux substrats indépendants (Lean/preuve vs Python/exécution), même loi de décomposition en dividendes de Harsanyi. L'op 14 quitte « en constitution » et rejoint l'op 9 dans les promotions par la mesure.

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

- Les labels `FIRSTHAND` ci-dessus renvoient aux preuves P1-P6, à A3 ou à A4 ; tout le reste est `RAPPORTE` (issu du body de l'EPIC ou de la revue, non relu ce cycle). Les conversions A2 (op 1) et A4 (op 4) sont livrées ; les `RAPPORTE` restants (ops 2, 5, 6) sont tous trois tombés en file d'attente (§Tombées 1-3) et n'ouvrent plus de tranche de conversion.
- Cette tranche **applique** des décisions déjà tranchées par la revue extérieure pour les 4 tombées ; elle **mesure** les 2 gains et la contrepartie Loi I. Elle ne crée aucune règle nouvelle (cf `audit-cross-source-distillation` règle 2 : grain au cas par cas).
- `RAPPORTE` n'est pas un déshonneur : c'est l'état honnête d'une table dont la fonction première (§6 du body) est précisément de distinguer le vérifié du rapporté.

## Effet demandé sur le body de l'EPIC

Le body §2 doit refléter : op 2, 5, 6 → file d'attente ; op 3 → file d'attente (1 attestation locale) ; mention Brown-Sandholm (op 5) → lecture structurelle ; §3 verdict de grade → Loi I : 1 · Loi II : 2 · Loi III : 2. L'édition du body est posée en commentaire de livraison sur l'issue (l'EPIC reste la source de vérité ; ce ledger en est la preuve).

## Tranche A6 (2026-09-07, po-2027:CoursIA-2) — statuer sur les quatre en constitution + file d'attente

Mandat §4bis : « A6 est donc une décision, plus une enquête. » Vérifications firsthand ce cycle :

**Op 11 — FIRSTHAND, 1 attestation.** `SymbolicAI/Lean/mimo_lean/Descent.lean` (+ sibling `Descent_en.lean`) : `descent_flips_le_barrier` (l.110 — décroissance stricte `hstrict` + barrière de confinement `hbarrier`) et théorème de terminaison sous plafond de flips (l.144). Le fichier se déclare lui-même « La thèse du chantier (opération 11, "descendre sous budget") » (l.148), et y consigne la dissociation-vs-échec — la dette du body. 0 `sorry` (grep direct + cohérent avec P3 : mimo_lean hors des 4 lakes porteurs). **Verdict : reste en constitution** — une seule attestation.

**Op 12 — décision : promotion REFUSÉE.** La table disait « 2+ (GT-21 + Loi III) ». Mesuré : la seconde attestation de la Loi III **est GT-21 lui-même** (§Gain 2) — compter GT-21 et « Loi III » comme deux attestations de l'op 12 est un double comptage du même artefact. Test d'une 2ᵉ attestation directe : `ICT-34-BancRecollementLectures.ipynb` (candidat naturel) porte recollement×26 mais forward/backward ×0 — c'est un banc d'op 5 (Recoller), pas une composition de regards play-forward/coplay-backward. **Verdict : reste en constitution, candidate forte confirmée** — première promotion quand une seconde instantiation directe atterrira.

**Op 13 — FIRSTHAND, 1 attestation.** PR #12364 MERGED (2026-08-22T22:45:49Z) ; `GameTheory-24-Chemin-Minimal-Robinson-Goforth.ipynb` sur disque : chambres×35, swaps×17, mur×12, 576×7 — le chemin minimal à travers le mur Robinson-Goforth est bien l'objet exécuté. Le compagnon `GameTheory-24b-Chemin-Minimal-Temoins-Impossibilite.ipynb` renforce la forme du témoin (impossibilité), mais c'est le **même substrat** — pas une seconde attestation indépendante. **Verdict : reste en constitution.**

**Op 14 — FIRSTHAND, 1 attestation.** `game_theory_lean/CooperativeGames/Shapley.lean:614-634` : namespace `Mobius`, `mobiusCoeff` (dividende de Harsanyi), `mobiusReconstruction` (`G = Σ_{T≠∅} a_T • u_T`) — la loi « Möbius sur le treillis des coalitions » attestée Lean-formel, sorry-free dans le fichier (le 1 sorry réel du lake mesuré en P3 est ailleurs). Réserve tranchée : `StableMarriage/GaleShapley.lean` n'est **pas** une 2ᵉ attestation — l'appariement stable n'est pas l'agrégation de coalitions sur le treillis. **Verdict : reste en constitution.**

**File d'attente — point fixe.** Second usage de Knaster-Tarski : `git grep -il knaster -- "*.lean"` → `argumentation_lean/Argumentation.lean` + `Argumentation/Characteristic.lean` (+ sibling `_en`) — un seul locus substantiel après dédoublonnage FR/EN (racine et module du même lake). Pas de second usage indépendant atterri : la promotion « dès le second usage » reste en attente.

**Bilan A6** : quatre opérations statuées, zéro promotion, zéro descente. La table reste à **6 opérations en TABLE** (1, 4, 7, 8, 9, 10), **4 en file d'attente** (2, 3, 5, 6), **4 en constitution — toutes quatre FIRSTHAND désormais**. Reste **A7** (relecture froide : la table est-elle un catalogue ? une quatrième loi est-elle apparue ?) — dernier grain.

## Tranche c.1208 (2026-09-16, po-2026:CoursIA-2) — op 11 : 2ᵉ attestation livrée (PR #16392)

**Op 11 — FIRSTHAND (ce cycle), 2ᵉ attestation sur substrat indépendant.** `Search/Part1-Foundations/Search-11d-Descente-Sous-Budget.ipynb` (série Search, Python stdlib, exécuté papermill, 0 erreur) : knapsack 0/1, potentiel Φ = −valeur, voisinage bit-flip, barrière = borne LP relaxée, budget = plafond d'évaluations. La loi de `Descent.lean` y est **exercée** (asserts runtime sur 60 exécutions : 0 violation `hstrict`, 0 violation `hbarrier`, 0 dépassement de plafond) et sa troisième hypothèse **réfutée exécutablement** : `hnostall` est fausse dans un paysage générique (100 % d'arrêts « blocage » hors cible à budget généreux, gap médian 10,4 %) — la dissociation budget-vs-blocage exigée par `Descent.lean` l.148 est mesurée dans deux régimes (budget serré : 30/30 arrêts « budget » sur 30 graines ; budget généreux : 60/60 arrêts « blocage » hors cible sur 60 graines) ; courbe qualité-budget médiane 86,3 % → 8,9 % (B ∈ {20..800}, 30 seeds, saturation = optima locaux). **Verdict : reste en constitution jusqu'au merge** (convention op 7 : non comptée tant qu'OPEN) — la promotion en TABLE appartient à A7, qui tranche sur deux attestations indépendantes (Lean-formel + empirique-notebook).

## Tranche c.1308 (2026-09-29, po-2024:CoursIA-2) — op 3 : re-vérification Infer-20 (piste vierge dans le ledger jusqu'ici)

**Op 3 — FIRSTHAND (ce cycle), re-vérification d'Infer-20 comme 2ᵉ attestation candidate.** Issue dispatchée par ai-01 ([#18405](https://github.com/jsboige/CoursIA/issues/18405)) à 14:30Z — le coordinateur pointe qu'`Infer-20-Quotients-et-Fibres-Python.ipynb` (`Probas/Modules/Infer/`, PR #12277 MERGED 2026-08-22) porte **le protocole de l'opération 3** : projection vers un alphabet `Q` (quantification de `X₁ + X₂`) et mesure de `I(X₁;X₂|Q)` vs `I(X₁;X₂)`, qui est la forme conditionnelle de la règle de chaîne `H(X) = H(π(X)) + H(X|π(X))`. Le ledger — re-vérifié ce cycle (`git grep -nE "Infer-20|12226" docs/ledgers/`) — ne mentionne ni l'un ni l'autre : la piste est vierge, donc le critère d'admission au chant1 (« deux attestations indépendantes ») n'a jamais été tranché sur cette candidate.

**Trois vérifications firsthand ce cycle :**

1. **Infer-20 sur disque** (`Probas/Applications/Infer-20-Quotients-et-Fibres-Python.ipynb`, PR #12277 MERGED 2026-08-22) : la cellule 10 (code) construit `Q = np.digitize(S, quantiles)` avec `Q_BINS = 4` et `S = X₁ + X₂`. La cellule 14 teste `Q_OPERATIONAL = (I(X₁;X₂|Q) < 0.5 · I(X₁;X₂))` — verdict imprimé **NON TENTE** (`ratio = 1.684`, > critère 0.5). **Infer-20 illustre la règle de chaîne conditionnelle** : c'est exactement l'opération 3 sous sa forme `I(X₁;X₂) = I(X₁;X₂|Q) + I(X₁;X₂;Q)`. Mais elle **échoue à produire un quotient opérationnel** sur des gaussiennes linéaires corrélées `ρ = 0.6` — la quantification 1D de la somme ne suffit pas.

2. **ANALYSE-04 sur disque** (`SymbolicAI/Lean/ANALYSE/ANALYSE-04-PFR-Primitives-Python.ipynb`) : cellule 7 — *« Lecture du résultat. La règle de chaîne `H(X) = H(X|Y) + I(X;Y)` est **vérifiée numériquement**. Information mutuelle `I(X;Y)` capture combien le cours (Y) explique la note (X) ; la résiduelle `H(X|Y)` capture la variation inexpliquée par le cours. Sémantique opérationnelle : `H(π(X))` ≈ ce que la projection capte ; `H(X|π(X))` ≈ ce qui reste dans les fibres. »* — Verdict de la cellule 9 : « Transportable large. Universelle en théorie de l'information. » C'est la **seule attestation locale** décomptée jusqu'ici (cf A3 l.97-106 : « teorth/pfr est une référence externe non incluse au dépôt, et la digestion EPIC l'a cité comme si elle était locale »).

3. **Critère d'indépendance** (règle op 7 étendue à l'op 3, protocole EPIC §1) : ANALYSE-04 ([#12252](https://github.com/jsboige/CoursIA/pull/12252), MERGED 2026-08-22T12:57:43Z) et Infer-20 ([#12277](https://github.com/jsboige/CoursIA/pull/12277), MERGED 2026-08-22T12:58:17Z) sont **nés le même jour (2026-08-22, à 34 secondes d'écart), du même EPIC [#12204](https://github.com/jsboige/CoursIA/issues/12204) — issues sœurs [#12214](https://github.com/jsboige/CoursIA/issues/12214) (Lean-21b PFR) et [#12226](https://github.com/jsboige/CoursIA/issues/12226) (Probas quotient/fibres/recollement). Le témoin formel de l'opération 3 (`H(X) = H(π(X)) + H(X|π(X))`) est universel info-théorique, mais la non-indépendance tient sur des constats vérifiables : **même chantier EPIC, même jour, même lane de dispatch**. ANALYSE-04 seul revendique le stimulus PFR-Tao ; Infer-20, fille de [#12226](https://github.com/jsboige/CoursIA/issues/12226), ne le cite pas. L'indépendance au sens strict du critère « deux endroits non reliés par le stimulus initial » n'est **pas** vérifiée.

**Verdict c.1308 — op 3 reste en file d'attente, mais le statut se précise :**

- **Pas de promotion** : 1 attestation locale indépendante (ANALYSE-04) + 1 attestation pédagogique **non-indépendante** (Infer-20, même chantier) = critère « deux endroits indépendants » non atteint.
- **Mais** Infer-20 **valorisera** l'op 3 si une seconde instantiation **sur substrat indépendant** arrive — le protocole est reproductible, le témoin négatif est déjà mesuré (1.684), le pipeline opérationnel est tracé.
- Le **témoin négatif** transportable d'Infer-20 (quantification 1D de la somme d'un couple gaussien corrélé ⇒ ratio `I(X₁;X₂|Q)/I(X₁;X₂)` = 1.684, **donc quotient informationnel non atteignable**) est noté comme tel dans le ledger — c'est un résultat négatif qui borne la classe des quotients opérationnels naïfs.

**Effet sur la table :** op 3 → toujours en file d'attente. Mention « 1 attestation locale + 1 pédagogique non-indépendante re-vérifiée c.1308 » dans le commentaire de livraison sur l'EPIC. **Pas de mouvement de table** ce cycle ; un futur A7bis qui trouve une 2ᵉ attestation sur un substrat hors-PFR (Probabilité élémentaire, codage, IC games) la fait basculer.

**Distance de Ruzsa** (point 3 de #18405) : objet ICT à groupe additif identifié = **`MyIA.AI.Notebooks/IIT/ICT-Series/ict/factor_geometry.py`** (espace des activations `(ℝ^D, +)`, primitives `weighted_pca` / `max_principal_angle` / `basis_overlap` extraites de ICT-36-FLens-FactoredGeometry, PR #15514 MERGED). La convolution `X′ − Y′` y est définie composante par composante. Application directe : `d_ruzsa(X;Y) = H(X′ − Y′) − ½ H(X′) − ½ H(Y′)` sur deux activations factorisées. **Non livré dans cette tranche** (hors périmètre dispatch —> à pousser en grain suivant si ai-01 l'autorise, après qu'A7 ou un grain subséquent ait statué sur l'op 3).

**Acceptance sortie ce cycle :** verdict d'attestation de l'opération 3 écrit dans le ledger (cette tranche), avec sa preuve (3 vérifications nommées) et le statut du témoin négatif.

## Tranche c.1114 (2026-10-06, po-2023:CoursIA-2) — Ruzsa : contrat de l'organ corrigé + application ICT + témoin de limite

Issue dispatchée par le coordinateur ai-01 (commentaire #18405, 2026-09-29) ; claim posé par cette lane le 2026-10-06. Précédent c.1308 (po-2024) laissait la **livraison** de la distance de Ruzsa sur objet ICT en suspens (« Non livré dans cette tranche —> à pousser en grain suivant si ai-01 l'autorise »). La présente tranche tranche ce volet : l'organ est qualifié firsthand, l'application à `factor_geometry.py` est livrée sous forme de carnet exécuté, et le **témoin de limite** demandé par le point 3 de #18405 est documenté.

**Quatre vérifications firsthand ce cycle** (toutes dans `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-36b-RuzsaOnFactorGeometry-Python.ipynb` — carnet compact, code exécuté papermill, 0 erreur) :

1. **Organ cellule 1 (invariants) sur-revendique `d[X;X] = 0`.** Reproduction : `d_ruzsa({0:0.5, 1:0.5}, {0:0.5, 1:0.5}, 4) = 0.500000` bit (cellule 5 du carnet, cas 2). Le 0.5 vient de `H(X'-X) = 1.5` bits (distribution `{0: 0.5, 1: 0.25, 3: 0.25}`) moins `H(X) = H(Y) = 1` bit. Le contrat correct est : `d[X;Y] = 0` si et seulement si Y est une translatee de X (`Y = X + a` pour un `a` du groupe), pas un cas général pour `X = Y`. L'invariant tient pour X uniforme sur G (cas 1 du carnet : Z/8Z uniforme → `d[X;X] = 0.000000`).

2. **L'invariant de translation COMMUNE tient :** `d[X+a; Y+a] = d[X;Y]` pour tout `a` (cellule 5 du carnet, cas 3). Test sur `X = {0:0.5, 1:0.5}` (non uniforme), translations 0, 1, 2 : les trois valeurs de `d_ruzsa(X;X+a)` sont **identiques à 1e-15** (mêmes 0.5). L'invariant cellule 1 est donc **vrai** sous sa forme littérale (`d[X+a; Y+a] = d[X;Y]`) ; c'est sa **conséquence** `d[X;X] = 0` qui est sur-revendiquée.

3. **Application à `factor_geometry.py` :** `synthesize_activations(bases, n_tokens=4000, signal_var=1.0, noise_var=0.1, rng)` produit `X ∈ ℝ^{4000 × 24}`. Quantification par signe (signe ±1 → groupe `Z/2Z` additif). Distribution marginale de la coordonnée 0 : `{0: 0.5045, 1: 0.4955}`, `H(X) = 0.9999` bits, `d_ruzsa(X;X) = 0.000058` bits — la structure orthogonale des facteurs + le bruit gaussien rendent la marginale **quasi-uniforme** sur Z/2Z, donc `d_ruzsa` est essentiellement 0. C'est le cas **favorable** d'application de l'organ sur un objet ICT.

4. **Témoin de limite :** sur le **même** objet d'activations, 3 schémas de quantification différents donnent des valeurs différentes de `d_ruzsa` (cellule 8 du carnet, witness). Signe (Z/2Z) → 0.000058 bit ; 3-quantiles (Z/3Z) → 0.000000 bit (par construction, marginales uniformes) ; 5-quantiles (Z/5Z) → 0.000000 bit (idem) ; hash LSB (Z/2Z, exercice 1) → 0.072061 bit (LSB biaisé de la mantisse IEEE 754 → marginale `{0: 0.665, 1: 0.335}`). **C'est précisément le "mapping affine" que l'organ cellule 5 dénonce** : la valeur de `d_ruzsa` dépend du schéma de quantification, pas seulement de l'objet sous-jacent. L'organ fonctionne sur son terrain (groupes abéliens, X uniforme), mais ne transporte pas tel quel sur les objets ICT — il faudrait soit garantir l'uniformité marginale par construction, soit contrôler la quantification comme une variable explicite de la mesure.

**Verdict c.1114** :

- **Op 3 reste en file d'attente** (statut inchangé depuis c.1308). Le présent carnet **ne promeut pas** l'op 3 : il documente un **test de limite** (aboutissant 2 du point 3 de #18405 : « Distance de Ruzsa : application sur un objet ICT à structure de groupe, **ou** test de limite documenté »), pas une seconde attestation indépendante. La règle d'admission reste : 2ᵉ attestation sur substrat indépendant.
- **Contrat de l'organ documenté** : `d[X+a; Y+a] = d[X;Y]` (vrai), `d[X;X] = 0` (vrai ssi X uniforme sur G, **sur-revendiqué** par la cellule 1). Le carnet ICT-36b documente l'overclaim et le mécanisme sous-jacent (entropie de la différence plus petite que l'entropie marginale pour X non uniforme). **Suivi proposé** (hors périmètre de cette tranche) : PR sur la série source `SymbolicAI/Lean/ANALYSE/` pour corriger l'invariant cellule 1 (ajouter la condition « X uniforme sur G »). La qualification de l'organ est **indépendante** de cette correction (po-2025 l'a identifiée 36 h avant, cf commentaire #18405 du 2026-10-05T20:25:53Z).
- **Le témoin de limite est mesuré** : sur le même objet ICT, 4 schémas de quantification donnent 4 valeurs de `d_ruzsa` (0, 0, 0.000058, 0.072). La dépendance au schéma est le **résultat** de cette tranche, pas un échec — c'est l'illustration ICT du « mapping affine » que l'organ cellule 5 met en garde.

**Effet sur la table #12204** : néant sur la promotion de l'op 3. La tranche **remplit** le point 3 de #18405 (test de limite documenté) et **étend** la qualification de l'organ source (overclaim cellule 1 identifié et reproduit). Pour une promotion en TABLE, il faudrait une 2ᵉ attestation sur substrat hors-PFR (cf précédent c.1308).

**Acceptance sortie ce cycle :**

- [x] Contrat organ qualifié firsthand (4 cas, 0 réécriture, organ cellule 2 vendorisé verbatim avec SPDX).
- [x] Overclaim cellule 1 reproduit et documenté (`d[X;X] = 0.5` pour X non uniforme sur Z/4Z).
- [x] Application à `ict.factor_geometry.synthesize_activations` livrée (carnet ICT-36b, 7 code cells exécutées).
- [x] Témoin de limite livré (3 schémas, 4 valeurs de `d_ruzsa` sur le même objet).
- [x] 5 questions organ-first documentées en cellule 9 du carnet.
- [x] Statut op 3 inchangé : file d'attente.

## Tranche réconciliation (2026-10-04, po-2027:CoursIA) — ops 2 et 6 : deux 2ᵉ attestations enregistrées (artefacts antérieurs au dernier toucher du ledger, non comptés)

Motif : pattern #11900 inversé — ce n'est pas le body qui a vieilli, c'est le **ledger**. Deux artefacts livrés sur `main` entre deux tranches n'ont jamais été enregistrés dans la table. Vérification firsthand des deux ce 04/10.

**Op 2 — GT-19, l'attestation locale qui existait déjà.** `GameTheory/GameTheory-19-Abstraction-a-Dette-Python.ipynb` : né de l'issue [#12229](https://github.com/jsboige/CoursIA/issues/12229) (CLOSED, même voyage de digestion du 2026-08-21, **jamais rattachée à cette EPIC** — 0 citation du body), livré par PR #12267 (2026-09-11), digéré par #18317 (2026-10-01), toutes les cellules code exécutées avec outputs. Contenu vérifié : cellule 3 (abstraction par fusion d'états, partition de 6 états, matrices moyennées) → cellule 7 (**solve exact de G̃, retransport, mesure DANS G** — le pipeline α→solve→ρ→σ_G de la loi) → cellule 12 (**courbe de dette sur la chaîne de raffinement P6 < P4 < P3 < P2**, chaîne vérifiée par `refines`), plus l'atlas des 15 paires (exercice 2) et la partition hors chaîne P3B vs P3 à taille égale (exercice 3, P3 = 1.9091) — la question « qu'ai-je le droit d'oublier » chiffrée. C'est la forme de témoin exigée par le critère §1, en force empirique-notebook.
**Réserve d'indépendance (précédent c.1308)** : GT-19 **cite Kroer-Sandholm** comme source théorique et naît du même batch de digestion — la non-indépendance par le stimulus initial invoquée pour op 3 / Infer-20 s'applique a priori au couple (théorème externe, instantiation locale qui le cite). La promotion TABLE appartient donc à A7, qui tranche : le critère « deux endroits indépendants » compte-t-il une instantiation pédagogique de la source elle-même ? **Statut : en constitution, pas de promotion auto-décidée.**

**Op 6 — Search-03f, la 2ᵉ attestation livrée hier par cette même lane.** `Search/Part1-Foundations/Search-03f-Reparer-Localement-Sous-Garantie-Python.ipynb`, PR #19013 **MERGED 2026-10-04T02:14:57Z** — postérieure au dernier toucher de ce ledger (2026-09-30 01:22), d'où la ligne restée en FILE D'ATTENTE. toutes les cellules code exécutées (exécution complète vérifiée), [DELIVERED] posé sur l'EPIC le 03/10 17:24Z. Trois témoins exigés par la table, vérifiés dans le carnet : garantie transportée (coût LPA\* = coût A\* from scratch, 8/8 concordances sur séquence de 8 changements), localité payée juste (12 expansions pour le repair), et le troisième lu en conclusion. **Indépendance par construction : 0 mention de Sandholm dans le carnet** (mesuré) — substrat recherche de chemin, pas jeux.
**Statut : en constitution, promotion TABLE à statuer par la revue** (convention des ops 11-13).

**Effet sur la table :** la file d'attente passe de 4 à 2 opérations (restent **3 et 5**) ; les ops 2 et 6 rejoignent les 4 en constitution → **6 en constitution**. Le bilan A6 ci-dessus reste historique. A7, quand il statuera, trouvera deux dossiers de plus sur son bureau — c'est précisément le geste attendu d'une réconciliation : rendre visible ce qui était déjà là.

## Références

- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · tranches : A3 ([ledger](12204-ict-chantier-1-a3.md), PR #12293) · audit-froid (ce fichier)
- Revue extérieure (protocole + 4 contestations) : commentaire #12204 du 2026-08-22
- Steering : ai-01 2026-08-22T20:54Z ([DISPATCH→inbox] dashboard workspace-CoursIA)
- Précédent de format : [`3801-sota-axe2.md`](3801-sota-axe2.md)
