/-
  `Conway.CHSHFreeWill` — Du CHSH au libre arbitre : la route statistique
  =====================================================================
  Sixième tranche du pilote quantique de l'Epic #13106. Les tranches
  précédentes ont borné la frontière classique déterministe
  (`Conway.CHSH`), son enveloppe randomisée (`Conway.CHSHRandomized`),
  importé la borne quantique `2√2` de Mathlib (`Conway.CHSHQuantum`), puis
  saturé Tsirelson par un témoin explicite et vérifié le critère de Landau
  (`Conway.CHSHLandau`, consommé par le notebook `Lean-13c`).

  Il manquait au pilote le pont annoncé par l'Epic : la série CHSH et le
  théorème du libre arbitre (`Conway.FreeWillTheorem`, notebook
  `Lean-16f`) concluent **tous deux** à l'indéterminisme des réponses
  quantiques, mais par deux routes formellement déconnectées :

  - la **route contextuelle** (Free Will Theorem) : trois directions de
    mesure, axiomes SPIN + TWIN + MIN, contradiction par l'absence de
    coloration de Kochen-Specker (`kochen_specker`) ;
  - la **route statistique** (CHSH) : deux réglages par parti, localité
    des réponses, contradiction par l'écart numérique `2 < 2√2`.

  Ce module formalise la route statistique dans le vocabulaire du FWT —
  un « modèle local déterministe » est une famille de fonctions de réponse
  de l'état caché, une par parti, chacune aveugle au réglage de l'autre
  (l'analogue structurel de MIN) — et démontre la conclusion
  d'indéterminisme : **aucun modèle local déterministe ne peut réaliser un
  score CHSH au-delà de la frontière classique, dans aucun état caché**,
  alors que la mécanique quantique atteint `2√2`. Les réponses ne peuvent
  donc pas être des fonctions du passé — la même conclusion que le FWT,
  obtenue sans coloration.

  ### Table d'état des énoncés

  | Énoncé | Statut |
  |---|---|
  | Frontière locale déterministe état-par-état : `|realizedScore| = 2` | **prouvé ici** (délégué à `CHSH.classical_abs_score`) |
  | Saturation par un modèle local explicite (`canonical`) | **prouvé ici** |
  | Aucun état où un modèle local dépasse `2` (entier) | **prouvé ici** |
  | La valeur de Tsirelson `2√2` majore strictement tout score local (réel) | **prouvé ici** |
  | Conclusion d'indéterminisme : aucun modèle local ne réalise `> 2` en réels | **prouvé ici** |
  | Interprétation probabiliste complète (états, mesures, espérances sur ℝ⁴) | **non établie** — déclarée ouverte, comme dans `Conway.CHSHQuantum` |
  | Équivalence des deux routes (FWT ⟷ CHSH) | **non établie** — les hypothèses diffèrent ; seule la conclusion commune est formalisée |

  ### Grille de digestion (10 points, Epic #13106)

  1. **Énoncés et niveau de garantie** : bornes et égalités exactes sur `ℤ`
     puis `ℝ`, sans analyse fonctionnelle ; la constante `2√2` est celle de
     `Conway.CHSHQuantum.classical_quantum_gap`.
  2. **Provenance** : Clauser, Horne, Shimony, Holt (1969), « Proposed
     experiment to test local hidden-variable theories » ; Bell (1964) pour
     l'inégalité mère ; Tsirelson (1980) pour la borne quantique. Le lien
     « violation de Bell ⟹ indéterminisme » est la lecture standard (Bell
     1964, §II) ; la formulation en « fonctions de réponse du passé » suit
     le vocabulaire de Conway-Kochen (2006/2009).
  3. **Nouveauté réelle** : le dépôt avait les deux ingrédients séparés
     (borne `CHSH.classical_abs_score`, écart `classical_quantum_gap`) ; le
     modèle local déterministe comme famille de fonctions de l'état caché,
     la borne état-par-état et la conclusion d'indéterminisme sont nouveaux
     dans le dépôt.
  4. **Carte des dépendances** : `Conway.CHSH` (score, frontière),
     `Conway.CHSHQuantum` (écart), `Conway.FreeWillTheorem` (`HiddenState`,
     vocabulaire) ; Mathlib restreinte à `Mathlib.Tactic.Ring` et aux
     `omega` sur `|s| = 2` / coercions `ℤ → ℝ`. Aucun `sorry`,
     aucun axiome au-delà des trois standard.
  5. **Trivial condensé / nouveau développé** : la frontière elle-même est
     déléguée (énumération 16 cas déjà payée par `Conway.CHSH`) ; le cœur
     nouveau est le passage **pour tout état** : la borne classique était un
     fait sur quatre résultats, elle devient un fait sur des familles
     entières de fonctions de réponse.
  6. **Friction** : la tentation d'un énoncé d'espérance (score moyen sous
     une distribution d'états cachés) a été écartée : la machinerie
     d'espérance n'apporte rien à la conclusion (la borne état-par-état est
     plus forte pour un modèle déterministe) et alourdirait le module.
  7. **Chemin de découverte** : la correspondance structurelle MIN ⟷
     localité-par-signature a été trouvée en relisant la signature de
     `TwoParticleResponse` de `Conway.FreeWillTheorem` — la localité n'y
     est pas une hypothèse mais une propriété du type. Le même encodage est
     repris ici à l'identique.
  8. **Limites** : la conclusion porte sur les modèles **déterministes
     locaux** ; elle ne dit rien des modèles stochastiques non locaux ni de
     la borne randomisée (voir `Conway.CHSHRandomized` pour l'enveloppe
     probabiliste classique).
  9. **Raccord au corpus** : consommé par le notebook
     `Lean-13d-CHSH-Indeterminisme-Native.ipynb` (pont croisé avec
     `Lean-16f`), prolongement de la série 13b/13c ; prérequis : score CHSH
     et frontière classique (`Lean-13b`).
  10. **Transmission** : notebook natif avec témoin calculé, tableau de
      correspondance des deux routes, et relecture croisée à la revue.

  ### i18n — convention #4980 (ratifiée 2026-07-04)

  Ce fichier est le **canonique français**. Le miroir anglais est le fichier
  frère `Conway/CHSHFreeWill_en.lean` (`namespace Conway_en` >
  `namespace CHSHFreeWill_en`, imports suffixés `_en`) — modèle sibling pair
  Pattern A, comme `Conway/CHSHLandau` c.240. Docstrings en français ici ;
  le corps (signatures, defs, preuves) reste byte-identique entre les deux
  fichiers, aux qualifieurs `_en` près. Pas de bloc bilingue inline.
-/

import Conway.CHSH
import Conway.CHSHQuantum
import Conway.FreeWillTheorem

namespace Conway

namespace CHSHFreeWill

open CHSH CHSHQuantum FreeWillTheorem

/-!
## Étape 1 : modèle local déterministe du jeu CHSH

Le vocabulaire est celui du théorème du libre arbitre : les réponses sont
des fonctions de l'état caché (le « passé » de l'univers). La **localité**
est encodée par la signature, exactement comme MIN dans
`Conway.FreeWillTheorem.TwoParticleResponse` : la réponse d'Alice ne voit
jamais le réglage de Bob, et réciproquement — ce n'est pas une hypothèse
à prouver, c'est une propriété du type.
-/

/-- Réponse locale d'Alice : pour chaque état caché et chacun de ses deux
réglages (`true` = x, `false` = y), un résultat prédéterminé `±1`.

C'est l'analogue à deux réglages de `Conway.FreeWillTheorem.DeterministicResponse`
(qui en portait trois, directions de spin). La localité (MIN) vit dans la
signature : le réglage de Bob n'apparaît pas. -/
abbrev AliceResponse := HiddenState → Bool → Outcome

/-- Réponse locale de Bob : même encodage, symétrique de celui d'Alice. -/
abbrev BobResponse := HiddenState → Bool → Outcome

/-- Score CHSH réalisé par le modèle `(α, β)` dans l'état caché `state` :
les quatre réponses prédéterminées sont injectées dans le score de
`Conway.CHSH`. -/
def realizedScore (α : AliceResponse) (β : BobResponse) (state : HiddenState) : ℤ :=
  score (α state true) (α state false) (β state true) (β state false)

/-!
## Étape 2 : la frontière locale, état par état

La frontière classique de `Conway.CHSH` était un fait sur quatre résultats
isolés. Pour un modèle local déterministe, elle vaut **dans chaque état
caché** — c'est le pont du particulier (une stratégie) au général (une
famille entière de stratégies indexée par le passé).
-/

/-- **Frontière locale déterministe, forme exacte.** Dans tout état caché,
le score réalisé par un modèle local déterministe vaut exactement `±2`.

La preuve délègue l'énumération des 16 assignations à
`Conway.CHSH.classical_abs_score` : chaque état caché instancie quatre
réponses, et la frontière s'applique. -/
theorem local_abs_score (α : AliceResponse) (β : BobResponse) (state : HiddenState) :
    |realizedScore α β state| = 2 :=
  classical_abs_score _ _ _ _

/-- Forme usuelle de la frontière locale. -/
theorem local_bound (α : AliceResponse) (β : BobResponse) (state : HiddenState) :
    |realizedScore α β state| ≤ 2 :=
  local_abs_score α β state ▸ le_refl _

/-- **Aucun modèle local déterministe ne dépasse la frontière classique,
dans aucun état caché.** La borne n'est pas une moyenne : elle vaut
état par état, donc aucun état privilégié ne peut sauver le modèle. -/
theorem no_state_beyond_classical :
    ¬ ∃ (α : AliceResponse) (β : BobResponse) (state : HiddenState),
        (2 : ℤ) < realizedScore α β state := by
  rintro ⟨α, β, state, h⟩
  have habs : |realizedScore α β state| = 2 := local_abs_score α β state
  have hle : realizedScore α β state ≤ |realizedScore α β state| := le_abs_self _
  omega

/-- La frontière locale est **atteinte** : le modèle canonique — les deux
partis répondent toujours `+1` — réalise le score `+2` dans tout état.
La borne de `local_bound` est donc serrée pour les modèles locaux. -/
def canonicalAlice : AliceResponse := fun _ _ => .positive

def canonicalBob : BobResponse := fun _ _ => .positive

@[simp]
theorem canonical_score (state : HiddenState) :
    realizedScore canonicalAlice canonicalBob state = 2 := by
  simp [realizedScore, canonicalAlice, canonicalBob, score, Outcome.value]

/-!
## Étape 3 : l'écart de Tsirelson exclut les modèles locaux déterministes

La mécanique quantique prédit (et l'expérience confirme) des corrélations
CHSH de valeur `2√2` — strictement au-dessus de la frontière locale
(`Conway.CHSHQuantum.classical_quantum_gap`). Puisque tout modèle local
déterministe est plafonné à `2` dans chaque état, aucun ne peut reproduire
la prédiction quantique.
-/

/-- Version réelle de la frontière locale : le score réalisé, vu comme
réel, reste sous la frontière classique. -/
theorem local_bound_real (α : AliceResponse) (β : BobResponse) (state : HiddenState) :
    (realizedScore α β state : ℝ) ≤ 2 := by
  have h : realizedScore α β state ≤ 2 := by
    have habs : |realizedScore α β state| = 2 := local_abs_score α β state
    have hle : realizedScore α β state ≤ |realizedScore α β state| := le_abs_self _
    omega
  exact_mod_cast h

/-- **L'écart de Tsirelson domine tous les scores locaux.** La valeur
quantique `2√2` est strictement supérieure à la frontière classique, et
tout modèle local déterministe réalise au plus `2` : l'écart est incompressible
pour ces modèles. -/
theorem tsirelson_beyond_every_local_score :
    (2 : ℝ) < 2 * √2 ∧
      ∀ (α : AliceResponse) (β : BobResponse) (state : HiddenState),
        (realizedScore α β state : ℝ) ≤ 2 :=
  ⟨classical_quantum_gap, local_bound_real⟩

/-- **Conclusion d'indéterminisme par la route CHSH.** Aucun modèle où les
réponses des deux partis sont des fonctions déterministes de l'état caché
(localité par signature) ne peut réaliser un score CHSH strictement
supérieur à la frontière classique — alors que la valeur quantique est
`2√2 > 2`.

C'est la même conclusion que `Conway.FreeWillTheorem.free_will_theorem`
(les réponses ne sont pas des fonctions du passé), obtenue par un argument
**statistique** (l'écart numérique de Tsirelson) là où le FWT utilise un
argument **contextuel** (l'absence de coloration de Kochen-Specker). Les
hypothèses diffèrent — deux réglages contre trois directions, écart
numérique contre coloration impossible —, la conclusion est commune. -/
theorem chsh_indeterminism :
    ¬ ∃ (α : AliceResponse) (β : BobResponse) (state : HiddenState),
        (2 : ℝ) < realizedScore α β state := by
  rintro ⟨α, β, state, h⟩
  exact no_state_beyond_classical ⟨α, β, state, by exact_mod_cast h⟩

/-!
## Étape 4 : correspondance structurelle des deux routes

  | | Route contextuelle (FWT, `Lean-16f`) | Route statistique (CHSH, `Lean-13b/13c/13d`) |
  |---|---|---|
  | Réglages par parti | 3 directions orthogonales | 2 réglages binaires |
  | Axiomes | SPIN + TWIN + MIN | localité (par signature) + statistiques quantiques |
  | Moteur de contradiction | `kochen_specker` : aucune coloration valide | `classical_quantum_gap` : `2 < 2√2` |
  | Ce qui est nié | toute réponse fonction du passé (déterminisme) | tout modèle local déterministe reproduisant `2√2` |
  | Force de la conclusion | exacte, sans hypothèse statistique | numérique : quantifie l'écart (`2√2 − 2`) |

  Les deux routes sont **complémentaires** : le FWT ne dit rien de l'écart
  numérique, la route CHSH ne dit rien des corrélations parfaites TWIN.
  Le notebook `Lean-13d` parcourt les deux colonnes sur le même témoin.
-/

end CHSHFreeWill

end Conway
