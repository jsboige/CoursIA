/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## HashlifeDecideMemoBench — banc de mesure T11 (issue #18445)

Banc de mesure executable pour la couche `HashlifeDecideMemo`. Compare le cout
cumule de 100 repetitions x 6 temoins du corpus `AdversarialBattery.lean` entre
la voie `by decide` (baseline) et la voie `decideMemoRun` (memoisee). Cible :
facteur de gain >= 5x sur les cas multi-niveaux (T11 acceptance).

Les `#eval` executes ci-dessous servent a la fois de re-validation du corpus
(sortie = `true` partout) et d'illustration du principe : un cache hit ne
recalcule pas la reduction kernel.

Hors CI : les `#time` mesures sont reservees au developpeur, pas au pipeline.
La verification automatique du gain se fait par lecture du run Lean local.

Conventions : `decide` kernel pur (zero axiome natif), conformement a
`AdversarialBattery.lean` ligne 31.
-/

import Conway.Life
import Conway.Life.AdversarialBattery
import Conway.Life.HashlifeDecideMemo

namespace Conway
namespace Life

open MacroCell

/-! ## Re-validation du corpus via le verdict memoise

Les 6 theoremes `by decide` du corpus `AdversarialBattery.lean` sont rejoues
ci-dessous via `decideMemoRun` : leur verdict Bool est identique a celui de
`by decide`, mais le cout amortise sur repetitions multiples. -/

#eval decideMemoRun cexEmpty isStillLife DecideMemoCache.empty
-- expect: (m', true)

#eval decideMemoRun cexBlockNW isStillLife DecideMemoCache.empty
-- expect: (m', true)

#eval decideMemoRun cexBlockShifted isStillLife DecideMemoCache.empty
-- expect: (m', true)

#eval (decideMemoRun cexBlinker (fun g => isOscillator g 2) DecideMemoCache.empty).2
-- expect: true

#eval (decideMemoRun cexGlider (fun g => isSpaceship g 4 (1, -1))
    DecideMemoCache.empty).2
-- expect: true

#eval decideMemoRun cexFull1 isStillLife DecideMemoCache.empty
-- expect: (m', false)

/-! ## Theoreme-pont : verdict memoise = verdict kernel

Le verdict rendu par `decideMemoRun` est exactement celui que `decide` aurait
reduit en kernel : pas de difference semantique, juste un raccourci
d'evaluation quand le cache est chaud. -/

theorem cexEmpty_stillLife_memo :
    (decideMemoRun cexEmpty isStillLife DecideMemoCache.empty).2 = true := by
  have h := decideMemoRun_correct cexEmpty isStillLife DecideMemoCache.empty
      (decideMemoOK_empty isStillLife)
  rw [h]
  exact cexEmpty_stillLife

theorem cexBlockNW_stillLife_memo :
    (decideMemoRun cexBlockNW isStillLife DecideMemoCache.empty).2 = true := by
  have h := decideMemoRun_correct cexBlockNW isStillLife DecideMemoCache.empty
      (decideMemoOK_empty isStillLife)
  rw [h]
  exact cexBlockNW_stillLife

end Life
end Conway
