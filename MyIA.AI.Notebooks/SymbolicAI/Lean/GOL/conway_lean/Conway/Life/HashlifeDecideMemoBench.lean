/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## HashlifeDecideMemoBench — banc de mesure T11 (issue #18445)

Banc de mesure **executable** pour la couche `HashlifeDecideMemo`. Il compare,
temoin par temoin, le cout cumule de N evaluations du predicat entre :

- la **voie baseline** : recalcul integral `p g` a chaque evaluation (ce que
  coute aujourd'hui chaque nouvelle preuve du meme verdict) ;
- la **voie memoisee** : `decideMemoRun` avec cache **patine d'une evaluation
  a l'autre** (la 1re evalue `p g` et peuple le cache, les suivantes lisent).

### Protocole de mesure (runtime IO, pas elaboration)

Les `#time` mesurent l'elaboration, pas des boucles : le banc utilise donc un
chronometre monotone (`IO.monoNanosNow`) autour de boucles IO pures. Les deux
voies passent par le **meme interprete** Lean (`lake env lean --run`), la
comparaison est donc valide ; la baseline runtime est de plus un **plancher
conservateur** du cout de la tactique `decide` (la reduction kernel est plus
lente que l'evaluation runtime), donc le gain mesure est une borne inferieure
du gain sur la voie kernel.

L'accumulateur de verdicts force l'evaluation de chaque iteration (aucune
iteration n'est morte), et un controle de coherence exige que les deux voies
rendent le **meme compte de verdicts vrais** — le banc echoue sinon.

### Reproduction

```
lake exe cache get   # une seule fois (oleans Mathlib)
lake build Conway.Life.HashlifeDecideMemoBench
lake env lean --run Conway/Life/HashlifeDecideMemoBench.lean
```

### Resultats mesures (2026-10-12, interprete Lean WSL, toolchain v4.33.0, Mathlib db584cd)

| temoin | reps | baseline (recalcul) | memoise (cache patine) | gain |
|---|---:|---:|---:|---:|
| cexEmpty | 100000 | 83.7 ms | 92.8 ms | 0.9x |
| cexBlockNW | 50000 | 10.9 s | 151 ms | 71.9x |
| cexBlockShifted | 50000 | 11.4 s | 156 ms | 73.0x |
| cexBlinker (T=2) | 20000 | 5.5 s | 50 ms | 110.4x |
| cexGlider (T=4) | 10000 | 12.1 s | 36 ms | 335.5x |
| cexFull1 (verdict false) | 10000 | 18.9 s | 85 ms | 222.2x |
| pulsar (48 cell., T=3) | 300 | 24.2 s | 89 ms | **272.2x** |
| pentadecathlon (T=15) | 100 | 5.7 s | 58 ms | **98.6x** |

**Verdict T11 : critere >= 5x sur les cas multi-niveaux TENU** (pulsar
272.2x, pentadecathlon 98.6x). La frontiere est mesuree ou l'acceptance la
predissait : `cexEmpty` rend 0.9x — sur grille vide, recalculer `step [] == []`
coûte moins cher que hash + consultation HashMap ; la memoisation paie des
que le calcul du predicat depasse le cout du hash structurel (deja 71.9x sur
un bloc 2x2, ou le recalcul integrale de `step` domine largement).

Note de transparence : les theoremes-ponts multi-niveaux ci-dessous
(`pulsar_period_three_memo`, `pentadecathlon_period_15_memo`) citent les
theoremes de periode **etablis** d'`Oscillators.lean`, tous deux prouves
`by native_decide` (temoins historiques admis par la convention du lake) ;
ces ponts heritent donc de leurs axiomes natifs — la couche memoisee
elle-meme (`decideMemoRun`, `decideMemoRun_correct`) n'en depend pas.

### Convention lake : `decide` kernel pur

Les `#eval` ci-dessous (verdicts, executables a l'elaboration, cout trivial)
servent de re-validation du corpus ; le chronometrage vit exclusivement dans
`main`, non execute par `lake build` — la CI ne paie jamais les boucles de
mesure. Conventions : `decide` kernel pur, zero axiome natif en redaction
courante (cf `AdversarialBattery.lean` ligne 31 ; `native_decide` reste
reserve aux temoins historiques `pulsar`/`pentadecathlon` deja admis).
-/

import Conway.Life
import Conway.Life.AdversarialBattery
import Conway.Life.Oscillators
import Conway.Life.HashlifeDecideMemo

namespace Conway
namespace Life

/-! ## Re-validation du corpus via le verdict memoise

Les 6 verdicts `by decide` du corpus `AdversarialBattery.lean` sont rejoues
ci-dessous via `decideMemoRun` : sortie identique a celle du kernel, cout
amorti des la deuxieme consultation. -/

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

/-! ## Boucles de mesure (runtime, executees uniquement par `--run`)

`benchBaseline` recalcule `p g` a chaque iteration ; `benchMemo` passe le
cache d'une iteration a la suivante (la 1re peuple, les suivantes consultent).
L'accumulateur rend chaque iteration observable : le compte de verdicts vrais
doit etre identique des deux cotes, sinon la mesure echoue. -/

/-- N evaluations integrales de `p g` ; rend le compte de verdicts vrais. -/
def benchBaseline (g : Grid) (p : Grid → Bool) (n : Nat) : IO Nat := do
  let mut acc := 0
  for _ in [0:n] do
    if p g then acc := acc + 1
  return acc

/-- N evaluations memoisees de `p g` (cache patine entre iterations) ;
    rend le compte de verdicts vrais. -/
def benchMemo (g : Grid) (p : Grid → Bool) (n : Nat) : IO Nat := do
  let mut m := DecideMemoCache.empty
  let mut acc := 0
  for _ in [0:n] do
    let (m', b) := decideMemoRun g p m
    m := m'
    if b then acc := acc + 1
  return acc

/-- Chronometre monotone autour d'une action IO ; rend (nanosecondes, resultat). -/
def timeNanos (act : IO Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  return (t1 - t0, r)

/-- Un temoin du banc : nom lisible, grille, predicat decidable, repetitions. -/
structure WitnessSpec where
  name : String
  grid : Grid
  pred : Grid → Bool
  reps : Nat

/-- Mesure un temoin : baseline vs memoise, coherence des comptes, affichage.
    Rend le facteur de gain en dixiemes (gain x10) pour l'agregation. -/
def measureWitness (w : WitnessSpec) : IO Nat := do
  let (tb, kb) ← timeNanos (benchBaseline w.grid w.pred w.reps)
  let (tm, km) ← timeNanos (benchMemo w.grid w.pred w.reps)
  if kb != km then
    throw (IO.userError
      s!"{w.name}: divergence de comptes baseline/memo ({kb} vs {km})")
  let tmSafe := if tm == 0 then 1 else tm
  let gain10 := tb * 10 / tmSafe
  IO.println s!"{w.name} | reps={w.reps} | baseline={tb} ns | memo={tm} ns | gain={gain10 / 10}.{gain10 % 10}x"
  return gain10

/-- Les 8 temoins : les 6 du corpus (triviaux a 1 niveau, non concernes par
    le critere de gain) puis les 2 multi-niveaux `Oscillators.lean` (pulsar
    periode 3, 48 cellules ; pentadecathlon periode 15) qui portent le critere
    T11 : facteur >= 5x. Les repetitions sont choisies pour que la voie
    baseline dure au moins ~0,5 s par temoin (bruit d'horloge negligeable). -/
def benchCorpus : List WitnessSpec :=
  [ ⟨"cexEmpty/isStillLife", cexEmpty, isStillLife, 100000⟩
  , ⟨"cexBlockNW/isStillLife", cexBlockNW, isStillLife, 50000⟩
  , ⟨"cexBlockShifted/isStillLife", cexBlockShifted, isStillLife, 50000⟩
  , ⟨"cexBlinker/isOscillator2", cexBlinker, fun g => isOscillator g 2, 20000⟩
  , ⟨"cexGlider/isSpaceship4", cexGlider, fun g => isSpaceship g 4 (1, -1), 10000⟩
  , ⟨"cexFull1/isStillLife(false)", cexFull1, isStillLife, 10000⟩
  , ⟨"pulsar/isOscillator3", pulsar, fun g => isOscillator g 3, 300⟩
  , ⟨"pentadecathlon/isOscillator15", pentadecathlon, fun g => isOscillator g 15, 100⟩
  ]

/-- Corps du banc. Non execute par `lake build` ni par l'elaboration :
    uniquement par le point d'entree racine `main` ci-dessous. -/
def benchMain : IO Unit := do
  IO.println "== T11 memo bench : baseline (recalcul integral) vs decideMemoRun (cache patine) =="
  IO.println "interprete Lean, horloge IO.monoNanosNow ; gain = baseline/memo (borne inferieure du gain kernel)"
  let mut worst := 0
  for w in benchCorpus do
    let g ← measureWitness w
    if g > worst then worst := g
  IO.println s!"meilleur gain observe tous temoins (dixiemes) : {worst / 10}.{worst % 10}x"
  IO.println "criteres T11 : gain >= 5x attendu sur pulsar/pentadecathlon ; cas triviaux non concernes (issue #18445)"

/-! ## Theoremes-ponts : verdict memoise = verdict etabli

Le verdict rendu par `decideMemoRun` est exactement celui du theoreme etabli
du corpus : pas de difference semantique, un raccourci d'evaluation quand le
cache est chaud. Les deux ponts multi-niveaux (`pulsar`, `pentadecathlon`)
s'appuient sur les theoremes de periode etablis d'Oscillators.lean. -/

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

theorem pulsar_period_three_memo :
    (decideMemoRun pulsar (fun g => isOscillator g 3) DecideMemoCache.empty).2
      = true := by
  have h := decideMemoRun_correct pulsar (fun g => isOscillator g 3)
      DecideMemoCache.empty (decideMemoOK_empty _)
  rw [h]
  exact pulsar_period_three

theorem pentadecathlon_period_15_memo :
    (decideMemoRun pentadecathlon (fun g => isOscillator g 15)
      DecideMemoCache.empty).2 = true := by
  have h := decideMemoRun_correct pentadecathlon (fun g => isOscillator g 15)
      DecideMemoCache.empty (decideMemoOK_empty _)
  rw [h]
  exact pentadecathlon_period_15

end Life
end Conway

/-- Point d'entree `lake env lean --run` (exige un `main` au namespace
    racine) ; delegue au corps du banc dans `Conway.Life`. -/
def main : IO Unit := Conway.Life.benchMain
