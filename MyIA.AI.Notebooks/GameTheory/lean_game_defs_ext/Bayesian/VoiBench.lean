/-
  Banc `voi` — instances JSON transcrites exactement, contrôles certifiés
  ======================================================================

  Le banc `MyIA.AI.Notebooks/Probas/DecisionTheory/voi/` compare deux moteurs
  (Infer.NET et PyMC) sur un contrat JSON commun. Ce module ferme la troisième
  comparaison : la même instance, transcrite dans la représentation `NoisyProblem`
  de `Bayesian/InformationNoisy.lean`, et ses valeurs calculées **exactement**,
  sans échantillonnage ni tolérance.

  Les deux instances ci-dessous ne sont **pas** écrites à la main : elles sont
  produites par `voi/lean_voi_adapter.py`, qui lit le JSON, choisit les
  dénominateurs communs et refuse toute entrée invalide. Le test
  `voi/tests/test_lean_voi_adapter.py` compare ce bloc à la sortie courante de
  l'adaptateur, de sorte qu'une instance éditée à la main diverge et rougit.

  Échelles (documentées par l'adaptateur, jamais devinées) :

  - `benchForagePetrolier` : `Lp = 100`, `Lu = 1`. Toute valeur du module vaut
    donc 100 fois la valeur en euros.
  - `benchForageNonInformatif` : `Lp = 20`, `Lu = 1`. Toute valeur du module
    vaut donc 20 fois la valeur en euros.

  La conversion est exacte de bout en bout : `p s x = Lp * prior s * vraisemblance`,
  `u s a = Lu * utilité`, et aucune valeur n'est arrondie. Un désaccord entre les
  deux moteurs du banc et les théorèmes de ce module signalerait une erreur de
  conversion ou de modèle, jamais un bruit d'échantillonnage.
-/

import Bayesian.InformationNoisy

/-! ## Instances du banc, telles que produites par l'adaptateur -/

/- BEGIN ADAPTER-GENERATED -- ne pas editer a la main, regenerer -/

/-- Banc `voi/forage-petrolier.json` transcrit exactement : poids joints
    `prior x vraisemblance` ramenes a des entiers par `Lp = 100`.
    Toute valeur de ce module vaut donc 100 fois la valeur en euros. -/
def benchForagePetrolier : NoisyProblem where
  nS := 2
  nA := 2
  nX := 1
  p := fun s x =>
    if s.val = 0 then (if x.val = 0 then 27 else 3)
    else (if x.val = 0 then 14 else 56)
  u := fun s a =>
    if s.val = 0 then (if a.val = 0 then 1500000 else 200000)
    else (if a.val = 0 then -500000 else 200000)

/-- Banc `voi/forage-non-informatif.json` : meme probleme, test independant
    de l'etat. Sa table est exactement factorisee (`w = (3, 7)`, `q = (1, 1)`),
    ce qui permet de certifier le zero par le theoreme et non par evaluation. -/
def benchForageNonInformatif : NoisyProblem where
  nS := 2
  nA := 2
  nX := 1
  p := fun s x =>
    if s.val = 0 then (if x.val = 0 then 3 else 3)
    else (if x.val = 0 then 7 else 7)
  u := fun s a =>
    if s.val = 0 then (if a.val = 0 then 1500000 else 200000)
    else (if a.val = 0 then -500000 else 200000)

/- END ADAPTER-GENERATED -/

/-! ## Contrôle discriminant : le forage informatif

Le banc committé (`voi/comparison.json`) rapporte, pour ce problème, une EVSI
brute de 253 000 EUR côté Infer.NET et de 252 796 EUR côté PyMC (200 000 tirages,
graine 42). Les théorèmes ci-dessous rendent **253 000 exactement** : l'écart de
204 EUR du côté PyMC est du bruit d'échantillonnage, et il est mesurable comme
tel parce que la valeur exacte existe indépendamment des deux moteurs.

En unités du module (`Lp = 100`), le coût du test `60000` devient `6000000`. -/

theorem benchForagePetrolier_valueNoisyNoInfo :
    valueNoisyNoInfo benchForagePetrolier = 20000000 := by decide

theorem benchForagePetrolier_valueNoisySignal :
    valueNoisySignal benchForagePetrolier = 45300000 := by decide

theorem benchForagePetrolier_valueNoisyPerfect :
    valueNoisyPerfect benchForagePetrolier = 59000000 := by decide

/-- EVSI brute du banc informatif : 253 000 EUR, exactement. -/
theorem benchForagePetrolier_evsiRaw :
    evsiRaw benchForagePetrolier = 25300000 := by decide

/-- EVSI nette après le coût du test (60 000 EUR) : 193 000 EUR. -/
theorem benchForagePetrolier_evsiNet :
    evsiNet benchForagePetrolier 6000000 = 19300000 := by decide

/-- Le contrôle `discriminant` du contrat JSON, certifié et non plus seulement
    constaté : le test est informatif (`0 < EVSI nette`) mais imparfait
    (`EVSI nette < EVPI`). -/
theorem benchForagePetrolier_discriminant :
    0 < evsiNet benchForagePetrolier 6000000 ∧
      evsiNet benchForagePetrolier 6000000 <
        valueNoisyPerfect benchForagePetrolier - valueNoisyNoInfo benchForagePetrolier := by
  decide

/-! ## Contrôle négatif : le même forage, test indépendant de l'état

La table du contrat jumeau est exactement factorisée. Le zéro est donc obtenu
**par le théorème** — sans jamais évaluer l'instance — puis retrouvé par
`decide`, second instrument indépendant du premier. -/

theorem benchForageNonInformatif_factored :
    Factored benchForageNonInformatif (fun s => if s.val = 0 then 3 else 7) (fun _ => 1) := by
  intro s x
  dsimp only [benchForageNonInformatif]
  by_cases hs : s.val = 0 <;> by_cases hx : x.val = 0 <;> simp [hs, hx]

/-- **Zéro exact, par le théorème** : l'EVSI brute du banc négatif s'annule
    parce que sa table est factorisée. -/
theorem benchForageNonInformatif_evsiRaw :
    evsiRaw benchForageNonInformatif = 0 := by
  unfold evsiRaw
  rw [valueNoisySignal_eq_valueNoisyNoInfo_of_factored _ _ _
    benchForageNonInformatif_factored]
  omega

/-- Le même zéro, par **évaluation** : un second instrument, indépendant du
    premier. Un désaccord entre les deux signalerait une erreur de l'un ou de
    l'autre, jamais un arrondi. -/
theorem benchForageNonInformatif_evsiRaw_decide :
    evsiRaw benchForageNonInformatif = 0 := by decide

/-- Conséquence sur la décision : sans gain brut, la valeur nette est exactement
    l'opposé du coût du test — observer n'est jamais rentable ici. -/
theorem benchForageNonInformatif_evsiNet :
    evsiNet benchForageNonInformatif 1200000 = -1200000 := by decide

theorem benchForageNonInformatif_valueNoisyPerfect :
    valueNoisyPerfect benchForageNonInformatif = 11800000 := by decide

/-! ## Ancres d'axiomes

Aucun `sorryAx`, aucun `native_decide`, aucun `Classical.choice`. -/

#print axioms benchForagePetrolier_valueNoisyNoInfo
#print axioms benchForagePetrolier_valueNoisySignal
#print axioms benchForagePetrolier_valueNoisyPerfect
#print axioms benchForagePetrolier_evsiRaw
#print axioms benchForagePetrolier_evsiNet
#print axioms benchForagePetrolier_discriminant
#print axioms benchForageNonInformatif_factored
#print axioms benchForageNonInformatif_evsiRaw
#print axioms benchForageNonInformatif_evsiRaw_decide
#print axioms benchForageNonInformatif_evsiNet
#print axioms benchForageNonInformatif_valueNoisyPerfect
