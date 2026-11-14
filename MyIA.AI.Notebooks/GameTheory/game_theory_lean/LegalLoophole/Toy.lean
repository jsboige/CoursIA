/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
-/

/-!
# LegalLoophole jouet : les regles fiscales comme jeu formel

Compagnon Lean du carnet `GameTheory-23-Loopholes-Fiscaux-Python-Lean.ipynb`
(issue #25686, distillation de l'article Lexifina).

**Copie pedagogique declaree** (regle organ-first, voie retenue par
l'etape 0 de #25686) : ce module est un modele jouet REDUIT ecrit pour
ce depot — 3 comptes, 4 coups, montants symboliques sur `Nat`, zero
dependance (pas de Mathlib, compilable en quelques secondes). Il ne
reprend PAS le modele US complet, qui reste la reference citee :
`lexifina/global-law`, dossier `lean-proofs/USTax/Retirement/`
(`Rules.lean` + `Theorems.lean`, commit `24036e9a`, licence CC0 1.0,
toolchain v4.35.0, zero Mathlib — 5 comptes, 7 coups, limites 2025,
theoremes `pretax_conservation`, `no_escape`, `income_limit_void`,
`roth_ceiling`). Source : Yahya A., « Lean proof to search for US tax
loopholes », Lexifina, 09/11/2026 (rubrique *Opinion* ; point de vue
methodologique, pas une publication evaluee). Le portage reduit est
motive par l'echelle pedagogique et l'ecart de toolchain (leur v4.35.0
contre notre lake v4.33.0 : la dependance Lake epinglee exigerait un
bump global, ecarte a l'etape 0).

## Le jeu

Un contribuable a haut revenu (`incomeRestricted = true`) veut financer
son compte Roth. Le coup direct `directRoth` lui est interdit : tout
chemin passe par le compte traditionnel, ou la conversion est taxee au
pro-rata de la part pre-tax (`convertTax = n * pretax / (pretax + basis)`).
Les contributions (deductible ou non) partagent un budget annuel
`maxContrib` suivi par le champ `used`. La recherche bornee (carnet,
Python) retrouve la sequence backdoor sans qu'on la lui decrive ; les
theoremes ci-dessous la generalisent a toute profondeur et bornent le
gain.

La semantique est **executable** (`step`/`run` sur `Option`), le meme
comput que le miroir Python du carnet : `#eval` temoigne, les theoremes
prouvent.

## Theoremes

* `wealth_conservation` : la richesse totale (comptes + taxes payees au
  Tresor) est invariante — aucun coup ne cree d'argent. (Jouet du
  theoreme 1 de l'article : le pre-tax ne quitte le traditionnel qu'en
  etant taxe ou converti, jamais evapore.)
* `cash_floor` : le cash ne peut baisser que par les contributions
  (plafonnees par `maxContrib`) et les taxes payees.
* `roth_ceiling` : pour toute sequence legale, le Roth final est au plus
  `roth + pretax + basis + maxContrib` de l'etat initial — a toute
  profondeur, le gain d'argent neuf non taxe est plafonne par le budget
  de contribution. Corollaire : sur un IRA vide (`pretax = 0`,
  `basis = 0`), aucun plan legal ne met plus de `maxContrib` en Roth
  sans taxe.
* `backdoor_exists` : pour un IRA vide de pre-tax et du cash suffisant,
  il existe une sequence legale qui atteint EXACTEMENT le plafond sans
  payer un centime — le plan trouve par la recherche est optimal
  (voir `backdoor_optimal`).
-/

namespace LegalLoophole

/-- Lois du jouet : budget annuel de contribution et restriction de
revenu (le coup `directRoth` est interdit aux hauts revenus, limite
jouet de la §408A de l'article). Montants symboliques : 1 unite =
1 000 $. -/
structure TaxLaws where
  /-- Plafond annuel (partage) des contributions IRA jouet. -/
  maxContrib : Nat
  /-- `true` : revenu au-dela de la limite, contribution Roth directe
  interdite. -/
  incomeRestricted : Bool
  deriving Repr

/-- Etat du contribuable : 3 comptes (cash, traditionnel, Roth) plus le
compteur de budget annuel. Le traditionnel est ventile en part pre-tax
(deductible, sera taxee a la sortie) et part after-tax (`basis`, deja
taxee, convertible sans taxe supplementaire). -/
structure Account where
  /-- Compte courant : argent neuf, deja taxe. -/
  cash : Nat
  /-- Part pre-tax du compte traditionnel. -/
  pretax : Nat
  /-- Part after-tax (basis) du compte traditionnel. -/
  basis : Nat
  /-- Compte Roth : sorties non imposables. -/
  roth : Nat
  /-- Budget de contribution deja consomme cette annee. -/
  used : Nat
  deriving Repr

/-- Les quatre coups du jouet, chacun derive d'une provision citee par
l'article. -/
inductive Move where
  /-- Contribution Roth directe : cash vers Roth, sans taxe. Interdite
  aux hauts revenus (limite de revenu). -/
  | directRoth (n : Nat)
  /-- Contribution deductible : cash vers la part pre-tax (deductible
  aujourd'hui, taxee a la sortie). -/
  | contributeDeductible (n : Nat)
  /-- Contribution non deductible : cash vers la basis (deja taxee,
  convertible sans taxe supplementaire). -/
  | contributeNondeductible (n : Nat)
  /-- Conversion : du traditionnel vers le Roth, taxee au pro-rata de la
  part pre-tax convertie. -/
  | convert (n : Nat)
  deriving Repr

/-- Taxe d'une conversion de `n` depuis un etat : part pre-tax de la
conversion, arrondi au plancher (hypothese declaree du modele — voir le
carnet, section limites). -/
def convertTax (s : Account) (n : Nat) : Nat :=
  n * s.pretax / (s.pretax + s.basis)

/-- Un coup legal menant de `s` a un etat suivant, en prelevant `tax` au
Tresor. `none` = coup illegal dans cet etat. Les gardes de solvabilite
(taxe payable, parts convertibles, pas de troncature `Nat`) sont
explicites : `tax ≤ n`, `tax ≤ pretax` et `n - tax ≤ basis` sont des
hypotheses de modele declarees, demonstrables depuis
`n ≤ pretax + basis` par l'arithmetique de la division au plancher. -/
def step (laws : TaxLaws) (s : Account) : Move → Option (Account × Nat)
  | .directRoth n =>
      if !laws.incomeRestricted ∧ n ≤ laws.maxContrib ∧ n + s.used ≤ laws.maxContrib ∧ n ≤ s.cash then
        some ({ s with cash := s.cash - n, roth := s.roth + n, used := s.used + n }, 0)
      else none
  | .contributeDeductible n =>
      if n ≤ laws.maxContrib ∧ n + s.used ≤ laws.maxContrib ∧ n ≤ s.cash then
        some ({ s with cash := s.cash - n, pretax := s.pretax + n, used := s.used + n }, 0)
      else none
  | .contributeNondeductible n =>
      if n ≤ laws.maxContrib ∧ n + s.used ≤ laws.maxContrib ∧ n ≤ s.cash then
        some ({ s with cash := s.cash - n, basis := s.basis + n, used := s.used + n }, 0)
      else none
  | .convert n =>
      let tax := convertTax s n
      if n ≤ s.pretax + s.basis ∧ tax ≤ n ∧ tax ≤ s.cash ∧ tax ≤ s.pretax ∧ n - tax ≤ s.basis then
        some ({ s with
                  cash := s.cash - tax
                  pretax := s.pretax - tax
                  basis := s.basis - (n - tax)
                  roth := s.roth + n }, tax)
      else none

/-- Execution d'une sequence de coups : etat final et taxe totale
payee, ou `none` si un coup est illegal en cours de route. -/
def run : TaxLaws → Account → List Move → Option (Account × Nat)
  | _, s, [] => some (s, 0)
  | laws, s, m :: ms =>
      match step laws s m with
      | some (s₁, t₁) =>
          match run laws s₁ ms with
          | some (s₂, t₂) => some (s₂, t₁ + t₂)
          | none => none
      | none => none

/-! ## Lemmes par coup -/

/-- Conservation pour un coup isole : richesse finale + taxe prelevee =
richesse initiale. Les gardes de `step` garantissent qu'aucune
soustraction ne tronque. -/
theorem step_conservation (laws : TaxLaws) (s : Account) (m : Move)
    (s₁ : Account) (t₁ : Nat) (h : step laws s m = some (s₁, t₁)) :
    s₁.cash + s₁.pretax + s₁.basis + s₁.roth + t₁
      = s.cash + s.pretax + s.basis + s.roth := by
  cases m with
  | directRoth n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show s.cash - n + s.pretax + s.basis + (s.roth + n) + 0
          = s.cash + s.pretax + s.basis + s.roth
        omega
      · simp at h
  | contributeDeductible n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show s.cash - n + (s.pretax + n) + s.basis + s.roth + 0
          = s.cash + s.pretax + s.basis + s.roth
        omega
      · simp at h
  | contributeNondeductible n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show s.cash - n + s.pretax + (s.basis + n) + s.roth + 0
          = s.cash + s.pretax + s.basis + s.roth
        omega
      · simp at h
  | convert n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show s.cash - convertTax s n + (s.pretax - convertTax s n)
            + (s.basis - (n - convertTax s n)) + (s.roth + n) + convertTax s n
          = s.cash + s.pretax + s.basis + s.roth
        simp only [convertTax] at hc
        obtain ⟨_, hn, _, _, _⟩ := hc
        simp only [convertTax]
        omega
      · simp at h

/-- Plancher du cash pour un coup isole, en forme ADDITIVE (composable
par induction : le `used` initial ne fuit pas dans la borne) : le cash
de depart plus le budget deja consomme est couvert par le cash final,
le budget final et la taxe ; et le budget consomme reste sous
`maxContrib` si l'etat de depart y etait deja. -/
theorem step_cash_floor (laws : TaxLaws) (s : Account) (m : Move)
    (s₁ : Account) (t₁ : Nat) (h : step laws s m = some (s₁, t₁))
    (hu : s.used ≤ laws.maxContrib) :
    s.cash + s.used ≤ s₁.cash + s₁.used + t₁ ∧ s₁.used ≤ laws.maxContrib := by
  cases m with
  | directRoth n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by show s.cash + s.used ≤ (s.cash - n) + (s.used + n) + 0; omega,
          by show s.used + n ≤ laws.maxContrib; omega⟩
      · simp at h
  | contributeDeductible n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by show s.cash + s.used ≤ (s.cash - n) + (s.used + n) + 0; omega,
          by show s.used + n ≤ laws.maxContrib; omega⟩
      · simp at h
  | contributeNondeductible n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by show s.cash + s.used ≤ (s.cash - n) + (s.used + n) + 0; omega,
          by show s.used + n ≤ laws.maxContrib; omega⟩
      · simp at h
  | convert n =>
      simp only [step] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by
            show s.cash + s.used ≤ (s.cash - convertTax s n) + s.used + convertTax s n
            omega,
          by show s.used ≤ laws.maxContrib; omega⟩
      · simp at h

/-! ## Theoreme 1 : aucun coup ne cree d'argent -/

/-- La richesse totale — les trois comptes plus les taxes versees au
Tresor — est invariante le long de toute execution legale. Jouet du
theoreme 1 de l'article (le pre-tax ne quitte le traditionnel qu'en
etant taxe ou converti, jamais evapore). -/
theorem wealth_conservation (laws : TaxLaws) (s : Account) :
    ∀ ms s' tax, run laws s ms = some (s', tax) →
      s'.cash + s'.pretax + s'.basis + s'.roth + tax
        = s.cash + s.pretax + s.basis + s.roth := by
  intro ms
  induction ms generalizing s with
  | nil =>
      intro s' tax h
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      omega
  | cons m ms ih =>
      intro s' tax h
      simp only [run] at h
      split at h
      · next s₁ t₁ hstep =>
        split at h
        · next s₂ t₂ hrun =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have h1 := step_conservation laws s m s₁ t₁ hstep
          have h2 := ih s₁ s₂ t₂ hrun
          omega
        · simp at h
      · simp at h

/-- Le cash ne peut baisser que par les contributions (toutes comprises
dans `used`, lui-meme plafonne par `maxContrib`) et les taxes payees —
forme additive composable : `cash initial + budget initial consomme`
reste couvert par `cash final + budget final + taxes totales`. -/
theorem cash_floor (laws : TaxLaws) (s : Account) (hu : s.used ≤ laws.maxContrib) :
    ∀ ms s' tax, run laws s ms = some (s', tax) →
      s.cash + s.used ≤ s'.cash + s'.used + tax ∧ s'.used ≤ laws.maxContrib := by
  intro ms
  induction ms generalizing s with
  | nil =>
      intro s' tax h
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, hu⟩
  | cons m ms ih =>
      intro s' tax h
      simp only [run] at h
      split at h
      · next s₁ t₁ hstep =>
        split at h
        · next s₂ t₂ hrun =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hstep' := step_cash_floor laws s m s₁ t₁ hstep hu
          have ih' := ih s₁ hstep'.2 s₂ t₂ hrun
          exact ⟨by omega, ih'.2⟩
        · simp at h
      · simp at h

/-! ## Theoreme 2 : le plafond -/

/-- Pour toute sequence legale — de n'importe quelle longueur, depuis
n'importe quel etat — le Roth final est au plus le Roth initial augmente
du traditionnel initial et du budget de contribution annuel. En
particulier sur un IRA vide (`pretax = 0`, `basis = 0`) : aucun plan
legal ne met plus de `maxContrib` en Roth, taxe ou pas. C'est le jouet
du theoreme 4 de l'article (plafond annuel). -/
theorem roth_ceiling (laws : TaxLaws) (s : Account) (hu : s.used ≤ laws.maxContrib) :
    ∀ ms s' tax, run laws s ms = some (s', tax) →
      s'.roth ≤ s.roth + s.pretax + s.basis + laws.maxContrib := by
  intro ms s' tax h
  have h1 := wealth_conservation laws s ms s' tax h
  have h2 := cash_floor laws s hu ms s' tax h
  omega

/-! ## Le temoin : la sequence backdoor atteint le plafond -/

/-- Meme bloque en contribution directe (`incomeRestricted = true`), un
contribuable disposant de cash et d'un IRA vide trouve une sequence
legale qui atteint EXACTEMENT le plafond `maxContrib` sans payer un
centime : contribution non deductible (l'argent neuf entre en basis,
deja taxee), puis conversion (la basis se convertit sans taxe
supplementaire). C'est le jouet du theoreme 3 de l'article — la limite
de revenu est contournable par construction dans le modele. -/
theorem backdoor_exists (laws : TaxLaws) (s : Account)
    (hp : s.pretax = 0) (hb : s.basis = 0) (hu : s.used = 0)
    (hcash : laws.maxContrib ≤ s.cash) :
    ∃ ms s' tax, run laws s ms = some (s', tax) ∧ tax = 0
      ∧ s'.roth = s.roth + laws.maxContrib
      ∧ s'.basis = 0 ∧ s'.used = laws.maxContrib := by
  refine ⟨[.contributeNondeductible laws.maxContrib, .convert laws.maxContrib],
    { cash := s.cash - laws.maxContrib, pretax := 0, basis := 0,
      roth := s.roth + laws.maxContrib, used := laws.maxContrib },
    0, ?_, rfl, rfl, rfl, rfl⟩
  simp [run, step, convertTax, hp, hb, hu, hcash]

/-- Sur un IRA vide, le temoin de `backdoor_exists` atteint exactement
le plafond de `roth_ceiling` : le plan trouve par la recherche bornee
est OPTIMAL dans le jouet — aucune sequence legale, de quelque
profondeur que ce soit, ne fait mieux. -/
theorem backdoor_optimal (laws : TaxLaws) (s : Account)
    (hp : s.pretax = 0) (hb : s.basis = 0) (hu : s.used = 0)
    (hcash : laws.maxContrib ≤ s.cash) :
    (∃ ms s' tax, run laws s ms = some (s', tax) ∧ tax = 0
        ∧ s'.roth = s.roth + laws.maxContrib)
    ∧ (∀ ms s' tax, run laws s ms = some (s', tax) →
        s'.roth ≤ s.roth + laws.maxContrib) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ms, s', tax, hrun, htax, hroth, _, _⟩ :=
      backdoor_exists laws s hp hb hu hcash
    exact ⟨ms, s', tax, hrun, htax, hroth⟩
  · intro ms s' tax hrun
    have h := roth_ceiling laws s (by omega) ms s' tax hrun
    omega

/- Temoin executable : les lois jouet (plafond 7, haut revenu) et la
sequence backdoor retrouvee par la recherche bornee du carnet. Taxe
totale nulle, Roth +7, budget epuise — exactement le plafond. -/
#eval run { maxContrib := 7, incomeRestricted := true }
      { cash := 10, pretax := 0, basis := 0, roth := 0, used := 0 }
      [.contributeNondeductible 7, .convert 7]

/- Contre-temoin executable : avec du pre-tax deja present dans l'IRA,
la meme sequence paie le pro-rata (ici 7 * 3 / (3 + 7) = 2) — le
backdoor ne fonctionne que sur un IRA vide, exactement ce que la
recherche bornee du carnet met en evidence. -/
#eval run { maxContrib := 7, incomeRestricted := true }
      { cash := 10, pretax := 3, basis := 0, roth := 0, used := 0 }
      [.contributeNondeductible 7, .convert 7]

end LegalLoophole
