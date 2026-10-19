import Mathlib

/-!
# McMillan — réalisation des longueurs (pli 3, EPIC #18706)

Le pli 1 (`PrefixCodes.lean`) a établi l'**inégalité de Kraft** : la somme de
Kraft d'un code préfixe ne dépasse jamais `1`. Ce module démontre la
**réciproque** — le sens « réalisation » du théorème de Kraft–McMillan :
si une liste de longueurs `(ℓ₁, …, ℓₙ)` triée dans l'ordre croissant satisfait
`Σᵢ 2 ^ (-ℓᵢ) ≤ 1`, alors il **existe** un code préfixe dont les mots ont
exactement ces longueurs. C'est la garantie qu'utilise le carnet Python
`Compression-02-HuffmanCanonique` quand il reconstruit un code depuis une
table de longueurs : toute bande de longueurs admissible est réalisable.

La preuve est **constructive** : elle exhibe le **code canonique**
(Schwartz–Miller 1964), celui qu'on range dans l'ordre lexicographique.
En traitant les longueurs par ordre croissant, chaque mot est l'écriture
binaire sur `ℓᵢ` bits d'un compteur :

* le premier mot est `c₁ = 0` (tous les zéros) ;
* au passage de `ℓᵢ` à `ℓᵢ₊₁`, le compteur devient
  `cᵢ₊₁ = (cᵢ + 1) · 2 ^ (ℓᵢ₊₁ - ℓᵢ)` — on saute **au-delà** de tous les
  prolongements du mot précédent, puis on décale.

Tout l'appareil arithmétique vit dans `ℕ`, à l'échelle `2 ^ L` (où `L` majore
toutes les longueurs) : l'hypothèse de Kraft s'écrit `mass L ls ≤ 2 ^ L`, et
l'invariant de la récurrence est `Inv L ℓ c queue` — le compteur et toute la
masse restante tiennent dans `2 ^ L`. C'est exactement le partage du gâteau
binaire du carnet 01 : chaque mot consomme sa part, et la contrainte de Kraft
est ce qui garantit qu'aucun compteur ne déborde.

Contenu :

1. `bits` — écriture binaire exacte de `c` sur `l` bits (MSB en tête), avec
   `bits_length` (longueur exacte), `bits_take` (les `k` bits de tête sont
   l'écriture de `c / 2 ^ (l - k)`) et `bits_inj` (injectivité sous `2 ^ l`).
2. `mass` / `Inv` — somme de Kraft remontée à l'échelle `2 ^ L` et invariant
   de masse de la récurrence, avec `inv_fits` (le compteur tient dans sa
   bande) et `inv_step` (l'invariant se propage au saut de compteur).
3. `canon` — la construction récursive elle-même.
4. `Pre` et ses deux lemmes de structure, puis `not_prefix_of_jumps` — le
   cœur : deux compteurs dont l'un saute au-delà des prolongements de
   l'autre donnent des mots incomparables.
5. `canon_above` / `canon_spec` — tout mot de la queue saute au-delà des
   prolongements du mot de tête ; la sortie est préfixe-libre et de
   longueurs exactes.
6. `mcmillan_converse` — la réciproque de Kraft sous forme d'existence.
7. Ancres `#eval` : les longueurs `(1, 2, 3, 3)` du code `a = 0, b = 10,
   c = 110, d = 111` du carnet 02, et le code fixe à 2 bits.

Roadmap (plis suivants) : le trie de décodage (tout code préfixe fini est
l'ensemble des feuilles d'un arbre), puis l'optimalité de Huffman.
-/

namespace CompressionLean

/-! ## Écriture binaire exacte -/

/-- Le mot binaire de `c` sur exactement `l` bits, bit de poids fort en tête :
`bits 3 6 = [true, true, false]`. -/
def bits : ℕ → ℕ → List Bool
  | 0, _ => []
  | l + 1, c => Nat.testBit c l :: bits l c

/-- Un mot de `bits` a exactement la longueur demandée. -/
theorem bits_length (l c : ℕ) : (bits l c).length = l := by
  induction l generalizing c with
  | zero => rfl
  | succ l ih => simp [bits, ih]

/-- Les `k` bits de tête de `bits l c` sont l'écriture du quotient
`c / 2 ^ (l - k)` : couper un mot canonique à hauteur `k`, c'est lire le
nombre dont il est le prolongement binaire. -/
theorem bits_take (l c k : ℕ) (hk : k ≤ l) :
    (bits l c).take k = bits k (c / 2 ^ (l - k)) := by
  induction l generalizing c k with
  | zero => cases hk; rfl
  | succ l ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hkl : k ≤ l := Nat.le_of_succ_le_succ hk
      have hshift : k + (l - k) = l := Nat.add_sub_cancel' hkl
      simp only [Nat.succ_sub_succ]
      show Nat.testBit c l :: (bits l c).take k =
        Nat.testBit (c / 2 ^ (l - k)) k :: bits k (c / 2 ^ (l - k))
      rw [ih c k hkl, Nat.testBit_div_two_pow, hshift]

/-- De mots égaux on lit l'égalité des bits bas. -/
theorem bits_testBit {l a b : ℕ} (h : bits l a = bits l b) :
    ∀ i < l, Nat.testBit a i = Nat.testBit b i := by
  induction l generalizing a b with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ l ih =>
    intro i hi
    have hcons : Nat.testBit a l :: bits l a = Nat.testBit b l :: bits l b := by
      simpa [bits] using h
    injection hcons with hhead htail
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | rfl
    · exact ih htail i hilt
    · exact hhead

/-- Monotonie de `2 ^ ·` : utilisée pour comparer les bandes de bits. -/
theorem pow_two_mono {m n : ℕ} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n := by
  have hsplit : 2 ^ m * 2 ^ (n - m) = 2 ^ n := by
    rw [← Nat.pow_add]; congr 1; omega
  have hge : 2 ^ m * 1 ≤ 2 ^ m * 2 ^ (n - m) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.two_pow_pos (n - m)))
  rwa [Nat.mul_one, hsplit] at hge

/-- `bits l` est injective sur `[0, 2 ^ l)` : deux compteurs distincts (et
bornés) donnent deux mots distincts. -/
theorem bits_inj {l a b : ℕ} (ha : a < 2 ^ l) (hb : b < 2 ^ l)
    (h : bits l a = bits l b) : a = b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hil : i < l
  · exact bits_testBit h i hil
  · have hle : l ≤ i := Nat.le_of_not_gt hil
    have ha' : Nat.testBit a i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (pow_two_mono hle))
    have hb' : Nat.testBit b i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (pow_two_mono hle))
    rw [ha', hb']

/-! ## Somme de Kraft à l'échelle `2 ^ L` -/

/-- Somme de Kraft remontée en entiers : `mass L ls = Σ ℓ ∈ ls, 2 ^ (L - ℓ)`.
L'hypothèse de Kraft `Σ 2 ^ (-ℓᵢ) ≤ 1` se lit `mass L ls ≤ 2 ^ L` dès que
`L` majore toutes les longueurs (on multiplie par `2 ^ L`). -/
def mass (L : ℕ) (ls : List ℕ) : ℕ :=
  (ls.map fun l => 2 ^ (L - l)).sum

/-- La masse d'une liste décompose tête / queue. -/
theorem mass_cons (L l : ℕ) (ls : List ℕ) :
    mass L (l :: ls) = 2 ^ (L - l) + mass L ls := by
  simp [mass]

/-- Invariant de masse au moment d'une émission : le compteur `c` (pour la
longueur `l`) et toute la masse restante tiennent dans `2 ^ L`. -/
def Inv (L l c : ℕ) (ls : List ℕ) : Prop :=
  c * 2 ^ (L - l) + mass L (l :: ls) ≤ 2 ^ L

/-- L'invariant garantit que le compteur tient dans sa bande : `c < 2 ^ l`,
donc `bits l c` est une écriture exacte. -/
theorem inv_fits (L l c : ℕ) (ls : List ℕ) (hlL : l ≤ L) (h : Inv L l c ls) :
    c < 2 ^ l := by
  have hA : 2 ^ (L - l) * 2 ^ l = 2 ^ L := by
    rw [← Nat.pow_add]; congr 1; omega
  simp only [Inv, mass_cons] at h
  have hring : (c + 1) * 2 ^ (L - l) = c * 2 ^ (L - l) + 2 ^ (L - l) := by ring
  have h1 : (c + 1) * 2 ^ (L - l) ≤ 2 ^ L := by omega
  rw [← hA, Nat.mul_comm (2 ^ (L - l)) (2 ^ l)] at h1
  have h3 : c + 1 ≤ 2 ^ l :=
    Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos (L - l))
  omega

/-- L'invariant se propage au saut de compteur : passer de `l` à `l''` avec
`c' = (c + 1) * 2 ^ (l'' - l)` préserve la contrainte de masse. C'est le
partage du gâteau : `(c + 1) * 2 ^ (L - l)`, c'est exactement le compteur
plus la masse émise jusqu'ici, redistribués à la nouvelle échelle. -/
theorem inv_step (L l l'' c : ℕ) (more : List ℕ) (hll : l ≤ l'') (hlL : l'' ≤ L)
    (h : Inv L l c (l'' :: more)) :
    Inv L l'' ((c + 1) * 2 ^ (l'' - l)) more := by
  have hpow : 2 ^ (l'' - l) * 2 ^ (L - l'') = 2 ^ (L - l) := by
    rw [← Nat.pow_add]; congr 1; omega
  simp only [Inv, mass_cons] at h ⊢
  rw [Nat.mul_assoc, hpow]
  have hring : (c + 1) * 2 ^ (L - l) = c * 2 ^ (L - l) + 2 ^ (L - l) := by ring
  omega

/-! ## Le code canonique -/

/-- Construction du code canonique : longueurs **triées croissantes**,
compteur initial `c`. Chaque mot est `bits ℓ c` ; au passage à la longueur
suivante `ℓ'`, le compteur saute à `(c + 1) * 2 ^ (ℓ' - ℓ)`. -/
def canon : List ℕ → ℕ → List (List Bool)
  | [], _ => []
  | [l], c => [bits l c]
  | l :: l' :: ls, c =>
      bits l c :: canon (l' :: ls) ((c + 1) * 2 ^ (l' - l))

/-- Liste de longueurs triée en ordre croissant (pairwise sur `Nat.le`). -/
abbrev SortedLe (ls : List ℕ) : Prop := List.Pairwise (fun a b => a ≤ b) ls

/-- `a` est un préfixe de `b` : `b` prolonge `a` à droite. -/
def Pre (a b : List Bool) : Prop := ∃ t, a ++ t = b

/-- La relation de préfixe-liberté : deux mots, aucun n'est préfixe de
l'autre. -/
def PrefixFreeR (a b : List Bool) : Prop :=
  ¬ Pre a b ∧ ¬ Pre b a

/-! ## Deux mots canoniques ne se prolongent pas -/

/-- Les `a.length` premiers éléments de `a ++ t` sont exactement `a`. -/
theorem take_append_exact (a t : List Bool) : (a ++ t).take a.length = a := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    show (a :: (as ++ t)).take (List.length as + 1) = a :: as
    rw [List.take_succ_cons, ih]

/-- Un préfixe est au plus aussi long que son prolongement. -/
theorem prefix_length_le {a b : List Bool} (h : Pre a b) : a.length ≤ b.length := by
  obtain ⟨t, ht⟩ := h
  rw [← ht, List.length_append]
  omega

/-- Deux mots de même longueur dont l'un est préfixe de l'autre sont égaux. -/
theorem eq_of_prefix_of_length_eq {a b : List Bool} (h : Pre a b)
    (hlen : a.length = b.length) : a = b := by
  obtain ⟨t, ht⟩ := h
  rw [← ht, List.length_append] at hlen
  have ht0 : t.length = 0 := by omega
  obtain rfl : t = [] := by simpa using ht0
  exact (ht.symm.trans (List.append_nil a)).symm

/-- Le cœur du théorème : si le compteur `cw` du mot long saute au-delà de
tous les prolongements du mot court — `(c + 1) * 2 ^ (ℓ - l) ≤ cw` — alors
les deux mots `bits l c` et `bits ℓ cw` sont incomparables pour la relation
de préfixe. La condition se lit : « les `l` bits de tête de `cw` ne sont pas
ceux de `c` », puisque prolonger `bits l c` en `ℓ` bits, c'est écrire un
compteur dans la bande `[c * 2 ^ (ℓ - l), (c + 1) * 2 ^ (ℓ - l))`. -/
theorem not_prefix_of_jumps {l ℓ c cw : ℕ} (hle : l ≤ ℓ) (hc : c < 2 ^ l)
    (hcw : cw < 2 ^ ℓ) (hjump : (c + 1) * 2 ^ (ℓ - l) ≤ cw) :
    ¬ Pre (bits l c) (bits ℓ cw) ∧ ¬ Pre (bits ℓ cw) (bits l c) := by
  constructor
  · rintro ⟨t, ht⟩
    have htake : (bits ℓ cw).take l = bits l c := by
      rw [← ht]
      have hap := take_append_exact (bits l c) t
      rwa [bits_length] at hap
    rw [bits_take ℓ cw l hle] at htake
    have hbound : cw / 2 ^ (ℓ - l) < 2 ^ l := by
      apply Nat.div_lt_of_lt_mul
      calc cw < 2 ^ ℓ := hcw
        _ = 2 ^ (ℓ - l) * 2 ^ l := by rw [← Nat.pow_add]; congr 1; omega
    have hdiv : cw / 2 ^ (ℓ - l) = c := bits_inj hbound hc htake
    have hmod : cw % 2 ^ (ℓ - l) < 2 ^ (ℓ - l) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsplit : cw / 2 ^ (ℓ - l) * 2 ^ (ℓ - l) + cw % 2 ^ (ℓ - l) = cw := by
      have := Nat.div_add_mod cw (2 ^ (ℓ - l))
      rwa [Nat.mul_comm] at this
    rw [hdiv] at hsplit
    have hring : (c + 1) * 2 ^ (ℓ - l) = c * 2 ^ (ℓ - l) + 2 ^ (ℓ - l) := by ring
    omega
  · rintro ⟨t, ht⟩
    have hlen := prefix_length_le ⟨t, ht⟩
    simp only [bits_length] at hlen
    have hℓl : ℓ = l := Nat.le_antisymm hlen hle
    rw [hℓl] at ht hcw hjump
    have hwords : bits l cw = bits l c :=
      eq_of_prefix_of_length_eq ⟨t, ht⟩ (by simp [bits_length])
    have hcwfit : cw = c := bits_inj hcw hc hwords
    rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at hjump
    omega

/-! ## Spécification de la construction -/

/-- Tout mot émis par la construction saute au-delà des prolongements d'une
émission précédente `bits p cp` : si la liste restante commence à `hd` et que
le compteur courant `c` vérifie `(cp + 1) * 2 ^ (hd - p) ≤ c` (saut cumulé),
alors chaque mot `bits ℓ cw` émis satisfait `p ≤ ℓ` et
`(cp + 1) * 2 ^ (ℓ - p) ≤ cw`. L'inégalité (et non l'égalité) est ce qui
fait composer les sauts le long de la récurrence. -/
theorem canon_above (L p cp : ℕ) : ∀ (ls : List ℕ) (c : ℕ),
    SortedLe ls → (∀ x ∈ ls, p ≤ x) → (∀ x ∈ ls, x ≤ L) →
    (∃ hd tl, ls = hd :: tl ∧ (cp + 1) * 2 ^ (hd - p) ≤ c ∧ Inv L hd c tl) →
    ∀ w ∈ canon ls c,
      ∃ ℓ cw, w = bits ℓ cw ∧ cw < 2 ^ ℓ ∧ p ≤ ℓ ∧ (cp + 1) * 2 ^ (ℓ - p) ≤ cw := by
  intro ls
  induction ls with
  | nil =>
    intro c _ _ _ hhead w hw
    obtain ⟨hd, tl, heq⟩ := hhead
    exact absurd heq (by simp)
  | cons l rest ih =>
    intro c hsort hge hleL hhead w hw
    cases rest with
    | nil =>
      obtain ⟨hd, tl, heq, hjump0, hinv⟩ := hhead
      injection heq with h1 h2
      subst h1; subst h2
      simp only [canon, List.mem_singleton] at hw
      subst hw
      have hlL : l ≤ L := hleL l (by simp)
      have hcfit : c < 2 ^ l := inv_fits L l c [] hlL hinv
      exact ⟨l, c, rfl, hcfit, hge l (by simp), hjump0⟩
    | cons l'' more =>
      obtain ⟨hd, tl, heq, hjump0, hinv⟩ := hhead
      injection heq with h1 h2
      subst h1; subst h2
      have hsortT : SortedLe (l'' :: more) := hsort.tail
      have hgeT : ∀ x ∈ l'' :: more, p ≤ x :=
        fun x hx => hge x (List.mem_cons_of_mem _ hx)
      have hleLT : ∀ x ∈ l'' :: more, x ≤ L :=
        fun x hx => hleL x (List.mem_cons_of_mem _ hx)
      have hll : l ≤ l'' := (List.pairwise_cons.mp hsort).1 l'' (by simp)
      have hlpl : p ≤ l := hge l (by simp)
      have hinv' : Inv L l'' ((c + 1) * 2 ^ (l'' - l)) more :=
        inv_step L l l'' c more hll (hleL l'' (by simp)) hinv
      have hcfit : c < 2 ^ l := inv_fits L l c (l'' :: more) (hleL l (by simp)) hinv
      -- le saut se compose : c' = (c + 1) * 2^(l'' - l) dépasse lui-même les
      -- prolongements cumulés de bits p cp
      have hpow : (cp + 1) * 2 ^ (l - p) * 2 ^ (l'' - l) = (cp + 1) * 2 ^ (l'' - p) := by
        have hexp : (l - p) + (l'' - l) = l'' - p := by omega
        rw [Nat.mul_assoc, ← Nat.pow_add, hexp]
      have hcjump : (cp + 1) * 2 ^ (l'' - p) ≤ (c + 1) * 2 ^ (l'' - l) := by
        have h1 : (cp + 1) * 2 ^ (l - p) ≤ c := hjump0
        calc (cp + 1) * 2 ^ (l'' - p)
            = (cp + 1) * 2 ^ (l - p) * 2 ^ (l'' - l) := hpow.symm
          _ ≤ c * 2 ^ (l'' - l) := Nat.mul_le_mul_right _ h1
          _ ≤ (c + 1) * 2 ^ (l'' - l) := Nat.mul_le_mul_right _ (Nat.le_succ c)
      simp only [canon] at hw
      rcases List.mem_cons.mp hw with rfl | hwtail
      · exact ⟨l, c, rfl, hcfit, hlpl, hjump0⟩
      · exact ih ((c + 1) * 2 ^ (l'' - l)) hsortT hgeT hleLT
          ⟨l'', more, rfl, hcjump, hinv'⟩ w hwtail

/-- Spécification complète de `canon` : sous l'hypothèse de Kraft (à
l'échelle `2 ^ L`) et pour des longueurs triées croissantes majorées par
`L`, la sortie est préfixe-libre et de longueurs exactes. -/
theorem canon_spec (L : ℕ) : ∀ (ls : List ℕ) (c : ℕ),
    SortedLe ls → (∀ x ∈ ls, x ≤ L) →
    (∃ hd tl, ls = hd :: tl ∧ Inv L hd c tl) →
    (canon ls c).Pairwise PrefixFreeR ∧ (canon ls c).map List.length = ls := by
  intro ls
  induction ls with
  | nil => intro c _ _ _; exact ⟨List.Pairwise.nil, rfl⟩
  | cons l rest ih =>
    intro c hsort hL hhead
    cases rest with
    | nil =>
      refine ⟨List.pairwise_singleton _ _, ?_⟩
      simp [canon, bits_length]
    | cons l'' more =>
      obtain ⟨hd, tl, heq, hinv⟩ := hhead
      injection heq with h1 h2
      subst h1; subst h2
      have hsortT : SortedLe (l'' :: more) := hsort.tail
      have hll : l ≤ l'' := (List.pairwise_cons.mp hsort).1 l'' (by simp)
      have hinv' : Inv L l'' ((c + 1) * 2 ^ (l'' - l)) more :=
        inv_step L l l'' c more hll (hL l'' (by simp)) hinv
      obtain ⟨hpf, hlen⟩ := ih ((c + 1) * 2 ^ (l'' - l)) hsortT
        (fun x hx => hL x (List.mem_cons_of_mem _ hx))
        ⟨l'', more, rfl, hinv'⟩
      refine ⟨?_, ?_⟩
      · simp only [canon]
        refine List.pairwise_cons.mpr ⟨?_, hpf⟩
        intro w hw
        obtain ⟨ℓ, cw, rfl, hcwfit, hlℓ, hjump⟩ :=
          canon_above L l c (l'' :: more) ((c + 1) * 2 ^ (l'' - l)) hsortT
            (fun x hx => (List.pairwise_cons.mp hsort).1 x hx)
            (fun x hx => hL x (List.mem_cons_of_mem _ hx))
            ⟨l'', more, rfl, le_refl _, hinv'⟩ w hw
        exact not_prefix_of_jumps hlℓ (inv_fits L l c (l'' :: more) (hL l (by simp)) hinv)
          hcwfit hjump
      · simp only [canon, List.map_cons, bits_length, hlen]

/-- **Réciproque de Kraft (théorème de McMillan, sens réalisation)** : toute
bande de longueurs triée croissante et admissible — `mass L ls ≤ 2 ^ L`,
c'est-à-dire `Σ 2 ^ (-ℓᵢ) ≤ 1` une fois tout remis à l'échelle `2 ^ L` —
est réalisée par un code préfixe : le code canonique, dont les mots ont
exactement les longueurs demandées. -/
theorem mcmillan_converse (L : ℕ) (ls : List ℕ) (hsort : SortedLe ls)
    (hL : ∀ l ∈ ls, l ≤ L) (hmass : mass L ls ≤ 2 ^ L) :
    ∃ ws : List (List Bool),
      ws.Pairwise PrefixFreeR ∧ ws.map List.length = ls := by
  cases ls with
  | nil => exact ⟨[], by simp⟩
  | cons l rest =>
    have hinv : Inv L l 0 rest := by
      simp only [Inv, Nat.zero_mul, Nat.zero_add]
      exact hmass
    obtain ⟨h1, h2⟩ := canon_spec L (l :: rest) 0 hsort hL ⟨l, rest, rfl, hinv⟩
    exact ⟨canon (l :: rest) 0, h1, h2⟩

/-! ## Ancres d'exécution -/

/- Le code du carnet 02 : longueurs `(1, 2, 3, 3)`, Kraft saturé
(`1/2 + 1/4 + 1/8 + 1/8 = 1`). On retrouve `a = 0`, `b = 10`,
`c = 110`, `d = 111` — la profondeur du trie du carnet, en mots. -/
#eval canon [1, 2, 3, 3] 0
-- [[false], [true, false], [true, true, false], [true, true, true]]

/- Masse de Kraft de la même bande, à l'échelle `2 ^ 3` :
`4 + 2 + 1 + 1 = 8 = 2 ^ 3` : la contrainte est saturée, chaque bit du
budget est consommé. -/
#eval mass 3 [1, 2, 3, 3]
-- 8

/- Le code fixe à 2 bits : quatre mots de longueur 2, tout l'espace. -/
#eval canon [2, 2, 2, 2] 0
-- [[false, false], [false, true], [true, false], [true, true]]

end CompressionLean
