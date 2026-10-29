import EnvelopeProperty.Cartier.Jacobian

/-!
# Independence of the Cartier operator from the `p`-basis

Let `F` be a field of characteristic `p` and `F^p` its subfield of `p`-th powers. A `p`-basis `y` of
`F` gives an `F^p`-basis of `F` (the monomials `y^a`, `a ∈ [0,p)^σ`), so all `p`-bases of `F` have the
same size, and a family of that size whose monomials are `F^p`-linearly independent is a `p`-basis
(`isPBasis_of_linearIndependent`).

*Exchange.* If `∂t/∂y_i ≠ 0` then `y[i ↦ t]` is again a `p`-basis (`IsPBasis.update`): the powers
`t^n`, `n < p`, are independent over the field of constants of `∂/∂y_i`
(`linearIndependent_pow_of_derivation`). Given two `p`-bases `y`, `u` and `u_j` not among the `y`,
some `y_i` not among the `u` has `∂u_j/∂y_i ≠ 0` (`IsPBasis.exists_pderiv_ne_zero`, from
`1 = ∂u_j/∂u_j = ∑_i (∂y_i/∂u_j)(∂u_j/∂y_i)`).

*Main theorem* (`IsPBasis.trace_eq_trace_jac_pow_mul`). For any two `p`-bases `y`, `u` of `F`
`Φ_u(f) = Φ_y(J(y/u)^{p-1} f)`, `J(y/u) = det(∂y_i/∂u_j)`;
equivalently the Cartier operator on top forms, `C(f du) = Φ_u(f) du`, does not depend on the
`p`-basis: `C(f J du) = Φ_u(fJ) du = Φ_y(f) J du = C(f dy)` for `dy = J du`. By induction on the
number of `u_j` not among the `y_i`, using the one-step case `IsPBasis.trace_update`, the chain rule
`IsPBasis.jac_mul` and the case of a permutation.

This is the classical fact that makes the Cartier operator (the Frobenius trace on top forms)
intrinsic, used in the proof of FHX Lemma 3.3 (`lem:divisorial-trace-estimate`).
-/

noncomputable section

open scoped NNReal ENNReal Topology

namespace EnvelopeProperty.Cartier

open Finset Module

variable {F : Type*} [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]

/-! ### The subfield of `p`-th powers -/

/-- The subfield `F^p` of `p`-th powers. -/
abbrev pthPowers : Subfield F :=
  (frobenius F p).fieldRange

variable {p}

theorem pow_mem_pthPowers (c : F) : c ^ p ∈ pthPowers (F := F) p :=
  ⟨c, frobenius_def p c⟩

theorem exists_pow_eq_of_mem_pthPowers {x : F} (hx : x ∈ pthPowers (F := F) p) :
    ∃ c : F, c ^ p = x := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c, (frobenius_def p c).symm⟩

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The monomials of a `p`-basis are linearly independent over `F^p`. -/
theorem IsPBasis.linearIndependent {y : σ → F} (hy : IsPBasis p y) :
    LinearIndependent (pthPowers (F := F) p) (fun a : Box σ p => mono y a.toNat) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  choose c hc using fun b => exists_pow_eq_of_mem_pthPowers (g b).2
  have h0 : pSum p y c = 0 := by
    rw [pSum_apply, ← hg]
    refine sum_congr rfl fun b _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, hc b]
  have := hy.injective (h0.trans (map_zero _).symm)
  have hca : c a = 0 := congr_fun this a
  apply Subtype.ext
  rw [← hc a, hca, zero_pow hp.out.ne_zero]
  rfl

/-- The monomials of a `p`-basis span `F` over `F^p`. -/
theorem IsPBasis.span_eq_top {y : σ → F} (hy : IsPBasis p y) :
    Submodule.span (pthPowers (F := F) p) (Set.range fun a : Box σ p => mono y a.toNat) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun a => ⟨hy.coeff f a ^ p, pow_mem_pthPowers _⟩, ?_⟩
  conv_rhs => rw [← hy.sum_coeff f]
  refine sum_congr rfl fun a _ => ?_
  rw [Subfield.smul_def, smul_eq_mul]

/-- The `F^p`-basis of `F` given by the monomials of a `p`-basis. -/
def IsPBasis.basis {y : σ → F} (hy : IsPBasis p y) : Basis (Box σ p) (pthPowers (F := F) p) F :=
  Basis.mk hy.linearIndependent hy.span_eq_top.ge

theorem IsPBasis.finrank_eq {y : σ → F} (hy : IsPBasis p y) :
    finrank (pthPowers (F := F) p) F = p ^ Fintype.card σ := by
  rw [finrank_eq_card_basis hy.basis, Fintype.card_fun, Fintype.card_fin]

/-- All `p`-bases of a field have the same size. -/
theorem IsPBasis.card_eq {σ' : Type*} [Fintype σ'] [DecidableEq σ'] {y : σ → F} {y' : σ' → F}
    (hy : IsPBasis p y) (hy' : IsPBasis p y') : Fintype.card σ' = Fintype.card σ := by
  have h := hy.finrank_eq.symm.trans hy'.finrank_eq
  exact (Nat.pow_right_injective hp.out.two_le h).symm

/-- A family of the right size whose monomials are independent over `F^p` is a `p`-basis. -/
theorem isPBasis_of_linearIndependent {σ' : Type*} [Fintype σ'] [DecidableEq σ'] {y : σ → F}
    (hy : IsPBasis p y) {y' : σ' → F} (hcard : Fintype.card σ' = Fintype.card σ)
    (hli : LinearIndependent (pthPowers (F := F) p) fun a : Box σ' p => mono y' a.toNat) :
    IsPBasis p y' := by
  have hcard' : Fintype.card (Box σ' p) = finrank (pthPowers (F := F) p) F := by
    rw [hy.finrank_eq, Fintype.card_fun, Fintype.card_fin, hcard]
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard'
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h0 : ∑ a, (⟨c a ^ p, pow_mem_pthPowers _⟩ : pthPowers (F := F) p) • mono y' a.toNat = 0 := by
      rw [← hc, pSum_apply]
      refine sum_congr rfl fun a _ => ?_
      rw [Subfield.smul_def, smul_eq_mul]
    have := Fintype.linearIndependent_iff.1 hli _ h0
    funext a
    have ha := congrArg Subtype.val (this a)
    exact pow_eq_zero_iff hp.out.ne_zero |>.1 ha
  · intro f
    have hf : f ∈ Submodule.span (pthPowers (F := F) p)
        (Set.range fun a : Box σ' p => mono y' a.toNat) := by rw [hspan]; trivial
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hf
    choose c hc using fun b => exists_pow_eq_of_mem_pthPowers (g b).2
    refine ⟨c, ?_⟩
    rw [pSum_apply, ← hg]
    refine sum_congr rfl fun b _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, hc b]

/-! ### Constants of a derivation -/

/-- The subfield of constants of a derivation of a field. -/
def kerSubfield (D : Derivation ℤ F F) : Subfield F where
  carrier := {x | D x = 0}
  zero_mem' := D.map_zero
  one_mem' := D.map_one_eq_zero
  add_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq] at *; rw [map_add, hx, hy, add_zero]
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at *; rw [map_neg, hx, neg_zero]
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  inv_mem' x hx := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Derivation.leibniz_inv, hx, smul_zero]

theorem mem_kerSubfield {D : Derivation ℤ F F} {x : F} : x ∈ kerSubfield D ↔ D x = 0 :=
  Iff.rfl

/-- If `Dt ≠ 0` then `1, t, …, t^{p-1}` are linearly independent over the constants of `D`. -/
theorem linearIndependent_pow_of_derivation (D : Derivation ℤ F F) {t : F} (ht : D t ≠ 0) :
    LinearIndependent (kerSubfield D) (fun n : Fin p => t ^ (n : ℕ)) := by
  -- the polynomial relations of degree `≤ d < p` with constant coefficients are trivial
  have key : ∀ d : ℕ, d < p → ∀ c : ℕ → F, (∀ n, D (c n) = 0) → (∀ n, d < n → c n = 0) →
      ∑ n ∈ range (d + 1), c n * t ^ n = 0 → ∀ n, c n = 0 := by
    intro d
    induction d with
    | zero =>
      intro _ c _ hc hsum n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hsum
      · exact hc n hn
    | succ d ih =>
      intro hd c hD hc hsum
      -- differentiate the relation
      have hder : ∑ m ∈ range (d + 1), (((m + 1 : ℕ) : F) * c (m + 1)) * t ^ m = 0 := by
        have h1 := congrArg D hsum
        rw [map_zero, map_sum] at h1
        have h2 : ∑ n ∈ range (d + 1 + 1), D (c n * t ^ n) =
            (∑ m ∈ range (d + 1), (((m + 1 : ℕ) : F) * c (m + 1)) * t ^ m) * D t := by
          rw [sum_range_succ', sum_mul]
          simp only [pow_zero, mul_one, hD, add_zero]
          refine sum_congr rfl fun m _ => ?_
          rw [Derivation.leibniz, hD, smul_zero, add_zero, Derivation.leibniz_pow, smul_eq_mul,
            nsmul_eq_mul, Nat.add_sub_cancel]
          ring
        rw [h2] at h1
        exact (mul_eq_zero.1 h1).resolve_right ht
      have hc' := ih (by omega) (fun m => ((m + 1 : ℕ) : F) * c (m + 1))
        (fun m => by rw [Derivation.leibniz, hD, smul_zero, Derivation.map_natCast, smul_zero,
          add_zero])
        (fun m hm => by rw [hc (m + 1) (by omega), mul_zero]) hder
      have hcs : ∀ m, m ≤ d → c (m + 1) = 0 := by
        intro m hm
        have hu : IsUnit ((m + 1 : ℕ) : F) := isUnit_natCast_of_not_dvd (fun h => by
          have := Nat.le_of_dvd (Nat.succ_pos m) h
          omega)
        exact (hu.mul_right_eq_zero).1 (hc' m)
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [sum_range_succ'] at hsum
        rw [sum_eq_zero (fun m hm => by rw [hcs m (by simp at hm; omega), zero_mul])] at hsum
        simpa using hsum
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        by_cases hm : m ≤ d
        · exact hcs m hm
        · exact hc (m + 1) (by omega)
  rw [Fintype.linearIndependent_iff]
  intro g hg n
  let c : ℕ → F := fun k => if h : k < p then (g ⟨k, h⟩ : F) else 0
  have hp1 : p - 1 < p := Nat.sub_lt hp.out.pos one_pos
  have hsum : ∑ k ∈ range (p - 1 + 1), c k * t ^ k = 0 := by
    rw [Nat.sub_add_cancel hp.out.one_lt.le, ← hg, Finset.sum_range (fun k => c k * t ^ k)]
    refine sum_congr rfl fun k _ => ?_
    simp only [c, k.2, dif_pos, Subfield.smul_def, smul_eq_mul]
  have := key (p - 1) hp1 c (fun k => by
      by_cases hk : k < p
      · simp only [c, hk, dif_pos]; exact (g ⟨k, hk⟩).2
      · simp only [c, hk, dif_neg, not_false_eq_true, map_zero])
    (fun k hk => by simp only [c, show ¬ k < p by omega, dif_neg, not_false_eq_true]) hsum n
  apply Subtype.ext
  simpa [c, n.2] using this

/-! ### Exchange -/

variable {y u : σ → F}

/-- A `p`-basis of a field is an injective family. -/
theorem IsPBasis.injective_family (hy : IsPBasis p y) : Function.Injective y := by
  intro i j hij
  by_contra hne
  have h1 := hy.pderiv_self i i
  have h2 := hy.pderiv_self i j
  rw [if_pos rfl] at h1
  rw [if_neg hne, ← hij, h1] at h2
  exact one_ne_zero h2

omit [Fintype σ] hp in
theorem Box.toNat_update (a : Box σ p) (i : σ) (n : Fin p) :
    Box.toNat (Function.update a i n) = Function.update a.toNat i n := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Box.toNat]
  · simp [Box.toNat, Function.update_of_ne hj]

/-- **Exchange criterion.** If `∂t/∂y_i ≠ 0` then `y[i ↦ t]` is a `p`-basis. -/
theorem IsPBasis.update (hy : IsPBasis p y) {i : σ} {t : F} (ht : hy.pderiv i t ≠ 0) :
    IsPBasis p (Function.update y i t) := by
  refine isPBasis_of_linearIndependent hy rfl ?_
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set L := kerSubfield (hy.pderiv i)
  -- the coefficient of `t^n`
  let κ : Fin p → F := fun n =>
    ∑ a ∈ univ.filter (fun a : Box σ p => a i = n), (g a : F) * mono y (Function.update a.toNat i 0)
  have hκL : ∀ n, κ n ∈ L := by
    intro n
    refine L.sum_mem fun a _ => L.mul_mem ?_ ?_
    · obtain ⟨c, hc⟩ := (g a).2
      rw [mem_kerSubfield, ← hc, frobenius_def p c, derivation_pow_char]
    · rw [mem_kerSubfield]
      simpa using hy.pderiv_pow_mul_mono_of_eq_zero i 1 (n := Function.update a.toNat i 0)
        (by simp)
  have hrel : ∑ n : Fin p, (⟨κ n, hκL n⟩ : L) • t ^ (n : ℕ) = 0 := by
    rw [← hg]
    simp only [Subfield.smul_def, smul_eq_mul, κ, sum_mul]
    rw [← Finset.sum_fiberwise univ (fun a : Box σ p => a i)]
    refine sum_congr rfl fun n _ => sum_congr rfl fun a ha => ?_
    rw [mem_filter] at ha
    rw [mono_update, ← ha.2]
    simp only [Box.toNat_apply]
    ring
  have hκ0 : ∀ n, κ n = 0 := fun n =>
    congrArg Subtype.val (Fintype.linearIndependent_iff.1
      (linearIndependent_pow_of_derivation (p := p) (hy.pderiv i) ht) _ hrel n)
  intro a₀
  -- reduce to the independence of the `y`-monomials
  let n₀ := a₀ i
  let g' : Box σ p → pthPowers (F := F) p := fun b =>
    if b i = 0 then g (Function.update b i n₀) else 0
  have hg' : ∑ b, g' b • mono y b.toNat = 0 := by
    rw [← hκ0 n₀]
    simp only [κ, g']
    rw [← sum_filter_add_sum_filter_not univ (fun b : Box σ p => b i = 0)]
    rw [sum_eq_zero (s := univ.filter fun b : Box σ p => ¬ b i = 0) (fun b hb => by
      rw [mem_filter] at hb; rw [if_neg hb.2, zero_smul]), add_zero]
    refine sum_bij' (fun b _ => Function.update b i n₀) (fun a _ => Function.update a i 0)
      ?_ ?_ ?_ ?_ ?_
    · intro b _; simp
    · intro a _; simp
    · intro b hb
      rw [mem_filter] at hb
      rw [Function.update_idem, ← hb.2, Function.update_eq_self]
    · intro a ha
      rw [mem_filter] at ha
      rw [Function.update_idem, ← ha.2, Function.update_eq_self]
    · intro b hb
      rw [mem_filter] at hb
      rw [if_pos hb.2, Subfield.smul_def, smul_eq_mul, Box.toNat_update, Function.update_idem]
      congr 2
      funext j
      by_cases hj : j = i
      · subst hj; simp [hb.2, Box.toNat]
      · simp [Function.update_of_ne hj]
  have := Fintype.linearIndependent_iff.1 hy.linearIndependent g' hg' (Function.update a₀ i 0)
  simp only [g', Function.update_self, if_pos, Function.update_idem, n₀,
    Function.update_eq_self] at this
  exact this

/-- **Steinitz exchange step.** If `u_j` is not among the `y`, some `y_i` not among the `u` has
`∂u_j/∂y_i ≠ 0`. -/
theorem IsPBasis.exists_pderiv_ne_zero (hy : IsPBasis p y) (hu : IsPBasis p u) {j : σ}
    (hj : u j ∉ Set.range y) : ∃ i, y i ∉ Set.range u ∧ hy.pderiv i (u j) ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := hy.derivation_apply_eq_sum (hu.pderiv j) (u j)
  rw [pderiv_self, if_pos rfl] at h1
  rw [sum_eq_zero fun i _ => ?_] at h1
  · exact one_ne_zero h1
  by_cases hi : y i ∈ Set.range u
  · obtain ⟨l, hl⟩ := hi
    have hlj : j ≠ l := by
      rintro rfl
      exact hj ⟨i, hl.symm⟩
    rw [← hl, pderiv_self, if_neg hlj, zero_mul]
  · rw [h i hi, mul_zero]

/-! ### Permutations -/

theorem neg_one_pow_char_sub_one : (-1 : F) ^ (p - 1) = 1 := by
  have h := neg_one_pow_char F p
  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
  rw [hp1, pow_succ] at h
  have : (-1 : F) ^ (p - 1) * (-1) * (-1) = (-1) * (-1) := by rw [h]
  simpa using this

/-- Reordering a `p`-basis does not change the trace. -/
theorem IsPBasis.trace_eq_of_perm (hy : IsPBasis p y) (hu : IsPBasis p u) (π : Equiv.Perm σ)
    (hπ : u = y ∘ π) (x : F) : hu.trace x = hy.trace x := by
  have hcoeff : hu.coeff x = fun a => hy.coeff x (a ∘ π.symm) := by
    apply hu.coeff_eq_of_sum_eq
    subst hπ
    conv_rhs => rw [← hy.sum_coeff x]
    let e : Box σ p ≃ Box σ p := Equiv.arrowCongr π (Equiv.refl _)
    refine Fintype.sum_equiv e _ _ fun a => ?_
    rw [mono_comp_equiv]
    rfl
  rw [trace_apply, trace_apply, hcoeff]
  rfl

theorem IsPBasis.jac_pow_eq_one_of_perm (hu : IsPBasis p u) (π : Equiv.Perm σ) (hπ : u = y ∘ π) : hu.jac y ^ (p - 1) = 1 := by
  have hM : (Matrix.of fun i j => hu.pderiv j (y i)) =
      (1 : Matrix σ σ F).submatrix π.symm id := by
    ext i j
    have : y i = u (π.symm i) := by rw [hπ]; simp
    rw [Matrix.of_apply, this, pderiv_self, Matrix.submatrix_apply, Matrix.one_apply, id]
    simp [eq_comm]
  rw [jac, hM, Matrix.det_permute, Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with h | h <;> rw [h]
  · simp
  · simpa using neg_one_pow_char_sub_one (F := F) (p := p)

/-! ### The main theorem -/

/-- **Independence of the Cartier operator from the `p`-basis.** For `p`-bases `y`, `u` of a
field of characteristic `p`, `Φ_u(f) = Φ_y(J(y/u)^{p-1} f)` where `J(y/u) = det(∂y_i/∂u_j)`. -/
theorem IsPBasis.trace_eq_trace_jac_pow_mul (hy : IsPBasis p y) (hu : IsPBasis p u) (x : F) :
    hu.trace x = hy.trace (hu.jac y ^ (p - 1) * x) := by
  classical
  -- induction on the number of `u_j` not among the `y_i`
  suffices H : ∀ k : ℕ, ∀ y : σ → F, ∀ hy : IsPBasis p y,
      (univ.filter fun j => u j ∉ Set.range y).card = k →
      ∀ x, hu.trace x = hy.trace (hu.jac y ^ (p - 1) * x) from H _ y hy rfl x
  intro k
  induction k with
  | zero =>
    intro y hy hk x
    have hall : ∀ j, u j ∈ Set.range y := by
      intro j
      by_contra hj
      have : j ∈ univ.filter fun j => u j ∉ Set.range y := mem_filter.2 ⟨mem_univ _, hj⟩
      rw [card_eq_zero.1 hk] at this
      simp at this
    choose π hπ using hall
    have hπinj : Function.Injective π := by
      intro a b hab
      apply hu.injective_family
      rw [← hπ a, ← hπ b, hab]
    let e : Equiv.Perm σ := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj)
    have he : u = y ∘ e := by
      funext j
      exact (hπ j).symm
    rw [hu.jac_pow_eq_one_of_perm e he, one_mul, hy.trace_eq_of_perm hu e he]
  | succ k ih =>
    intro y hy hk x
    obtain ⟨j, hj⟩ : ∃ j, j ∈ univ.filter fun j => u j ∉ Set.range y := by
      rw [← Finset.nonempty_def, ← card_pos, hk]
      exact Nat.succ_pos k
    rw [mem_filter] at hj
    obtain ⟨i, hi, hne⟩ := hy.exists_pderiv_ne_zero hu hj.2
    have hy' := hy.update hne
    set y' := Function.update y i (u j)
    -- the count drops by one
    have hk' : (univ.filter fun l => u l ∉ Set.range y').card = k := by
      have hfilt : (univ.filter fun l => u l ∉ Set.range y') =
          (univ.filter fun l => u l ∉ Set.range y).erase j := by
        ext l
        simp only [mem_filter, mem_univ, true_and, mem_erase]
        constructor
        · intro hl
          refine ⟨fun hlj => hl ⟨i, by rw [hlj]; exact Function.update_self i (u j) y⟩, ?_⟩
          rintro ⟨m, hm⟩
          apply hl
          refine ⟨m, ?_⟩
          have hmi : m ≠ i := by
            rintro rfl
            exact hi ⟨l, hm.symm⟩
          rw [show y' m = y m from Function.update_of_ne hmi _ _, hm]
        · rintro ⟨hlj, hl⟩ ⟨m, hm⟩
          by_cases hmi : m = i
          · subst hmi
            rw [show y' m = u j from Function.update_self _ _ _] at hm
            exact hlj (hu.injective_family hm).symm
          · rw [show y' m = y m from Function.update_of_ne hmi _ _] at hm
            exact hl ⟨m, hm⟩
      rw [hfilt, card_erase_of_mem (by simpa using hj.2), hk, Nat.add_sub_cancel]
    rw [ih y' hy' hk' x, hy.trace_update hy', jac_mul hu hy' y, mul_pow, mul_assoc]

end EnvelopeProperty.Cartier
