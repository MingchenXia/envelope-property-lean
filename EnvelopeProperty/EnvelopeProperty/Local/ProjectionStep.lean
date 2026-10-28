/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.GluingCover
import EnvelopeProperty.Local.HullMap
import EnvelopeProperty.Berkovich.Finite
import EnvelopeProperty.Berkovich.ClosedImmersion

/-!
# The projection step

FHX Proposition 5.24 (`prop:projection-step`), **conditional on FHX Proposition 5.22
(`prop:nonflat-norm`, an explicit hypothesis) and on the closure properties of weakly psh functions**.

Let `Y = Spec A` be a normal affine variety, `π = Spec φ : Y → Spec B` a finite morphism
(`φ : B → A` integral), and `Z = V(S) ⊊ Y` such that `π|_Z` is a closed immersion and
`Z' = π⁻¹(π(Z)) \ Z` is closed. If `u` is weakly psh of logarithmic growth and regularizable on
principal opens covering `Y \ Z`, then `u` is regularizable.

## How the missing inputs are handled

* The barrier argument is proved for an abstract class
  `W : (Berk k A → EReal) → Prop` satisfying `IsPshClass W`: members are upper semicontinuous, and
  the class is stable under adding and taking the maximum with a regularizable function. These
  are exactly the properties of weakly psh functions used in the proof (FHX Lemma 5.11(3),(4)).
  Weakly psh functions satisfy them (`isPshClass_isWeaklyPSHOn_univ`, Local/WeaklyPSH.lean), and the
  proposition for weakly psh functions is `IsRegularizable.of_projection_weaklyPSH`
  (Local/ProjectionWeakly.lean).
* The conclusion of FHX Proposition 5.22 for `π` and `Z` (the norm `N_π u = ∑ m_y u(y)` of every
  `u ∈ W` of logarithmic growth regularizable off `Z` is regularizable on `Spec B`, for integer
  weights `m_y ≥ 1` with `∑_{π(y)=s} m_y = d`) is the explicit hypothesis structure
  `NormWeights φ S W d`.

## Encoding of the geometric hypotheses

* `Z^an = {y | |f|_y = 0 for all f ∈ S}`; `Z ≠ Y` is `hS : ∃ f ∈ S, f ≠ 0` (only needed in the
  final corollary, to see that `u` is not identically `-∞`).
* `π|_Z` is a closed immersion: `B → A → A/(S)` is surjective (`hZimm`). When `S` generates the
  (radical) ideal of the reduced subscheme `Z`, which can always be arranged, this is exactly the
  statement that `π|_Z` is a closed immersion. It implies that `π^an` is injective on `Z^an`
  (`eq_of_comap_eq_of_surjective_quotient`).
* `Z'` closed: since `Z` and `Z'` are disjoint closed subsets of the affine variety `Y`, there are
  `f₁ + f₂ = 1` with `f₁ = 0` on `Z'` and `f₂ = 0` on `Z`. We take `f₁, f₂` as data with
  `hf₂ : f₂ = 0 on Z^an` and `hf₁ : f₁ = 0 at every point of π^an⁻¹(π^an(Z^an)) \ Z^an`
  (such points have their support in `Z'`).
* On `Ỹ = Spec A[X] → Spec B[X]` we use `φ̃ = mapAlgHom φ`, `S̃ = S.map C` and `f̃ᵢ = C fᵢ`; the
  hypotheses on `Ỹ` are derived from those on `Y` (`isIntegral_mapAlgHom`,
  `surjective_quotient_mapAlgHom`, `proj_comap_mapAlgHom`, `isRegularizable_awayComap_CAlgHom`),
  except for the two inputs listed above.

## Main results

* `projection_hullIneq`: the core barrier argument (source proof, paragraphs 2–4): for a strict
  exhaustion `ρ` and rational `c > 0`, `u + cρ` satisfies the hull inequality.
* `IsRegularizable.of_projection`: the proposition itself, via the hull criterion
  (FHX Lemma 5.19) on `Ỹ = Y × 𝔸¹`. The data on `Ỹ → Spec B[X]` (a class `W'` of functions on
  `Ỹ^an` containing `u ∘ p + log|w|`, and the conclusion of Proposition 5.22 for
  `π × id` and `Z × 𝔸¹`) are explicit hypotheses; all other hypotheses on `Ỹ` are derived.

## Deviation from the source

The source normalises `u_c(x) = 0`; we do the same by subtracting the real constant `u_c(x)`
(regularizable functions are stable under constants). The final contradiction uses the explicit
bound `h(π(y)) ≤ -min(δ/2, cδ')` on `K = ∂B ∩ L̂` instead of upper semicontinuity of `h ∘ π`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk Polynomial

universe u v

/-! ### The hypothesis structures -/

section defs

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
  {B : Type*} [CommRing B] [Algebra k B]

/-- **Closure properties of weakly psh functions** used in the projection step: weakly psh
functions are upper semicontinuous (FHX Definition 5.6), and adding or taking the maximum with a
regularizable function preserves weak plurisubharmonicity (with the same witness `μ`, since
regularizable functions pull back to locally psh functions). -/
structure IsPshClass (W : (Berk k A → EReal) → Prop) : Prop where
  /-- Members of the class are upper semicontinuous. -/
  usc : ∀ u, W u → UpperSemicontinuous u
  /-- Stability under adding a regularizable function. -/
  add_reg : ∀ u v, W u → IsRegularizable v → W fun x => u x + v x
  /-- Stability under the maximum with a regularizable function. -/
  max_reg : ∀ u v, W u → IsRegularizable v → W fun x => max (u x) (v x)

/-- **The conclusion of FHX Proposition 5.22** (`prop:nonflat-norm`) for `π = Spec φ`,
`Z = V(S)` and the class `W` (standing in for weakly psh functions): integer weights `m_y ≥ 1`
on `Y^an` with `∑_{π(y) = s} m_y = d` for every `s`, such that the norm
`N_π u (s) = ∑_{π(y) = s} m_y u(y)` is regularizable on `Spec B` for every `u ∈ W` of logarithmic
growth that is regularizable on principal opens covering `Y \ Z`. -/
structure NormWeights (φ : B →ₐ[k] A) (S : Finset A) (W : (Berk k A → EReal) → Prop)
    (d : ℕ) where
  /-- The weights `m_y`. -/
  m : Berk k A → ℕ
  /-- The weights are positive. -/
  one_le : ∀ y, 1 ≤ m y
  /-- The fibres of `π^an` are finite. -/
  finite : ∀ s, (comap φ ⁻¹' {s}).Finite
  /-- The weights over each point add up to the degree `d`. -/
  sum_eq : ∀ s, ∑ y ∈ (finite s).toFinset, m y = d
  /-- The norm of a function of the class, of logarithmic growth and regularizable off `Z`, is
  regularizable. -/
  isRegularizable_norm : ∀ u, W u → HasLogGrowth u →
    (∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) →
    IsRegularizable fun s => ∑ y ∈ (finite s).toFinset, ((m y : ℝ) : EReal) * u y

end defs

/-! ### Elementary lemmas -/

section lemmas

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
  {B : Type*} [CommRing B] [Algebra k B]

/-- **Injectivity on `Z^an`.** If `B → A → A/(S)` is surjective (`π|_Z` is a closed immersion),
two points of `Z^an = V(S)^an` with the same image under `π^an` coincide. -/
theorem eq_of_comap_eq_of_surjective_quotient {φ : B →ₐ[k] A} {S : Finset A}
    (hZimm : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span (S : Set A))).comp (φ : B →+* A)))
    {y y' : Berk k A} (h : comap φ y = comap φ y') (hy : ∀ f ∈ S, y.val f = 0)
    (hy' : ∀ f ∈ S, y'.val f = 0) : y = y' := by
  exact comap_injOn_zeroLocus_of_surjective_quotient φ (Ideal.span (S : Set A)) hZimm
    (Ideal.span_le.2 fun f hf => (Valuation.mem_supp_iff _ _).2 (hy f hf))
    (Ideal.span_le.2 fun f hf => (Valuation.mem_supp_iff _ _).2 (hy' f hf)) h

/-- A weighted sum `∑ m_z w(z)` over a finite set, with weights `m_z ∈ ℕ` adding up to `d` and
`m_y ≥ 1`, is at most `a + d b` if `w(y) ≤ a ≤ 0` and `w ≤ b` (`b ≥ 0`) elsewhere. -/
theorem sum_natCast_mul_le {X : Type*} [DecidableEq X] {F : Finset X} {y : X} (hy : y ∈ F)
    {m : X → ℕ} (hm : 1 ≤ m y) {d : ℕ} (hd : ∑ z ∈ F, m z = d) {w : X → EReal} {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hwy : w y ≤ (a : EReal)) (hw : ∀ z ∈ F, z ≠ y → w z ≤ (b : EReal)) :
    ∑ z ∈ F, ((m z : ℝ) : EReal) * w z ≤ ((a + d * b : ℝ) : EReal) := by
  set β : X → ℝ := fun z => if z = y then a else b with hβ
  calc ∑ z ∈ F, ((m z : ℝ) : EReal) * w z ≤ ∑ z ∈ F, (((m z * β z : ℝ)) : EReal) := by
        refine Finset.sum_le_sum fun z hz => ?_
        rw [EReal.coe_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast (Nat.cast_nonneg (m z)))
        by_cases hzy : z = y
        · subst hzy; simpa [hβ] using hwy
        · simpa [hβ, hzy] using hw z hz hzy
    _ = ((∑ z ∈ F, m z * β z : ℝ) : EReal) := (ereal_coe_finset_sum _ _).symm
    _ ≤ _ := by
        rw [EReal.coe_le_coe_iff, ← Finset.add_sum_erase F _ hy]
        have h1 : ∑ z ∈ F.erase y, (m z : ℝ) * β z = b * ∑ z ∈ F.erase y, (m z : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z hz => ?_
          simp only [hβ, if_neg (Finset.ne_of_mem_erase hz)]
          ring
        have h2 : (m y : ℝ) + ∑ z ∈ F.erase y, (m z : ℝ) = d := by
          rw [Finset.add_sum_erase F (fun z => (m z : ℝ)) hy]
          exact_mod_cast hd
        have hβy : β y = a := if_pos rfl
        rw [h1, hβy]
        have hmy : (1 : ℝ) ≤ m y := by exact_mod_cast hm
        have hs : 0 ≤ ∑ z ∈ F.erase y, (m z : ℝ) :=
          Finset.sum_nonneg fun z _ => Nat.cast_nonneg _
        nlinarith [mul_nonneg (sub_nonneg.2 hmy) (neg_nonneg.2 ha), mul_nonneg hb hs]

/-- An upper semicontinuous function with values `< ⊤` is bounded above on a compact set by a
nonnegative rational. -/
theorem exists_rat_forall_le_of_upperSemicontinuous {X : Type*} [TopologicalSpace X]
    {f : X → EReal} (hf : UpperSemicontinuous f) (hft : ∀ x, f x ≠ ⊤) {K : Set X}
    (hK : IsCompact K) : ∃ M : ℚ, 0 ≤ M ∧ ∀ x ∈ K, f x ≤ ((M : ℝ) : EReal) := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨0, le_rfl, by simp [h]⟩
  · obtain ⟨p, hp, hmax⟩ := (hf.upperSemicontinuousOn K).exists_isMaxOn hne hK
    obtain ⟨M, hM⟩ := exists_rat_gt (max 0 (f p).toReal)
    refine ⟨M, ?_, fun x hx => (hmax hx).trans ?_⟩
    · exact_mod_cast ((le_max_left _ _).trans hM.le)
    · calc f p ≤ ((f p).toReal : EReal) := EReal.le_coe_toReal (hft p)
        _ ≤ _ := EReal.coe_le_coe_iff.2 ((le_max_right _ _).trans hM.le)

/-- If `X + s ≤ r` with `r, s` real, then `X ≤ r - s`. -/
theorem le_coe_sub_of_add_coe_le {X : EReal} {r s : ℝ} (h : X + (s : EReal) ≤ (r : EReal)) :
    X ≤ ((r - s : ℝ) : EReal) := by
  rw [EReal.coe_sub]
  exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot s)) (Or.inl (EReal.coe_ne_top s))).2 h

/-- If `b' + t ≤ b` with `b ≠ ⊤` and `c > 0`, then `a + c b' + c t ≤ a + c b`. -/
theorem add_coe_mul_add_le {a b b' : EReal} {c t : ℝ} (hc : 0 < c) (hb : b ≠ ⊤)
    (h : b' + (t : EReal) ≤ b) :
    a + (c : EReal) * b' + ((c * t : ℝ) : EReal) ≤ a + (c : EReal) * b := by
  by_cases hb' : b' = ⊥
  · rw [hb', EReal.coe_mul_bot_of_pos hc, EReal.add_bot, EReal.bot_add]
    exact bot_le
  · have hb't : b' ≠ ⊤ := by
      rintro rfl
      exact hb (top_le_iff.1 (by simpa using h))
    have hbb : b ≠ ⊥ := by
      rintro rfl
      rw [le_bot_iff, EReal.add_eq_bot_iff] at h
      exact h.elim hb' (EReal.coe_ne_bot t)
    lift b' to ℝ using ⟨hb't, hb'⟩ with r'
    lift b to ℝ using ⟨hb, hbb⟩ with r
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [add_assoc, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul]
    gcongr
    nlinarith

end lemmas

/-! ### The barrier argument -/

section core

variable {k : Type u} [Field k] [IsAlgClosed k] [WuRegularization.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A] {B : Type*} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

/-- The contradiction at the heart of FHX Proposition 5.24, after normalisation: `x ∈ L̂` is a
maximum point of `u_c = u + cρ` on `L̂` with `u_c(x) = 0`, and `u_c ≤ -δ` on `L`. -/
theorem projection_core (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).IsIntegral) (S : Finset A)
    (hZimm : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span (S : Set A))).comp (φ : B →+* A)))
    {f₁ f₂ : A} (hf : f₁ + f₂ = 1)
    (hf₂ : ∀ y : Berk k A, (∀ f ∈ S, y.val f = 0) → y.val f₂ = 0)
    (hf₁ : ∀ y y' : Berk k A, (∀ f ∈ S, y.val f = 0) → comap φ y' = comap φ y →
      (∃ f ∈ S, y'.val f ≠ 0) → y'.val f₁ = 0)
    {W : (Berk k A → EReal) → Prop} (hW : IsPshClass W) {d : ℕ} (N : NormWeights φ S W d)
    {u : Berk k A → EReal} (hu : W u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y))
    {ρ : Berk k A → EReal} (hρ : IsStrictExhaustion ρ) {c : ℚ} (hc : 0 < c)
    {L : Set (Berk k A)} (hL : IsCompact L) {x : Berk k A} (hx : x ∈ hull L)
    (hx0 : u x + ((c : ℝ) : EReal) * ρ x = 0)
    (hmax : ∀ y ∈ hull L, u y + ((c : ℝ) : EReal) * ρ y ≤ 0)
    {δ : ℚ} (hδ : 0 < δ) (hLδ : ∀ y ∈ L, u y + ((c : ℝ) : EReal) * ρ y ≤ ((-δ : ℝ) : EReal)) :
    False := by
  classical
  obtain ⟨hρreg, hρ0, hρstrict⟩ := hρ
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast hδ
  have husc : UpperSemicontinuous u := hW.usc u hu
  have hutop : ∀ y, u y ≠ ⊤ := by
    obtain ⟨g0, C0, hg0⟩ := hlog
    exact fun y => ne_top_of_le_ne_top
      (EReal.add_ne_top (g0.eval_ne_top y) (EReal.coe_ne_top C0)) (hg0 y)
  have hcρtop : ∀ y, ((c : ℝ) : EReal) * ρ y ≠ ⊤ := (hρreg.smul hc).ne_top
  set uc : Berk k A → EReal := fun y => u y + ((c : ℝ) : EReal) * ρ y with huc
  have hucusc : UpperSemicontinuous uc :=
    upperSemicontinuous_add_of_ne_top husc (hρreg.smul hc).upperSemicontinuous hutop hcρtop
  -- the hull inequality off `Z` (FHX Proposition 5.20(1))
  have hglue : ∀ y ∈ hull L, (∃ f ∈ S, y.val f ≠ 0) → uc y ≤ ((-δ : ℝ) : EReal) := fun y hy hyZ =>
    (gluing_hullIneq husc hlog S hcover ⟨hρreg, hρ0, hρstrict⟩ hc hL hy hyZ).trans
      (iSup₂_le hLδ)
  have hneg : ((-δ : ℝ) : EReal) < 0 := by exact_mod_cast neg_lt_zero.2 hδpos
  have hxL : x ∉ L := fun hxL => absurd ((hLδ x hxL).trans_lt hneg) (by rw [hx0]; exact lt_irrefl _)
  -- `x ∈ Z^an`
  have hxZ : ∀ f ∈ S, x.val f = 0 := by
    by_contra h
    push Not at h
    exact absurd ((hglue x hx h).trans_lt hneg)
      (by rw [huc]; simp only; rw [hx0]; exact lt_irrefl _)
  -- the partition `f₁ + f₂ = 1`
  have hval1 : ∀ y : Berk k A, y.val f₂ < 1 → y.val f₁ = 1 := fun y h =>
    val_eq_one_of_add_eq_one hf h
  have hval2 : ∀ y : Berk k A, y.val f₁ < 1 → y.val f₂ = 1 := fun y h =>
    val_eq_one_of_add_eq_one ((add_comm f₂ f₁).trans hf) h
  have hlog0 : ∀ (f : A) (y : Berk k A), y.val f = 1 → logAbs f y = 0 := fun f y h => by
    simp [logAbs, h]
  have hlt1 : ∀ (f : A) (y : Berk k A), logAbs f y < ((-1 : ℝ) : EReal) → y.val f < 1 :=
    fun f y h => by
      have : logAbs f y < logAbs 1 y := h.trans (by rw [logAbs_one]; exact_mod_cast neg_one_lt_zero)
      simpa using (logAbs_lt_logAbs_iff f 1 y).1 this
  -- the fibre over `π(x)` consists of `x` and points where `f₁` vanishes
  have hfib : ∀ y y' : Berk k A, (∀ f ∈ S, y.val f = 0) → comap φ y' = comap φ y → y' ≠ y →
      y'.val f₁ = 0 := by
    intro y y' hy hyy' hne
    refine hf₁ y y' hy hyy' ?_
    by_contra h
    push Not at h
    exact hne (eq_of_comap_eq_of_surjective_quotient hZimm hyy' h hy)
  have hx₂ : x.val f₂ = 0 := hf₂ x hxZ
  have hx₁ : x.val f₁ = 1 := hval1 x (by rw [hx₂]; exact zero_lt_one)
  have hf₁ne : f₁ ≠ 0 := by
    rintro rfl
    simp at hx₁
  have hxF : x ∈ (N.finite (comap φ x)).toFinset := (Set.Finite.mem_toFinset _).2 rfl
  have hd : 1 ≤ d := by
    have := Finset.single_le_sum (f := N.m) (fun _ _ => Nat.zero_le _) hxF
    rw [N.sum_eq] at this
    exact (N.one_le x).trans this
  set Γ : Set (Berk k A) := comap φ ⁻¹' {comap φ x} \ {x} with hΓ
  have hΓfin : Γ.Finite := (N.finite _).subset Set.sdiff_subset
  -- (1) a relatively compact neighbourhood `A'` of `Γ` inside `{log|f₁| < -1}`, and `M`
  set U₁ : Set (Berk k A) := {y | logAbs f₁ y < ((-1 : ℝ) : EReal)} with hU₁
  have hU₁o : IsOpen U₁ := isOpen_lt (continuous_logAbs f₁) continuous_const
  have hΓU₁ : Γ ⊆ U₁ := fun y hy => by
    have : y.val f₁ = 0 := hfib x y hxZ hy.1 hy.2
    simp only [hU₁, Set.mem_ofPred_eq, (logAbs_eq_bot_iff f₁ y).2 this]
    exact EReal.bot_lt_coe _
  obtain ⟨L₁, hL₁c, hΓL₁, hL₁U₁⟩ := exists_compact_between hΓfin.isCompact hU₁o hΓU₁
  obtain ⟨M, hM0, hM⟩ := exists_rat_forall_le_of_upperSemicontinuous hucusc
    (fun y => EReal.add_ne_top (hutop y) (hcρtop y)) hL₁c
  -- (2) the neighbourhood `V_x` of `x`
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set ε : ℝ := δ / (2 * d) with hε
  have hεpos : 0 < ε := by positivity
  set Vx : Set (Berk k A) :=
    {y | logAbs f₂ y < ((-1 : ℝ) : EReal)} ∩ {y | uc y < (ε : EReal)} with hVx
  have hVxo : IsOpen Vx :=
    (isOpen_lt (continuous_logAbs f₂) continuous_const).inter (hucusc.isOpen_preimage _)
  have hxVx : x ∈ Vx := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, (logAbs_eq_bot_iff f₂ x).2 hx₂]
      exact EReal.bot_lt_coe _
    · simp only [Set.mem_ofPred_eq, huc, hx0]
      exact_mod_cast hεpos
  -- (3) the neighbourhood `V` of `π(x)`
  set V : Set (Berk k B) := (comap φ '' (Vx ∪ interior L₁)ᶜ)ᶜ with hV
  have hVo : IsOpen V :=
    (Berk.isClosedMap_comap φ hφ _ (hVxo.union isOpen_interior).isClosed_compl).isOpen_compl
  have hpre : ∀ y, comap φ y ∈ V → y ∈ Vx ∪ interior L₁ := fun y hy => by
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hxV : comap φ x ∈ V := by
    rintro ⟨y, hy, hyx⟩
    apply hy
    by_cases hyx' : y = x
    · subst hyx'; exact Or.inl hxVx
    · exact Or.inr (hΓL₁ ⟨hyx, hyx'⟩)
  -- (4) the relatively compact neighbourhood `B'` of `x`
  obtain ⟨Bs, hBo, hxB, hBc, hBsub⟩ := exists_isOpen_isCompact_closure_subset
    ((hVxo.inter (hVo.preimage (continuous_comap φ))).inter hL.isClosed.isOpen_compl)
    ⟨⟨hxVx, hxV⟩, hxL⟩
  -- (5) `ρ'` and `δ'` from the strict exhaustion
  obtain ⟨ρ', δ', hδ', hρ'reg, hρ'le, hρ'x, hρ'off⟩ := hρstrict x Bs (hBo.mem_nhds hxB)
  -- the barrier `u♯`
  set q₁ : ℚ := M + 1 with hq₁
  have hq₁pos : (0 : ℝ) < q₁ := by
    rw [hq₁]; push_cast; linarith [(Rat.cast_nonneg.2 hM0 : (0 : ℝ) ≤ M)]
  set u' : Berk k A → EReal := fun y => u y + ((c : ℝ) : EReal) * ρ' y with hu'
  set η : Berk k A → EReal := fun y => max (((δ : ℝ) : EReal) * logAbs f₂ y) ((-δ : ℝ) : EReal)
    with hη
  set us : Berk k A → EReal := fun y => max (u' y + ((q₁ : ℝ) : EReal) * logAbs f₁ y) (η y)
    with hus
  have hlog₁ : IsRegularizable fun y : Berk k A => ((q₁ : ℝ) : EReal) * logAbs f₁ y := by
    have h := isRegularizable_finsetSup_fsTerm (k := k) (A := A) (s := {(f₁, q₁, 0)})
      (by simp only [Finset.mem_singleton, forall_eq]; exact_mod_cast hq₁pos)
      ⟨triv, by simp [fsTerm, triv_val_of_ne_zero hf₁ne]⟩
    exact h.congr fun y => by simp [fsTerm]
  have hηreg : IsRegularizable η := by
    have : Nonempty (Berk k A) := ⟨triv⟩
    have h := isRegularizable_max_const_finsetSup_fsTerm (k := k) (A := A) (-δ)
      (s := {(f₂, δ, 0)}) (by simpa using hδ)
    exact h.congr fun y => by simp [hη, fsTerm, max_comm]
  have hWus : W us :=
    hW.max_reg _ _ (hW.add_reg _ _ (hW.add_reg _ _ hu (hρ'reg.smul hc)) hlog₁) hηreg
  have hlogus : HasLogGrowth us :=
    ((hlog.add (hρ'reg.smul hc).hasLogGrowth).add hlog₁.hasLogGrowth).sup hηreg.hasLogGrowth
  have hcovus : ∀ y : Berk k A, (∃ f ∈ S, y.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ y.val g ≠ 0 ∧ IsRegularizable fun w => us (awayComap g w) := by
    intro y hy
    obtain ⟨g, hg0, hyg, hug⟩ := hcover y hy
    have := isDomain_localizationAway hg0
    exact ⟨g, hg0, hyg, ((hug.add ((hρ'reg.comp_awayComap hg0).smul hc)).add
      (hlog₁.comp_awayComap hg0)).sup (hηreg.comp_awayComap hg0)⟩
  -- the norm `h = N_π u♯` is regularizable on `Spec B` (FHX Proposition 5.22)
  set h : Berk k B → EReal := fun s =>
    ∑ y ∈ (N.finite s).toFinset, ((N.m y : ℝ) : EReal) * us y with hh
  have hhreg : IsRegularizable h := N.isRegularizable_norm us hWus hlogus hcovus
  -- Rossi: `x` lies in the hull of `K = ∂B' ∩ L̂`, so `π(x)` lies in the hull of `π(K)`
  set K : Set (Berk k A) := frontier Bs ∩ hull L with hK
  have hdisj : Disjoint (closure Bs) L := Set.disjoint_left.2 fun y hy hyL => (hBsub hy).2 hyL
  have hxK : x ∈ hull K := mem_hull_frontier_inter_hull hL hx hBo hxB hBc hdisj
  have hKc : IsCompact K := hBc.of_isClosed_subset (isClosed_frontier.inter (isClosed_hull L))
    fun y hy => frontier_subset_closure hy.1
  have hineq : h (comap φ x) ≤ ⨆ s ∈ comap φ '' K, h s :=
    hhreg.satisfiesHullIneq _ (hKc.image (continuous_comap φ)) _ (comap_mem_hull_image φ hxK)
  -- `h(π(x)) ≥ 0`
  have hu'le : ∀ z, u' z ≤ uc z := fun z =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left (hρ'le z)
      (by exact_mod_cast hcpos.le : (0 : EReal) ≤ ((c : ℝ) : EReal)))
  have hη1 : ∀ z : Berk k A, z.val f₂ = 1 → η z = 0 := by
    intro z hz
    simp only [hη]
    rw [hlog0 f₂ z hz, mul_zero]
    exact max_eq_left (by exact_mod_cast neg_nonpos.2 hδpos.le)
  have hmemF : ∀ (s : Berk k B) (y : Berk k A), y ∈ (N.finite s).toFinset → comap φ y = s :=
    fun s y hy => (Set.Finite.mem_toFinset (N.finite s)).1 hy
  have hus_Γ : ∀ y : Berk k A, y.val f₁ = 0 → us y ≤ 0 ∧ 0 ≤ us y := by
    intro y hy
    have hy₂ : y.val f₂ = 1 := hval2 y (by rw [hy]; exact zero_lt_one)
    have hη0 : η y = 0 := hη1 y hy₂
    have hfirst : u' y + ((q₁ : ℝ) : EReal) * logAbs f₁ y = ⊥ := by
      rw [(logAbs_eq_bot_iff f₁ y).2 hy, EReal.coe_mul_bot_of_pos hq₁pos, EReal.add_bot]
    simp only [hus, hfirst, hη0, bot_le, max_eq_right, le_refl, and_self]
  have hhx : 0 ≤ h (comap φ x) := by
    refine Finset.sum_nonneg fun y hy => mul_nonneg (by exact_mod_cast Nat.cast_nonneg _) ?_
    by_cases hyx : y = x
    · subst hyx
      refine le_max_of_le_left ?_
      simp only [hu', hρ'x, hlog0 f₁ y hx₁, mul_zero, add_zero]
      exact hx0.ge
    · exact (hus_Γ y (hfib x y hxZ (hmemF _ y hy) hyx)).2
  -- `h(π(y)) ≤ -τ` on `K`
  set τ : ℝ := min (δ / 2) (c * δ') with hτ
  have hτpos : 0 < τ := lt_min (by positivity) (mul_pos hcpos hδ')
  have hbound : ∀ y ∈ K, h (comap φ y) ≤ ((-τ : ℝ) : EReal) := by
    intro y hyK
    simp only [hh]
    have hyU := hBsub (frontier_subset_closure hyK.1)
    have hyVx : y ∈ Vx := hyU.1.1
    have hyV : comap φ y ∈ V := hyU.1.2
    have hyB : y ∉ Bs := by
      have := hyK.1
      rw [hBo.frontier_eq] at this
      exact this.2
    have hyhull : y ∈ hull L := hyK.2
    -- `u'(y) ≤ -cδ'`
    have hu'y : u' y ≤ ((-(c * δ') : ℝ) : EReal) := by
      have h1 := add_coe_mul_add_le (a := u y) hcpos (hρreg.ne_top y) (hρ'off y hyB)
      have h2 : u' y + ((c * δ' : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) :=
        h1.trans (by exact_mod_cast hmax y hyhull)
      simpa using le_coe_sub_of_add_coe_le h2
    have hyF : y ∈ (N.finite (comap φ y)).toFinset := (Set.Finite.mem_toFinset _).2 rfl
    by_cases hyZ : ∀ f ∈ S, y.val f = 0
    · -- `y ∈ Z^an`: the other points of the fibre lie in `Z'^an`, where `u♯ = 0`
      have hy₂ : y.val f₂ = 0 := hf₂ y hyZ
      have hy₁ : y.val f₁ = 1 := hval1 y (by rw [hy₂]; exact zero_lt_one)
      have hbd := sum_natCast_mul_le hyF (N.one_le y) (N.sum_eq _) (w := us) (a := -τ) (b := 0)
        (by linarith) le_rfl ?_ ?_
      · simpa using hbd
      · refine max_le ?_ ?_
        · rw [hlog0 f₁ y hy₁, mul_zero, add_zero]
          exact hu'y.trans
            (EReal.coe_le_coe_iff.2 (by linarith [min_le_right (δ / 2 : ℝ) (c * δ')]))
        · simp only [hη, (logAbs_eq_bot_iff f₂ y).2 hy₂, EReal.coe_mul_bot_of_pos hδpos]
          exact max_le bot_le
            (EReal.coe_le_coe_iff.2 (by linarith [min_le_left (δ / 2 : ℝ) (c * δ')]))
      · intro z hz hzy
        exact (hus_Γ z (hfib y z hyZ (hmemF _ z hz) hzy)).1
    · -- `y ∉ Z^an`: `u♯(y) = -δ` and `u♯ ≤ ε` on the fibre
      push Not at hyZ
      have hglue_y := hglue y hyhull hyZ
      have hy₁ : y.val f₁ = 1 := hval1 y (hlt1 f₂ y hyVx.1)
      have hηVx : ∀ z ∈ Vx, η z ≤ ((-δ : ℝ) : EReal) := by
        intro z hz
        refine max_le ?_ le_rfl
        calc ((δ : ℝ) : EReal) * logAbs f₂ z ≤ ((δ : ℝ) : EReal) * ((-1 : ℝ) : EReal) :=
              mul_le_mul_of_nonneg_left hz.1.le (by exact_mod_cast hδpos.le)
          _ = ((-δ : ℝ) : EReal) := by rw [← EReal.coe_mul]; congr 1; ring
      have hbd := sum_natCast_mul_le hyF (N.one_le y) (N.sum_eq _) (w := us) (a := -δ) (b := ε)
        (by linarith) hεpos.le ?_ ?_
      · refine hbd.trans (EReal.coe_le_coe_iff.2 ?_)
        have : (d : ℝ) * ε = δ / 2 := by rw [hε]; field_simp
        linarith [min_le_left (δ / 2 : ℝ) (c * δ')]
      · refine max_le ?_ (hηVx y hyVx)
        rw [hlog0 f₁ y hy₁, mul_zero, add_zero]
        exact (hu'le y).trans hglue_y
      · intro z hz _
        have hzV : comap φ z ∈ V := by
          rw [hmemF _ z hz]
          exact hyV
        rcases hpre z hzV with hzVx | hzA
        · have hz₁ : z.val f₁ = 1 := hval1 z (hlt1 f₂ z hzVx.1)
          refine max_le ?_ ((hηVx z hzVx).trans (EReal.coe_le_coe_iff.2 (by linarith)))
          rw [hlog0 f₁ z hz₁, mul_zero, add_zero]
          exact (hu'le z).trans hzVx.2.le
        · have hzL₁ : z ∈ L₁ := interior_subset hzA
          have hz₁ : logAbs f₁ z < ((-1 : ℝ) : EReal) := hL₁U₁ hzL₁
          have hz₂ : z.val f₂ = 1 := hval2 z (hlt1 f₁ z hz₁)
          refine max_le ?_ ?_
          · calc u' z + ((q₁ : ℝ) : EReal) * logAbs f₁ z
                ≤ ((M : ℝ) : EReal) + (((q₁ : ℝ) * (-1) : ℝ) : EReal) := by
                  refine add_le_add ((hu'le z).trans (hM z hzL₁)) ?_
                  rw [EReal.coe_mul]
                  exact mul_le_mul_of_nonneg_left hz₁.le (by exact_mod_cast hq₁pos.le)
              _ ≤ (ε : EReal) := by
                  rw [← EReal.coe_add, EReal.coe_le_coe_iff, hq₁]
                  push_cast
                  linarith
          · rw [hη1 z hz₂]
            exact_mod_cast hεpos.le
  have hsup : (⨆ s ∈ comap φ '' K, h s) ≤ ((-τ : ℝ) : EReal) := iSup₂_le fun s hs => by
    obtain ⟨y, hy, rfl⟩ := hs
    exact hbound y hy
  have : ((0 : ℝ) : EReal) ≤ ((-τ : ℝ) : EReal) := hhx.trans (hineq.trans hsup)
  rw [EReal.coe_le_coe_iff] at this
  linarith

/-- **The projection step, hull inequality** (FHX Proposition 5.24, the barrier argument),
conditional on FHX Proposition 5.22 (the hypothesis `N : NormWeights φ S W d`) and on the closure
properties `IsPshClass W` of weakly psh functions.

Let `φ : B → A` be integral (`π = Spec φ` finite), `Z = V(S)` with `π|_Z` a closed immersion
(`hZimm`), and `f₁ + f₂ = 1` with `f₂ = 0` on `Z^an` and `f₁ = 0` on `π⁻¹(π(Z^an)) \ Z^an`. Let
`u ∈ W` be of logarithmic growth and regularizable on principal opens covering `Y \ Z`, and let
`ρ` be a strict exhaustion. Then `u + cρ` satisfies the hull inequality for every rational
`c > 0`. -/
theorem projection_hullIneq (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).IsIntegral) (S : Finset A)
    (hZimm : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span (S : Set A))).comp (φ : B →+* A)))
    {f₁ f₂ : A} (hf : f₁ + f₂ = 1)
    (hf₂ : ∀ y : Berk k A, (∀ f ∈ S, y.val f = 0) → y.val f₂ = 0)
    (hf₁ : ∀ y y' : Berk k A, (∀ f ∈ S, y.val f = 0) → comap φ y' = comap φ y →
      (∃ f ∈ S, y'.val f ≠ 0) → y'.val f₁ = 0)
    {W : (Berk k A → EReal) → Prop} (hW : IsPshClass W) {d : ℕ} (N : NormWeights φ S W d)
    {u : Berk k A → EReal} (hu : W u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y))
    {ρ : Berk k A → EReal} (hρ : IsStrictExhaustion ρ) {c : ℚ} (hc : 0 < c) :
    SatisfiesHullIneq fun x => u x + ((c : ℝ) : EReal) * ρ x := by
  classical
  intro L hL x₀ hx₀
  by_contra hcon
  rw [not_le] at hcon
  have husc : UpperSemicontinuous u := hW.usc u hu
  have hutop : ∀ y, u y ≠ ⊤ := by
    obtain ⟨g0, C0, hg0⟩ := hlog
    exact fun y => ne_top_of_le_ne_top
      (EReal.add_ne_top (g0.eval_ne_top y) (EReal.coe_ne_top C0)) (hg0 y)
  have hcρtop : ∀ y, ((c : ℝ) : EReal) * ρ y ≠ ⊤ := (hρ.1.smul hc).ne_top
  set uc : Berk k A → EReal := fun y => u y + ((c : ℝ) : EReal) * ρ y with huc
  have hucusc : UpperSemicontinuous uc :=
    upperSemicontinuous_add_of_ne_top husc (hρ.1.smul hc).upperSemicontinuous hutop hcρtop
  -- a maximum point `x` of `u_c` on `L̂`
  obtain ⟨x, hx, hxmax⟩ :=
    (hucusc.upperSemicontinuousOn (hull L)).exists_isMaxOn ⟨x₀, hx₀⟩ (isCompact_hull hL)
  have hx₀x : uc x₀ ≤ uc x := hxmax hx₀
  have hxbot : uc x ≠ ⊥ := ne_bot_of_gt (hcon.trans_le hx₀x)
  have hxtop : uc x ≠ ⊤ := EReal.add_ne_top (hutop x) (hcρtop x)
  set a : ℝ := (uc x).toReal with ha_def
  have ha : (a : EReal) = uc x := EReal.coe_toReal hxtop hxbot
  -- a rational `δ > 0` with `u_c ≤ u_c(x) - δ` on `L`
  obtain ⟨δ, hδ, hδL⟩ : ∃ δ : ℚ, 0 < δ ∧ ∀ y ∈ L, uc y ≤ ((a - δ : ℝ) : EReal) := by
    have hsx : (⨆ y ∈ L, uc y) < (a : EReal) := ha ▸ hcon.trans_le hx₀x
    by_cases hsbot : (⨆ y ∈ L, uc y) = ⊥
    · refine ⟨1, one_pos, fun y hy => ?_⟩
      have : uc y ≤ ⨆ y ∈ L, uc y := le_iSup₂ (f := fun y _ => uc y) y hy
      rw [hsbot, le_bot_iff] at this
      rw [this]
      exact bot_le
    · have hstop : (⨆ y ∈ L, uc y) ≠ ⊤ := ne_top_of_lt hsx
      have hsr : (((⨆ y ∈ L, uc y).toReal : ℝ) : EReal) = ⨆ y ∈ L, uc y :=
        EReal.coe_toReal hstop hsbot
      have hlt : (⨆ y ∈ L, uc y).toReal < a := by
        rw [← hsr] at hsx
        exact_mod_cast hsx
      obtain ⟨δ, hδ0, hδ1⟩ := exists_rat_btwn (sub_pos.2 hlt)
      refine ⟨δ, by exact_mod_cast hδ0, fun y hy =>
        (le_iSup₂ (f := fun y _ => uc y) y hy).trans ?_⟩
      rw [← hsr, EReal.coe_le_coe_iff]
      linarith
  -- normalisation: `u₀ = u - u_c(x)`
  have : Nonempty (Berk k A) := ⟨triv⟩
  set u₀ : Berk k A → EReal := fun y => u y + ((-a : ℝ) : EReal) with hu₀
  have hu₀W : W u₀ := hW.add_reg _ _ hu (isRegularizable_const (-a))
  have hlog₀ : HasLogGrowth u₀ := hlog.add_const (-a)
  have hcover₀ : ∀ y : Berk k A, (∃ f ∈ S, y.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ y.val g ≠ 0 ∧ IsRegularizable fun w => u₀ (awayComap g w) := by
    intro y hy
    obtain ⟨g, hg0, hyg, hug⟩ := hcover y hy
    exact ⟨g, hg0, hyg, hug.add_const (-a)⟩
  have hshift : ∀ y, u₀ y + ((c : ℝ) : EReal) * ρ y = uc y + ((-a : ℝ) : EReal) := fun y => by
    simp only [hu₀, huc]
    exact add_right_comm _ _ _
  have hle_shift : ∀ y {r : ℝ}, uc y ≤ (r : EReal) →
      u₀ y + ((c : ℝ) : EReal) * ρ y ≤ ((r + -a : ℝ) : EReal) := fun y r hr => by
    rw [hshift, EReal.coe_add]
    exact add_le_add hr le_rfl
  refine projection_core φ hφ S hZimm hf hf₂ hf₁ hW N hu₀W hlog₀ hcover₀ hρ hc hL hx ?_
    (fun y hy => ?_) hδ (fun y hy => ?_)
  · rw [hshift, ← ha, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  · have := hle_shift y (r := a) (ha ▸ hxmax hy)
    rwa [add_neg_cancel, EReal.coe_zero] at this
  · have := hle_shift y (hδL y hy)
    rw [show a - δ + -a = -δ by ring] at this
    exact this

end core

/-! ### Transfer to `Ỹ = Y × 𝔸¹` -/

section poly

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
  {B : Type*} [CommRing B] [Algebra k B]

/-- `π × id : Ỹ → Spec B[X]` is finite: if `A` is integral over `B`, then `A[X]` is integral
over `B[X]`. -/
theorem isIntegral_mapAlgHom {φ : B →ₐ[k] A} (hφ : (φ : B →+* A).IsIntegral) :
    ((mapAlgHom φ : B[X] →ₐ[k] A[X]) : B[X] →+* A[X]).IsIntegral := by
  intro p
  set ψ : B[X] →+* A[X] := ((mapAlgHom φ : B[X] →ₐ[k] A[X]) : B[X] →+* A[X]) with hψ
  have hψC : ψ.comp C = C.comp (φ : B →+* A) := RingHom.ext fun b => by simp [hψ]
  have hC : ∀ a : A, ψ.IsIntegralElem (C a) := by
    intro a
    obtain ⟨P, hPm, hPa⟩ := hφ a
    refine ⟨P.map C, hPm.map C, ?_⟩
    rw [eval₂_map, hψC, ← hom_eval₂, hPa, map_zero]
  have hX : ψ.IsIntegralElem X := by
    have : ψ X = X := by simp [hψ]
    rw [← this]
    exact ψ.isIntegralElem_map
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => exact RingHom.IsIntegralElem.add ψ hp hq
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    exact RingHom.IsIntegralElem.mul ψ ih hX

/-- `(π × id)|_{Z × 𝔸¹}` is a closed immersion if `π|_Z` is: if `B → A/(S)` is surjective, so is
`B[X] → A[X]/(S)`. -/
theorem surjective_quotient_mapAlgHom {φ : B →ₐ[k] A} {S : Finset A}
    (hZimm : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span (S : Set A))).comp (φ : B →+* A))) :
    Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span ((S.map ⟨C, C_injective⟩ : Finset A[X]) : Set A[X]))).comp
        ((mapAlgHom φ : B[X] →ₐ[k] A[X]) : B[X] →+* A[X])) := by
  classical
  set I := Ideal.span (S : Set A) with hI
  have hspan : Ideal.span ((S.map ⟨C, C_injective⟩ : Finset A[X]) : Set A[X]) = Ideal.map C I := by
    rw [hI, Ideal.map_span, Finset.coe_map]
    rfl
  rw [hspan]
  have heq : (Ideal.Quotient.mk (Ideal.map C I)).comp
      ((mapAlgHom φ : B[X] →ₐ[k] A[X]) : B[X] →+* A[X]) =
      (I.polynomialQuotientEquivQuotientPolynomial : (A ⧸ I)[X] →+* A[X] ⧸ Ideal.map C I).comp
        (mapRingHom ((Ideal.Quotient.mk I).comp (φ : B →+* A))) := by
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, coe_mapRingHom, RingEquiv.coe_toRingHom]
    rw [← Polynomial.map_map, Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk]
    rfl
  rw [heq]
  exact I.polynomialQuotientEquivQuotientPolynomial.surjective.comp
    (Polynomial.map_surjective _ hZimm)

/-- The square `π ∘ p = p ∘ (π × id)`. -/
theorem proj_comap_mapAlgHom (φ : B →ₐ[k] A) (z : Berk k A[X]) :
    proj (comap (mapAlgHom φ) z) = comap φ (proj z) :=
  ext_val fun b => by simp [proj_val_apply, comap_val_apply]

end poly

section cover

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- If `u` is regularizable on `Y_g`, then `u ∘ p + log|w|` is regularizable on `Ỹ_g`
(FHX Lemma 5.11(3),(4); the argument of `IsRegularizable.of_cover_principal`). -/
theorem isRegularizable_awayComap_CAlgHom {u : Berk k A → EReal} {g : A} (hg0 : g ≠ 0)
    (hug : IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable fun w : Berk k (Localization.Away (CAlgHom (R := k) (A := A) g)) =>
      u (proj (awayComap (CAlgHom (R := k) (A := A) g) w)) +
        logAbs (X : A[X]) (awayComap (CAlgHom (R := k) (A := A) g) w) := by
  have hCg : (CAlgHom (R := k) (A := A) g) ≠ 0 := by simpa [CAlgHom] using hg0
  have := isDomain_localizationAway hCg
  -- first summand
  have h1 : IsRegularizable fun w : Berk k (Localization.Away (CAlgHom (R := k) (A := A) g)) =>
      u (awayComap g (comap (awayPolyMap g) w)) := by
    refine hug.comp_comap (awayPolyMap g) ?_
    obtain ⟨⟨y₀, hy₀⟩, -⟩ := hug
    set y := awayComap g y₀
    have hyC : (gauss y 1).val (CAlgHom (R := k) (A := A) g) ≠ 0 := by
      change (gauss y 1).val (C g) ≠ 0
      rw [gauss_val_C]
      exact awayComap_val_ne_zero g y₀
    refine ⟨awayLift _ (gauss y 1) hyC, ?_⟩
    rw [← proj_awayComap_C, awayComap_awayLift, proj_gauss]
    exact hy₀
  -- second summand
  have h2 : IsRegularizable fun w : Berk k (Localization.Away (CAlgHom (R := k) (A := A) g)) =>
      logAbs (X : A[X]) (awayComap (CAlgHom (R := k) (A := A) g) w) := by
    have hs := isRegularizable_finsetSup_fsTerm
      (k := k) (A := Localization.Away (CAlgHom (R := k) (A := A) g))
      (s := {(algebraMap A[X] _ X, (1 : ℚ), (0 : ℚ))}) (by simp)
      ⟨triv, by
        rw [Finset.sup_singleton]
        simp only [fsTerm, Rat.cast_one, EReal.coe_one, one_mul, Rat.cast_zero,
          EReal.coe_zero, add_zero]
        rw [Ne, logAbs_eq_bot_iff, triv_val_of_ne_zero]
        · exact one_ne_zero
        · intro h
          rw [IsLocalization.to_map_eq_zero_iff
            (M := Submonoid.powers (CAlgHom (R := k) (A := A) g))
            (Localization.Away (CAlgHom (R := k) (A := A) g))
            (powers_le_nonZeroDivisors_of_noZeroDivisors hCg)] at h
          exact Polynomial.X_ne_zero h⟩
    refine hs.congr fun w => ?_
    rw [Finset.sup_singleton]
    simp [fsTerm]
  refine (h1.add h2).congr fun w => ?_
  simp only [proj_awayComap_C]

end cover

/-! ### The projection step -/

section main

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [WuRegularization.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A] {B : Type*} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

/-- **The projection step** (FHX Proposition 5.24, `prop:projection-step`), conditional on FHX
Proposition 5.22 for `π × id : Ỹ = Y × 𝔸¹ → Spec B[X]` and `Z × 𝔸¹` (the hypothesis
`N' : NormWeights (mapAlgHom φ) (S.map ⟨C, C_injective⟩) W' d`) and on the closure properties of
weakly psh functions (`IsPshClass W`, `IsPshClass W'`, with `u ∈ W` and `u ∘ p + log|w| ∈ W'`).

Let `φ : B → A` be integral, `Z = V(S) ⊊ Y` with `π|_Z` a closed immersion, and `f₁ + f₂ = 1`
separating `Z` from `π⁻¹(π(Z)) \ Z`. If `u` is of logarithmic growth and regularizable on
principal opens covering `Y \ Z`, then `u` is regularizable. -/
theorem IsRegularizable.of_projection (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).IsIntegral)
    (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0)
    (hZimm : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span (S : Set A))).comp (φ : B →+* A)))
    {f₁ f₂ : A} (hf : f₁ + f₂ = 1)
    (hf₂ : ∀ y : Berk k A, (∀ f ∈ S, y.val f = 0) → y.val f₂ = 0)
    (hf₁ : ∀ y y' : Berk k A, (∀ f ∈ S, y.val f = 0) → comap φ y' = comap φ y →
      (∃ f ∈ S, y'.val f ≠ 0) → y'.val f₁ = 0)
    {W : (Berk k A → EReal) → Prop} (hW : IsPshClass W)
    {W' : (Berk k A[X] → EReal) → Prop} (hW' : IsPshClass W') {d : ℕ}
    (N' : NormWeights (mapAlgHom φ) (S.map ⟨C, C_injective⟩) W' d)
    {u : Berk k A → EReal} (hu : W u) (hu' : W' fun z => u (proj z) + logAbs (X : A[X]) z)
    (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_isStrictExhaustion (k := k) (A := A[X])
  -- `u` is not identically `-∞`: it is regularizable near the trivial valuation
  have hne : ∃ x, u x ≠ ⊥ := by
    obtain ⟨f, hfS, hf0⟩ := hS
    obtain ⟨g, -, -, ⟨⟨w, hw⟩, -⟩⟩ := hcover triv
      ⟨f, hfS, by rw [triv_val_of_ne_zero hf0]; exact one_ne_zero⟩
    exact ⟨_, hw⟩
  -- the hypotheses on `Ỹ`
  have hf' : C f₁ + C f₂ = (1 : A[X]) := by rw [← C_add, hf, C_1]
  have hZ : ∀ z : Berk k A[X], (∀ f ∈ S.map ⟨C, C_injective⟩, z.val f = 0) →
      ∀ f ∈ S, (proj z).val f = 0 :=
    fun z hz f hf => hz (C f) (Finset.mem_map_of_mem _ hf)
  have hZ' : ∀ z : Berk k A[X], (∃ f ∈ S.map ⟨C, C_injective⟩, z.val f ≠ 0) →
      ∃ f ∈ S, (proj z).val f ≠ 0 := by
    rintro z ⟨f, hf, hf0⟩
    obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_map.1 hf
    exact ⟨f₀, hf₀, hf0⟩
  have hf₂' : ∀ z : Berk k A[X], (∀ f ∈ S.map ⟨C, C_injective⟩, z.val f = 0) → z.val (C f₂) = 0 :=
    fun z hz => hf₂ (proj z) (hZ z hz)
  have hf₁' : ∀ z z' : Berk k A[X], (∀ f ∈ S.map ⟨C, C_injective⟩, z.val f = 0) →
      comap (mapAlgHom φ) z' = comap (mapAlgHom φ) z →
      (∃ f ∈ S.map ⟨C, C_injective⟩, z'.val f ≠ 0) →
      z'.val (C f₁) = 0 := fun z z' hz hzz' hz' =>
    hf₁ (proj z) (proj z') (hZ z hz)
      (by rw [← proj_comap_mapAlgHom, ← proj_comap_mapAlgHom, hzz']) (hZ' z' hz')
  have hlog' : HasLogGrowth fun z : Berk k A[X] => u (proj z) + logAbs (X : A[X]) z :=
    (hlog.comp_comap (CAlgHom (R := k) (A := A))).add (hasLogGrowth_logAbs _)
  have hcover' : ∀ z : Berk k A[X], (∃ f ∈ S.map ⟨C, C_injective⟩, z.val f ≠ 0) →
      ∃ g : A[X], g ≠ 0 ∧ z.val g ≠ 0 ∧ IsRegularizable fun w =>
        u (proj (awayComap g w)) + logAbs (X : A[X]) (awayComap g w) := by
    intro z hz
    obtain ⟨g, hg0, hzg, hug⟩ := hcover (proj z) (hZ' z hz)
    exact ⟨CAlgHom (R := k) (A := A) g, by simpa [CAlgHom] using hg0, by simpa using hzg,
      isRegularizable_awayComap_CAlgHom hg0 hug⟩
  -- the hull criterion (FHX Lemma 5.19)
  refine IsRegularizable.of_hullIneq_add_smul u (hW.usc u hu) hlog hne ρ hρ.2.1 hρ.1.ne_top
    (fun c hc => (hρ.1.smul hc).upperSemicontinuous) fun c hc => ?_
  exact projection_hullIneq (mapAlgHom φ) (isIntegral_mapAlgHom hφ) (S.map ⟨C, C_injective⟩)
    (surjective_quotient_mapAlgHom hZimm) hf' hf₂' hf₁' hW' N' hu' hlog' hcover' hρ hc

end main

end EnvelopeProperty
