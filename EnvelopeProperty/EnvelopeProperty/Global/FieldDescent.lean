/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyComparison
import EnvelopeProperty.Projective.SubvarietyNormal
import EnvelopeProperty.Char0.BaseChangeDVR
import EnvelopeProperty.Global.Divisorial

/-!
# Descent to a countable field and the envelope property over arbitrary fields

This file implements the blueprint nodes `lem:gl-field-descent` and `prop:gl-ample-rational` of the
global chapter `global.tex` (subsection `subsec:gl-ample`) of the formalization of Fang–Han–Xia,
*The envelope property for unibranch projective varieties* (FHX, revision `832e086`,
`thm:normal-ample-EP`, Step 2): the envelope property `EP_X(1)` of a projectively normal
`X = V(I) ⊆ ℙᴹ_k` over an algebraically closed field `k` follows from the envelope property over
the countable algebraically closed subfields `k₀ ⊆ k` (Step 1, `prop:gl-ample-countable`). As
recorded in `rmk:gl-test-configurations` (and PLAN-68, literature item 4), neither test
configurations nor flat base change of base ideals are used: the proof goes through Fubini–Study
envelopes (`lem:sg-fs-envelope`, BJ addendum `lem:FSenv`), the extension of scalars of divisorial
valuation rings (`lem:c0-base-change-dvr`, `cor:c0-base-change-orders`, lane Z1) and divisorial
comparison on `X₀` (`thm:sg-comparison`).

## Setting

`k / k₀` is a field extension (`[Algebra k₀ k]`), `X = V(I) ⊆ ℙᴹ_k` a projective subvariety
(`EnvelopeProperty.ProjSubvariety`), `X₀ = V(I₀) ⊆ ℙᴹ_{k₀}` with `I₀ = I ∩ k₀[x]`.

## Main definitions

* `EnvelopeProperty.linearCoeffMap ρ`: the coefficientwise application `k[x] → k₀[x]` of a
  `k₀`-linear map `ρ : k → k₀`; it is `k₀[x]`-linear (`linearCoeffMap_map_mul`).
  `EnvelopeProperty.coordPoly k₀ β f` is the coordinate of `f` along the vector `β` of the basis
  `Module.Basis.ofVectorSpace k₀ k`, and `EnvelopeProperty.coeffSupport k₀ P` the finite set of
  basis vectors occurring in a finite set `P` of polynomials, so that `f = ∑_β c_β f_β`
  (`sum_C_mul_map_coordPoly`).
* `ProjBerk.restrictField k₀ : (ℙᴹ_k)^an → (ℙᴹ_{k₀})^an`, the restriction along
  `k₀[x] ⊆ k[x]`; `ProjBerk.FSData.extendField`, `ProjBerk.FSData.descendField`,
  `ProjBerk.FSData.coordData`: Fubini–Study data viewed over `k`, descended to `k₀`, and the
  coordinate data `m⁻¹ max_{t, β} (log|s_{tβ}| + λ_t)`.
* `ProjSubvariety.descendField X k₀ = X₀` and the restriction map
  `ProjSubvariety.restrictField X k₀ : X^an → X₀^an` (`r` in the blueprint).
* `ProjSubvariety.liftMap X k₀ : k[x] → k ⊗_{k₀} T₀`, `xᵢ ↦ 1 ⊗ x̄ᵢ`, into the extension of
  scalars of the cone ring `T₀ = S₀[t]` of `X₀`.

## Main results

* `lem:gl-field-descent`:
  `EnvelopeProperty.exists_isAlgClosed_countable_subfield` and `ProjSubvariety.exists_descendField`
  (a countable algebraically closed `k₀ ⊆ k` containing a given countable set, with
  `I = I₀ k[x]`); `ProjSubvariety.IsProjNormal.descendField` (if `S` is integrally closed, so is
  `S₀`); `ProjSubvariety.exists_restrictField_eq_of_isDivisorial` (every `v₀ ∈ X₀^div` has a lift
  `v ∈ X^an`, `r(v) = v₀`, with `|∑_β c_β p_β|_v = max_β |p_β|_{v₀}` for `k₀`-linearly independent
  `c_β ∈ k` and `p_β ∈ k₀[x]`) and `ProjSubvariety.exists_restrictField_eq_of_isDivisorial_basis`.
* Pullback along `r` (`lem:gl-pullback` for `r`): `ProjSubvariety.IsFS.comp_restrictField`,
  `ProjSubvariety.IsPSH.comp_restrictField`, `ProjSubvariety.restrictField_triv`.
* `prop:gl-ample-rational`: `ProjSubvariety.envelope_comp_restrictField`
  (`P_a(φ₀ ∘ r) = P_a(φ₀) ∘ r` for continuous `φ₀ : X₀^an → ℝ` and `a ∈ ℚ_{>0}`, with
  `ProjSubvariety.le_envelope_comp_restrictField_of_isFinFS`),
  `ProjSubvariety.hasEnvelopeProperty_one_of_countable` and, with the hypothesis in the shape of
  decision D-H5, `ProjSubvariety.hasEnvelopeProperty_one_of_forall_countable`.

## Deviations from the blueprint

* The identification `S = S₀ ⊗_{k₀} k` is not formalized as an isomorphism. Its two uses are
  replaced by the `k₀[x]`-linear coefficientwise retraction `Λ = linearCoeffMap ρ` of
  `k₀[x] → k[x]` (descent of normality: `Λ(I) ⊆ I₀` as `I = I₀ k[x]`) and by the `k`-algebra map
  `Ψ = liftMap` (the lift of divisorial points: `|f|_v = e^{-c ord_{R'}(Ψ f)}`, which vanishes on
  `I = I₀ k[x]`); primality of `I₀` is that of a contraction.
* In `prop:gl-ample-rational` the descended obstacle is not shown to be PL on `X₀` (which needs the
  descent of base point freeness by faithful flatness): with constants `C_i ≥ |φ_i|`,
  `φ₀ = max(φ₁₀, -C₁) - max(φ₂₀, -C₂)` is a continuous real function on `X₀^an` with
  `φ₀ ∘ r = φ = φ₁ - φ₂`, and the envelope property applies to continuous obstacles
  (`FSSystem.HasEnvelopeProperty.isPSH_envelope_of_continuous`).
* `P_a(φ₀ ∘ r) = P_a(φ₀) ∘ r` is proved for every rational `a > 0` and without any envelope
  property; `EP_{X₀}(1)` is used only to conclude that `P_1(φ₀)` is psh.
* The hypothesis of `prop:gl-ample-rational` is the conclusion of `prop:gl-ample-countable`
  (`EP_{X₀}(1)` for projectively normal `X₀`) for every countable algebraically closed field `k₀`
  with a `k₀`-algebra structure on `k` (i.e. every countable algebraically closed subfield, up to
  isomorphism); this is weaker than the D-H5 shape, which is the corollary
  `ProjSubvariety.hasEnvelopeProperty_one_of_forall_countable`.
* `lem:gl-field-descent` is stated for a countable set `A ⊆ k` of coefficients (for a countable set
  `Φ` of forms, take their coefficients); only the restriction `r` and the lift of divisorial points
  need `k₀` algebraically closed, the existence of `k₀` needs `k` algebraically closed.
-/

open scoped NNReal ENNReal Topology TensorProduct

open Set Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Coefficientwise linear maps of polynomials -/

section LinearCoeffMap

variable {k₀ : Type*} [Field k₀] {k : Type*} [Field k] [Algebra k₀ k] {σ : Type*}

/-- The coefficientwise application `∑_m c_m x^m ↦ ∑_m ρ(c_m) x^m` of a `k₀`-linear map
`ρ : k → k₀` to polynomials over `k`. -/
def linearCoeffMap (ρ : k →ₗ[k₀] k₀) (f : MvPolynomial σ k) : MvPolynomial σ k₀ :=
  ∑ m ∈ f.support, monomial m (ρ (coeff m f))

@[simp]
theorem coeff_linearCoeffMap (ρ : k →ₗ[k₀] k₀) (f : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (linearCoeffMap ρ f) = ρ (coeff m f) := by
  classical
  rw [linearCoeffMap, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem linearCoeffMap_add (ρ : k →ₗ[k₀] k₀) (f g : MvPolynomial σ k) :
    linearCoeffMap ρ (f + g) = linearCoeffMap ρ f + linearCoeffMap ρ g := by
  ext m
  simp

theorem linearCoeffMap_sub (ρ : k →ₗ[k₀] k₀) (f g : MvPolynomial σ k) :
    linearCoeffMap ρ (f - g) = linearCoeffMap ρ f - linearCoeffMap ρ g := by
  ext m
  simp

theorem linearCoeffMap_sum (ρ : k →ₗ[k₀] k₀) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ k) :
    linearCoeffMap ρ (∑ i ∈ s, f i) = ∑ i ∈ s, linearCoeffMap ρ (f i) := by
  ext m
  simp [coeff_sum]

/-- `linearCoeffMap ρ` is `k₀[x]`-linear: `ρ(g f) = g ρ(f)` for `g ∈ k₀[x]`. -/
theorem linearCoeffMap_map_mul (ρ : k →ₗ[k₀] k₀) (g : MvPolynomial σ k₀) (f : MvPolynomial σ k) :
    linearCoeffMap ρ (map (algebraMap k₀ k) g * f) = g * linearCoeffMap ρ f := by
  classical
  ext m
  rw [coeff_linearCoeffMap, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_map, coeff_linearCoeffMap, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- If `ρ` is a retraction of `k₀ → k`, then `linearCoeffMap ρ` is a retraction of
`k₀[x] → k[x]`. -/
theorem linearCoeffMap_map {ρ : k →ₗ[k₀] k₀} (hρ : ∀ a, ρ (algebraMap k₀ k a) = a)
    (g : MvPolynomial σ k₀) : linearCoeffMap ρ (map (algebraMap k₀ k) g) = g := by
  ext m
  simp [coeff_map, hρ]

theorem isHomogeneous_linearCoeffMap {f : MvPolynomial σ k} {d : ℕ} (hf : f.IsHomogeneous d)
    (ρ : k →ₗ[k₀] k₀) : (linearCoeffMap ρ f).IsHomogeneous d := fun {m} hm =>
  hf fun h0 => hm (by rw [coeff_linearCoeffMap, h0, map_zero])

/-- Homogeneous components commute with extension of scalars. -/
theorem homogeneousComponent_map_algebraMap (d : ℕ) (f : MvPolynomial σ k₀) :
    homogeneousComponent d (map (algebraMap k₀ k) f) =
      map (algebraMap k₀ k) (homogeneousComponent d f) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

/-- A polynomial over `k₀` is homogeneous if its image over `k` is. -/
theorem isHomogeneous_of_map_algebraMap {f : MvPolynomial σ k₀} {d : ℕ}
    (h : (map (algebraMap k₀ k) f).IsHomogeneous d) : f.IsHomogeneous d := fun {m} hm =>
  h (by rw [coeff_map]; exact (map_ne_zero _).2 hm)

theorem map_algebraMap_injective :
    Function.Injective (map (algebraMap k₀ k) : MvPolynomial σ k₀ → MvPolynomial σ k) :=
  map_injective _ (algebraMap k₀ k).injective

/-! #### Coordinates in a basis of `k / k₀` -/

variable (k₀) in
/-- The finite set of basis vectors (of the basis `Module.Basis.ofVectorSpace k₀ k` of `k` over
`k₀`) occurring in the coefficients of a finite set `P` of polynomials over `k`. -/
def coeffSupport (P : Finset (MvPolynomial σ k)) :
    Finset (Module.Basis.ofVectorSpaceIndex k₀ k) := by
  classical
  exact P.biUnion fun f => f.support.biUnion fun m =>
    ((Module.Basis.ofVectorSpace k₀ k).repr (coeff m f)).support

theorem support_repr_subset_coeffSupport {P : Finset (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : f ∈ P) (m : σ →₀ ℕ) :
    ((Module.Basis.ofVectorSpace k₀ k).repr (coeff m f)).support ⊆ coeffSupport k₀ P := by
  classical
  by_cases hm : m ∈ f.support
  · intro β hβ
    simp only [coeffSupport, Finset.mem_biUnion]
    exact ⟨f, hf, m, hm, hβ⟩
  · rw [notMem_support_iff.1 hm, map_zero, Finsupp.support_zero]
    exact Finset.empty_subset _

variable (k₀) in
/-- The coordinate `f_β ∈ k₀[x]` of `f ∈ k[x]` along the basis vector `β` of the basis
`Module.Basis.ofVectorSpace k₀ k` of `k` over `k₀`. -/
def coordPoly (β : Module.Basis.ofVectorSpaceIndex k₀ k) (f : MvPolynomial σ k) :
    MvPolynomial σ k₀ :=
  linearCoeffMap ((Module.Basis.ofVectorSpace k₀ k).coord β) f

theorem isHomogeneous_coordPoly {f : MvPolynomial σ k} {d : ℕ} (hf : f.IsHomogeneous d)
    (β : Module.Basis.ofVectorSpaceIndex k₀ k) : (coordPoly k₀ β f).IsHomogeneous d :=
  isHomogeneous_linearCoeffMap hf _

/-- **Decomposition of polynomials in a basis of `k / k₀`**: every `f ∈ P` is
`f = ∑_β c_β f_β` with `c_β` the basis vectors of `coeffSupport k₀ P` (linearly independent over
`k₀`, `linearIndependent_basis_finset`) and `f_β = coordPoly k₀ β f ∈ k₀[x]`. -/
theorem sum_C_mul_map_coordPoly {P : Finset (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : f ∈ P) :
    ∑ β ∈ coeffSupport k₀ P, C ((Module.Basis.ofVectorSpace k₀ k) β) *
      map (algebraMap k₀ k) (coordPoly k₀ β f) = f := by
  classical
  set 𝔟 := Module.Basis.ofVectorSpace k₀ k
  ext m
  rw [coeff_sum]
  simp only [coordPoly, coeff_C_mul, coeff_map, coeff_linearCoeffMap, Module.Basis.coord_apply]
  have hx : ∑ β ∈ (𝔟.repr (coeff m f)).support, 𝔟.repr (coeff m f) β • 𝔟 β = coeff m f := by
    conv_rhs => rw [← 𝔟.linearCombination_repr (coeff m f)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  conv_rhs => rw [← hx]
  rw [Finset.sum_subset (support_repr_subset_coeffSupport hf m) fun β _ hβ => by
    rw [Finsupp.notMem_support_iff.1 hβ, zero_smul]]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Algebra.smul_def, mul_comm]

/-- The vectors of a finite set of indices of the basis `Module.Basis.ofVectorSpace k₀ k` are
linearly independent over `k₀`. -/
theorem linearIndependent_basis_finset (B : Finset (Module.Basis.ofVectorSpaceIndex k₀ k)) :
    LinearIndependent k₀ fun β : B => (Module.Basis.ofVectorSpace k₀ k) β :=
  (Module.Basis.ofVectorSpace k₀ k).linearIndependent.comp _ Subtype.val_injective

/-- A choice of preimage under `k₀[x] → k[x]` (`0` outside the image). -/
def descendPoly (k₀ : Type*) [Field k₀] [Algebra k₀ k] (p : MvPolynomial σ k) :
    MvPolynomial σ k₀ := by
  classical
  exact if h : p ∈ Set.range (map (algebraMap k₀ k)) then h.choose else 0

theorem map_descendPoly {p : MvPolynomial σ k}
    (h : p ∈ Set.range (map (algebraMap k₀ k) : MvPolynomial σ k₀ → MvPolynomial σ k)) :
    map (algebraMap k₀ k) (descendPoly k₀ p) = p := by
  rw [descendPoly, dif_pos h]
  exact h.choose_spec

end LinearCoeffMap

/-! ### Restriction of points to a subfield -/

namespace ProjBerk

variable {k : Type u} [Field k] {k₀ : Type u} [Field k₀] [Algebra k₀ k] {M : ℕ}

variable (k₀) in
/-- The **restriction** `r : (ℙᴹ_k)^an → (ℙᴹ_{k₀})^an` along `k₀[x] ⊆ k[x]`:
`|f|_{r(v)} = |f|_v` for `f ∈ k₀[x]`. -/
def restrictField (v : ProjBerk k M) : ProjBerk k₀ M :=
  ⟨⟨v.1.val.comap (map (algebraMap k₀ k)), fun c hc => by
      rw [Valuation.comap_apply, MvPolynomial.algebraMap_eq, map_C, ← MvPolynomial.algebraMap_eq]
      exact v.1.val_algebraMap _ ((map_ne_zero _).2 hc)⟩,
    (isGraded_iff _).2 fun f d => by
      change v.1.val (map _ (homogeneousComponent d f)) ≤ v.1.val (map _ f)
      rw [← homogeneousComponent_map_algebraMap]
      exact (isGraded_iff _).1 v.isGraded _ d, by
      have h : ∀ i, v.1.val (map (algebraMap k₀ k) (X i : MvPolynomial (Fin (M + 1)) k₀)) =
          v.1.val (X i) := fun i => by rw [map_X]
      simpa only [Valuation.comap_apply, RingHom.coe_coe, h] using v.sup_val_X⟩

@[simp]
theorem restrictField_val_apply (v : ProjBerk k M) (f : MvPolynomial (Fin (M + 1)) k₀) :
    (restrictField k₀ v).1.val f = v.1.val (map (algebraMap k₀ k) f) :=
  rfl

theorem continuous_restrictField :
    Continuous (restrictField k₀ : ProjBerk k M → ProjBerk k₀ M) :=
  continuous_iff.2 fun f =>
    (show Continuous fun y : ProjBerk k M => y.1.val (map (algebraMap k₀ k) f) from
      (Berk.continuous_val_apply _).comp continuous_val)

theorem logAbs_restrictField (s : MvPolynomial (Fin (M + 1)) k₀) (v : ProjBerk k M) :
    logAbs s (restrictField k₀ v) = logAbs (map (algebraMap k₀ k) s) v :=
  rfl

namespace FSData

variable {a : ℚ}

open Classical in
variable (k) in
/-- Extension of scalars of Fubini–Study data: the same data, with forms in `k[x] ⊇ k₀[x]`. -/
def extendField (D : FSData k₀ M a) : FSData k M a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun t => (map (algebraMap k₀ k) t.1, t.2)
  isHomogeneous t ht := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact (D.isHomogeneous s hs).map _
  exists_ne_zero := by
    obtain ⟨t, ht, h0⟩ := D.exists_ne_zero
    refine ⟨_, Finset.mem_image_of_mem _ ht, fun h => h0 ?_⟩
    apply map_algebraMap_injective (k := k)
    rw [map_zero]
    exact h

theorem mem_extendField_terms {D : FSData k₀ M a} {t : MvPolynomial (Fin (M + 1)) k₀ × ℝ}
    (ht : t ∈ D.terms) : (map (algebraMap k₀ k) t.1, t.2) ∈ (D.extendField k).terms := by
  classical
  exact Finset.mem_image_of_mem _ ht

/-- `(D_k).eval = D.eval ∘ r`. -/
theorem eval_extendField (D : FSData k₀ M a) (v : ProjBerk k M) :
    (D.extendField k).eval v = D.eval (restrictField k₀ v) := by
  classical
  rw [eval_def, eval_def]
  change _ * (D.terms.image _).sup _ = _
  rw [Finset.sup_image]
  rfl

open Classical in
/-- **Descent of Fubini–Study data** whose forms have coefficients in `k₀`: the same data with the
forms regarded in `k₀[x]`. -/
def descendField (D : FSData k M a)
    (hD : ∀ t ∈ D.terms, t.1 ∈ Set.range
      (map (algebraMap k₀ k) : MvPolynomial (Fin (M + 1)) k₀ → MvPolynomial (Fin (M + 1)) k)) :
    FSData k₀ M a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun t => (descendPoly k₀ t.1, t.2)
  isHomogeneous t ht := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    refine isHomogeneous_of_map_algebraMap (k := k) ?_
    rw [map_descendPoly (hD s hs)]
    exact D.isHomogeneous s hs
  exists_ne_zero := by
    obtain ⟨t, ht, h0⟩ := D.exists_ne_zero
    refine ⟨_, Finset.mem_image_of_mem _ ht, fun h => h0 ?_⟩
    rw [← map_descendPoly (hD t ht)]
    change map (algebraMap k₀ k) (descendPoly k₀ t.1) = 0
    rw [show descendPoly k₀ t.1 = 0 from h, map_zero]

/-- `D.eval = (D descended to k₀).eval ∘ r`. -/
theorem eval_descendField (D : FSData k M a)
    (hD : ∀ t ∈ D.terms, t.1 ∈ Set.range
      (map (algebraMap k₀ k) : MvPolynomial (Fin (M + 1)) k₀ → MvPolynomial (Fin (M + 1)) k))
    (v : ProjBerk k M) : (D.descendField hD).eval (restrictField k₀ v) = D.eval v := by
  classical
  rw [eval_def, eval_def]
  change _ * (D.terms.image _).sup _ = _
  rw [Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun t ht => ?_
  change logAbs (map (algebraMap k₀ k) (descendPoly k₀ t.1)) v + _ = _
  rw [map_descendPoly (hD t ht)]
  rfl

open Classical in
variable (k₀) in
/-- The **coordinate data** `m⁻¹ max_{t, β} (log|s_{tβ}| + λ_t)` over `k₀` of Fubini–Study data
`m⁻¹ max_t (log|s_t| + λ_t)` over `k`, where `s_{tβ} = coordPoly k₀ β s_t` for `β` in a finite set
`B` of vectors of the basis of `k / k₀` (`prop:gl-ample-rational`). -/
def coordData (D : FSData k M a) (B : Finset (Module.Basis.ofVectorSpaceIndex k₀ k))
    (hB : ∃ t ∈ D.terms, ∃ β ∈ B, coordPoly k₀ β t.1 ≠ 0) : FSData k₀ M a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := (D.terms ×ˢ B).image fun tβ => (coordPoly k₀ tβ.2 tβ.1.1, tβ.1.2)
  isHomogeneous s hs := by
    obtain ⟨⟨t, β⟩, htβ, rfl⟩ := Finset.mem_image.1 hs
    exact isHomogeneous_coordPoly (D.isHomogeneous t (Finset.mem_product.1 htβ).1) _
  exists_ne_zero := by
    obtain ⟨t, ht, β, hβ, hne⟩ := hB
    exact ⟨_, Finset.mem_image.2 ⟨(t, β), Finset.mem_product.2 ⟨ht, hβ⟩, rfl⟩, hne⟩

variable {D : FSData k M a} {B : Finset (Module.Basis.ofVectorSpaceIndex k₀ k)}
  {hB : ∃ t ∈ D.terms, ∃ β ∈ B, coordPoly k₀ β t.1 ≠ 0}

theorem mem_coordData_terms {t : MvPolynomial (Fin (M + 1)) k × ℝ} (ht : t ∈ D.terms)
    {β : Module.Basis.ofVectorSpaceIndex k₀ k} (hβ : β ∈ B) :
    (coordPoly k₀ β t.1, t.2) ∈ (D.coordData k₀ B hB).terms := by
  classical
  exact Finset.mem_image.2 ⟨(t, β), Finset.mem_product.2 ⟨ht, hβ⟩, rfl⟩

theorem exists_of_mem_coordData_terms {s : MvPolynomial (Fin (M + 1)) k₀ × ℝ}
    (hs : s ∈ (D.coordData k₀ B hB).terms) :
    ∃ t ∈ D.terms, ∃ β ∈ B, s = (coordPoly k₀ β t.1, t.2) := by
  classical
  obtain ⟨⟨t, β⟩, htβ, rfl⟩ := Finset.mem_image.1 hs
  exact ⟨t, (Finset.mem_product.1 htβ).1, β, (Finset.mem_product.1 htβ).2, rfl⟩

@[simp]
theorem coordData_m : (D.coordData k₀ B hB).m = D.m :=
  rfl

end FSData

end ProjBerk

/-! ### Countable algebraically closed subfields -/

/-- Every countable subset `A` of an algebraically closed field `k` lies in a countable
algebraically closed subfield `k₀ ⊆ k`: the algebraic closure in `k` of the subfield generated by
`A` (countable by `Subfield.cardinalMk_closure_le_max` and
`Algebra.IsAlgebraic.cardinalMk_le_max`). -/
theorem exists_isAlgClosed_countable_subfield {k : Type u} [Field k] [IsAlgClosed k] {A : Set k}
    (hA : A.Countable) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Algebra k₀ k), IsAlgClosed k₀ ∧ Countable k₀ ∧
      A ⊆ Set.range (algebraMap k₀ k) := by
  let F := Subfield.closure A
  refine ⟨algebraicClosure F k, inferInstance, inferInstance, IsAlgClosure.isAlgClosed F, ?_, ?_⟩
  · have hF : Cardinal.mk F ≤ Cardinal.aleph0 :=
      (Subfield.cardinalMk_closure_le_max A).trans (max_le hA.le_aleph0 le_rfl)
    exact Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max F
      (algebraicClosure F k)).trans (max_le hF le_rfl))
  · intro x hx
    exact ⟨⟨x, IntermediateField.algebraMap_mem _ (⟨x, Subfield.subset_closure hx⟩ : F)⟩, rfl⟩

/-! ### The variety `X₀ = V(I ∩ k₀[x])` and the restriction map -/

namespace ProjSubvariety

variable {k : Type u} [Field k] {k₀ : Type u} [Field k₀] [Algebra k₀ k] {M : ℕ}
  (X : ProjSubvariety k M)

variable (k₀) in
/-- **The descended variety** `X₀ = V(I₀) ⊆ ℙᴹ_{k₀}`, `I₀ = I ∩ k₀[x]` (`lem:gl-field-descent`),
for a field extension `k / k₀`. -/
def descendField : ProjSubvariety k₀ M where
  ideal := X.ideal.comap (map (algebraMap k₀ k))
  isHomogeneousIdeal f hf d := by
    rw [Ideal.mem_comap, ← homogeneousComponent_map_algebraMap]
    exact X.isHomogeneousIdeal _ hf d
  isPrime := Ideal.comap_isPrime _ _
  exists_X_notMem := by
    obtain ⟨i, hi⟩ := X.exists_X_notMem
    exact ⟨i, by rwa [Ideal.mem_comap, map_X]⟩

theorem mem_descendField_ideal {f : MvPolynomial (Fin (M + 1)) k₀} :
    f ∈ (X.descendField k₀).ideal ↔ map (algebraMap k₀ k) f ∈ X.ideal :=
  Iff.rfl

/-- `I₀ k[x] ⊆ I`. -/
theorem map_descendField_ideal_le :
    Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal ≤ X.ideal :=
  Ideal.map_le_iff_le_comap.2 le_rfl

variable (k₀) in
/-- **The restriction map** `r : X^an → X₀^an` (`lem:gl-field-descent`). -/
def restrictField (v : X.an) : (X.descendField k₀).an :=
  ⟨ProjBerk.restrictField k₀ v.1, fun _ hf => v.2 _ hf⟩

@[simp]
theorem restrictField_val_apply (v : X.an) (f : MvPolynomial (Fin (M + 1)) k₀) :
    ((X.restrictField k₀ v : (X.descendField k₀).an) : ProjBerk k₀ M).1.val f =
      (v : ProjBerk k M).1.val (map (algebraMap k₀ k) f) :=
  rfl

theorem continuous_restrictField : Continuous (X.restrictField k₀) :=
  (ProjBerk.continuous_restrictField.comp continuous_subtype_val).subtype_mk _

/-- `r(⋆) = ⋆`. -/
theorem restrictField_triv : X.restrictField k₀ X.triv = (X.descendField k₀).triv := by
  refine Subtype.ext (ProjBerk.ext (Berk.ext_val fun f => ?_))
  change (X.triv : ProjBerk k M).1.val (map _ f) =
    ((X.descendField k₀).triv : ProjBerk k₀ M).1.val f
  by_cases hf : f ∈ (X.descendField k₀).ideal
  · rw [X.triv.2 _ hf, (X.descendField k₀).triv.2 _ hf]
  · rw [X.triv_val_of_notMem hf, (X.descendField k₀).triv_val_of_notMem hf]

variable {X}

/-- Fubini–Study functions pull back along `r`: `𝓗(X₀, a) ∘ r ⊆ 𝓗(X, a)`. -/
theorem IsFS.comp_restrictField {a : ℚ} {f : (X.descendField k₀).an → EReal}
    (h : (X.descendField k₀).IsFS a f) : X.IsFS a fun v => f (X.restrictField k₀ v) := by
  obtain ⟨D, ⟨t, ht, htI⟩, hf⟩ := h
  refine ⟨D.extendField k, ⟨_, ProjBerk.FSData.mem_extendField_terms ht, htI⟩, fun v => ?_⟩
  dsimp only
  rw [hf, ProjBerk.FSData.eval_extendField]
  rfl

/-- **Psh functions pull back along `r`** (`lem:gl-pullback` for `r`):
`PSH(X₀, θ) ∘ r ⊆ PSH(X, θ)`. -/
theorem IsPSH.comp_restrictField {θ : ℝ} {u : (X.descendField k₀).an → EReal}
    (h : (X.descendField k₀).IsPSH θ u) : X.IsPSH θ fun v => u (X.restrictField k₀ v) := by
  obtain ⟨-, husc, ι, h₁, h₂, h₃, a, f, hf, ha, hanti, hinf⟩ := id h
  refine ⟨⟨X.triv, ?_⟩, husc.comp X.continuous_restrictField, ι, h₁, h₂, h₃, a,
    fun i v => f i (X.restrictField k₀ v), fun i => IsFS.comp_restrictField (hf i), ha,
    fun v => hanti _, fun v => hinf _⟩
  dsimp only
  rw [restrictField_triv]
  exact FSSystem.IsPSH.apply_triv_ne_bot h

/-! ### Values at divisorial points -/

/-- At a divisorial point `v` of `X`, with data `(R', c)`, `|f|_v = e^{-c ord_{R'}(f̄)}` for every
`f ∈ k[x]` (the case of constant polynomials in `t` of `def:sg-div`). -/
theorem IsDivisorial.exists_val_eq {v : X.an} (hv : X.IsDivisorial v) :
    ∃ (R' : BirationalDVR k X.ConeRing) (c : ℚ), 0 < c ∧ ∀ f : MvPolynomial (Fin (M + 1)) k,
      (v : ProjBerk k M).1.val f = expOrd (expNeg c) (R'.ord (X.coneMk (Polynomial.C f))) := by
  obtain ⟨R', c, hc, h⟩ := hv
  refine ⟨R', c, hc, fun f => ?_⟩
  have h₁ := h (Polynomial.C f)
  rw [Berk.logAbs_def, ProjBerk.gaussExt_val_C, ← log_expOrd_expNeg (by exact_mod_cast hc)] at h₁
  exact ENNReal.coe_injective (ENNReal.log_injective h₁)

/-! ### Lifting divisorial points (`lem:gl-field-descent`, last part) -/

section Lift

variable (X k₀) in
/-- The `k`-algebra map `Ψ : k[x] → k ⊗_{k₀} T₀`, `xᵢ ↦ 1 ⊗ x̄ᵢ`, into the extension of scalars of
the cone ring `T₀ = S₀[t]` of `X₀`; on `k₀[x]` it is `f ↦ 1 ⊗ f̄`
(`ProjSubvariety.liftMap_map`). -/
def liftMap : MvPolynomial (Fin (M + 1)) k →ₐ[k] k ⊗[k₀] (X.descendField k₀).ConeRing :=
  aeval fun i => (1 : k) ⊗ₜ[k₀] (X.descendField k₀).coneMk (Polynomial.C (MvPolynomial.X i))

theorem liftMap_map (p : MvPolynomial (Fin (M + 1)) k₀) :
    X.liftMap k₀ (map (algebraMap k₀ k) p) =
      (1 : k) ⊗ₜ[k₀] (X.descendField k₀).coneMk (Polynomial.C p) := by
  set g : MvPolynomial (Fin (M + 1)) k₀ →ₐ[k₀] (X.descendField k₀).ConeRing :=
    (X.descendField k₀).coneMk.comp Polynomial.CAlgHom
  have hg : ∀ q, g q = (X.descendField k₀).coneMk (Polynomial.C q) := fun _ => rfl
  rw [liftMap, aeval_map_algebraMap]
  have h := congrArg (fun φ => φ p)
    (comp_aeval (fun i => g (MvPolynomial.X i)) (Algebra.TensorProduct.includeRight :
      (X.descendField k₀).ConeRing →ₐ[k₀] k ⊗[k₀] (X.descendField k₀).ConeRing))
  simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply] at h
  change (aeval fun i => (1 : k) ⊗ₜ[k₀] g (MvPolynomial.X i)) p = (1 : k) ⊗ₜ[k₀] g p
  rw [← h]
  exact congrArg _ (DFunLike.congr_fun (aeval_unique g).symm p)

theorem liftMap_C_mul_map (c : k) (p : MvPolynomial (Fin (M + 1)) k₀) :
    X.liftMap k₀ (C c * map (algebraMap k₀ k) p) =
      c ⊗ₜ[k₀] (X.descendField k₀).coneMk (Polynomial.C p) := by
  rw [map_mul, liftMap_map, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one]
  rfl

theorem liftMap_eq_zero_of_mem
    (hI : X.ideal = Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal)
    {f : MvPolynomial (Fin (M + 1)) k} (hf : f ∈ X.ideal) : X.liftMap k₀ f = 0 := by
  have hle : X.ideal ≤ RingHom.ker (X.liftMap k₀).toRingHom := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change X.liftMap k₀ (map (algebraMap k₀ k) p) = 0
    rw [liftMap_map, coneMk_C]
    have h0 : (X.descendField k₀).coordMk p = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hp
    rw [h0, Polynomial.C_0, TensorProduct.tmul_zero]
  exact hle hf

variable [IsAlgClosed k₀]

/-- **Lift of divisorial points** (`lem:gl-field-descent`, last part): if `I = I₀ k[x]` and `k₀`
is algebraically closed, every divisorial point `v₀ ∈ X₀^div` has a lift `v ∈ X^an`, `r(v) = v₀`,
with `|∑_β c_β p_β|_v = max_β |p_β|_{v₀}` for all `k₀`-linearly independent `c_β ∈ k` and all
`p_β ∈ k₀[x]`. With the data `(R'₀, c)` of `v₀` (`def:sg-div`), `|f|_v = e^{-c ord_{R'}(Ψ f)}` for
the extension of scalars `R' = (R'₀ ⊗_{k₀} k)_{𝔪 ⊗ k}` (`lem:c0-base-change-dvr`), whose order of
`∑ c_β ⊗ g_β` is `min_β ord_{R'₀}(g_β)` (`cor:c0-base-change-orders`). -/
theorem exists_restrictField_eq_of_isDivisorial
    (hI : X.ideal = Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal)
    {v₀ : (X.descendField k₀).an} (hv₀ : (X.descendField k₀).IsDivisorial v₀) :
    ∃ v : X.an, X.restrictField k₀ v = v₀ ∧
      ∀ {ι : Type u} [Fintype ι] {c : ι → k}, LinearIndependent k₀ c →
        ∀ p : ι → MvPolynomial (Fin (M + 1)) k₀,
          (v : ProjBerk k M).1.val (∑ i, C (c i) * map (algebraMap k₀ k) (p i)) =
            Finset.univ.sup fun i => (v₀ : ProjBerk k₀ M).1.val (p i) := by
  classical
  obtain ⟨R'₀, c₀, hc₀, hval⟩ := hv₀.exists_val_eq
  set R' := R'₀.baseChange k
  set q := expNeg (c₀ : ℝ)
  have hq : q ≤ 1 := ProjBerk.expNeg_le_one (by exact_mod_cast hc₀.le)
  set w : Berk k (MvPolynomial (Fin (M + 1)) k) := Berk.comap (X.liftMap k₀) (R'.berkPoint q hq)
  have hw : ∀ f, w.val f = expOrd q (R'.ord (X.liftMap k₀ f)) := fun f => rfl
  have hwmap : ∀ p, w.val (map (algebraMap k₀ k) p) = (v₀ : ProjBerk k₀ M).1.val p := fun p => by
    rw [hw, liftMap_map, BirationalDVR.ord_baseChange_one_tmul, hval]
  have hwsum : ∀ {ι : Type u} [Fintype ι] {c : ι → k}, LinearIndependent k₀ c →
      ∀ p : ι → MvPolynomial (Fin (M + 1)) k₀,
        w.val (∑ i, C (c i) * map (algebraMap k₀ k) (p i)) =
          Finset.univ.sup fun i => (v₀ : ProjBerk k₀ M).1.val (p i) := by
    intro ι _ c hc p
    rw [hw, map_sum]
    simp only [liftMap_C_mul_map]
    rw [R'₀.ord_baseChange_sum k hc, expOrd_iInf_eq_finset_sup hq Finset.univ _
      fun i hi => absurd (Finset.mem_univ i) hi]
    simp only [hval]
  -- `w` is graded
  have hgr : IsGraded w := (isGraded_iff w).2 fun f d => by
    have hf := sum_C_mul_map_coordPoly (k₀ := k₀) (Finset.mem_singleton_self f)
    set B := coeffSupport k₀ ({f} : Finset (MvPolynomial (Fin (M + 1)) k))
    have hfd : homogeneousComponent d f = ∑ β ∈ B, C ((Module.Basis.ofVectorSpace k₀ k) β) *
        map (algebraMap k₀ k) (homogeneousComponent d (coordPoly k₀ β f)) := by
      conv_lhs => rw [← hf]
      rw [map_sum]
      simp only [homogeneousComponent_C_mul, homogeneousComponent_map_algebraMap]
    rw [hfd]
    conv_rhs => rw [← hf]
    rw [← Finset.sum_coe_sort B, ← Finset.sum_coe_sort B,
      hwsum (linearIndependent_basis_finset _), hwsum (linearIndependent_basis_finset _)]
    exact Finset.sup_mono_fun fun β _ => (isGraded_iff _).1 v₀.1.isGraded _ d
  -- `w` is normalized
  have hnorm : Finset.univ.sup (fun i => w.val (MvPolynomial.X i)) = 1 := by
    have h : ∀ i, w.val (MvPolynomial.X i) = (v₀ : ProjBerk k₀ M).1.val (MvPolynomial.X i) :=
      fun i => by rw [← hwmap, map_X]
    simp only [h]
    exact v₀.1.sup_val_X
  refine ⟨⟨⟨w, hgr, hnorm⟩, fun f hf => ?_⟩, Subtype.ext (ProjBerk.ext (Berk.ext_val fun p =>
    hwmap p)), fun hc p => hwsum hc p⟩
  change w.val f = 0
  rw [hw, liftMap_eq_zero_of_mem hI hf, BirationalDVR.ord_zero, expOrd_top]

/-- `ProjSubvariety.exists_restrictField_eq_of_isDivisorial` for the vectors of a finite set `B`
of the basis `Module.Basis.ofVectorSpace k₀ k` of `k / k₀`. -/
theorem exists_restrictField_eq_of_isDivisorial_basis
    (hI : X.ideal = Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal)
    {v₀ : (X.descendField k₀).an} (hv₀ : (X.descendField k₀).IsDivisorial v₀) :
    ∃ v : X.an, X.restrictField k₀ v = v₀ ∧
      ∀ (B : Finset (Module.Basis.ofVectorSpaceIndex k₀ k))
        (p : Module.Basis.ofVectorSpaceIndex k₀ k → MvPolynomial (Fin (M + 1)) k₀),
          (v : ProjBerk k M).1.val (∑ β ∈ B, C ((Module.Basis.ofVectorSpace k₀ k) β) *
            map (algebraMap k₀ k) (p β)) = B.sup fun β => (v₀ : ProjBerk k₀ M).1.val (p β) := by
  obtain ⟨v, h₁, h₂⟩ := exists_restrictField_eq_of_isDivisorial hI hv₀
  refine ⟨v, h₁, fun B p => ?_⟩
  rw [← Finset.sum_coe_sort B, h₂ (linearIndependent_basis_finset B) fun β => p β,
    Finset.univ_eq_attach]
  exact Finset.sup_attach B fun β => (v₀ : ProjBerk k₀ M).1.val (p β)

end Lift

/-! ### Descent of projective normality (`lem:gl-field-descent`, second part) -/

/-- **Projective normality descends** (`lem:gl-field-descent`): if `I = I₀ k[x]` and
`S = k[x] / I` is integrally closed, so is `S₀ = k₀[x] / I₀`. An element `α / γ` of `Frac S₀`
integral over `S₀` lies in `S`, `α = γ s`; applying a `k₀[x]`-linear retraction
`Λ : k[x] → k₀[x]` (coefficientwise, from a `k₀`-linear retraction `k → k₀`), which maps `I` to
`I₀`, gives `α = γ Λ(s)` in `S₀` (the faithful flatness argument of the blueprint). -/
theorem IsProjNormal.descendField (hX : X.IsProjNormal)
    (hI : X.ideal = Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal) :
    (X.descendField k₀).IsProjNormal := by
  classical
  -- a `k₀`-linear retraction `ρ : k → k₀`
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k₀ k)
    (LinearMap.ker_eq_bot.2 (algebraMap k₀ k).injective)
  have hρ' : ∀ a, ρ (algebraMap k₀ k a) = a := fun a => LinearMap.congr_fun hρ a
  -- `Λ = linearCoeffMap ρ` maps `I` into `I₀`
  have hΛ : ∀ f ∈ X.ideal, linearCoeffMap ρ f ∈ (X.descendField k₀).ideal := by
    intro f hf
    rw [hI, Ideal.map, Ideal.span, Submodule.mem_span_set'] at hf
    obtain ⟨n, a, g, rfl⟩ := hf
    rw [linearCoeffMap_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨g₀, hg₀, hg⟩ := (g i).2
    rw [smul_eq_mul, ← hg, mul_comm, linearCoeffMap_map_mul]
    exact Ideal.mul_mem_right _ _ hg₀
  have hX' : IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal) := hX
  let j : MvPolynomial (Fin (M + 1)) k₀ ⧸ (X.descendField k₀).ideal →+*
      MvPolynomial (Fin (M + 1)) k ⧸ X.ideal :=
    Ideal.quotientMap X.ideal (map (algebraMap k₀ k)) fun _ hf => hf
  have hj : Function.Injective j := Ideal.quotientMap_injective
  have hjmk : ∀ x, j (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk X.ideal (map (algebraMap k₀ k) x) := fun _ => rfl
  refine isIntegrallyClosed_of_forall_mul_mem_range j hj fun w q a hq hw => ?_
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨Ideal.Quotient.mk _ (linearCoeffMap ρ h), ?_⟩
  have hjq : j (Ideal.Quotient.mk _ g) ≠ 0 := (map_ne_zero_iff j hj).2 hq
  refine mul_right_cancel₀ hjq ?_
  rw [hw, ← map_mul]
  congr 1
  rw [hjmk, hjmk, ← map_mul, Ideal.Quotient.eq] at hw
  have hmem := hΛ _ hw
  rw [linearCoeffMap_sub, mul_comm, linearCoeffMap_map_mul, linearCoeffMap_map hρ'] at hmem
  rw [← map_mul, Ideal.Quotient.eq, mul_comm]
  exact hmem

/-! ### Choice of the countable field (`lem:gl-field-descent`, first part) -/

/-- **`lem:gl-field-descent`, first part**: for `X = V(I) ⊆ ℙᴹ_k` over an algebraically closed
field `k` and a countable set `A ⊆ k` (e.g. the coefficients of a countable set `Φ` of forms),
there is a countable algebraically closed field `k₀ ⊆ k` containing `A` such that
`I₀ = I ∩ k₀[x]` generates `I`. Take for `k₀` the algebraic closure in `k` of the field generated
by `A` and by the coefficients of finitely many generators of `I`. -/
theorem exists_descendField [IsAlgClosed k] {A : Set k} (hA : A.Countable) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Algebra k₀ k), IsAlgClosed k₀ ∧ Countable k₀ ∧
      A ⊆ Set.range (algebraMap k₀ k) ∧
        X.ideal = Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian X.ideal : X.ideal.FG)
  obtain ⟨k₀, _, _, h₁, h₂, h₃⟩ := exists_isAlgClosed_countable_subfield
    (hA.union (Finset.countable_toSet (G.biUnion fun g => g.coeffs)))
  refine ⟨k₀, inferInstance, inferInstance, h₁, h₂, subset_union_left.trans h₃,
    le_antisymm (fun f hf => ?_) X.map_descendField_ideal_le⟩
  rw [← hG] at hf
  refine (Submodule.span_le.2 ?_ : Submodule.span _ _ ≤ _) hf
  intro g hg
  have hgc : (g.coeffs : Set k) ⊆ Set.range (algebraMap k₀ k) := fun c hc =>
    h₃ (Or.inr (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨g, hg, hc⟩)))
  obtain ⟨g₀, rfl⟩ := mem_range_map_iff_coeffs_subset.2 hgc
  refine Ideal.mem_map_of_mem _ ?_
  rw [mem_descendField_ideal, ← hG]
  exact Submodule.subset_span hg

/-! ### Envelopes and restriction (`prop:gl-ample-rational`) -/

section Envelope

variable [IsAlgClosed k₀]

/-- The key step of `prop:gl-ample-rational`: for `I = I₀ k[x]`, `k₀` algebraically closed and a
continuous `φ₀ : X₀^an → ℝ`, every `ψ ∈ 𝓗_fin(X, a)` with `ψ ≤ φ₀ ∘ r` satisfies
`ψ ≤ P_a(φ₀) ∘ r`. Writing the forms of `ψ = m⁻¹ max_t (log|s_t| + λ_t)` as
`s_t = ∑_β c_β s_{tβ}` with `s_{tβ} ∈ k₀[x]` and `c_β ∈ k` linearly independent over `k₀`,
`ψ₀ = m⁻¹ max_{t,β} (log|s_{tβ}| + λ_t) ∈ 𝓗(X₀, a)` satisfies `ψ ≤ ψ₀ ∘ r` (ultrametric
inequality), and `ψ₀(v₀) ≤ ψ(v) ≤ φ₀(v₀)` at the lift `v` of a divisorial point `v₀`
(`ProjSubvariety.exists_restrictField_eq_of_isDivisorial`); by divisorial comparison on `X₀`
(`thm:sg-comparison`), `ψ₀ ≤ φ₀`, hence `ψ₀ ≤ P_a(φ₀)`. -/
theorem le_envelope_comp_restrictField_of_isFinFS
    (hI : X.ideal = Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal) {a : ℚ}
    {φ₀ : (X.descendField k₀).an → ℝ} (hφ₀ : Continuous φ₀) {ψ : X.an → EReal}
    (hψ : X.IsFinFS a ψ) (hψφ : ψ ≤ fun v => (φ₀ (X.restrictField k₀ v) : EReal)) (v : X.an) :
    ψ v ≤ (X.descendField k₀).envelope a (fun w => (φ₀ w : EReal)) (X.restrictField k₀ v) := by
  classical
  obtain ⟨D, -, hDfin, hψD⟩ := hψ
  -- the decomposition `s_t = ∑_{β ∈ B} c_β s_{tβ}` of the forms of `D`
  obtain ⟨B, hdec⟩ : ∃ B : Finset (Module.Basis.ofVectorSpaceIndex k₀ k), ∀ t ∈ D.terms,
      ∑ β ∈ B, C ((Module.Basis.ofVectorSpace k₀ k) β) *
        map (algebraMap k₀ k) (coordPoly k₀ β t.1) = t.1 :=
    ⟨_, fun t ht => sum_C_mul_map_coordPoly (Finset.mem_image_of_mem Prod.fst ht)⟩
  -- a coordinate of a form of `D` which is not in `I₀`
  obtain ⟨t₀, ht₀, ht₀I⟩ : ∃ t ∈ D.terms, t.1 ∉ X.ideal := by
    obtain ⟨t, ht, hne⟩ := hDfin X.triv X.triv.2
    exact ⟨t, ht, notMem_ideal_of_val_ne_zero hne⟩
  obtain ⟨β₀, hβ₀, hβ₀I⟩ : ∃ β ∈ B, coordPoly k₀ β t₀.1 ∉ (X.descendField k₀).ideal := by
    by_contra hcon
    push Not at hcon
    exact ht₀I (hdec t₀ ht₀ ▸ Ideal.sum_mem _ fun β hβ => Ideal.mul_mem_left _ _ (hcon β hβ))
  have hB : ∃ t ∈ D.terms, ∃ β ∈ B, coordPoly k₀ β t.1 ≠ 0 :=
    ⟨t₀, ht₀, β₀, hβ₀, fun h0 => hβ₀I (h0 ▸ Ideal.zero_mem _)⟩
  -- the Fubini–Study function `ψ₀` on `X₀`
  have hψ₀ : (X.descendField k₀).IsPSH a fun w => (D.coordData k₀ B hB).eval w.1 :=
    IsFS.isPSH ⟨D.coordData k₀ B hB, ⟨_, ProjBerk.FSData.mem_coordData_terms ht₀ hβ₀, hβ₀I⟩,
      fun _ => rfl⟩
  have hlog : ∀ {x y : ℝ≥0} (c : ℝ), x ≤ y →
      ENNReal.log (x : ℝ≥0∞) + (c : EReal) ≤ ENNReal.log (y : ℝ≥0∞) + (c : EReal) :=
    fun c hxy => add_le_add_left (ENNReal.log_monotone (ENNReal.coe_le_coe.2 hxy)) _
  -- `ψ ≤ ψ₀ ∘ r`
  have hG1 : ψ v ≤ (D.coordData k₀ B hB).eval (ProjBerk.restrictField k₀ v.1) := by
    rw [hψD v, ProjBerk.FSData.eval_def, ProjBerk.FSData.eval_def,
      ProjBerk.FSData.coordData_m]
    refine ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sup_le fun t ht => ?_)
    have hle : (v : ProjBerk k M).1.val t.1 ≤
        B.sup fun β => (ProjBerk.restrictField k₀ v.1).1.val (coordPoly k₀ β t.1) := by
      conv_lhs => rw [← hdec t ht]
      refine Valuation.map_sum_le _ fun β hβ => ?_
      rw [Valuation.map_mul]
      refine le_trans ?_ (Finset.le_sup (f := fun β =>
        (ProjBerk.restrictField k₀ v.1).1.val (coordPoly k₀ β t.1)) hβ)
      calc (v : ProjBerk k M).1.val (C ((Module.Basis.ofVectorSpace k₀ k) β)) *
            (v : ProjBerk k M).1.val (map (algebraMap k₀ k) (coordPoly k₀ β t.1))
          ≤ 1 * (v : ProjBerk k M).1.val (map (algebraMap k₀ k) (coordPoly k₀ β t.1)) := by
            gcongr
            rw [← MvPolynomial.algebraMap_eq]
            exact Berk.abs_algebraMap_le_one _ _
        _ = _ := one_mul _
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · have h0 : (v : ProjBerk k M).1.val t.1 = 0 := by
        rw [hBe, Finset.sup_empty] at hle
        exact le_bot_iff.1 hle
      rw [ProjBerk.termVal_def, (ProjBerk.logAbs_eq_bot_iff _ _).2 h0, EReal.bot_add]
      exact bot_le
    · obtain ⟨β, hβ, hβmax⟩ := Finset.exists_mem_eq_sup _ hBne
        fun β => (ProjBerk.restrictField k₀ v.1).1.val (coordPoly k₀ β t.1)
      rw [hβmax] at hle
      calc ProjBerk.termVal t v.1
          = ENNReal.log ((v : ProjBerk k M).1.val t.1 : ℝ≥0∞) + (t.2 : EReal) := rfl
        _ ≤ ENNReal.log ((ProjBerk.restrictField k₀ v.1).1.val (coordPoly k₀ β t.1) : ℝ≥0∞) +
            (t.2 : EReal) := hlog t.2 hle
        _ = ProjBerk.termVal (coordPoly k₀ β t.1, t.2) (ProjBerk.restrictField k₀ v.1) := rfl
        _ ≤ _ := Finset.le_sup (f := fun s => ProjBerk.termVal s
            (ProjBerk.restrictField k₀ v.1)) (ProjBerk.FSData.mem_coordData_terms ht hβ)
  -- divisorial comparison on `X₀`: `ψ₀ ≤ φ₀`
  have hG3 : (fun w : (X.descendField k₀).an => (D.coordData k₀ B hB).eval w.1) ≤
      fun w => (φ₀ w : EReal) := by
    refine IsPSH.le_of_forall_isDivisorial_le hψ₀
      (continuous_coe_real_ereal.comp hφ₀).upperSemicontinuous (fun _ => EReal.coe_ne_top _)
      fun v₀ hv₀ => ?_
    obtain ⟨w, hwr, hwsum⟩ := exists_restrictField_eq_of_isDivisorial_basis hI hv₀
    have hφw : ((φ₀ (X.restrictField k₀ w) : ℝ) : EReal) = φ₀ v₀ := by rw [hwr]
    refine le_trans ?_ ((hψφ w).trans_eq hφw)
    rw [hψD w, ProjBerk.FSData.eval_def, ProjBerk.FSData.eval_def,
      ProjBerk.FSData.coordData_m]
    refine ProjBerk.ereal_coe_mul_monotone (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sup_le fun s hs => ?_)
    obtain ⟨t, ht, β, hβ, rfl⟩ := ProjBerk.FSData.exists_of_mem_coordData_terms hs
    have hval : (w : ProjBerk k M).1.val t.1 =
        B.sup fun β' => (v₀ : ProjBerk k₀ M).1.val (coordPoly k₀ β' t.1) := by
      conv_lhs => rw [← hdec t ht]
      exact hwsum B _
    have hle : (v₀ : ProjBerk k₀ M).1.val (coordPoly k₀ β t.1) ≤
        (w : ProjBerk k M).1.val t.1 := by
      rw [hval]
      exact Finset.le_sup (f := fun β' => (v₀ : ProjBerk k₀ M).1.val (coordPoly k₀ β' t.1)) hβ
    calc ProjBerk.termVal (coordPoly k₀ β t.1, t.2) v₀.1
        = ENNReal.log ((v₀ : ProjBerk k₀ M).1.val (coordPoly k₀ β t.1) : ℝ≥0∞) +
            (t.2 : EReal) := rfl
      _ ≤ ENNReal.log ((w : ProjBerk k M).1.val t.1 : ℝ≥0∞) + (t.2 : EReal) := hlog t.2 hle
      _ = ProjBerk.termVal t w.1 := rfl
      _ ≤ _ := Finset.le_sup (f := fun s => ProjBerk.termVal s w.1) ht
  exact hG1.trans (FSSystem.le_envelope (F := (X.descendField k₀).fsSystem) hψ₀ hG3
    (X.restrictField k₀ v))

/-- **Envelopes commute with restriction** (`prop:gl-ample-rational`, proof): if `I = I₀ k[x]`
with `k₀` algebraically closed, `a ∈ ℚ_{>0}` and `φ₀ : X₀^an → ℝ` is continuous, then
`P_a(φ₀ ∘ r) = P_a(φ₀) ∘ r` on `X^an`. The inequality `≥` holds because `PSH(X₀, a) ∘ r ⊆ PSH(X, a)`
(`lem:gl-pullback`); for `≤`, `P_a(φ₀ ∘ r)` is the supremum of the `ψ ∈ 𝓗_fin(X, a)` below
`φ₀ ∘ r` (`lem:sg-fs-envelope`), and each of them is `≤ P_a(φ₀) ∘ r`
(`ProjSubvariety.le_envelope_comp_restrictField_of_isFinFS`). No envelope property is used. -/
theorem envelope_comp_restrictField
    (hI : X.ideal = Ideal.map (map (algebraMap k₀ k)) (X.descendField k₀).ideal) {a : ℚ}
    (ha : 0 < a) {φ₀ : (X.descendField k₀).an → ℝ} (hφ₀ : Continuous φ₀) :
    X.envelope a (fun v => (φ₀ (X.restrictField k₀ v) : EReal)) =
      fun v => (X.descendField k₀).envelope a (fun w => (φ₀ w : EReal)) (X.restrictField k₀ v) := by
  funext v
  refine le_antisymm ?_ ?_
  · have hlsc : LowerSemicontinuous fun v => (φ₀ (X.restrictField k₀ v) : EReal) :=
      (continuous_coe_real_ereal.comp (hφ₀.comp X.continuous_restrictField)).lowerSemicontinuous
    rw [envelope_eq_iSup_isFinFS ha hlsc (fun _ => EReal.coe_ne_bot _)]
    exact iSup₂_le fun ψ hψ => le_envelope_comp_restrictField_of_isFinFS hI hφ₀ hψ.1 hψ.2 v
  · exact iSup₂_le fun τ hτ =>
      FSSystem.le_envelope (F := X.fsSystem) (IsPSH.comp_restrictField hτ.1) (fun w => hτ.2 _) v

end Envelope

/-! ### The envelope property over arbitrary fields (`prop:gl-ample-rational`) -/

/-- **`prop:gl-ample-rational`** (FHX `thm:normal-ample-EP`, Step 2): let `k` be algebraically
closed and `X = V(I) ⊆ ℙᴹ_k` projectively normal. If `EP_{X₀}(1)` holds for every projectively
normal `X₀ ⊆ ℙᴹ_{k₀}` over every countable algebraically closed subfield `k₀ ⊆ k` (the conclusion
of `prop:gl-ample-countable`), then `EP_X(1)`.

By the envelope criterion (`prop:sg-envelope-criterion`) it suffices that `P_1(φ)` is psh for
`φ ∈ PL(X)`. Choose `k₀` containing the coefficients of the forms defining `φ` and with
`I₀ k[x] = I` (`ProjSubvariety.exists_descendField`); then `X₀` is projectively normal
(`ProjSubvariety.IsProjNormal.descendField`) and `φ = φ₀ ∘ r` for a continuous `φ₀` on `X₀^an`,
so
`P_1(φ) = P_1(φ₀) ∘ r` (`ProjSubvariety.envelope_comp_restrictField`), which is psh since
`P_1(φ₀) ∈ PSH(X₀, 1)` by `EP_{X₀}(1)`. -/
theorem hasEnvelopeProperty_one_of_countable [IsAlgClosed k] (hX : X.IsProjNormal)
    (h : ∀ (k₀ : Type u) [Field k₀] [Algebra k₀ k] [IsAlgClosed k₀] [Countable k₀]
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1) :
    X.HasEnvelopeProperty 1 := by
  classical
  refine hasEnvelopeProperty_of_forall_isPL (separatesPoints_isPL X) fun φ hφ => ?_
  obtain ⟨a₁, a₂, φ₁, φ₂, hφ₁, hφ₂, hφeq⟩ := isPL_iff.1 hφ
  obtain ⟨D₁, -, -, hD₁⟩ := id hφ₁
  obtain ⟨D₂, -, -, hD₂⟩ := id hφ₂
  -- the countable field `k₀`
  obtain ⟨k₀, _, _, hk₀, hk₀c, hA, hI⟩ := X.exists_descendField (Finset.countable_toSet
    ((D₁.terms.biUnion fun t => t.1.coeffs) ∪ D₂.terms.biUnion fun t => t.1.coeffs))
  have hD₁c : ∀ t ∈ D₁.terms, t.1 ∈ Set.range (map (algebraMap k₀ k) :
      MvPolynomial (Fin (M + 1)) k₀ → MvPolynomial (Fin (M + 1)) k) := fun t ht =>
    mem_range_map_iff_coeffs_subset.2 fun c hc => hA (Finset.mem_coe.2
      (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨t, ht, hc⟩)))
  have hD₂c : ∀ t ∈ D₂.terms, t.1 ∈ Set.range (map (algebraMap k₀ k) :
      MvPolynomial (Fin (M + 1)) k₀ → MvPolynomial (Fin (M + 1)) k) := fun t ht =>
    mem_range_map_iff_coeffs_subset.2 fun c hc => hA (Finset.mem_coe.2
      (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨t, ht, hc⟩)))
  have hEP := h k₀ (X.descendField k₀) (hX.descendField hI)
  -- the descended obstacle `φ₀`
  obtain ⟨C₁, hC₁⟩ := FSSystem.exists_abs_le_of_continuous hφ₁.continuous
  obtain ⟨C₂, hC₂⟩ := FSSystem.exists_abs_le_of_continuous hφ₂.continuous
  have hcont : ∀ {b : ℚ} (E : ProjBerk.FSData k₀ M b) (C : ℝ),
      Continuous fun w : (X.descendField k₀).an =>
        (max (E.eval w.1) ((-C : ℝ) : EReal)).toReal := by
    intro b E C
    refine EReal.continuousOn_toReal.comp_continuous
      ((E.continuous_eval.comp continuous_subtype_val).max continuous_const) fun w => ?_
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _),
      (max_lt (lt_top_iff_ne_top.2 (E.eval_ne_top _)) (EReal.coe_lt_top _)).ne⟩
  have hdesc : ∀ {b : ℚ} (D : ProjBerk.FSData k M b) (hD : ∀ t ∈ D.terms, t.1 ∈ Set.range
      (map (algebraMap k₀ k) : MvPolynomial (Fin (M + 1)) k₀ → MvPolynomial (Fin (M + 1)) k))
      (ψ : X.an → ℝ) (C : ℝ), (∀ v, (ψ v : EReal) = D.eval v.1) → (∀ v, |ψ v| ≤ C) →
        ∀ v, (max ((D.descendField hD).eval (X.restrictField k₀ v).1)
          ((-C : ℝ) : EReal)).toReal = ψ v := by
    intro b D hD ψ C hψ hC v
    change (max ((D.descendField hD).eval (ProjBerk.restrictField k₀ v.1)) _).toReal = _
    rw [ProjBerk.FSData.eval_descendField, ← hψ v,
      max_eq_left (EReal.coe_le_coe_iff.2 (neg_le_of_abs_le (hC v))), EReal.toReal_coe]
  set φ₀ : (X.descendField k₀).an → ℝ := fun w =>
    (max ((D₁.descendField hD₁c).eval w.1) ((-C₁ : ℝ) : EReal)).toReal -
      (max ((D₂.descendField hD₂c).eval w.1) ((-C₂ : ℝ) : EReal)).toReal
  have hφ₀ : Continuous φ₀ := (hcont _ C₁).sub (hcont _ C₂)
  have hφ' : (fun v => (φ v : EReal)) = fun v => (φ₀ (X.restrictField k₀ v) : EReal) :=
    funext fun v => by
      rw [hφeq v]
      simp only [φ₀]
      rw [hdesc D₁ hD₁c φ₁ C₁ hD₁ hC₁, hdesc D₂ hD₂c φ₂ C₂ hD₂ hC₂]
  have key := X.envelope_comp_restrictField hI (a := 1) one_pos hφ₀
  rw [Rat.cast_one] at key
  rw [hφ', key]
  exact IsPSH.comp_restrictField
    (FSSystem.HasEnvelopeProperty.isPSH_envelope_of_continuous hEP (fun _ => zero_le_one) hφ₀)

/-- **`prop:gl-ample-rational`** with the hypothesis in the shape of decision D-H5: if `EP_{X₀}(1)`
holds for every projectively normal `X₀ ⊆ ℙᴹ_{k₀}` over every countable algebraically closed field
`k₀`, then `EP_X(1)` holds for every projectively normal `X ⊆ ℙᴹ_k` over an algebraically closed
`k`. -/
theorem hasEnvelopeProperty_one_of_forall_countable [IsAlgClosed k] (hX : X.IsProjNormal)
    (h : ∀ (k₀ : Type u) [Field k₀] [IsAlgClosed k₀] [Countable k₀]
      (X₀ : ProjSubvariety k₀ M), X₀.IsProjNormal → X₀.HasEnvelopeProperty 1) :
    X.HasEnvelopeProperty 1 :=
  X.hasEnvelopeProperty_one_of_countable hX fun k₀ _ _ _ _ X₀ hX₀ => h k₀ X₀ hX₀

end ProjSubvariety

end EnvelopeProperty
