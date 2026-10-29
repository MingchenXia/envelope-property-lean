/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.PolynomialGrowth

/-!
# Lebesgue measure on `EuclideanSpace ℂ ι` and on `ι → ℂ`

The files `EnvelopeProperty.Char0.CauchyN`, `…PolynomialGrowth`, `…Weights` and `…BergmanFinite`
work on `Fin N → ℂ` with the product Lebesgue measure, while
`ComplexGeometry.Pluripotential.ComplexModel N` is `EuclideanSpace ℂ (Fin N)` with the Lebesgue
measure of a real inner product space. This file proves that the identification `WithLp.ofLp : EuclideanSpace ℂ ι → (ι → ℂ)` (`EuclideanSpace.equiv ι ℂ`) is
measure preserving.

The proof compares Haar measures: `(e_j, i e_j)` is a real orthonormal basis of
`EuclideanSpace ℂ ι` (`complexEuclideanRealBasis`), whose parallelepiped corresponds to the
product of unit squares in `ι → ℂ`, of product measure `1`.

## Main results

* `EnvelopeProperty.Char0.complexEuclideanRealBasis`;
* `EnvelopeProperty.Char0.measurePreserving_euclideanSpace_ofLp`,
  `EnvelopeProperty.Char0.measurePreserving_euclideanSpace_toLp`;
* `EnvelopeProperty.Char0.exists_mvPolynomial_of_lintegral_polyWeight_euclidean`:
  `lem:c0-polynomial-growth` on `EuclideanSpace ℂ (Fin (n + 2))`.
-/

open scoped Real NNReal ENNReal Topology
open Complex MeasureTheory Set

noncomputable section

namespace EnvelopeProperty.Char0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vectors `e_j` and `i e_j` of `EuclideanSpace ℂ ι`. -/
def complexEuclideanRealVec (k : ι × Fin 2) : EuclideanSpace ℂ ι :=
  EuclideanSpace.single k.1 (if k.2 = 0 then 1 else I)

theorem ofLp_sum_smul_complexEuclideanRealVec (t : ι × Fin 2 → ℝ) (j : ι) :
    (∑ k, t k • complexEuclideanRealVec k).ofLp j = t (j, 0) + t (j, 1) * I := by
  rw [WithLp.ofLp_sum, Finset.sum_apply, Fintype.sum_prod_type]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, complexEuclideanRealVec, PiLp.single_apply,
    Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
  simp [Finset.sum_add_distrib, Complex.real_smul]

/-- The real coordinates `(Re z_j, Im z_j)`. -/
def complexEuclideanRealCoord (z : ι → ℂ) (k : ι × Fin 2) : ℝ :=
  if k.2 = 0 then (z k.1).re else (z k.1).im

theorem sum_complexEuclideanRealCoord_smul (z : ι → ℂ) :
    ∑ k, complexEuclideanRealCoord z k • complexEuclideanRealVec k = WithLp.toLp 2 z := by
  refine PiLp.ext fun j => ?_
  rw [ofLp_sum_smul_complexEuclideanRealVec]
  simp [complexEuclideanRealCoord, Complex.re_add_im]

theorem orthonormal_complexEuclideanRealVec :
    Orthonormal ℝ (complexEuclideanRealVec (ι := ι)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, a⟩ ⟨j, b⟩
  rw [PiLp.inner_apply]
  simp only [complexEuclideanRealVec, PiLp.single_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    fin_cases a <;> fin_cases b <;> simp [Complex.inner]
  · rw [Finset.sum_eq_zero fun k _ => ?_]
    · simp [hij]
    · by_cases hk : k = i
      · subst hk; simp [hij]
      · simp [hk]

/-- The real orthonormal basis `(e_j, i e_j)` of `EuclideanSpace ℂ ι`. -/
def complexEuclideanRealBasis : OrthonormalBasis (ι × Fin 2) ℝ (EuclideanSpace ℂ ι) :=
  OrthonormalBasis.mk orthonormal_complexEuclideanRealVec (by
    intro z _
    rw [← WithLp.toLp_ofLp 2 z, ← sum_complexEuclideanRealCoord_smul]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self k)))

theorem coe_complexEuclideanRealBasis :
    ⇑(complexEuclideanRealBasis (ι := ι)) = complexEuclideanRealVec :=
  OrthonormalBasis.coe_mk _ _

/-- The parallelepiped of `(e_j, i e_j)` corresponds to the product of unit squares. -/
theorem toLp_preimage_parallelepiped :
    WithLp.toLp 2 ⁻¹' parallelepiped (complexEuclideanRealVec (ι := ι)) =
      Set.univ.pi fun _ => {w : ℂ | w.re ∈ Icc (0 : ℝ) 1 ∧ w.im ∈ Icc (0 : ℝ) 1} := by
  ext z
  simp only [Set.mem_preimage, mem_parallelepiped_iff, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, hz⟩ j
    have h := congrArg (fun x : EuclideanSpace ℂ ι => x.ofLp j) hz
    simp only at h
    rw [ofLp_sum_smul_complexEuclideanRealVec] at h
    rw [h]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    exact ⟨⟨(ht.1 (j, 0)), ht.2 (j, 0)⟩, ⟨ht.1 (j, 1), ht.2 (j, 1)⟩⟩
  · intro hz
    refine ⟨complexEuclideanRealCoord z, ⟨fun k => ?_, fun k => ?_⟩,
      (sum_complexEuclideanRealCoord_smul z).symm⟩
    · rcases k with ⟨j, a⟩
      fin_cases a
      · exact (hz j).1.1
      · exact (hz j).2.1
    · rcases k with ⟨j, a⟩
      fin_cases a
      · exact (hz j).1.2
      · exact (hz j).2.2

theorem volume_unitSquare :
    volume {w : ℂ | w.re ∈ Icc (0 : ℝ) 1 ∧ w.im ∈ Icc (0 : ℝ) 1} = 1 := by
  have h : {w : ℂ | w.re ∈ Icc (0 : ℝ) 1 ∧ w.im ∈ Icc (0 : ℝ) 1} =
      measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    ext w
    simp [measurableEquivRealProd]
    tauto
  rw [h, volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc]
  simp

omit [DecidableEq ι] in
/-- **The bridge**: `WithLp.toLp : (ι → ℂ) → EuclideanSpace ℂ ι` is measure preserving. -/
theorem measurePreserving_euclideanSpace_toLp :
    MeasurePreserving (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) volume volume := by
  classical
  set e := (EuclideanSpace.equiv ι ℂ).symm
  have he : ⇑e = WithLp.toLp 2 := rfl
  refine ⟨e.continuous.measurable, ?_⟩
  rw [← he]
  have : (Measure.map e (volume : Measure (ι → ℂ))).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map _
  rw [← (complexEuclideanRealBasis (ι := ι)).addHaar_eq_volume, eq_comm,
    Module.Basis.addHaar_eq_iff]
  rw [Measure.map_apply e.continuous.measurable
    (complexEuclideanRealBasis.toBasis.parallelepiped.isCompact.isClosed.measurableSet)]
  rw [Module.Basis.coe_parallelepiped, OrthonormalBasis.coe_toBasis,
    coe_complexEuclideanRealBasis, he, toLp_preimage_parallelepiped, volume_pi_pi]
  exact Finset.prod_eq_one fun _ _ => volume_unitSquare

omit [DecidableEq ι] in
/-- **The bridge**: `WithLp.ofLp : EuclideanSpace ℂ ι → (ι → ℂ)` (i.e. `EuclideanSpace.equiv ι ℂ`)
is measure preserving. -/
theorem measurePreserving_euclideanSpace_ofLp :
    MeasurePreserving (WithLp.ofLp : EuclideanSpace ℂ ι → ι → ℂ) volume volume := by
  have h := measurePreserving_euclideanSpace_toLp (ι := ι)
  let E : (ι → ℂ) ≃ᵐ EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm.toHomeomorph.toMeasurableEquiv
  exact (show MeasurePreserving E volume volume from h).symm


/-- **`lem:c0-polynomial-growth` on `EuclideanSpace ℂ (Fin (n + 2))`** (that is, on
`ComplexModel (n + 2)`), deduced from `exists_mvPolynomial_of_lintegral_polyWeight` by the bridge
`measurePreserving_euclideanSpace_toLp`. -/
theorem exists_mvPolynomial_of_lintegral_polyWeight_euclidean {n : ℕ}
    {F : EuclideanSpace ℂ (Fin (n + 2)) → ℂ} (hF : Differentiable ℂ F) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hI : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z.ofLp) < ∞) :
    ∃ P : MvPolynomial (Fin (n + 2)) ℂ, (∀ z, F z = MvPolynomial.eval z.ofLp P) ∧
      ∀ m ∈ P.support, ((∑ i : Fin (n + 1), m i.succ : ℕ) : ℝ) ≤ a - (n + 1) ∧
        (m 0 : ℝ) ≤ b - 1 := by
  set G : (Fin (n + 2) → ℂ) → ℂ := fun w => F (WithLp.toLp 2 w)
  have hG : Differentiable ℂ G :=
    hF.comp (EuclideanSpace.equiv (Fin (n + 2)) ℂ).symm.differentiable
  let E : (Fin (n + 2) → ℂ) ≃ᵐ EuclideanSpace ℂ (Fin (n + 2)) :=
    (EuclideanSpace.equiv (Fin (n + 2)) ℂ).symm.toHomeomorph.toMeasurableEquiv
  have hE : MeasurePreserving E volume volume := measurePreserving_euclideanSpace_toLp
  have hIG : ∫⁻ w, ENNReal.ofReal (‖G w‖ ^ 2 * polyWeight a b w) < ∞ := by
    have := hE.lintegral_comp_emb E.measurableEmbedding
      (fun z => ENNReal.ofReal (‖F z‖ ^ 2 * polyWeight a b z.ofLp))
    rw [← this] at hI
    exact hI
  obtain ⟨P, hP, hdeg⟩ := exists_mvPolynomial_of_lintegral_polyWeight hG ha hb hIG
  exact ⟨P, fun z => hP z.ofLp, hdeg⟩

end EnvelopeProperty.Char0
