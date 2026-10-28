/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.ReesChartTree
import Hironaka.Scheme.BlowUp.AffineAlgebra

/-!
# Actual affine blowup charts as subalgebras of the fraction field

The affine blowup algebra used by the algebraic principalization theorem is identified with
the ratio algebra of `ReesChartTree`. This is the first adapter in `hironaka-charts.tex`.
The finite-tree and relative-Jacobian producers are separate obligations.
-/

noncomputable section

namespace EnvelopeProperty.Char0

universe u

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- The actual away-localization of a chart algebra maps into its ambient field. -/
def reesChartLocalizationMap (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) : Localization.Away (g i) →+* K :=
  IsLocalization.Away.lift (g i) (g := C.val.toRingHom)
    (isUnit_iff_ne_zero.mpr (fun h => hi (Subtype.ext h)))

@[simp]
theorem reesChartLocalizationMap_algebraMap (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) (c : C) :
    reesChartLocalizationMap C g i hi (algebraMap C (Localization.Away (g i)) c) = (c : K) := by
  simp [reesChartLocalizationMap]

/-- The inverse denominator is evaluated as the actual field fraction. -/
theorem reesChartLocalizationMap_invSelf (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) :
    reesChartLocalizationMap C g i hi (IsLocalization.Away.invSelf (g i)) = 1 / (g i : K) := by
  have hiK : (g i : K) ≠ 0 := fun h => hi (Subtype.ext h)
  apply (eq_div_iff hiK).mpr
  have h := congrArg (reesChartLocalizationMap C g i hi)
    (IsLocalization.Away.mul_invSelf (g i) (S := Localization.Away (g i)))
  simpa only [map_mul, map_one, reesChartLocalizationMap_algebraMap, mul_comm] using h

/-- The fraction used by the scheme-theoretic chart maps to the same fraction in the field. -/
theorem reesChartLocalizationMap_ratio (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) (c : C) :
    reesChartLocalizationMap C g i hi
      (algebraMap C (Localization.Away (g i)) c * IsLocalization.Away.invSelf (g i)) =
        (c : K) / (g i : K) := by
  rw [map_mul, reesChartLocalizationMap_algebraMap, reesChartLocalizationMap_invSelf]
  simp [div_eq_mul_inv]

/-- Localization introduces no kernel when the original chart algebra embeds in a field. -/
theorem reesChartLocalizationMap_injective (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) : Function.Injective (reesChartLocalizationMap C g i hi) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (g i))
    (reesChartLocalizationMap C g i hi)).mpr
  intro x y
  constructor
  · exact congrArg _
  · intro h
    simp only [reesChartLocalizationMap_algebraMap] at h
    exact congrArg (algebraMap C (Localization.Away (g i))) (Subtype.ext h)

/-- Every centre-ideal fraction is already in the finite-generator ratio algebra. -/
theorem div_mem_reesTreeChart_of_mem_span (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) {c : C} (hc : c ∈ Ideal.span (Set.range g)) :
    (c : K) / (g i : K) ∈ reesTreeChart C g i := by
  have hm : reesTreeChartIncl C g i c ∈ Ideal.span {reesTreeChartIncl C g i (g i)} := by
    rw [← reesTreeChart_map_span_eq C g i hi]
    exact Ideal.mem_map_of_mem _ hc
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hm
  have hiK : (g i : K) ≠ 0 := fun h => hi (Subtype.ext h)
  have heq : (c : K) / (g i : K) = (q : K) := by
    apply (div_eq_iff hiK).mpr
    have hqK := congrArg Subtype.val hq
    change (c : K) = (g i : K) * (q : K) at hqK
    simpa only [mul_comm] using hqK
  rw [heq]
  exact q.property

/-- The map from the actual affine blowup algebra lands in the finite Rees chart algebra. -/
theorem reesChartLocalizationMap_mem (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) {z : Localization.Away (g i)}
    (hz : z ∈ AlgebraicGeometry.affineBlowUpAlgebra (Ideal.span (Set.range g)) (g i)) :
    reesChartLocalizationMap C g i hi z ∈ reesTreeChart C g i := by
  induction hz using AlgebraicGeometry.affineBlowUpAlgebra.induction_on with
  | mem c hc =>
    rw [reesChartLocalizationMap_ratio]
    exact div_mem_reesTreeChart_of_mem_span C g i hi hc
  | algebraMap c =>
    rw [reesChartLocalizationMap_algebraMap]
    exact le_reesTreeChart C g i c.property
  | add y z _ _ hy hz =>
    rw [map_add]
    exact (reesTreeChart C g i).add_mem hy hz
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact (reesTreeChart C g i).mul_mem hy hz

/-- The canonical ring map from the scheme-theoretic affine chart to the finite ratio chart. -/
def affineBlowUpToReesChart (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) :
    AlgebraicGeometry.affineBlowUpAlgebra (Ideal.span (Set.range g)) (g i) →+*
      reesTreeChart C g i :=
  ((reesChartLocalizationMap C g i hi).comp
    (AlgebraicGeometry.affineBlowUpAlgebra (Ideal.span (Set.range g)) (g i)).val.toRingHom).codRestrict
    (reesTreeChart C g i).toSubring (fun z => reesChartLocalizationMap_mem C g i hi z.property)

/-- The actual chart-to-chart map is injective. -/
theorem affineBlowUpToReesChart_injective (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) : Function.Injective (affineBlowUpToReesChart C g i hi) := by
  intro x y h
  apply Subtype.ext
  exact reesChartLocalizationMap_injective C g i hi (congrArg Subtype.val h)

/-- Every element of the finite ratio chart comes from the actual affine blowup chart. -/
theorem affineBlowUpToReesChart_surjective (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) : Function.Surjective (affineBlowUpToReesChart C g i hi) := by
  let I := Ideal.span (Set.range g)
  let F : AlgebraicGeometry.affineBlowUpAlgebra I (g i) →+* K :=
    (reesChartLocalizationMap C g i hi).comp
      (AlgebraicGeometry.affineBlowUpAlgebra I (g i)).val.toRingHom
  let D : Subalgebra B K :=
    { F.range with
      algebraMap_mem' := fun b => by
        refine ⟨algebraMap C (AlgebraicGeometry.affineBlowUpAlgebra I (g i)) (algebraMap B C b), ?_⟩
        change reesChartLocalizationMap C g i hi
          (algebraMap C (Localization.Away (g i)) (algebraMap B C b)) = algebraMap B K b
        rw [reesChartLocalizationMap_algebraMap]
        rfl }
  have hCD : C ≤ D := by
    intro c hc
    refine ⟨algebraMap C (AlgebraicGeometry.affineBlowUpAlgebra I (g i)) ⟨c, hc⟩, ?_⟩
    change reesChartLocalizationMap C g i hi
      (algebraMap C (Localization.Away (g i)) ⟨c, hc⟩) = c
    exact reesChartLocalizationMap_algebraMap C g i hi ⟨c, hc⟩
  have hratio : ∀ j, (g j : K) / (g i : K) ∈ D := by
    intro j
    refine ⟨AlgebraicGeometry.affineBlowUpAlgebra.frac (I := I) (a := g i)
      (Ideal.subset_span ⟨j, rfl⟩), ?_⟩
    change reesChartLocalizationMap C g i hi
      (algebraMap C (Localization.Away (g i)) (g j) * IsLocalization.Away.invSelf (g i)) = _
    exact reesChartLocalizationMap_ratio C g i hi (g j)
  have hle : reesTreeChart C g i ≤ D := (reesTreeChart_le_iff C D g i).mpr ⟨hCD, hratio⟩
  intro z
  obtain ⟨w, hw⟩ := hle z.property
  exact ⟨w, Subtype.ext hw⟩

/-- The scheme-theoretic affine blowup chart is exactly the Rees chart inside the field. -/
def affineBlowUpReesChartEquiv (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) :
    AlgebraicGeometry.affineBlowUpAlgebra (Ideal.span (Set.range g)) (g i) ≃+*
      reesTreeChart C g i :=
  RingEquiv.ofBijective (affineBlowUpToReesChart C g i hi)
    ⟨affineBlowUpToReesChart_injective C g i hi,
      affineBlowUpToReesChart_surjective C g i hi⟩

/-- The chart equivalence identifies the actual structure maps from the original algebra. -/
theorem affineBlowUpReesChartEquiv_algebraMap (C : Subalgebra B K) {n : ℕ} (g : Fin n → C)
    (i : Fin n) (hi : g i ≠ 0) (c : C) :
    affineBlowUpReesChartEquiv C g i hi
      (algebraMap C (AlgebraicGeometry.affineBlowUpAlgebra (Ideal.span (Set.range g)) (g i)) c) =
        reesTreeChartIncl C g i c := by
  apply Subtype.ext
  exact reesChartLocalizationMap_algebraMap C g i hi c

end EnvelopeProperty.Char0
