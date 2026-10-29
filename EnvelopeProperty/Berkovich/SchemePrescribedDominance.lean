import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints
import EnvelopeProperty.Berkovich.GaussValuation
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Original prescribed native points derive actual scheme dominance -/
open scoped NNReal Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace Classical
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

/-- A genuine original prescribed point over a zero-support base valuation
forces actual whole scheme dominance, without a supplied generic comparison. -/
theorem isDominant_of_prescribedPoint
    {R : Type u} [CommRing R] [IsDomain R] {X : Scheme.{u}}
    (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) (f : X ⟶ Spec (CommRingCat.of R))
    (y : RelativeSchemeValuedPoint v f) : IsDominant f := by
  have hb : (SchemeValuedPoint.basePoint v).point = genericPoint (Spec (CommRingCat.of R)) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change v.supp = ⊥
    exact hv
  have hp : f y.1.point = genericPoint (Spec (CommRingCat.of R)) := by
    have h := congrArg SchemeValuedPoint.point y.2
    exact h.trans hb
  rw [isDominant_iff]
  change Dense (Set.range f)
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec (Spec (CommRingCat.of R))).def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨y.1.point,hp⟩)

/-- The original positive-radius trivial Gauss point derives actual dominance
of the SAME original polynomial-base structure map. -/
theorem isDominant_of_gaussPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (r : ℝ≥0) (hr : 0 < r)
    (f : X ⟶ Spec (CommRingCat.of (Polynomial k)))
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f) : IsDominant f := by
  apply isDominant_of_prescribedPoint _ _ f y
  apply le_antisymm _ bot_le
  intro F hF
  change gaussValuation (1 : Valuation k ℝ≥0) r F = 0 at hF
  change F = 0
  by_contra hne
  have hex : ∃ i, F.coeff i ≠ 0 := by
    by_contra h
    have hh : ∀ i, F.coeff i = 0 := by simpa only [not_exists,not_not] using h
    apply hne
    ext i
    simpa only [Polynomial.coeff_zero] using hh i
  obtain ⟨i,hi⟩ := hex
  have hpos : 0 < (1 : Valuation k ℝ≥0) (F.coeff i) * r ^ i := by
    rw [Valuation.one_apply_of_ne_zero hi,one_mul]
    exact pow_pos hr _
  exact (ne_of_gt (hpos.trans_le (le_gaussFun (1 : Valuation k ℝ≥0) r F i))) hF

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
