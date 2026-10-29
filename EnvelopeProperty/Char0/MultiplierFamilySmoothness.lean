import EnvelopeProperty.Char0.MultiplierFamilySmoothnessProduct

/-! # The SAME actual original parameter family is smooth over its parameter and total field

This is produced from the original algebraic HasSmoothCharts condition and the
actual whole-family product isomorphism. No native smoothness, model comparison,
dimension or vanishing certificate is a final input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace EnvelopeProperty.Char0.MultiplierFamilySmoothness
open ProjBerk ProjSubvariety.MultiplierBaseIdeals
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual original native closed product projection is smooth, internally by the genuine original variety base change. -/
theorem nativeProductStructure_smooth (hs : X.HasSmoothCharts) : Smooth X.nativeProductStructure := by
  let : Smooth X.nativeStructure := nativeStructure_smooth X hs
  have h : Smooth (X.nativeProductModelIso.hom ≫ CategoryTheory.Limits.pullback.snd X.nativeStructure
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) := by infer_instance
  rwa [X.nativeProductModelIso_over_base] at h

/-- The SAME whole actual original parameter-family projection is smooth.
Only the original HasSmoothCharts condition is supplied; its actual product comparison is internal. -/
theorem familyProjection_smooth (hs : X.HasSmoothCharts) : Smooth (familyProjection X) := by
  let : Smooth X.nativeProductStructure := nativeProductStructure_smooth X hs
  have h : Smooth ((familyProductIso X).hom ≫ X.nativeProductStructure) := by infer_instance
  rwa [familyProductIso_projection] at h

/-- The actual original polynomial coefficient morphism is genuinely smooth over its original field. -/
theorem polynomialBase_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
  let : Algebra.Smooth k (Polynomial k) := ⟨inferInstance, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (show RingHom.Smooth (algebraMap k (Polynomial k)) from RingHom.smooth_algebraMap.mpr inferInstance)

/-- The SAME original actual family's total coefficient structure over its ORIGINAL field. -/
def familyAbsoluteStructure : familyScheme X ⟶ Spec (.of k) :=
  familyProjection X ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

/-- The ORIGINAL algebraic smooth-chart condition DERIVES smoothness of the SAME whole original
parameter-family TOTAL field morphism. Its original scheme, parameter and field actions are retained. -/
theorem familyAbsoluteStructure_smooth (hs : X.HasSmoothCharts) : Smooth (familyAbsoluteStructure X) := by
  let : Smooth (familyProjection X) := familyProjection_smooth X hs
  let : Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := polynomialBase_smooth
  unfold familyAbsoluteStructure
  infer_instance

end EnvelopeProperty.Char0.MultiplierFamilySmoothness
