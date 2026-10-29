import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyNormal
import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyAnalytic

/-! # Actual whole scheme charts of the SAME original admissible algebra -/
open scoped Classical
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open EnvelopeProperty.ProjBerk
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
private local instance qgr : GradedRing (GradedQuotient.grading (ProjectiveGrading k n) X.ideal) :=
  GradedQuotient.gradedRing _ X.ideal X.homogeneousIdeal.isHomogeneous

private def coefficientZero : k →+* GradedQuotient.grading (ProjectiveGrading k n) X.ideal 0 where
  toFun c := GradedQuotient.componentMap _ _ 0 ⟨C c, isHomogeneous_C _ c⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
/-- The actual original coefficient-field algebra structure on the SAME
native homogeneous quotient-away ring, through its true degree-zero map. -/
@[instance_reducible]
def nativeQuotientAwayAlgebra (F : MvPolynomial (Fin (n+1)) k) :
    Algebra k (X.nativeQuotientAway F) :=
  ((fromZeroRingHom _ _).comp (coefficientZero X)).toAlgebra
attribute [local instance] nativeQuotientAwayAlgebra

/-- The SAME original native variety's genuine open where the original form
F does not vanish, using the literal original projective closed inclusion. -/
def nativeAdmissibleOpen (F : MvPolynomial (Fin (n+1)) k) : X.NativeScheme.Opens :=
  X.nativeInclusion ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) F

/-- The ORIGINAL arbitrary admissible quotient chart algebra maps to the
SAME original native variety through its TRUE homogeneous quotient chart. -/
def nativeAdmissibleChartMap {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    Spec (.of (QuotChartAlg X.ideal F d)) ⟶ X.NativeScheme :=
  (Scheme.Spec.mapIso (X.quotChartNativeAwayEquiv hF hFI).toRingEquiv.toCommRingCatIso.op).inv ≫
    Proj.awayι (GradedQuotient.grading (ProjectiveGrading k n) X.ideal)
      (Ideal.Quotient.mk X.ideal F)
      ((GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).map_mem hF) hd ≫
        X.quotientNativeIso.hom

/-- Actual original fraction charts and whole scheme isomorphisms derive
that the SAME literal arbitrary admissible chart map is an open immersion. -/
theorem nativeAdmissibleChartMap_isOpenImmersion
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    IsOpenImmersion (X.nativeAdmissibleChartMap hF hFI hd) := by
  dsimp only [nativeAdmissibleChartMap]
  infer_instance
attribute [local instance] nativeAdmissibleChartMap_isOpenImmersion

/-- The WHOLE actual open range is exactly the original form-nonvanishing
open on the SAME original native variety. -/
theorem nativeAdmissibleChartMap_opensRange
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    (X.nativeAdmissibleChartMap hF hFI hd).opensRange = X.nativeAdmissibleOpen F := by
  have hpre : X.quotientNativeIso.hom ⁻¹ᵁ X.nativeAdmissibleOpen F =
      Proj.basicOpen (GradedQuotient.grading (ProjectiveGrading k n) X.ideal)
        (Ideal.Quotient.mk X.ideal F) := by
    dsimp only [nativeAdmissibleOpen]
    rw [← Scheme.Hom.comp_preimage, X.quotientNativeIso_inclusion]
    change Proj.map (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal) _ ⁻¹ᵁ _ = _
    rw [Proj.map_preimage_basicOpen]
    rfl
  dsimp only [nativeAdmissibleChartMap]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp,
    Proj.opensRange_awayι, ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_of_isIso, top_inf_eq]

/-- The ENTIRE original arbitrary admissible quotient algebra is the actual
affine scheme of the SAME native original form-nonvanishing open. -/
def nativeAdmissibleChartIso {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    Spec (.of (QuotChartAlg X.ideal F d)) ≅ (X.nativeAdmissibleOpen F).toScheme :=
  IsOpenImmersion.isoOfRangeEq (X.nativeAdmissibleChartMap hF hFI hd)
    (X.nativeAdmissibleOpen F).ι (by
      rw [← Scheme.Hom.coe_opensRange, X.nativeAdmissibleChartMap_opensRange]
      exact Subtype.range_coe.symm)

/-- The whole original affine-chart isomorphism retains the LITERAL same
original native variety inclusion. -/
theorem nativeAdmissibleChartIso_hom_ι {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    (X.nativeAdmissibleChartIso hF hFI hd).hom ≫ (X.nativeAdmissibleOpen F).ι =
      X.nativeAdmissibleChartMap hF hFI hd :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
/-- The SAME actual original admissible open is genuinely affine, derived
from the actual whole original quotient-chart isomorphism. -/
theorem nativeAdmissibleOpen_isAffine {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    IsAffineOpen (X.nativeAdmissibleOpen F) := by
  rw [← X.nativeAdmissibleChartMap_opensRange hF hFI hd]
  exact isAffineOpen_opensRange _
end EnvelopeProperty.ProjSubvariety
