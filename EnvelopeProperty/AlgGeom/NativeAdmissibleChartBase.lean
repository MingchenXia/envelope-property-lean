import EnvelopeProperty.AlgGeom.NativeAdmissibleCharts
import EnvelopeProperty.Alterations.Geometry.ProjStructureMap

/-! # Literal original coefficient structures on actual admissible charts -/
open scoped Classical
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open EnvelopeProperty.ProjBerk
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] nativeQuotientAwayAlgebra
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
private local instance qgr : GradedRing (GradedQuotient.grading (ProjectiveGrading k n) X.ideal) :=
  GradedQuotient.gradedRing _ X.ideal X.homogeneousIdeal.isHomogeneous

/-- The SAME literal original coefficient homomorphism into the actual
homogeneous quotient degree-zero ring. -/
def nativeQuotientBaseZero : k →+* GradedQuotient.grading (ProjectiveGrading k n) X.ideal 0 :=
  (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal).gradedZeroRingHom.comp
    (algebraMap k (ProjectiveGrading k n 0))

/-- The whole actual original quotient structure is precisely its true
degree-zero structure followed by the literal ORIGINAL coefficient map. -/
theorem quotientNativeStructure_eq_toSpecZero :
    X.quotientNativeStructure =
      Proj.toSpecZero (GradedQuotient.grading (ProjectiveGrading k n) X.ideal) ≫
        Spec.map (CommRingCat.ofHom X.nativeQuotientBaseZero) :=
  Alterations.Geometry.ProjStructureMap.map_toSpec_base
    (GradedQuotient.gradedMk (ProjectiveGrading k n) X.ideal)
    (GradedQuotient.irrelevant_le_map (ProjectiveGrading k n) X.homogeneousIdeal)
    (algebraMap k (ProjectiveGrading k n 0)) X.nativeQuotientBaseZero rfl

private def chartRingIso {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    CommRingCat.of (QuotChartAlg X.ideal F d) ≅ CommRingCat.of (X.nativeQuotientAway F) :=
  (X.quotChartNativeAwayEquiv hF hFI).toRingEquiv.toCommRingCatIso
private theorem chartRingIso_inv_coeff {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (c : k) :
    (chartRingIso X hF hFI).inv.hom (algebraMap k (X.nativeQuotientAway F) c) =
      algebraMap k (QuotChartAlg X.ideal F d) c :=
  (X.quotChartNativeAwayEquiv hF hFI).symm.commutes c

/-- The SAME original arbitrary admissible chart map preserves the actual
original field structure, not merely the underlying affine scheme. -/
theorem nativeAdmissibleChartMap_over_base
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    X.nativeAdmissibleChartMap hF hFI hd ≫ X.nativeStructure =
      Spec.map (CommRingCat.ofHom (algebraMap k (QuotChartAlg X.ideal F d))) := by
  dsimp only [nativeAdmissibleChartMap]
  rw [Category.assoc, Category.assoc, X.quotientNativeIso_structure,
    X.quotientNativeStructure_eq_toSpecZero]
  rw [← Category.assoc _ (Proj.toSpecZero _) _, Proj.awayι_toSpecZero,
    ← Spec.map_comp, CategoryTheory.Functor.mapIso_inv]
  change Scheme.Spec.map (chartRingIso X hF hFI).op.inv ≫
    Scheme.Spec.map (CommRingCat.ofHom X.nativeQuotientBaseZero ≫
      CommRingCat.ofHom (fromZeroRingHom
        (GradedQuotient.grading (ProjectiveGrading k n) X.ideal)
        (Submonoid.powers (Ideal.Quotient.mk X.ideal F)))).op = _
  rw [← Scheme.Spec.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommRingCat.hom_ext
  ext c
  exact chartRingIso_inv_coeff X hF hFI c

/-- The actual whole affine-chart isomorphism retains the SAME original
coefficient structure after its literal original open inclusion. -/
theorem nativeAdmissibleChartIso_over_base
    {F : MvPolynomial (Fin (n+1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) (hd : 0 < d) :
    (X.nativeAdmissibleChartIso hF hFI hd).hom ≫
      (X.nativeAdmissibleOpen F).ι ≫ X.nativeStructure =
      Spec.map (CommRingCat.ofHom (algebraMap k (QuotChartAlg X.ideal F d))) := by
  rw [← Category.assoc, X.nativeAdmissibleChartIso_hom_ι,
    X.nativeAdmissibleChartMap_over_base]
end EnvelopeProperty.ProjSubvariety
