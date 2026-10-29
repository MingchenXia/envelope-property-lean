import EnvelopeProperty.Char0.MultiplierFamilySmoothnessChartAlgebra
import EnvelopeProperty.Local.PLIdealSubvarietyModels
import EnvelopeProperty.Berkovich.SchemeCenterAffine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The SAME original native coordinate opens, coefficients and algebra smoothness -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
universe u
namespace EnvelopeProperty.Char0.MultiplierFamilySmoothness
open ProjBerk Berkovich
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The SAME actual native coordinate inverse-image open. -/
def nativeChartOpen (j : Fin (M + 1)) : X.NativeScheme.Opens :=
  X.nativeInclusion ⁻¹ᵁ nativeCoordinateOpen (R := k) j

/-- Its affineness is internally supplied by the original closed immersion. -/
theorem nativeChartOpen_isAffine (j : Fin (M + 1)) : IsAffineOpen (nativeChartOpen X j) :=
  (nativeCoordinateOpen_isAffine (R := k) j).preimage X.nativeInclusion

/-- The actual ORIGINAL field structure supplies the SAME original chart coefficient action. -/
@[instance_reducible]
def nativeChartAlgebra (j : Fin (M + 1)) : Algebra k Γ(X.NativeScheme, nativeChartOpen X j) :=
  SchemeValuedPoint.sectionBaseAlgebra X.nativeStructure (nativeChartOpen X j)

/-- Native whole coordinate sections identify with the entire original dehomogenized quotient, over the ORIGINAL field action. -/
def nativeChartCoordinateSectionsEquiv (j : Fin (M + 1)) :
    letI := nativeChartAlgebra X j
    Γ(X.NativeScheme, nativeChartOpen X j) ≃ₐ[k]
      CoordinateRing k j ⧸ X.ideal.map (coordinateDehom j).toRingHom :=
  nativeQuotientCoordinateSectionsAlgEquiv X.nativeHomogeneousIdeal j

/-- The SAME native chart algebra is the original old quotient chart used in HasSmoothCharts. -/
def nativeChartSectionsEquiv (j : Fin (M + 1))
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    letI := nativeChartAlgebra X j
    Γ(X.NativeScheme, nativeChartOpen X j) ≃ₐ[k] QuotChartAlg X.ideal (MvPolynomial.X j) 1 := by
  letI := nativeChartAlgebra X j
  exact (nativeChartCoordinateSectionsEquiv X j).trans (coordinateQuotientEquiv X j hj)

/-- Every actual pulled coordinate polynomial has its ORIGINAL quotient class, without a support replacement. -/
theorem nativeChartCoordinateSectionsEquiv_pullback (j : Fin (M + 1)) (F : CoordinateRing k j) :
    nativeChartCoordinateSectionsEquiv X j
      ((X.nativeInclusion.app (nativeCoordinateOpen j)).hom ((nativeCoordinateSectionsIso j).hom.hom F)) =
      Ideal.Quotient.mk (X.ideal.map (coordinateDehom j).toRingHom) F :=
  nativeQuotientCoordinateSectionsEquiv_pullback X.nativeHomogeneousIdeal j F

/-- The full section ring on EVERY actual native chart is smooth for the ORIGINAL field action.
Nonrelevant coordinates are handled as actual zero-ring charts, not silently discarded. -/
theorem nativeChartSections_smooth (hs : X.HasSmoothCharts) (j : Fin (M + 1)) :
    letI := nativeChartAlgebra X j
    Algebra.Smooth k Γ(X.NativeScheme, nativeChartOpen X j) := by
  let : Algebra k Γ(X.NativeScheme, nativeChartOpen X j) := nativeChartAlgebra X j
  by_cases hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal
  · let : Algebra.Smooth k (QuotChartAlg X.ideal (MvPolynomial.X j) 1) := hs j hj
    exact Algebra.Smooth.of_equiv (A := QuotChartAlg X.ideal (MvPolynomial.X j) 1)
      (B := Γ(X.NativeScheme, nativeChartOpen X j)) (nativeChartSectionsEquiv X j hj).symm
  · have hx : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∈ X.ideal := not_not.mp hj
    have h1 : (1 : CoordinateRing k j) ∈ X.ideal.map (coordinateDehom j).toRingHom := by
      have h := Ideal.mem_map_of_mem (coordinateDehom j).toRingHom hx
      simpa [coordinateDehom, coordinateDehomCoord] using h
    have ht : X.ideal.map (coordinateDehom j).toRingHom = ⊤ := Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one
    let : Subsingleton (CoordinateRing k j ⧸ X.ideal.map (coordinateDehom j).toRingHom) := by
      rw [ht]
      infer_instance
    let : Algebra.IsStandardSmooth k (CoordinateRing k j ⧸ X.ideal.map (coordinateDehom j).toRingHom) :=
      inferInstance
    let : Algebra.Smooth k (CoordinateRing k j ⧸ X.ideal.map (coordinateDehom j).toRingHom) :=
      inferInstance
    exact Algebra.Smooth.of_equiv (nativeChartCoordinateSectionsEquiv X j).symm

/-- The WHOLE original field triangle for the SAME actual native affine chart. -/
theorem nativeChart_structure (j : Fin (M + 1)) :
    (nativeChartOpen_isAffine X j).fromSpec ≫ X.nativeStructure =
      Spec.map (CommRingCat.ofHom (SchemeValuedPoint.sectionBaseMap X.nativeStructure (nativeChartOpen X j))) :=
  SchemeValuedPoint.fromSpec_structureMap X.nativeStructure (nativeChartOpen_isAffine X j)

/-- The original chart condition DERIVES genuine smoothness of this SAME actual native affine chart morphism. -/
theorem nativeChart_smooth (hs : X.HasSmoothCharts) (j : Fin (M + 1)) :
    Smooth ((nativeChartOpen_isAffine X j).fromSpec ≫ X.nativeStructure) := by
  let : Algebra k Γ(X.NativeScheme, nativeChartOpen X j) := nativeChartAlgebra X j
  let : Algebra.Smooth k Γ(X.NativeScheme, nativeChartOpen X j) := nativeChartSections_smooth X hs j
  rw [nativeChart_structure]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

end EnvelopeProperty.Char0.MultiplierFamilySmoothness
