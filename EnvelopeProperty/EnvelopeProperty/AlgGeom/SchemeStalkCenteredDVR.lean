import EnvelopeProperty.Algebra.EssentiallyFiniteTypeCenteredDVR
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras
import Hironaka.Algebra.RegularSmooth.SmoothAt

/-! # Actual same-function-field DVR morphisms centered at original scheme points -/
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeStalkCenteredDVR
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/-- Actual local finite type geometry derives essentially finite type on the
SAME original stalk, for the original structure morphism's native algebra. -/
theorem essFiniteType_stalkAlgebra (x : X) :
    letI := f.stalkAlgebra x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  have hx : x ∈ U := X.affineCover.covers x
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk (⟨x,hx⟩ : U)
  let : IsScalarTower k Γ(X,U) (X.presheaf.stalk x) :=
    f.isScalarTower_sectionsAlgebra_stalk U hx
  let : Algebra.FiniteType k Γ(X,U) := f.finiteType_sectionsAlgebra hU
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x,hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x,hx⟩
  let : Algebra.EssFiniteType Γ(X,U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk x) ((hU.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl)
  exact Algebra.EssFiniteType.comp k Γ(X,U) (X.presheaf.stalk x)

include f in
/-- A true original DVR morphism into the SAME integral scheme has exactly the
original point as center and the SAME whole original function-field generic map. -/
theorem exists_centeredDVR_morphism [IsIntegral X] (x : X)
    (hx : ¬IsField (X.presheaf.stalk x)) :
    ∃ (V : Subalgebra (X.presheaf.stalk x) X.functionField) (hV : IsDiscreteValuationRing V),
      let := hV
      ∃ q : Spec (CommRingCat.of V) ⟶ X,
        q (IsLocalRing.closedPoint V) = x ∧
        Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q =
          X.fromSpecStalk (genericPoint X) := by
  let _ := f.stalkAlgebra x
  let : Algebra.EssFiniteType k (X.presheaf.stalk x) := essFiniteType_stalkAlgebra f x
  obtain ⟨V,hV,hcenter⟩ := EssentiallyFiniteTypeCenteredDVR.exists_centeredDVR k
    (X.presheaf.stalk x) X.functionField hx
  let := hV
  let q : Spec (CommRingCat.of V) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) V)) ≫ X.fromSpecStalk x
  refine ⟨V,hV,q,?_,?_⟩
  · have hc : (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) V)))
        (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      PrimeSpectrum.ext hcenter
    change (X.fromSpecStalk x) ((Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) V))) (IsLocalRing.closedPoint V)) = x
    rw [hc,Scheme.fromSpecStalk_closedPoint]
  · change Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) V)) ≫ X.fromSpecStalk x) = _
    rw [← Category.assoc,← Spec.map_comp]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)

end EnvelopeProperty.SchemeStalkCenteredDVR
