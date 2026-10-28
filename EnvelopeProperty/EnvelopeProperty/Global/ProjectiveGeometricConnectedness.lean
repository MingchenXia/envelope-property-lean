import EnvelopeProperty.Global.FibreProjectiveModels
import EnvelopeProperty.Global.FibreProjectiveFormalSections
import EnvelopeProperty.Global.FibreCompatibleConnectedness
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Whole original projective birational fibres are geometrically connected

Actual formal H0 algebraizes infinitesimal idempotents on the constructed
complete flat local model. The entire original closed fibre is retained,
including its nilpotents. No normality of a completion or field-valued
fibre, and no equality of closed-fibre global sections with its residue
field, is assumed.
-/

open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveGeometricConnectedness

variable {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] [IsDomain A] [IsIntegrallyClosed A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsReduced X]

/-- Genuine original projective birational geometry and actual formal H0
make EVERY whole original field-valued fibre connected, without extra inputs. -/
theorem connectedSpace_fieldFibre {K : Type u} [Field K] [Algebra F K]
    (w : A →ₐ[F] K) (hf : IsProjectiveFactorization f)
    (h : Scheme.BirationalOver f (𝟙 (Spec (.of A)))) :
    ConnectedSpace (pullback f (Spec.map (CommRingCat.ofHom w.toRingHom)) : Scheme.{u}) := by
  obtain ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, hfB, hBij,
      γ, hγs, hγk, hγw, e, he⟩ :=
    FibreProjectiveModels.exists_birational_presentation w f hf h
  let fB := FlatGlobalSections.structureMap (S := B) f
  let c : B ≃+* Γ(FlatGlobalSections.baseChange (S := B) f, ⊤) :=
    RingEquiv.ofBijective (ProperBirationalSections.coefficientMap fB) hBij
  let E : B ≃+* InfinitesimalIdempotents.compatibleSections
      (IsLocalRing.maximalIdeal B) fB :=
    c.trans (FibreProjectiveFormalSections.formalEquiv (IsLocalRing.maximalIdeal B) fB hfB)
  let : Nontrivial (InfinitesimalIdempotents.compatibleSections
      (IsLocalRing.maximalIdeal B) fB) := E.injective.nontrivial
  let : IsLocalRing (InfinitesimalIdempotents.compatibleSections
      (IsLocalRing.maximalIdeal B) fB) := IsLocalRing.of_surjective' E.toRingHom E.surjective
  have hc := FibreCompatibleConnectedness.modelOne_connectedSpace
    (IsLocalRing.maximalIdeal B) fB
  exact e.hom.homeomorph.connectedSpace_iff.mp hc

include F in
/-- Standard geometric connectedness of the literal original morphism is
DERIVED from its original normal-base projective birational geometry. -/
theorem geometricallyConnected (hf : IsProjectiveFactorization f)
    (h : Scheme.BirationalOver f (𝟙 (Spec (.of A)))) : GeometricallyConnected f := by
  constructor
  refine (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} => ConnectedSpace Y) (f := f)).mpr ?_
  intro K _ _
  let : Algebra F K := ((algebraMap A K).comp (algebraMap F A)).toAlgebra
  let w : A →ₐ[F] K :=
    { toRingHom := algebraMap A K
      commutes' := fun _ => rfl }
  exact connectedSpace_fieldFibre f w hf h

end EnvelopeProperty.ProjectiveGeometricConnectedness
