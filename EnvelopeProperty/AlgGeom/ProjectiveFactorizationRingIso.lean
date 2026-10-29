import EnvelopeProperty.AlgGeom.AffineProjectiveBundleComparison
import EnvelopeProperty.Projective.FactorizationBaseChange

/-! # Actual coefficient-isomorphism transport of finite projective factorizations -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveFactorizationRingIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Genuine coefficient base change along a ring isomorphism retains the
literal original scheme and its entire original structural composite. -/
theorem postcomp_inverse (e : R ≃+* S) (hf : IsProjectiveFactorization f) :
    IsProjectiveFactorization (f ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let E : Spec (.of S) ≅ Spec (.of R) := Scheme.Spec.mapIso e.toCommRingCatIso.op
  let j : X ⟶ pullback f E.hom :=
    pullback.lift (𝟙 X) (f ≫ E.inv) (by simp [Category.assoc])
  have hjfst : j ≫ pullback.fst f E.hom = 𝟙 X := pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd f E.hom = f ≫ E.inv := pullback.lift_snd _ _ _
  have : IsClosedImmersion (j ≫ pullback.fst f E.hom) := by rw [hjfst]; infer_instance
  have hj : IsClosedImmersion j := IsClosedImmersion.of_comp j (pullback.fst f E.hom)
  have hbase : IsProjectiveFactorization (pullback.snd f E.hom) :=
    ProjectiveFactorizationBaseChange.baseChange (S := S) f hf
  have h := hbase.comp_isClosedImmersion j hj
  rw [hjsnd] at h
  exact h

/-- Every actual projective morphism to the original coefficient spectrum has
an ACTUAL finite polynomial closed factorization over that SAME original ring. -/
theorem of_isProjective [IsProjective f] : IsProjectiveFactorization f := by
  have h := AffineProjectiveBundleComparison.isProjectiveFactorization_of_isProjective f
  let e : Γ(Spec (.of R), ⊤) ≃+* R :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have h' := postcomp_inverse (f ≫ (Spec (.of R)).isoSpec.hom) e h
  have he : Spec.map (CommRingCat.ofHom e.symm.toRingHom) = (Spec (.of R)).isoSpec.inv :=
    (Scheme.isoSpec_Spec_inv (.of R)).symm
  rw [he, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact h'

end EnvelopeProperty.ProjectiveFactorizationRingIso
