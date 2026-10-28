/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.PolynomialSchemeBaseChangeNormal
import EnvelopeProperty.AlgGeom.NormalizationAffineIsomorphism

/-! # Normal actual polynomial products of original integral normal schemes -/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Polynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.PolynomialSchemeBaseChangeNormal
open FlatGlobalSections
variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of R))

private def affineOpenBaseChangeMap (U : X.Opens) :
    baseChange (S := R[X]) (U.ι ≫ p) ⟶ baseChange (S := R[X]) p :=
  (pullbackRightPullbackFstIso p (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) U.ι).inv ≫
    pullback.snd U.ι (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))))

private instance affineOpenBaseChangeMap_isOpenImmersion (U : X.Opens) :
    IsOpenImmersion (affineOpenBaseChangeMap p U) := by
  dsimp [affineOpenBaseChangeMap]
  infer_instance

omit [IsIntegral X] in
private theorem affineOpenBaseChangeMap_cover (U : X.Opens)
    (z : baseChange (S := R[X]) p) (hz : firstProjection (S := R[X]) p z ∈ U) :
    ∃ y, affineOpenBaseChangeMap p U y = z := by
  have hm : z ∈ Set.range (pullback.snd U.ι (firstProjection (S := R[X]) p)) := by
    rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι]
    exact hz
  obtain ⟨q, hq⟩ := hm
  let e := pullbackRightPullbackFstIso p (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) U.ι
  refine ⟨e.hom q, ?_⟩
  have he : e.hom ≫ affineOpenBaseChangeMap p U =
      pullback.snd U.ι (firstProjection (S := R[X]) p) := by
    simp [e, affineOpenBaseChangeMap, firstProjection]
  exact (congrArg (fun f => f q) he).trans hq

/-- Every actual original polynomial-product stalk is a domain, derived
from original scheme integrality and actual affine polynomial charts. -/
theorem polynomialBaseChange_stalk_isDomain (z : baseChange (S := R[X]) p) :
    IsDomain ((baseChange (S := R[X]) p).presheaf.stalk z) := by
  obtain ⟨U, hU, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (show firstProjection (S := R[X]) p z ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨_, hz⟩⟩
  let : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨firstProjection (S := R[X]) p z, hz⟩, trivial⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsAffine U.toScheme := hU
  obtain ⟨y, hy⟩ := affineOpenBaseChangeMap_cover p U z hz
  let := affinePolynomial_stalk_isDomain (U.ι ≫ p) y
  rw [← hy]
  let e := (asIso ((affineOpenBaseChangeMap p U).stalkMap y)).commRingCatIsoToRingEquiv
  exact Function.Injective.isDomain e e.injective

/-- Original normal local rings alone derive normality of EVERY same actual
polynomial-product local ring, with no normal-product or smoothness certificate. -/
theorem polynomialBaseChange_stalk_isIntegrallyClosed
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (z : baseChange (S := R[X]) p) :
    IsIntegrallyClosed ((baseChange (S := R[X]) p).presheaf.stalk z) := by
  obtain ⟨U, hU, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (show firstProjection (S := R[X]) p z ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨_, hz⟩⟩
  let : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨firstProjection (S := R[X]) p z, hz⟩, trivial⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsAffine U.toScheme := hU
  have hNU : ∀ x : U.toScheme, IsIntegrallyClosed (U.toScheme.presheaf.stalk x) := by
    intro x
    let := hN (U.ι x)
    exact IsIntegrallyClosed.of_equiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
  let : IsIntegrallyClosed Γ(U.toScheme, ⊤) :=
    IntegralSchemeNormalization.affine_sections_isIntegrallyClosed U.toScheme hNU ⊤ (isAffineOpen_top _)
  obtain ⟨y, hy⟩ := affineOpenBaseChangeMap_cover p U z hz
  let := affinePolynomial_stalk_isIntegrallyClosed (U.ι ≫ p) y
  rw [← hy]
  exact IsIntegrallyClosed.of_equiv
    (asIso ((affineOpenBaseChangeMap p U).stalkMap y)).commRingCatIsoToRingEquiv.symm

end EnvelopeProperty.PolynomialSchemeBaseChangeNormal
