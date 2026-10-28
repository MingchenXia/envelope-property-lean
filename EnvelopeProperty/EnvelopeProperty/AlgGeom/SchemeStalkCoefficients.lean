import EnvelopeProperty.AlgGeom.SchemeStalkCenteredDVR
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Whole actual original coefficient maps into original scheme stalks -/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeStalkCoefficients
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The literal original structure morphism induces the actual stalk coefficient map. -/
def coefficientMap (f : X ⟶ Spec (CommRingCat.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  letI := f.stalkAlgebra x
  algebraMap R (X.presheaf.stalk x)

/-- The WHOLE actual original stalk structure triangle. -/
theorem fromSpecStalk_structureMap (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (coefficientMap f x)) := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (X.fromSpecStalk x ≫ f).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (coefficientMap f x))).appTop
  rw [Scheme.Hom.comp_appTop,Scheme.fromSpecStalk_appTop,← Scheme.ΓSpecIso_inv_naturality]
  simp only [homOfLE_refl,op_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  rfl

/-- The original coefficient map contracts the SAME original stalk maximal ideal
EXACTLY to the original base prime of the original point. -/
theorem maximalIdeal_comap_coefficientMap (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (coefficientMap f x) = (f x).asIdeal := by
  have h := congrArg (fun q : Spec (X.presheaf.stalk x) ⟶ Spec (CommRingCat.of R) =>
    q (IsLocalRing.closedPoint (X.presheaf.stalk x))) (fromSpecStalk_structureMap f x)
  rw [Scheme.Hom.comp_apply,Scheme.fromSpecStalk_closedPoint] at h
  exact (congrArg PrimeSpectrum.asIdeal h).symm

/-- Actual integral source and reduced-base dominance imply true injectivity
of the SAME original coefficient map into every original stalk. -/
theorem coefficientMap_injective [IsIntegral X] [IsReduced R]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsDominant f] [QuasiCompact f] (x : X) :
    Function.Injective (coefficientMap f x) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  exact (germ_injective_of_isIntegral X x (show x ∈ f ⁻¹ᵁ ⊤ from trivial)).comp
    ((f.app_injective ⊤).comp (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv).injective)

end EnvelopeProperty.SchemeStalkCoefficients
