import SGPT.Okounkov.SchemeCoordinateModelTransport
import BingWangEntropy.SchemeGenericSections

/-!
# Original global structure sections and the chosen analytic stalk map

Actual Spec localization, open-immersion stalk naturality and the original
point equality identify the chosen affine coefficient with the actual global
section germ. The resulting function-field readback retains native generic germs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending

private theorem actual_stalk_global_readback {X : Scheme} {A : CommRingCat}
    (c : Spec A ⟶ X) [IsOpenImmersion c] (y : Spec A) (x : X) (hxy : c y = x)
    (r : Γ(X, ⊤)) :
    ((Spec.stalkIso A y).symm ≪≫ (asIso (c.stalkMap y)).symm ≪≫
      X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom
        (algebraMap A (Localization.AtPrime y.asIdeal)
          ((Scheme.ΓSpecIso A).hom (c.appTop r))) =
      X.presheaf.germ ⊤ x trivial r := by
  have h : c.appTop ≫ (Scheme.ΓSpecIso A).hom ≫
      CommRingCat.ofHom (algebraMap A (Localization.AtPrime y.asIdeal)) ≫
      (Spec.stalkIso A y).inv ≫ (asIso (c.stalkMap y)).inv ≫
      (X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom =
        X.presheaf.germ ⊤ x trivial := by
    rw [Spec.algebraMap_stalkIso_inv_assoc, Iso.hom_inv_id_assoc]
    change c.app ⊤ ≫ (Spec A).presheaf.germ (c ⁻¹ᵁ ⊤) y trivial ≫
      (asIso (c.stalkMap y)).inv ≫
      (X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom = _
    rw [← c.germ_stalkMap_assoc]
    rw [asIso_inv, IsIso.hom_inv_id_assoc]
    simp only [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes]
  exact congrArg (fun q : Γ(X, ⊤) ⟶ X.presheaf.stalk x => q r) h

private theorem affine_global_constant_coefficient {X : Scheme} {A : CommRingCat}
    (c : Spec A ⟶ X) (f : X ⟶ Spec (.of ℂ)) (z : ℂ) :
    (Scheme.ΓSpecIso A).hom (c.appTop (schemeGlobalConstants f z)) =
      (Spec.preimage (c ≫ f)).hom z := by
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage (c ≫ f))
  rw [Spec.map_preimage] at h
  have hz := congrArg (fun q : Γ(Spec (.of ℂ), ⊤) ⟶ A =>
    q ((Scheme.ΓSpecIso (.of ℂ)).inv z)) h
  simpa only [schemeGlobalConstants, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply] using hz

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) [IsIntegral X]

local instance globalCoordinateComplexAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The actual coefficient of an original global structure section in the SAME
chosen original affine chart. -/
def schemeCoordinateGlobalCoefficient (r : Γ(X, ⊤)) : SchemeCoordinateAffineRing f n p :=
  (Scheme.ΓSpecIso (SchemeCoordinateAffineRing f n p)).hom
    ((standardSmoothComplexAffineChart f n p).val.map.appTop r)

omit [IsIntegral X] in
/-- The already produced SAME stalk equivalence sends the actual affine
coefficient to the original global section's genuine stalk germ. -/
theorem schemeCoordinateStalkEquiv_global (r : Γ(X, ⊤)) :
    schemeCoordinateStalkEquiv f n p
      (algebraMap _ (SchemeCoordinateLocalRing f n p) (schemeCoordinateGlobalCoefficient f n p r)) =
      X.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial r := by
  exact actual_stalk_global_readback (standardSmoothComplexAffineChart f n p).val.map
    (schemeCoordinateAlgebraicPoint f n p) (schemeComplexPointImage f p)
    (schemeCoordinateAlgebraicPoint_map f n p) r

/-- The actual affine coefficient represents exactly the original native generic
germ in the actual global function field. -/
theorem schemeCoordinateRegularFunctionField_global (r : Γ(X, ⊤)) :
    schemeCoordinateRegularFunctionField f n p (schemeCoordinateGlobalCoefficient f n p r) =
      X.germToFunctionField ⊤ r := by
  rw [schemeCoordinateRegularFunctionField, schemeCoordinateStalkEquiv_global,
    Scheme.algebraMap_germ_eq_germToFunctionField]

/-- Whole analytic readback on every actual global structure section. -/
theorem schemeCoordinateFunctionFieldGerm_global (r : Γ(X, ⊤)) :
    schemeCoordinateFunctionFieldGerm f n p (X.germToFunctionField ⊤ r) =
      algebraMap _ (FractionRing (HolGerm (Fin n → ℂ)))
        (schemeCoordinateRegularGerm f n p (schemeCoordinateGlobalCoefficient f n p r)) := by
  rw [← schemeCoordinateRegularFunctionField_global f n p r,
    schemeCoordinateFunctionFieldGerm_regular]

omit [IsIntegral X] in
/-- The SAME original structural pullback produces the actual affine scalars. -/
theorem schemeCoordinateGlobalCoefficient_const (z : ℂ) :
    schemeCoordinateGlobalCoefficient f n p (schemeGlobalConstants f z) =
      algebraMap ℂ (SchemeCoordinateAffineRing f n p) z :=
  affine_global_constant_coefficient (standardSmoothComplexAffineChart f n p).val.map f z

/-- Exact compatibility with BWE's original structure-induced function-field
algebra is DERIVED from actual global sections and scalar-germ readbacks. -/
theorem schemeCoordinateFunctionFieldGerm_const (z : ℂ) :
    letI := schemeFunctionFieldAlgebra f
    schemeCoordinateFunctionFieldGerm f n p (algebraMap ℂ X.functionField z) =
      algebraMap (HolGerm (Fin n → ℂ)) (FractionRing (HolGerm (Fin n → ℂ)))
        (HolGerm.constHom z) := by
  change schemeCoordinateFunctionFieldGerm f n p
    (X.germToFunctionField ⊤ (schemeGlobalConstants f z)) = _
  rw [schemeCoordinateFunctionFieldGerm_global, schemeCoordinateGlobalCoefficient_const,
    schemeCoordinateRegularGerm_scalar]

end SGPT.Okounkov
