import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateLocalGerm
import Mathlib.Algebra.Group.Units.Equiv

/-!
# The actual original scheme stalk in its chosen coordinate germ

The evaluation kernel is proved to be the actual affine point over the
original complex point. Native Spec and open-immersion stalk isomorphisms
then identify the actual scheme stalk with the already used localization.
No injectivity of the resulting analytic germ map is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.AnalyticGeometry
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The actual affine prime defined by the actual original point evaluation. -/
def schemeCoordinateAlgebraicPoint : Spec (SchemeCoordinateAffineRing f n p) :=
  ⟨schemeCoordinatePointIdeal f n p, inferInstance⟩

/-- The actual Spec map sends the unique complex-field point to this kernel. -/
theorem schemeCoordinateAlgebraicPoint_specMap :
    Spec.map (CommRingCat.ofHom (standardSmoothComplexAlgebraPoint f n p).toRingHom)
      (default : Spec (.of ℂ)) = schemeCoordinateAlgebraicPoint f n p := by
  rw [Spec.map_apply]
  apply PrimeSpectrum.ext
  have hC : (default : Spec (.of ℂ)).asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (show PrimeSpectrum ℂ from (default : Spec (.of ℂ)))
        ⟨⊥, inferInstance⟩)
  rw [PrimeSpectrum.comap_asIdeal, hC]
  rfl

/-- The actual affine kernel maps to the SAME underlying original scheme point. -/
theorem schemeCoordinateAlgebraicPoint_map :
    (standardSmoothComplexAffineChart f n p).val.map (schemeCoordinateAlgebraicPoint f n p) =
      schemeComplexPointImage f p := by
  let c := (standardSmoothComplexAffineChart f n p).val
  let q := standardSmoothComplexAlgebraPoint f n p
  calc
    c.map (schemeCoordinateAlgebraicPoint f n p) =
        c.map (Spec.map (CommRingCat.ofHom q.toRingHom) default) :=
      congrArg c.map (schemeCoordinateAlgebraicPoint_specMap f n p).symm
    _ = (Spec.map (CommRingCat.ofHom q.toRingHom) ≫ c.map) default :=
      (Scheme.Hom.comp_apply _ _ _).symm
    _ = (complexAffineAlgebraPointMap f c q).val default :=
      congrArg (fun h : Spec (.of ℂ) ⟶ X => h default)
        (complexAffineAlgebraPointMap_val f c q).symm
    _ = schemeComplexPointImage f p :=
      congrArg (fun r : SchemeComplexPoint f => r.val default)
        (standardSmoothComplexAlgebraPoint_map f n p)

/-- Existing actual Spec/open-immersion stalk isomorphisms and the proved
point readback identify the actual local algebra with the actual scheme stalk. -/
def schemeCoordinateStalkEquiv : SchemeCoordinateLocalRing f n p ≃+*
    X.presheaf.stalk (schemeComplexPointImage f p) :=
  ((Spec.stalkIso (SchemeCoordinateAffineRing f n p)
      (schemeCoordinateAlgebraicPoint f n p)).symm ≪≫
    (asIso ((standardSmoothComplexAffineChart f n p).val.map.stalkMap
      (schemeCoordinateAlgebraicPoint f n p))).symm ≪≫
    X.presheaf.stalkCongr (Inseparable.of_eq
      (schemeCoordinateAlgebraicPoint_map f n p))).commRingCatIsoToRingEquiv

/-- The produced analytic germ map starts in the actual ORIGINAL scheme stalk. -/
def schemeCoordinateStalkRegularGerm :
    X.presheaf.stalk (schemeComplexPointImage f p) →+* HolGerm (Fin n → ℂ) :=
  (schemeCoordinateLocalRegularGerm f n p).comp
    ((schemeCoordinateStalkEquiv f n p).symm :
      X.presheaf.stalk (schemeComplexPointImage f p) →+* SchemeCoordinateLocalRing f n p)

/-- Whole readback on every actual affine local element. -/
theorem schemeCoordinateStalkRegularGerm_equiv (a : SchemeCoordinateLocalRing f n p) :
    schemeCoordinateStalkRegularGerm f n p (schemeCoordinateStalkEquiv f n p a) =
      schemeCoordinateLocalRegularGerm f n p a := by
  change schemeCoordinateLocalRegularGerm f n p
    ((schemeCoordinateStalkEquiv f n p).symm (schemeCoordinateStalkEquiv f n p a)) = _
  rw [RingEquiv.symm_apply_apply]

/-- Every actual original affine regular function retains its literal germ. -/
theorem schemeCoordinateStalkRegularGerm_regular (a : SchemeCoordinateAffineRing f n p) :
    schemeCoordinateStalkRegularGerm f n p (schemeCoordinateStalkEquiv f n p
      (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p) a)) =
        schemeCoordinateRegularGerm f n p a := by
  rw [schemeCoordinateStalkRegularGerm_equiv, schemeCoordinateLocalRegularGerm_algebraMap]

/-- The actual original local fraction keeps its proved residue. -/
theorem schemeCoordinateStalkRegularGerm_eval_mk'
    (a : SchemeCoordinateAffineRing f n p)
    (s : (schemeCoordinatePointIdeal f n p).primeCompl) :
    HolGerm.eval (schemeCoordinateStalkRegularGerm f n p
      (schemeCoordinateStalkEquiv f n p
        (IsLocalization.mk' (SchemeCoordinateLocalRing f n p) a s))) =
      standardSmoothComplexAlgebraPoint f n p a / standardSmoothComplexAlgebraPoint f n p s := by
  rw [schemeCoordinateStalkRegularGerm_equiv, schemeCoordinateLocalRegularGerm_eval_mk']

/-- The actual scheme-stalk map is genuinely local. -/
instance schemeCoordinateStalkRegularGerm_isLocalHom :
    IsLocalHom (schemeCoordinateStalkRegularGerm f n p) := by
  unfold schemeCoordinateStalkRegularGerm
  infer_instance

end HolomorphicGerms
