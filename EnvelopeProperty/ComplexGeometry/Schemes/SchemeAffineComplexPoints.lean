import EnvelopeProperty.ComplexGeometry.Schemes.AffineComplexPoints
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Actual affine scheme complex points

Complex points are scheme morphisms from Spec ℂ compatible with the structural
morphism. The affine algebra point correspondence is proved using the actual
fully faithful Spec functor. It supplies the evaluation topology on these affine
scheme points. Analytic gluing for arbitrary schemes is a separate construction.
-/

open CategoryTheory AlgebraicGeometry

namespace ComplexSchemes

noncomputable section

/-- Genuine complex points of a scheme over the complex field. -/
def SchemeComplexPoint {X : Scheme} (f : X ⟶ Spec (.of ℂ)) :=
  {p : Spec (.of ℂ) ⟶ X // p ≫ f = 𝟙 _}

/-- Actual scheme morphisms over ℂ act on actual complex points by composition. -/
def schemeComplexPointMap {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
    (g : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y) (hh : h ≫ g = f)
    (p : SchemeComplexPoint f) : SchemeComplexPoint g :=
  ⟨p.val ≫ h, by rw [Category.assoc, hh, p.property]⟩

variable (A : Type) [CommRing A] [Algebra ℂ A]

/-- The actual structural scheme morphism of a complex affine algebra. -/
def complexAffineStructureMap : Spec (.of A) ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ A))

/-- An algebra point defines its actual scheme point by the Spec functor. -/
def complexAlgebraPoint_toScheme (p : ComplexAlgebraPoint A) :
    SchemeComplexPoint (complexAffineStructureMap A) :=
  ⟨Spec.map (CommRingCat.ofHom p.toRingHom), by
    rw [complexAffineStructureMap, ← Spec.map_comp]
    have h : CommRingCat.ofHom (algebraMap ℂ A) ≫ CommRingCat.ofHom p.toRingHom =
        𝟙 (CommRingCat.of ℂ) := by
      ext c
      exact p.commutes c
    rw [h, Spec.map_id]⟩

/-- A genuine affine scheme point recovers its algebra point by full
faithfulness, with complex-linearity derived from its structural compatibility. -/
def affineSchemePoint_toAlgebra
    (p : SchemeComplexPoint (complexAffineStructureMap A)) : ComplexAlgebraPoint A :=
  { (Spec.preimage p.val).hom with
    commutes' c := by
      have h := congrArg Spec.preimage p.property
      have hc := congrArg (fun q : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => q c) h
      simpa [Spec.preimage_comp, complexAffineStructureMap] using hc }

/-- Actual scheme and algebra complex points are equivalent. -/
def affineSchemeComplexPointEquiv :
    SchemeComplexPoint (complexAffineStructureMap A) ≃ ComplexAlgebraPoint A where
  toFun := affineSchemePoint_toAlgebra A
  invFun := complexAlgebraPoint_toScheme A
  left_inv p := by
    apply Subtype.ext
    exact Spec.map_preimage p.val
  right_inv p := by
    apply AlgHom.ext
    intro a
    exact congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of ℂ => q a)
      (Spec.preimage_map (CommRingCat.ofHom p.toRingHom))

/-- The analytic evaluation topology on the genuine affine scheme point set. -/
instance affineSchemeComplexPointTopology :
    TopologicalSpace (SchemeComplexPoint (complexAffineStructureMap A)) :=
  TopologicalSpace.induced (affineSchemeComplexPointEquiv A) inferInstance

/-- The actual affine scheme point identification respects its analytic topology. -/
def affineSchemeComplexPointHomeomorph :
    SchemeComplexPoint (complexAffineStructureMap A) ≃ₜ ComplexAlgebraPoint A where
  toEquiv := affineSchemeComplexPointEquiv A
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    convert (continuous_id : Continuous (id : ComplexAlgebraPoint A → ComplexAlgebraPoint A))
      using 1
    funext p
    exact (affineSchemeComplexPointEquiv A).right_inv p

/-- The affine point equivalence commutes with the actual contravariant
scheme morphism induced by an algebra map. -/
theorem complexAlgebraPoint_toScheme_naturality {B : Type} [CommRing B] [Algebra ℂ B]
    (h : A →ₐ[ℂ] B) (p : ComplexAlgebraPoint B) :
    (complexAlgebraPoint_toScheme A (p.comp h)).val =
      (complexAlgebraPoint_toScheme B p).val ≫ Spec.map (CommRingCat.ofHom h.toRingHom) := by
  rw [complexAlgebraPoint_toScheme, complexAlgebraPoint_toScheme, ← Spec.map_comp]
  rfl

end

end ComplexSchemes
