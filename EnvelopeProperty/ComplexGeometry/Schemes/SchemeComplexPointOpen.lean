import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAffineComplexPoints
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Actual scheme-point charts

A complex scheme point has one underlying image point. The genuine universal
property of an open immersion gives the unique lift of that point into any open
chart containing its image. This is point-level chart gluing; analytic topology
and manifold charts are further constructions.
-/

open CategoryTheory AlgebraicGeometry

namespace ComplexSchemes

noncomputable section

variable {X U : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- The underlying image of a genuine complex scheme point. -/
def schemeComplexPointImage (p : SchemeComplexPoint f) : X := p.val default

/-- The source is the actual one-point spectrum of the complex field. -/
theorem schemeComplexPoint_range (p : SchemeComplexPoint f) :
    Set.range p.val = {schemeComplexPointImage f p} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg p.val (Subsingleton.elim y default)
  · rintro rfl
    exact ⟨default, rfl⟩

variable (g : U ⟶ X) [IsOpenImmersion g]

omit [IsOpenImmersion g] in
/-- Containment of the image point derives the range condition required by
the actual universal property of the open immersion. -/
theorem schemeComplexPoint_range_subset (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ Set.range g) : Set.range p.val ⊆ Set.range g := by
  rw [schemeComplexPoint_range]
  exact Set.singleton_subset_iff.mpr hp

/-- Unique lift into a genuine open chart, with compatibility over ℂ derived. -/
def schemeComplexPointLift (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ Set.range g) : SchemeComplexPoint (g ≫ f) :=
  ⟨IsOpenImmersion.lift g p.val (schemeComplexPoint_range_subset f g p hp), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, p.property]⟩

/-- The lifted point composes to its actual original scheme morphism. -/
theorem schemeComplexPointLift_fac (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ Set.range g) :
    (schemeComplexPointLift f g p hp).val ≫ g = p.val :=
  IsOpenImmersion.lift_fac g p.val _

/-- Every genuine chart point maps to a point whose image is in that chart. -/
def schemeComplexPointChart (p : SchemeComplexPoint (g ≫ f)) :
    {q : SchemeComplexPoint f // schemeComplexPointImage f q ∈ Set.range g} :=
  ⟨schemeComplexPointMap (g ≫ f) f g rfl p,
    ⟨p.val default, by
      change g (p.val default) = (p.val ≫ g) default
      exact (Scheme.Hom.comp_apply p.val g default).symm⟩⟩

/-- Actual complex points in an open subscheme are precisely the global
complex points whose underlying image lies in the open chart. -/
def schemeComplexPointOpenEquiv : SchemeComplexPoint (g ≫ f) ≃
    {p : SchemeComplexPoint f // schemeComplexPointImage f p ∈ Set.range g} where
  toFun := schemeComplexPointChart f g
  invFun p := schemeComplexPointLift f g p.val p.property
  left_inv p := by
    apply Subtype.ext
    apply (cancel_mono g).mp
    exact schemeComplexPointLift_fac f g _ _
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact schemeComplexPointLift_fac f g p.val p.property

end

end ComplexSchemes
