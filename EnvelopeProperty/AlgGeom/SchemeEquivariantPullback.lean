/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.PullbackConeMonoidAction
import EnvelopeProperty.AlgGeom.SchemeFlatProductDominance
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Genuine action on the SAME original scheme-theoretic fibre product

The original base scheme may itself carry a nontrivial action. The SAME
native scheme pullback and both original projection morphisms are retained,
without changing them to a chosen abstract pullback in the over category.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.SchemeEquivariantPullback

variable {T : Scheme.{u}} {X Y S : Over T} (f : X ⟶ S) (g : Y ⟶ S)

/-- The SAME native scheme pullback, with its actual original coefficient map. -/
def object : Over T := Over.mk (pullback.fst f.left g.left ≫ X.hom)

/-- The actual original first projection over the coefficient scheme. -/
def firstProjection : object f g ⟶ X := Over.homMk (pullback.fst f.left g.left) rfl

/-- The actual original second projection over the coefficient scheme. -/
def secondProjection : object f g ⟶ Y :=
  Over.homMk (pullback.snd f.left g.left) (by
    change pullback.snd f.left g.left ≫ Y.hom = pullback.fst f.left g.left ≫ X.hom
    rw [← g.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.w])

/-- The original native scheme fibre square is Cartesian over the SAME coefficient scheme. -/
theorem square : IsPullback (firstProjection f g) (secondProjection f g) f g := by
  apply IsPullback.of_map_of_faithful (Over.forget T)
  exact IsPullback.of_hasPullback f.left g.left

variable (G : Over T) [MonObj G] [ModObj G X] [ModObj G Y] [ModObj G S]
  [IsModHom G f] [IsModHom G g]

/-- The genuine derived group/monoid action on the SAME original native scheme product. -/
@[instance_reducible]
def modObj : ModObj G (object f g) := PullbackConeMonoidAction.modObj G (square f g)

/-- The whole actual first native scheme projection is equivariant. -/
theorem firstProjection_isModHom : letI := modObj f g G
    IsModHom G (firstProjection f g) := PullbackConeMonoidAction.fst_isModHom G (square f g)

/-- The whole actual second native scheme projection is equivariant. -/
theorem secondProjection_isModHom : letI := modObj f g G
    IsModHom G (secondProjection f g) := PullbackConeMonoidAction.snd_isModHom G (square f g)

/-- An actual original map to the SAME native scheme product is equivariant as soon
as its two original projection composites are equivariant. -/
theorem isModHom_of_comp {A : Over T} [ModObj G A] (a : A ⟶ object f g)
    [IsModHom G (a ≫ firstProjection f g)] [IsModHom G (a ≫ secondProjection f g)] :
    letI := modObj f g G
    IsModHom G a := PullbackConeMonoidAction.isModHom_of_comp G (square f g) a

end EnvelopeProperty.SchemeEquivariantPullback
