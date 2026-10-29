import EnvelopeProperty.Char0.RoundedCanonicalModule
import EnvelopeProperty.AlgGeom.Canonical.ExteriorCotangentMorphism

/-! # The SAME original exterior differential as an actual relative-canonical section -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The ORIGINAL actual exterior differential is a genuine whole section of the original
relative canonical tensor. Only invertibility of its original source is required. -/
def differentialSection (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] : Scheme.Modules.unitObj Y ⟶ relative f g n :=
  SchemeInvertibleHomSection.equiv _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g) _
    (CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)

/-- Recovering the section recovers the ENTIRE original exterior differential morphism. -/
theorem differentialSection_recover (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    (SchemeInvertibleHomSection.equiv _
      ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g)
      (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n)).symm (differentialSection f g n) =
      CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n :=
  SchemeInvertibleHomSection.recover _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g) _ _

end EnvelopeProperty.Char0.RoundedCanonicalModule
