import Hironaka.Scheme.Snc.RelativeDimensionConstant

/-! # A produced pure dimension of the SAME original integral smooth scheme

The actual native relative-dimension constancy theorem already proves the
mathematics. Original integral geometry supplies preconnectedness/nonemptiness;
no dimension, finite-type or projectivity certificate is a new input.
-/

noncomputable section
open AlgebraicGeometry
universe u
namespace EnvelopeProperty.Char0.SmoothPureDimension

/-- Original integral smooth geometry internally produces its true pure
dimension, by the proved native locally-constant dimension theorem. -/
theorem exists_smoothOfRelativeDimension {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [Smooth p] :
    ∃ n : ℕ, SmoothOfRelativeDimension n p :=
  AlgebraicGeometry.exists_smoothOfRelativeDimension_of_preconnectedSpace p

/-- The original characteristic-zero field internally supplies perfectness;
the consumer supplies no dimension or pure-dimension hypothesis. -/
theorem exists_smoothOfRelativeDimension_charZero {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [Smooth p] :
    ∃ n : ℕ, SmoothOfRelativeDimension n p :=
  exists_smoothOfRelativeDimension p

/-- An actual natural witness chosen from the PROVED original geometric
producer, retaining the SAME original scheme and structure map. -/
def dimension {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [Smooth p] : ℕ :=
  Classical.choose (exists_smoothOfRelativeDimension p)

/-- The chosen dimension satisfies the actual native original property. -/
theorem smooth_dimension {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [Smooth p] :
    SmoothOfRelativeDimension (dimension p) p :=
  Classical.choose_spec (exists_smoothOfRelativeDimension p)

end EnvelopeProperty.Char0.SmoothPureDimension
