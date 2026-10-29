import EnvelopeProperty.PolynomialProjProper
import EnvelopeProperty.ReesPresentation
import EnvelopeProperty.Projective.HomogeneousQuotient

/-!
# Actual Rees quotient schemes and their original proper projections

The original homogeneous presentation kernel is used without a radical.
No domain, nonzero family, Noetherianity or reducedness is assumed. Finiteness
is required only for properness; chart and literal graded Rees comparisons
are separate genuine constructions.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ReesPresentation
variable {A ι : Type u} [CommRing A] (g : ι → A)

/-- The actual quotient images of the original homogeneous components. -/
abbrev grading :=
  GradedQuotient.grading (MvPolynomial.homogeneousSubmodule ι A) (homogeneousKernel g).toIdeal

/-- The genuine projective scheme of the ORIGINAL homogeneous kernel quotient. -/
abbrev Scheme := Proj (grading g)

/-- The real homogeneous quotient morphism into the actual polynomial projective scheme. -/
def immersion : Scheme g ⟶ PolynomialProj.Scheme A ι :=
  GradedQuotient.quotientSchemeMap (MvPolynomial.homogeneousSubmodule ι A) (homogeneousKernel g)

/-- The actual original homogeneous Rees quotient gives a closed immersion. -/
instance instIsClosedImmersion_immersion : IsClosedImmersion (immersion g) := by
  unfold immersion
  infer_instance

/-- The whole original projection into the original coefficient scheme. -/
def projection : Scheme g ⟶ Spec (CommRingCat.of A) :=
  immersion g ≫ PolynomialProj.projection A ι

/-- Its factorization uses the actual original scheme morphisms on the whole scheme. -/
theorem immersion_comp_projection :
    immersion g ≫ PolynomialProj.projection A ι = projection g := rfl

/-- The actual original Rees scheme projection is proper for every finite family. -/
theorem projection_isProper [Finite ι] : IsProper (projection g) := by
  let : IsProper (PolynomialProj.projection A ι) := PolynomialProj.projection_isProper A ι
  unfold projection
  infer_instance

end EnvelopeProperty.ReesPresentation
