import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPadding

/-! # The actual projective coefficient morphism for evaluation at zero is closed -/

noncomputable section
open AlgebraicGeometry CategoryTheory
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoefficientImmersion
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Surjectivity of the ACTUAL original coefficient ring map proves closedness
of the SAME actual native projective coefficient morphism. -/
theorem projectiveCoefficientMap_isClosedImmersion_of_surjective
    {R A : Type u} [CommRing R] [CommRing A] (r : R →+* A)
    (hr : Function.Surjective r) (m : ℕ) :
    IsClosedImmersion (projectiveCoefficientMap r m) := by
  have hpoly : Function.Surjective (polynomialCoefficientMap r m) := by
    change Function.Surjective (MvPolynomial.map r)
    exact MvPolynomial.map_surjective r hr
  exact DeJongAlterations.Geometry.ProjClosedImmersion.isClosedImmersion_map _ hpoly _

/-- The SAME original projective evaluation-at-zero morphism is closed,
with its ACTUAL original coefficient surjection derived internally. -/
theorem projectiveEvalZeroMap_isClosedImmersion (k : Type u) [CommRing k] (m : ℕ) :
    IsClosedImmersion (projectiveCoefficientMap (Polynomial.evalRingHom (0 : k)) m) := by
  apply projectiveCoefficientMap_isClosedImmersion_of_surjective
  intro a
  refine ⟨Polynomial.C a, ?_⟩
  change Polynomial.eval 0 (Polynomial.C a) = a
  exact Polynomial.eval_C

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoefficientImmersion
