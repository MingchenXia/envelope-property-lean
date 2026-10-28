/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeMultiplicativeProductNormality
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Actual reduced Laurent products, without irreducibility or normality

The genuine Laurent group is flat and geometrically reduced over ANY
original coefficient ring. Its original product with ANY reduced locally
Noetherian model is therefore reduced, with no perfection hypothesis.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjBerk
variable (R : Type u) [CommRing R]

/-- The SAME original Laurent group is geometrically reduced over ANY original commutative ring. -/
theorem nativeMultiplicativeGroup_isGeometricallyReduced :
    GeometricallyReduced (nativeMultiplicativeGroup R).hom := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  let : IsIntegral (pullback (nativeMultiplicativeGroup R).hom y) :=
    nativeMultiplicativeGroup_pullback_isIntegral y
  infer_instance

/-- The SAME original Laurent group structure morphism is genuinely flat over its ORIGINAL ring. -/
theorem nativeMultiplicativeGroup_isFlat : Flat (nativeMultiplicativeGroup R).hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr (inferInstanceAs (Module.Flat R R[T;T⁻¹]))

/-- The whole original Laurent product of ANY actual reduced locally Noetherian
scheme is reduced, with no irreducibility, normality or perfectness hypothesis. -/
theorem nativeMultiplicativeGroup_pullback_isReduced {X : Scheme.{u}}
    [IsReduced X] [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of R)) :
    IsReduced (pullback (nativeMultiplicativeGroup R).hom f) := by
  let : GeometricallyReduced (nativeMultiplicativeGroup R).hom :=
    nativeMultiplicativeGroup_isGeometricallyReduced R
  let : Flat (nativeMultiplicativeGroup R).hom := nativeMultiplicativeGroup_isFlat R
  infer_instance

end EnvelopeProperty.ProjBerk
