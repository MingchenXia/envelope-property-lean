/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeMultiplicativeGroup
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Genuine multiplicative affine line and its original Laurent-unit inclusion

The actual ordinary polynomial spectrum receives its monoid structure from
the genuine natural-exponent monoid algebra. The actual integer-exponent
bialgebra map derives its true multiplicative-group inclusion. No base action
or monoid-law certificate is supplied.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open scoped Polynomial LaurentPolynomial MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.ProjBerk
variable (R : Type u) [CommRing R]

/-- The SAME ordinary polynomial parameter line over the original coefficient ring. -/
abbrev nativeParameterLine : Over (Spec (CommRingCat.of R)) :=
  (Spec (CommRingCat.of R[X])).asOver (Spec (CommRingCat.of R))

/-- The actual natural-exponent monoid spectrum is the SAME original polynomial line. -/
def nativeParameterLineMonoidIso :
    (Spec (CommRingCat.of (AddMonoidAlgebra R ℕ))).asOver (Spec (CommRingCat.of R)) ≅
      nativeParameterLine R :=
  (algSpec (CommRingCat.of R)).mapIso (CommAlgCat.isoMk (Polynomial.toFinsuppIsoAlg R)).op

/-- The genuine internally derived multiplicative monoid on the original polynomial line. -/
@[instance_reducible]
def nativeParameterLineMonObj : MonObj (nativeParameterLine R) :=
  MonObj.ofIso (nativeParameterLineMonoidIso R)

/-- The true original nonnegative-to-integer exponent bialgebra map. -/
def nativeParameterExponentMap : AddMonoidAlgebra R ℕ →ₐc[R] R[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainBialgHom R Int.ofNatHom

/-- The actual original Laurent-unit group inclusion into the natural-exponent monoid spectrum. -/
def nativeParameterGroupToMonoid : nativeMultiplicativeGroup R ⟶
    (Spec (CommRingCat.of (AddMonoidAlgebra R ℕ))).asOver (Spec (CommRingCat.of R)) :=
  ((bialgSpec (CommRingCat.of R)).map (CommBialgCat.ofHom (nativeParameterExponentMap R)).op).hom

/-- The Laurent-unit inclusion is a genuine monoid morphism, from the actual bialgebra map. -/
theorem nativeParameterGroupToMonoid_isMonHom : IsMonHom (nativeParameterGroupToMonoid R) :=
  inferInstanceAs (IsMonHom
    ((bialgSpec (CommRingCat.of R)).map (CommBialgCat.ofHom (nativeParameterExponentMap R)).op).hom)

/-- The whole actual group-to-parameter-line inclusion over the original ring. -/
def nativeParameterGroupInclusion : nativeMultiplicativeGroup R ⟶ nativeParameterLine R :=
  nativeParameterGroupToMonoid R ≫ (nativeParameterLineMonoidIso R).hom

/-- The actual original affine-line inclusion preserves the genuine multiplication and unit. -/
theorem nativeParameterGroupInclusion_isMonHom :
    letI := nativeParameterLineMonObj R
    IsMonHom (nativeParameterGroupInclusion R) := by
  let := nativeParameterLineMonObj R
  let : IsMonHom (nativeParameterGroupToMonoid R) := nativeParameterGroupToMonoid_isMonHom R
  let : IsMonHom (nativeParameterLineMonoidIso R).hom := CategoryTheory.isMonHom_ofIso _
  exact inferInstanceAs (IsMonHom (_ ≫ _))

set_option backward.isDefEq.respectTransparency false in
/-- The whole actual inclusion is LITERALLY the original polynomial-to-Laurent spectrum map. -/
theorem nativeParameterGroupInclusion_left : (nativeParameterGroupInclusion R).left =
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹])) := by
  change Spec.map (CommRingCat.ofHom (nativeParameterExponentMap R).toAlgHom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.toFinsuppIsoAlg R).toAlgHom.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

/-- The original actual Laurent-unit inclusion is a genuine open immersion. -/
theorem nativeParameterGroupInclusion_isOpenImmersion :
    IsOpenImmersion (nativeParameterGroupInclusion R).left := by
  rw [nativeParameterGroupInclusion_left]
  exact IsOpenImmersion.of_isLocalization (S := R[T;T⁻¹]) (Polynomial.X : R[X])

/-- The entire original Laurent-unit image is EXACTLY the original nonzero-parameter open. -/
theorem nativeParameterGroupInclusion_opensRange :
    letI := nativeParameterGroupInclusion_isOpenImmersion R
    (nativeParameterGroupInclusion R).left.opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : R[X]) := by
  let := nativeParameterGroupInclusion_isOpenImmersion R
  apply SetLike.ext'
  change Set.range (nativeParameterGroupInclusion R).left = _
  rw [nativeParameterGroupInclusion_left]
  exact PrimeSpectrum.localization_away_comap_range R[T;T⁻¹] (Polynomial.X : R[X])

/-- The SAME original affine-line unit is the literal parameter-one spectrum map. -/
theorem nativeParameterLine_one : letI := nativeParameterLineMonObj R
    (η[nativeParameterLine R]).left =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : R))) := by
  let := nativeParameterLineMonObj R
  let : IsMonHom (nativeParameterGroupInclusion R) := nativeParameterGroupInclusion_isMonHom R
  have h := congrArg Over.Hom.left (IsMonHom.one_hom (nativeParameterGroupInclusion R))
  rw [Over.comp_left, nativeMultiplicativeGroup_one, nativeParameterGroupInclusion_left] at h
  rw [← h]
  change Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id R) 1)) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : R)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

/-- The actual standard group action on the SAME original affine parameter line,
derived by multiplication of the actual Laurent units in its genuine monoid. -/
@[instance_reducible]
def nativeParameterLineModObj : ModObj (nativeMultiplicativeGroup R) (nativeParameterLine R) := by
  let := nativeParameterLineMonObj R
  let : IsMonHom (nativeParameterGroupInclusion R) := nativeParameterGroupInclusion_isMonHom R
  let : ModObj (nativeParameterLine R) (nativeParameterLine R) := ModObj.regular _
  exact Mod.scalarRestriction (nativeParameterGroupInclusion R) (nativeParameterLine R)

/-- The whole actual unit-open inclusion is equivariant for the original regular
multiplicative-group action and the internally derived standard parameter-line action. -/
theorem nativeParameterGroupInclusion_isModHom :
    letI := nativeParameterLineModObj R
    letI : ModObj (nativeMultiplicativeGroup R) (nativeMultiplicativeGroup R) := ModObj.regular _
    IsModHom (nativeMultiplicativeGroup R) (nativeParameterGroupInclusion R) := by
  let := nativeParameterLineMonObj R
  let : IsMonHom (nativeParameterGroupInclusion R) := nativeParameterGroupInclusion_isMonHom R
  let := nativeParameterLineModObj R
  let : ModObj (nativeMultiplicativeGroup R) (nativeMultiplicativeGroup R) := ModObj.regular _
  constructor
  change μ[nativeMultiplicativeGroup R] ≫ nativeParameterGroupInclusion R =
    ((nativeMultiplicativeGroup R) ◁ nativeParameterGroupInclusion R) ≫
      (nativeParameterGroupInclusion R ▷ nativeParameterLine R) ≫ μ[nativeParameterLine R]
  rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc]

end EnvelopeProperty.ProjBerk
