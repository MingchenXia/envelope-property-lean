/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeParameterFamily
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# The genuine geometric source of the Laurent family

The universal native Laurent family has the whole actual multiplicative-group
product as source, using actual polynomial tensor pushouts and whole native
Proj base change.  The transported morphism and its full unit-specialization
identity precede the action diagrams and the variety/blowup restrictions.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty

/-- The genuine product of the two independent Laurent parameter units. -/
def parameterLaurentProductUnit (R : Type u) [CommRing R] : R[T;T⁻¹][T;T⁻¹]ˣ :=
  parameterLaurentUnit R[T;T⁻¹] *
    Units.map (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]).toMonoidHom
      (parameterLaurentUnit R)

/-- The actual multiplicative-group multiplication ring map z ↦ w z, in
iterated Laurent coordinates. -/
def parameterLaurentMultiplicationHom {R : Type u} [CommRing R] :
    R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹] :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp LaurentPolynomial.C)
    (parameterLaurentProductUnit R)

end EnvelopeProperty

namespace EnvelopeProperty.ProjBerk
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

/-- The true polynomial coefficient square is an actual affine scheme pullback. -/
theorem isPullback_parameterPolynomialBaseChange (f : R →+* S) :
    IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom f)) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R[X] S[X] := Polynomial.algebra R S
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S R[X] S[X])).flip

/-- The entire native polynomial family is actual original-base coefficient
extension, rather than merely an identification on affine-valued points. -/
theorem isPullback_nativeParameterProduct (f : R →+* S) :
    IsPullback (nativeCoefficientMap (n := n) (Polynomial.mapRingHom f))
      (nativeStructureMap ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])))
      (nativeStructureMap ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_nativeCoefficientBaseChange (Polynomial.mapRingHom f)).paste_vert
    (isPullback_parameterPolynomialBaseChange f)

/-- The whole genuine coefficient-extended parameter-family product isomorphism. -/
def nativeParameterProductIso (f : R →+* S) :
    NativeProjectiveScheme S[X] n ≅
      pullback (nativeStructureMap (R := R[X]) (n := n) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
        (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_nativeParameterProduct (n := n) f).isoPullback

/-- The entire geometric product comparison has its actual first projection. -/
@[reassoc]
theorem nativeParameterProductIso_hom_fst (f : R →+* S) :
    (nativeParameterProductIso (n := n) f).hom ≫ pullback.fst _ _ =
      nativeCoefficientMap (Polynomial.mapRingHom f) :=
  (isPullback_nativeParameterProduct f).isoPullback_hom_fst

/-- The entire geometric product comparison has its actual coefficient projection. -/
@[reassoc]
theorem nativeParameterProductIso_hom_snd (f : R →+* S) :
    (nativeParameterProductIso (n := n) f).hom ≫ pullback.snd _ _ =
      nativeStructureMap ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])) :=
  (isPullback_nativeParameterProduct f).isoPullback_hom_snd

/-- A single actual morphism from the whole multiplicative-group product
implements universal parameter multiplication on native polynomial Proj. -/
def nativeParameterLaurentActionMorphism :
    pullback (nativeStructureMap (R := R[X]) (n := n) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* R[T;T⁻¹]))) ⟶
        NativeProjectiveScheme R[X] n :=
  (nativeParameterProductIso LaurentPolynomial.C).inv ≫ nativeParameterLaurentFamily

/-- Evaluating the single entire Laurent family at any actual extended
coefficient unit recovers the whole genuine native parameter-family morphism. -/
theorem nativeParameterLaurentFamily_evaluate (f : R →+* S) (u : Sˣ) :
    nativeCoefficientMap (n := n)
        (Polynomial.mapRingHom (LaurentPolynomial.eval₂ f u)) ≫
        nativeParameterLaurentFamily = nativeParameterFamilyMap f u := by
  change nativeCoefficientMap (Polynomial.mapRingHom (LaurentPolynomial.eval₂ f u)) ≫
    nativeCoefficientMap (parameterLaurentHom (R := R)) =
      nativeCoefficientMap (parameterUnitBaseChangeHom f u)
  rw [← nativeCoefficientMap_comp, parameterLaurentHom_evaluate]

/-- The universal unit identity diagram is an equality of whole native scheme
morphisms, rather than only equality at field-valued points. -/
theorem nativeParameterLaurentFamily_one :
    nativeCoefficientMap (n := n)
        (Polynomial.mapRingHom (LaurentPolynomial.eval₂ (RingHom.id R) 1)) ≫
        nativeParameterLaurentFamily = 𝟙 _ := by
  rw [nativeParameterLaurentFamily_evaluate, nativeParameterFamilyMap_id]

/-- The universal multiplication action diagram on the entire actual iterated
Laurent native coordinate scheme. -/
theorem nativeParameterLaurentFamily_mul :
    nativeCoefficientMap (n := n)
        (Polynomial.mapRingHom (parameterLaurentMultiplicationHom (R := R))) ≫
        nativeParameterLaurentFamily =
      nativeParameterLaurentFamily (R := R[T;T⁻¹]) ≫
        nativeParameterLaurentFamily (R := R) := by
  unfold parameterLaurentMultiplicationHom
  rw [nativeParameterLaurentFamily_evaluate]
  exact nativeParameterFamilyMap_comp
    (LaurentPolynomial.C : R →+* R[T;T⁻¹])
    (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹])
    (parameterLaurentUnit R) (parameterLaurentUnit R[T;T⁻¹])

end EnvelopeProperty.ProjBerk
