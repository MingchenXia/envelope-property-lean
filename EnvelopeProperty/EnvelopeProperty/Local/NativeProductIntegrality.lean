/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Algebra.PolynomialCoefficientIdeals
import EnvelopeProperty.AlgGeom.PrimeProjectiveQuotient
import EnvelopeProperty.Local.PLIdealSubvarietyModels

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The SAME original actual native polynomial-line product of an original
projective subvariety is integral over every original coefficient field. -/
theorem nativeProductModel_isIntegral : IsIntegral X.NativeProductModel := by
  let J := X.nativeHomogeneousIdeal.map (coefficientGradedMap (Polynomial.C : k →+* k[X]))
  let : J.toIdeal.IsPrime := by
    change (X.ideal.map (MvPolynomial.map (Polynomial.C : k →+* k[X]))).IsPrime
    exact isPrime_polynomialCoefficientIdeal X.ideal
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  have hj' : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k[X]) ∉ J.toIdeal := by
    intro h
    change MvPolynomial.X j ∈ X.ideal.map
      (MvPolynomial.map (Polynomial.C : k →+* k[X])) at h
    have hc := (mem_polynomialCoefficientIdeal_iff X.ideal (MvPolynomial.X j)).mp h 0
    exact hj (by simpa using hc)
  have hK : IsIntegral (nativeHomogeneousIdealSheaf J).subscheme :=
    GradedQuotient.isIntegral_quotientKernelSubscheme _ J (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X k[X] j) hj'
  let K := nativeHomogeneousIdealSheaf J
  let e := nativePolynomialLineProductIso k M
  let : IsIntegral K.subscheme := hK
  let : IsIntegral (pullback e.inv K.subschemeι) :=
    IsIntegral.of_isIso (inv (pullback.snd e.inv K.subschemeι))
  have hh : IsIntegral (K.comap e.inv).subscheme :=
    IsIntegral.of_isIso (K.comapIso e.inv).inv
  change IsIntegral X.nativeProductCutIdeal.subscheme
  rw [X.nativeProductCutIdeal_eq]
  exact hh

end EnvelopeProperty.ProjSubvariety
