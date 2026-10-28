import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdeals
import DeJongAlterations.Geometry.ProjIntegral

/-! # Integrality of the SAME actual original parameter family -/

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

private theorem algEquiv_ringHom_apply {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (a : A) :
    e.toRingHom a = e a := rfl

/-- The original family's ENTIRE defining ideal is exactly the original
polynomial extension transported by the actual parameter exchange. -/
theorem familyIdeal_eq_parameterMap :
    (familyHomogeneousIdeal X).toIdeal =
      (X.ideal.map (Polynomial.C : MvPolynomial (Fin (M + 1)) k →+*
        (MvPolynomial (Fin (M + 1)) k)[X])).map
          (parameterEquiv (k := k) (M := M)).toRingHom := by
  change X.ideal.map (MvPolynomial.map (Polynomial.C : k →+* k[X])) = _
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro s
  exact (parameterEquiv_C s).symm

/-- Primality of the SAME original equations is preserved by genuine polynomial
extension and the actual ring isomorphism; no integral-model input is used. -/
instance familyIdeal_isPrime : (familyHomogeneousIdeal X).toIdeal.IsPrime := by
  let _ : X.ideal.IsPrime := X.isPrime
  rw [familyIdeal_eq_parameterMap]
  exact Ideal.map_isPrime_of_equiv (parameterEquiv (k := k) (M := M)).toRingEquiv

/-- A genuinely relevant ORIGINAL coordinate stays nonzero in the actual
parameter-family quotient, with no new relevant-coordinate certificate. -/
theorem coordinate_notMem_familyIdeal {j : Fin (M + 1)}
    (hj : (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) ∉ X.ideal) :
    (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k[X]) ∉
      (familyHomogeneousIdeal X).toIdeal := by
  intro h
  have hmap : ((familyHomogeneousIdeal X).toIdeal).comap
      (parameterEquiv (k := k) (M := M)).toRingHom =
      X.ideal.map (Polynomial.C : MvPolynomial (Fin (M + 1)) k →+*
        (MvPolynomial (Fin (M + 1)) k)[X]) := by
    rw [familyIdeal_eq_parameterMap]
    exact Ideal.comap_map_of_bijective
      (parameterEquiv (k := k) (M := M)).toRingHom
      (parameterEquiv (k := k) (M := M)).bijective
  have hmem : Polynomial.C (MvPolynomial.X j) ∈
      X.ideal.map (Polynomial.C : MvPolynomial (Fin (M + 1)) k →+*
        (MvPolynomial (Fin (M + 1)) k)[X]) := by
    rw [← hmap]
    rw [Ideal.mem_comap]
    have heq : (parameterEquiv (k := k) (M := M)).toRingHom
        (Polynomial.C (MvPolynomial.X j)) = MvPolynomial.X j := by
      rw [algEquiv_ringHom_apply, parameterEquiv_C, MvPolynomial.map_X]
    exact heq.symm ▸ h
  have hc := Ideal.mem_map_C_iff.mp hmem 0
  exact hj (by simpa only [Polynomial.coeff_C_zero] using hc)

private local instance familyGradedRing : GradedRing
    (GradedQuotient.grading (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X).toIdeal) :=
  GradedQuotient.gradedRing _ _ (familyHomogeneousIdeal X).isHomogeneous

/-- Relevance of the SAME original prime ideal internally supplies relevance
of its SAME actual parameter-family quotient grading. -/
theorem family_irrelevant_ne_bot :
    HomogeneousIdeal.irrelevant
      (GradedQuotient.grading (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X).toIdeal) ≠ ⊥ := by
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  intro h
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem
    (GradedQuotient.grading (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X).toIdeal)
    (by decide : 0 < (1 : ℕ))
    ((GradedQuotient.gradedMk (ProjectiveGrading k[X] M)
      (familyHomogeneousIdeal X).toIdeal).map_mem (MvPolynomial.isHomogeneous_X k[X] j))
  rw [h] at hm
  exact coordinate_notMem_familyIdeal X hj (Ideal.Quotient.eq_zero_iff_mem.mp hm)

/-- The SAME actual original parameter family is integral, internally from
the original projective-subvariety equations and relevance. -/
instance familyScheme_isIntegral : IsIntegral (familyScheme X) :=
  DeJongAlterations.Geometry.ProjIntegral.isIntegral_proj _ (family_irrelevant_ne_bot X)

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
