import EnvelopeProperty.Projective.SubvarietyJm
import EnvelopeProperty.Projective.NativeQuotient

/-! # The original obstacle ideals over the original parameter coefficient ring -/

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety
namespace MultiplierBaseIdeals
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- Exchange only the native polynomial presentation: every original x and
parameter t is retained. -/
def parameterEquiv : (MvPolynomial (Fin (M + 1)) k)[X] ≃ₐ[k]
    MvPolynomial (Fin (M + 1)) k[X] :=
  (MvPolynomial.optionEquivLeft k (Fin (M + 1))).symm.trans
    (MvPolynomial.optionEquivRight k (Fin (M + 1)))

/-- The original homogeneous form is coefficient-extended without changing it. -/
theorem parameterEquiv_C (s : MvPolynomial (Fin (M + 1)) k) :
    parameterEquiv (Polynomial.C s) = MvPolynomial.map Polynomial.C s := by
  induction s using MvPolynomial.induction_on with
  | C a => simp [parameterEquiv]
  | add s t hs ht => simp only [map_add, hs, ht]
  | mul_X s i hs =>
    rw [Polynomial.C_mul, map_mul, hs]
    simp [parameterEquiv]

/-- The SAME original parameter becomes the literal coefficient parameter. -/
theorem parameterEquiv_X :
    parameterEquiv (Polynomial.X : (MvPolynomial (Fin (M + 1)) k)[X]) =
      MvPolynomial.C (Polynomial.X : k[X]) := by
  simp [parameterEquiv]

/-- Every original bihomogeneous generator keeps its original form and
original parameter exponent. -/
theorem parameterEquiv_monomial (l : ℕ) (s : MvPolynomial (Fin (M + 1)) k) :
    parameterEquiv (Polynomial.monomial l s) =
      MvPolynomial.map Polynomial.C s * MvPolynomial.C ((Polynomial.X : k[X]) ^ l) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    parameterEquiv_C, parameterEquiv_X, ← map_pow]

/-- The ENTIRE original obstacle ideal, with the parameter moved only into
the coefficient ring. -/
def parameterObstacleIdeal (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    Ideal (MvPolynomial (Fin (M + 1)) k[X]) :=
  (X.obstacleIdeal d φ m).map (parameterEquiv (k := k) (M := M)).toRingHom

/-- The original bihomogeneous generator theorem internally proves genuine
homogeneity of the complete original ideal over k[t]. -/
theorem parameterObstacleIdeal_isHomogeneous (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    (parameterObstacleIdeal X d φ m).IsHomogeneous
      (ProjBerk.ProjectiveGrading k[X] M) := by
  rw [parameterObstacleIdeal, obstacleIdeal_eq_span_monomial, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨g, ⟨hg, l, s, rfl⟩, rfl⟩
  have hs : s.IsHomogeneous (m * d) := by simpa using hg.1 l
  refine ⟨m * d, ?_⟩
  change parameterEquiv (Polynomial.monomial l s) ∈
    ProjBerk.ProjectiveGrading k[X] M (m * d)
  rw [parameterEquiv_monomial]
  have hh := (hs.map (Polynomial.C : k →+* Polynomial k)).C_mul
    ((Polynomial.X : Polynomial k) ^ l)
  change (MvPolynomial.map Polynomial.C s *
    MvPolynomial.C ((Polynomial.X : k[X]) ^ l)).IsHomogeneous (m * d)
  simpa only [mul_comm] using hh

/-- The actual original homogeneous ideal used by the native Proj quotient. -/
def homogeneousObstacleIdeal (d : ℕ) (φ : X.an → ℝ) (m : ℕ) :
    HomogeneousIdeal (ProjBerk.ProjectiveGrading k[X] M) :=
  ⟨parameterObstacleIdeal X d φ m, parameterObstacleIdeal_isHomogeneous X d φ m⟩

/-- The native homogeneous obstacle sequence is internally graded. -/
theorem homogeneousObstacleIdeal_mul_le (d : ℕ) (φ : X.an → ℝ) (m r : ℕ) :
    homogeneousObstacleIdeal X d φ m * homogeneousObstacleIdeal X d φ r ≤
      homogeneousObstacleIdeal X d φ (m + r) := by
  change (parameterObstacleIdeal X d φ m) * (parameterObstacleIdeal X d φ r) ≤
    parameterObstacleIdeal X d φ (m + r)
  unfold parameterObstacleIdeal
  rw [← Ideal.map_mul]
  exact Ideal.map_mono (obstacleIdeal_mul_le m r)

/-- The SAME actual original zeroth homogeneous ideal is the unit ideal. -/
theorem homogeneousObstacleIdeal_zero (d : ℕ) (φ : X.an → ℝ) :
    homogeneousObstacleIdeal X d φ 0 = ⊤ := by
  apply HomogeneousIdeal.toIdeal_injective
  change parameterObstacleIdeal X d φ 0 = ⊤
  rw [parameterObstacleIdeal, obstacleIdeal_zero, Ideal.map_top]

end MultiplierBaseIdeals
end EnvelopeProperty.ProjSubvariety
