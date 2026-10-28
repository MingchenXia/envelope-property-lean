import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsGeometry
import Hironaka.Scheme.IdealSheaf.StalkLe

/-! # Nonzero generic stalks of the SAME original obstacle scheme sequence -/

open CategoryTheory AlgebraicGeometry MvPolynomial TopologicalSpace
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
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (a : A) : e.toRingHom a = e a := rfl

/-- The actual parameter family keeps the ENTIRE original polynomial
coefficient membership criterion for its defining ideal. -/
theorem parameterEquiv_mem_familyIdeal_iff
    (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    parameterEquiv g ∈ (familyHomogeneousIdeal X).toIdeal ↔
      ∀ l : ℕ, g.coeff l ∈ X.ideal := by
  rw [← algEquiv_ringHom_apply (parameterEquiv (k := k) (M := M)) g]
  change g ∈ ((familyHomogeneousIdeal X).toIdeal).comap
    (parameterEquiv (k := k) (M := M)).toRingHom ↔ _
  rw [familyIdeal_eq_parameterMap]
  have hh := Ideal.comap_map_of_bijective
    (parameterEquiv (k := k) (M := M)).toRingHom
    (parameterEquiv (k := k) (M := M)).bijective
    (I := X.ideal.map (Polynomial.C : MvPolynomial (Fin (M + 1)) k →+*
      (MvPolynomial (Fin (M + 1)) k)[X]))
  rw [hh]
  exact Ideal.mem_map_C_iff

private local instance familyGradedRing : GradedRing
    (GradedQuotient.grading (ProjectiveGrading k[X] M) (familyHomogeneousIdeal X).toIdeal) :=
  GradedQuotient.gradedRing _ _ (familyHomogeneousIdeal X).isHomogeneous

/-- The true zero homogeneous prime is the SAME actual family's generic point. -/
theorem family_genericPoint_eq_zeroPoint :
    genericPoint (familyScheme X) =
      DeJongAlterations.Geometry.ProjIntegral.zeroPoint _ (family_irrelevant_ne_bot X) := by
  apply (genericPoint_spec (familyScheme X)).eq
  exact DeJongAlterations.Geometry.ProjIntegral.isGenericPoint_of_asHomogeneousIdeal_eq_bot _ _ rfl

/-- The original whole inclusion sends the actual zero homogeneous prime
to exactly the prime of the original defining equations. -/
theorem familyInclusion_zeroPoint_mem_iff
    (F : MvPolynomial (Fin (M + 1)) k[X]) :
    F ∈ (familyInclusion X
      (DeJongAlterations.Geometry.ProjIntegral.zeroPoint _ (family_irrelevant_ne_bot X))).asHomogeneousIdeal ↔
      F ∈ (familyHomogeneousIdeal X).toIdeal := by
  change Ideal.Quotient.mk (familyHomogeneousIdeal X).toIdeal F = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- An ORIGINAL lower obstacle bound internally proves that the SAME whole
scheme ideal is a unit at the original generic point, in EVERY index. -/
theorem schemeIdeal_generic_stalk_eq_top (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m : ℕ) :
    (schemeIdeal X d φ m).stalkIdeal (genericPoint (familyScheme X)) = ⊤ := by
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  let N : ℕ := ⌈-((m : ℝ) * C)⌉₊
  let g : (MvPolynomial (Fin (M + 1)) k)[X] :=
    Polynomial.C (MvPolynomial.X j ^ (m * d)) * Polynomial.X ^ N
  have hg : g ∈ X.obstacleSpace d φ m :=
    C_X_pow_mul_X_pow_mem_obstacleSpace (neg_ceil_le_mul_obstacle hC m) j
  have hnon : parameterEquiv g ∉ (familyHomogeneousIdeal X).toIdeal := by
    intro h
    have hc := (parameterEquiv_mem_familyIdeal_iff X g).mp h N
    change (Polynomial.C (MvPolynomial.X j ^ (m * d)) * Polynomial.X ^ N).coeff N ∈ X.ideal at hc
    rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
    exact hj (X.isPrime.mem_of_pow_mem (m * d) hc)
  apply Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support
  rw [family_genericPoint_eq_zeroPoint, schemeIdeal, Scheme.IdealSheafData.support_comap]
  change familyInclusion X _ ∉ (ambientSchemeIdeal X d φ m).support
  intro hs
  have hsupport := GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus
    (ProjectiveGrading k[X] M) (homogeneousObstacleIdeal X d φ m)
  have h := Eq.mp (congrArg (fun U : Set (Proj (ProjectiveGrading k[X] M)) =>
      (familyInclusion X
        (DeJongAlterations.Geometry.ProjIntegral.zeroPoint _ (family_irrelevant_ne_bot X))) ∈ U)
      hsupport) hs
  have hm : parameterEquiv g ∈ (homogeneousObstacleIdeal X d φ m).toIdeal :=
    Ideal.mem_map_of_mem (parameterEquiv (k := k) (M := M)).toRingHom
      (mem_obstacleIdeal_of_mem hg)
  exact hnon ((familyInclusion_zeroPoint_mem_iff X _).mp (h hm))

/-- No generic nonvanishing premise is required for the actual original
obstacle scheme sequence, even at index zero. -/
theorem schemeIdeal_generic_stalk_ne_bot (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m : ℕ) :
    (schemeIdeal X d φ m).stalkIdeal (genericPoint (familyScheme X)) ≠ ⊥ := by
  rw [schemeIdeal_generic_stalk_eq_top X d φ hC m]
  exact top_ne_bot

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
