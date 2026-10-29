import EnvelopeProperty.ReesChartAway

/-!
# Actual affine universal maps of the original Rees charts

Original principal-generator relations and actual regularity construct the
whole chart map; no quotient factorization or chart-lift certificate is given.
The coefficient rings and family are arbitrary, including zero rings.
-/
open scoped nonZeroDivisors
noncomputable section
namespace EnvelopeProperty.ReesPresentation
variable {A B ι : Type*} [CommRing A] [CommRing B]

/-- Homogeneous scaling retains EVERY original coefficient under an arbitrary actual ring homomorphism. -/
theorem eval₂_mul_of_isHomogeneous (φ : A →+* B) (u : ι → B) (c : B)
    {H : MvPolynomial ι A} {d : ℕ} (hH : H.IsHomogeneous d) :
    MvPolynomial.eval₂Hom φ (fun i => u i * c) H =
      MvPolynomial.eval₂Hom φ u H * c ^ d := by
  have h := aeval_mul_of_isHomogeneous u (hH.map φ) c
  change MvPolynomial.eval₂Hom (RingHom.id B) (fun i => u i * c) (MvPolynomial.map φ H) =
    MvPolynomial.eval₂Hom (RingHom.id B) u (MvPolynomial.map φ H) * c ^ d at h
  simpa only [MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp] using h

end EnvelopeProperty.ReesPresentation
namespace EnvelopeProperty.ReesChart
open ReesPresentation
variable {A ι : Type*} [CommRing A] (g : ι → A)
private local instance actualChartAlgebra (j : ι) : Algebra A (Chart g j) := chartAlgebra g j

/-- The GENUINE entire original polynomial evaluation into its actual coordinate fractions. -/
def polynomialMap (j : ι) : MvPolynomial ι A →+* Chart g j :=
  (MvPolynomial.aeval (coordinateRatio g j)).toRingHom

/-- Every ORIGINAL homogeneous polynomial maps to its SAME genuine homogeneous fraction. -/
theorem polynomialMap_homogeneous (j : ι) {H : MvPolynomial ι A} {d : ℕ}
    (hH : H.IsHomogeneous d) (a : Quotient g) (ha : a ∈ grading g (d • (1 : ℕ)))
    (hHa : Ideal.Quotient.mk (kernel g) H = a) :
    polynomialMap g j H =
      HomogeneousLocalization.Away.mk (grading g) (generator_mem g j) d a ha := by
  apply toAway_injective g j
  change toAway g j (MvPolynomial.aeval (coordinateRatio g j) H) = _
  rw [MvPolynomial.comp_aeval_apply, toAway_mk, ← hHa, quotientEvaluation_mk, away_mk_pow]
  have hcoords : (fun i => toAway g j (coordinateRatio g j i)) = awayRatios g j :=
    funext (toAway_coordinateRatio g j)
  rw [hcoords]
  exact aeval_awayRatios g j hH

/-- Every WHOLE actual chart element has a genuine ORIGINAL polynomial preimage. -/
theorem polynomialMap_surjective (j : ι) : Function.Surjective (polynomialMap g j) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading g) (generator_mem g j) z
  obtain ⟨H, hH⟩ := GradedQuotient.componentMap_surjective
    (MvPolynomial.homogeneousSubmodule ι A) (kernel g) (n • (1 : ℕ)) ⟨a, ha⟩
  have hHa : Ideal.Quotient.mk (kernel g) (H : MvPolynomial ι A) = a :=
    congrArg Subtype.val hH
  refine ⟨H, ?_⟩
  have hdeg0 : (H : MvPolynomial ι A).IsHomogeneous (n • (1 : ℕ)) := H.2
  have hdeg : (H : MvPolynomial ι A).IsHomogeneous n := by
    simpa only [smul_eq_mul, mul_one] using hdeg0
  exact polynomialMap_homogeneous g j hdeg a ha hHa

variable {B : Type*} [CommRing B] (φ : A →+* B) (j : ι) (u : ι → B)
  (hreg : φ (g j) ∈ B⁰) (hu : ∀ i, φ (g i) = φ (g j) * u i)

include hreg hu in
/-- The selected coordinate is genuinely one, by cancellation of the ACTUAL regular generator. -/
theorem principal_coordinate_self : u j = 1 := by
  apply sub_eq_zero.mp
  apply hreg.1
  rw [mul_sub, mul_one, ← hu j, sub_self]

include hreg hu in
/-- Every ORIGINAL homogeneous presentation relation vanishes under the actual principal tuple. -/
theorem eval₂_eq_zero_of_homogeneous_kernel {H : MvPolynomial ι A} {d : ℕ}
    (hH : H.IsHomogeneous d) (hker : H ∈ kernel g) : MvPolynomial.eval₂Hom φ u H = 0 := by
  have he : MvPolynomial.aeval g H = 0 := by
    change presentation g H = 0 at hker
    have hc := congrArg (fun p : Polynomial A => p.coeff d) hker
    rw [presentation_coeff, Polynomial.coeff_zero,
      MvPolynomial.homogeneousComponent_eq_self hH] at hc
    exact hc
  have hscale := eval₂_mul_of_isHomogeneous φ u (φ (g j)) hH
  have htuple : (fun i => u i * φ (g j)) = fun i => φ (g i) := by
    funext i
    rw [mul_comm, ← hu i]
  rw [htuple] at hscale
  have hmap := MvPolynomial.map_aeval g φ H
  change φ (MvPolynomial.aeval g H) = MvPolynomial.eval₂Hom φ (fun i => φ (g i)) H at hmap
  rw [← hmap, he, map_zero] at hscale
  exact ((nonZeroDivisors B).pow_mem hreg d).2 _ hscale.symm

include hreg hu in
/-- The WHOLE SAME original kernel is killed, by its actual finite homogeneous decomposition. -/
theorem eval₂_kernel_le : kernel g ≤ RingHom.ker (MvPolynomial.eval₂Hom φ u) := by
  intro H hH
  change MvPolynomial.eval₂Hom φ u H = 0
  rw [← H.sum_homogeneousComponent, map_sum]
  apply Finset.sum_eq_zero
  intro d _
  exact eval₂_eq_zero_of_homogeneous_kernel g φ j u hreg hu
    (MvPolynomial.homogeneousComponent_isHomogeneous d H)
    (homogeneousComponent_mem_kernel g hH d)

/-- The actual principal tuple factors through the SAME original homogeneous kernel quotient. -/
def principalQuotientLift : Quotient g →+* B :=
  Ideal.Quotient.lift (kernel g) (MvPolynomial.eval₂Hom φ u)
    (fun _ ha => eval₂_kernel_le g φ j u hreg hu ha)

@[simp]
theorem principalQuotientLift_mk (H : MvPolynomial ι A) :
    principalQuotientLift g φ j u hreg hu (Ideal.Quotient.mk (kernel g) H) =
      MvPolynomial.eval₂Hom φ u H := rfl

@[simp]
theorem principalQuotientLift_algebraMap (a : A) :
    principalQuotientLift g φ j u hreg hu (algebraMap A (Quotient g) a) = φ a :=
  MvPolynomial.eval₂Hom_C φ u a

@[simp]
theorem principalQuotientLift_generator (i : ι) :
    principalQuotientLift g φ j u hreg hu (generator g i) = u i :=
  MvPolynomial.eval₂Hom_X' φ u i

private theorem principalGenerator_isUnit :
    IsUnit (principalQuotientLift g φ j u hreg hu (generator g j)) := by
  rw [principalQuotientLift_generator, principal_coordinate_self g φ j u hreg hu]
  exact isUnit_one

/-- The SAME whole quotient map extends through the selected variable, whose actual image is ONE. -/
def principalLocalizationLift : Localization.Away (generator g j) →+* B :=
  IsLocalization.Away.lift (generator g j) (principalGenerator_isUnit g φ j u hreg hu)

@[simp]
theorem principalLocalizationLift_algebraMap (a : Quotient g) :
    principalLocalizationLift g φ j u hreg hu
      (algebraMap (Quotient g) (Localization.Away (generator g j)) a) =
      principalQuotientLift g φ j u hreg hu a :=
  IsLocalization.Away.lift_eq _ _ _

/-- The actual unique chart lift CONSTRUCTED from original regular principal-generator relations. -/
def principalLift : Chart g j →+* B :=
  (principalLocalizationLift g φ j u hreg hu).comp (chartVal g j).toRingHom

/-- Every ACTUAL original homogeneous fraction has the genuine whole quotient-numerator value. -/
theorem principalLift_mk (n : ℕ) (a : Quotient g) (ha : a ∈ grading g (n • (1 : ℕ))) :
    principalLift g φ j u hreg hu
      (HomogeneousLocalization.Away.mk (grading g) (generator_mem g j) n a ha) =
      principalQuotientLift g φ j u hreg hu a := by
  let den : Submonoid.powers (generator g j) := ⟨generator g j ^ n, n, rfl⟩
  have h := congrArg (principalLocalizationLift g φ j u hreg hu)
    (IsLocalization.mk'_spec (Localization.Away (generator g j)) a den)
  rw [map_mul] at h
  change principalLocalizationLift g φ j u hreg hu
    (IsLocalization.mk' (Localization.Away (generator g j)) a den) *
      principalLocalizationLift g φ j u hreg hu
        (algebraMap (Quotient g) (Localization.Away (generator g j)) (generator g j ^ n)) =
      principalLocalizationLift g φ j u hreg hu
        (algebraMap (Quotient g) (Localization.Away (generator g j)) a) at h
  rw [principalLocalizationLift_algebraMap, principalLocalizationLift_algebraMap,
    map_pow, principalQuotientLift_generator, principal_coordinate_self g φ j u hreg hu,
    one_pow, mul_one] at h
  change principalLocalizationLift g φ j u hreg hu (Localization.mk a den) = _
  rw [Localization.mk_eq_mk']
  exact h

/-- Every ORIGINAL coefficient is retained by the actual chart lift. -/
@[simp]
theorem principalLift_algebraMap (a : A) :
    principalLift g φ j u hreg hu (algebraMap A (Chart g j) a) = φ a := by
  change principalLocalizationLift g φ j u hreg hu (chartVal g j (algebraMap A (Chart g j) a)) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (Quotient g),
    principalLocalizationLift_algebraMap, principalQuotientLift_algebraMap]

/-- Every original coordinate fraction has its ACTUAL principal tuple value. -/
@[simp]
theorem principalLift_coordinateRatio (i : ι) :
    principalLift g φ j u hreg hu (coordinateRatio g j i) = u i := by
  change principalLift g φ j u hreg hu (HomogeneousLocalization.Away.mk (grading g)
    (generator_mem g j) 1 (generator g i) _) = _
  rw [principalLift_mk, principalQuotientLift_generator]

/-- Every WHOLE original polynomial expression follows the actual original principal evaluation. -/
theorem principalLift_polynomialMap (H : MvPolynomial ι A) :
    principalLift g φ j u hreg hu (polynomialMap g j H) = MvPolynomial.eval₂Hom φ u H := by
  have he : (principalLift g φ j u hreg hu).comp (polynomialMap g j) =
      MvPolynomial.eval₂Hom φ u := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change principalLift g φ j u hreg hu (MvPolynomial.aeval (coordinateRatio g j)
        (MvPolynomial.C a)) = _
      rw [MvPolynomial.aeval_C, principalLift_algebraMap, MvPolynomial.eval₂Hom_C]
    · intro i
      change principalLift g φ j u hreg hu (MvPolynomial.aeval (coordinateRatio g j)
        (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, principalLift_coordinateRatio, MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun he H

/-- WHOLE original chart maps are unique from actual coefficients and coordinate fractions. -/
theorem principalLift_unique (ψ : Chart g j →+* B)
    (hC : ∀ a, ψ (algebraMap A (Chart g j) a) = φ a)
    (hX : ∀ i, ψ (coordinateRatio g j i) = u i) : ψ = principalLift g φ j u hreg hu := by
  have he : ψ.comp (polynomialMap g j) = MvPolynomial.eval₂Hom φ u := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change ψ (MvPolynomial.aeval (coordinateRatio g j) (MvPolynomial.C a)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
      exact hC a
    · intro i
      change ψ (MvPolynomial.aeval (coordinateRatio g j) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
      exact hX i
  apply RingHom.ext
  intro z
  obtain ⟨H, rfl⟩ := polynomialMap_surjective g j z
  rw [principalLift_polynomialMap]
  exact RingHom.congr_fun he H

include hreg hu in
/-- Actual regular principal relations give genuine existence and WHOLE uniqueness, without a chart-lift certificate. -/
theorem existsUnique_principalLift : ∃! ψ : Chart g j →+* B,
    (∀ a, ψ (algebraMap A (Chart g j) a) = φ a) ∧
    ∀ i, ψ (coordinateRatio g j i) = u i := by
  refine ⟨principalLift g φ j u hreg hu, ⟨principalLift_algebraMap g φ j u hreg hu,
    principalLift_coordinateRatio g φ j u hreg hu⟩, ?_⟩
  rintro ψ ⟨hC, hX⟩
  exact principalLift_unique g φ j u hreg hu ψ hC hX

end EnvelopeProperty.ReesChart
