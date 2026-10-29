import EnvelopeProperty.ReesChart
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Actual Rees degree-zero charts over arbitrary commutative rings

The true chart maps injectively into the ORIGINAL coefficient localization.
No domain, nonzero/regular coefficient, finite family or fraction field is
assumed. Original localization annihilators retain the SAME presentation kernel.
-/
open scoped nonZeroDivisors
noncomputable section
namespace EnvelopeProperty.ReesChart
open ReesPresentation
variable {A ι : Type*} [CommRing A] (g : ι → A)

private local instance originalChartAlgebra (j : ι) : Algebra A (Chart g j) := chartAlgebra g j

private theorem generatorAway_isUnit (j : ι) :
    IsUnit (((Algebra.ofId A (Localization.Away (g j))).comp (quotientEvaluation g))
      (generator g j)) := by
  change IsUnit (algebraMap A (Localization.Away (g j)) (quotientEvaluation g (generator g j)))
  rw [quotientEvaluation_generator]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Actual quotient evaluation extends to its genuine selected-coordinate localization over ANY ring. -/
def localizationToAway (j : ι) : Localization.Away (generator g j) →ₐ[A] Localization.Away (g j) :=
  IsLocalization.Away.liftAlgHom
    (f := (Algebra.ofId A (Localization.Away (g j))).comp (quotientEvaluation g))
    (generator g j) (generatorAway_isUnit g j)

/-- Every original quotient element follows the SAME entire evaluation map. -/
@[simp]
theorem localizationToAway_algebraMap (j : ι) (a : Quotient g) :
    localizationToAway g j (algebraMap (Quotient g) (Localization.Away (generator g j)) a) =
      algebraMap A (Localization.Away (g j)) (quotientEvaluation g a) := by
  change IsLocalization.Away.lift (generator g j) (generatorAway_isUnit g j)
    (algebraMap (Quotient g) (Localization.Away (generator g j)) a) = _
  rw [IsLocalization.Away.lift_eq]
  rfl

/-- The GENUINE whole chart homomorphism into the ORIGINAL coefficient localization. -/
def toAway (j : ι) : Chart g j →ₐ[A] Localization.Away (g j) :=
  (localizationToAway g j).comp (chartVal g j)

/-- Every homogeneous fraction has the ORIGINAL numerator/denominator value, even for zero divisors. -/
theorem toAway_mk (j : ι) (n : ℕ) (a : Quotient g) (ha : a ∈ grading g (n • (1 : ℕ))) :
    toAway g j (HomogeneousLocalization.Away.mk (grading g) (generator_mem g j) n a ha) =
      IsLocalization.mk' (Localization.Away (g j)) (quotientEvaluation g a)
        (⟨g j ^ n, n, rfl⟩ : Submonoid.powers (g j)) := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  let den : Submonoid.powers (generator g j) := ⟨generator g j ^ n, n, rfl⟩
  have h := congrArg (localizationToAway g j)
    (IsLocalization.mk'_spec (Localization.Away (generator g j)) a den)
  rw [map_mul] at h
  change localizationToAway g j (IsLocalization.mk' (Localization.Away (generator g j)) a den) *
    localizationToAway g j (algebraMap (Quotient g)
      (Localization.Away (generator g j)) (generator g j ^ n)) =
    localizationToAway g j (algebraMap (Quotient g)
      (Localization.Away (generator g j)) a) at h
  rw [localizationToAway_algebraMap, localizationToAway_algebraMap,
    map_pow, quotientEvaluation_generator] at h
  change localizationToAway g j (Localization.mk a den) * _ = _
  rw [Localization.mk_eq_mk']
  exact h

/-- WHOLE chart injection follows from ORIGINAL localization torsion and the SAME homogeneous kernel. -/
theorem toAway_injective (j : ι) : Function.Injective (toAway g j) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading g) (generator_mem g j) z
  obtain ⟨H, hH⟩ := GradedQuotient.componentMap_surjective
    (MvPolynomial.homogeneousSubmodule ι A) (kernel g) (n • (1 : ℕ)) ⟨a, ha⟩
  have hHa : Ideal.Quotient.mk (kernel g) (H : MvPolynomial ι A) = a :=
    congrArg Subtype.val hH
  rw [toAway_mk] at hz
  obtain ⟨m, hm⟩ := (IsLocalization.mk'_eq_zero_iff (S := Localization.Away (g j))
    (quotientEvaluation g a) (⟨g j ^ n, n, rfl⟩ : Submonoid.powers (g j))).mp hz
  obtain ⟨t, ht⟩ := m.2
  have hkill : g j ^ t * MvPolynomial.aeval g (H : MvPolynomial ι A) = 0 := by
    rw [← ht, ← hHa, quotientEvaluation_mk] at hm
    exact hm
  have hker : MvPolynomial.X j ^ t * (H : MvPolynomial ι A) ∈ kernel g := by
    change presentation g (MvPolynomial.X j ^ t * (H : MvPolynomial ι A)) = 0
    rw [presentation_of_isHomogeneous g ((MvPolynomial.isHomogeneous_X_pow j t).mul H.2)]
    simp only [map_mul, map_pow, MvPolynomial.aeval_X, hkill, map_zero, zero_mul]
  have hq : generator g j ^ t * a = 0 := by
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hker
    rw [map_mul, map_pow, hHa] at he
    exact he
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨generator g j ^ t, t, rfl⟩, hq⟩

/-- The SAME actual target is localization of the chart by its ORIGINAL selected coefficient; no scalar tower is assumed. -/
theorem toAway_isLocalization (j : ι) :
    letI : Algebra (Chart g j) (Localization.Away (g j)) := (toAway g j).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap A (Chart g j) (g j)) (Localization.Away (g j)) := by
  let : Algebra (Chart g j) (Localization.Away (g j)) := (toAway g j).toRingHom.toAlgebra
  constructor; constructor
  · rintro ⟨y, ⟨n, rfl⟩⟩
    change IsUnit (toAway g j (algebraMap A (Chart g j) (g j) ^ n))
    rw [map_pow, AlgHom.commutes]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (g j)) (g j)).pow n
  · intro z
    obtain ⟨⟨r, m⟩, he⟩ := IsLocalization.surj (Submonoid.powers (g j)) z
    refine ⟨⟨algebraMap A (Chart g j) r, ⟨algebraMap A (Chart g j) m, ?_⟩⟩, ?_⟩
    · obtain ⟨n, hn⟩ := m.2
      exact ⟨n, by simpa only [map_pow] using congrArg (algebraMap A (Chart g j)) hn⟩
    · change z * toAway g j (algebraMap A (Chart g j) m) =
        toAway g j (algebraMap A (Chart g j) r)
      rw [AlgHom.commutes, AlgHom.commutes]
      exact he
  · intro x y hxy
    change toAway g j x = toAway g j y at hxy
    exact ⟨1, by simpa using toAway_injective g j hxy⟩

/-- The true ORIGINAL ratios in the actual coefficient localization, including zero rings. -/
def awayRatios (j i : ι) : Localization.Away (g j) :=
  algebraMap A (Localization.Away (g j)) (g i) *
    IsLocalization.Away.invSelf (S := Localization.Away (g j)) (g j)

/-- The actual inverse powers compute EVERY genuine original numerator fraction. -/
theorem away_mk_pow (j : ι) (a : A) (n : ℕ) :
    IsLocalization.mk' (Localization.Away (g j)) a
      (⟨g j ^ n, n, rfl⟩ : Submonoid.powers (g j)) =
    algebraMap A (Localization.Away (g j)) a *
      (IsLocalization.Away.invSelf (S := Localization.Away (g j)) (g j)) ^ n := by
  symm
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  have hu : IsLocalization.Away.invSelf (S := Localization.Away (g j)) (g j) *
      algebraMap A (Localization.Away (g j)) (g j) = 1 := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  change (algebraMap A (Localization.Away (g j)) a * _) *
    algebraMap A (Localization.Away (g j)) (g j ^ n) = _
  rw [map_pow, mul_assoc, ← mul_pow, hu, one_pow, mul_one]

/-- EVERY true original coordinate fraction retains its whole actual ratio value. -/
@[simp]
theorem toAway_coordinateRatio (j i : ι) :
    toAway g j (coordinateRatio g j i) = awayRatios g j i := by
  change toAway g j (HomogeneousLocalization.Away.mk (grading g)
    (generator_mem g j) 1 (generator g i) _) = _
  rw [toAway_mk, quotientEvaluation_generator, away_mk_pow, pow_one]
  rfl

/-- The original selected coordinate ratio is genuinely one, including the empty chart case. -/
@[simp]
theorem coordinateRatio_self (j : ι) : coordinateRatio g j j = 1 := by
  apply toAway_injective g j
  rw [toAway_coordinateRatio, map_one]
  exact IsLocalization.Away.mul_invSelf _

/-- The whole original homogeneous scaling identity is valid in the SAME actual localization. -/
theorem aeval_awayRatios (j : ι) {H : MvPolynomial ι A} {d : ℕ}
    (hH : H.IsHomogeneous d) :
    MvPolynomial.aeval (awayRatios g j) H =
      algebraMap A (Localization.Away (g j)) (MvPolynomial.aeval g H) *
        (IsLocalization.Away.invSelf (S := Localization.Away (g j)) (g j)) ^ d := by
  change MvPolynomial.aeval (fun i => algebraMap A (Localization.Away (g j)) (g i) *
    IsLocalization.Away.invSelf (S := Localization.Away (g j)) (g j)) H = _
  exact aeval_mul_of_isHomogeneous g hH _

/-- The ACTUAL original fraction-adjoin algebra INSIDE A[1/g_j], not an assumed fraction field. -/
def awayAlgebra (j : ι) : Subalgebra A (Localization.Away (g j)) :=
  Algebra.adjoin A (Set.range (awayRatios g j))

/-- The WHOLE chart image is exactly the genuine original ratio-adjoin algebra. -/
theorem range_toAway (j : ι) : (toAway g j).range = awayAlgebra g j := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (grading g) (generator_mem g j) z
    obtain ⟨H, hH⟩ := GradedQuotient.componentMap_surjective
      (MvPolynomial.homogeneousSubmodule ι A) (kernel g) (n • (1 : ℕ)) ⟨a, ha⟩
    have hHa : Ideal.Quotient.mk (kernel g) (H : MvPolynomial ι A) = a :=
      congrArg Subtype.val hH
    change toAway g j (HomogeneousLocalization.Away.mk (grading g)
      (generator_mem g j) n a ha) ∈ awayAlgebra g j
    rw [toAway_mk, ← hHa, quotientEvaluation_mk, away_mk_pow]
    have hdeg0 : (H : MvPolynomial ι A).IsHomogeneous (n • (1 : ℕ)) := H.2
    have hdeg : (H : MvPolynomial ι A).IsHomogeneous n := by
      simpa only [smul_eq_mul, mul_one] using hdeg0
    rw [← aeval_awayRatios g j hdeg]
    change MvPolynomial.aeval (awayRatios g j) (H : MvPolynomial ι A) ∈
      Algebra.adjoin A (Set.range (awayRatios g j))
    rw [← MvPolynomial.aeval_range]
    exact ⟨H, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact ⟨coordinateRatio g j i, toAway_coordinateRatio g j i⟩

/-- Every original commutative-ring chart is GENUINELY its whole actual localization-adjoin algebra. -/
def awayEquiv (j : ι) : Chart g j ≃ₐ[A] awayAlgebra g j :=
  (AlgEquiv.ofInjective (toAway g j) (toAway_injective g j)).trans
    (Subalgebra.equivOfEq _ _ (range_toAway g j))

/-- The equivalence retains the SAME entire original ring map. -/
@[simp]
theorem awayEquiv_coe (j : ι) (z : Chart g j) :
    (awayEquiv g j z : Localization.Away (g j)) = toAway g j z := rfl

/-- Every original coefficient is preserved by the genuine chart equivalence. -/
@[simp]
theorem awayEquiv_algebraMap (j : ι) (a : A) :
    awayEquiv g j (algebraMap A (Chart g j) a) =
      algebraMap A (awayAlgebra g j) a := (awayEquiv g j).commutes a

/-- Every ORIGINAL center generator satisfies the entire genuine coordinate-fraction relation. -/
theorem coefficient_mul_coordinateRatio (j i : ι) :
    algebraMap A (Chart g j) (g j) * coordinateRatio g j i =
      algebraMap A (Chart g j) (g i) := by
  apply toAway_injective g j
  rw [map_mul, AlgHom.commutes, toAway_coordinateRatio, AlgHom.commutes]
  change algebraMap A (Localization.Away (g j)) (g j) *
    (algebraMap A (Localization.Away (g j)) (g i) *
      IsLocalization.Away.invSelf (S := Localization.Away (g j)) (g j)) = _
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]

/-- The ORIGINAL center ideal extended by the true whole chart coefficient map. -/
def centerIdeal (j : ι) : Ideal (Chart g j) :=
  (generatorIdeal g).map (algebraMap A (Chart g j))

/-- The actual extended original center is EXACTLY its original selected-generator ideal. -/
theorem centerIdeal_eq_span (j : ι) :
    centerIdeal g j = Ideal.span ({algebraMap A (Chart g j) (g j)} : Set (Chart g j)) := by
  rw [centerIdeal, generatorIdeal, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.mpr ⟨coordinateRatio g j i,
      (coefficient_mul_coordinateRatio g j i).symm⟩
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.subset_span ⟨j, rfl⟩

/-- The original selected coefficient is genuinely regular on the true chart, even if the chart is zero. -/
theorem coefficient_mem_nonZeroDivisors (j : ι) :
    algebraMap A (Chart g j) (g j) ∈ (Chart g j)⁰ := by
  apply mem_nonZeroDivisors_of_injective (toAway_injective g j)
  rw [AlgHom.commutes]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (g j)) (g j)).mem_nonZeroDivisors

/-- Actual multiplication into the ORIGINAL extended center ideal, not an assumed invertible module. -/
def centerMultiplication (j : ι) : Chart g j →ₗ[Chart g j] centerIdeal g j where
  toFun a := ⟨a * algebraMap A (Chart g j) (g j), by
    rw [centerIdeal_eq_span]
    exact Ideal.mem_span_singleton.mpr ⟨a, mul_comm _ _⟩⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' r a := Subtype.ext (mul_assoc _ _ _)

/-- Multiplication by the actual regular center generator gives a genuine whole module equivalence. -/
def centerLinearEquiv (j : ι) : Chart g j ≃ₗ[Chart g j] centerIdeal g j :=
  LinearEquiv.ofBijective (centerMultiplication g j) ⟨by
    intro a b h
    have he := congrArg Subtype.val h
    change a * algebraMap A (Chart g j) (g j) = b * algebraMap A (Chart g j) (g j) at he
    apply sub_eq_zero.mp
    exact (coefficient_mem_nonZeroDivisors g j).2 _ (by rw [sub_mul, he, sub_self]), by
    intro b
    have hb : (b : Chart g j) ∈ Ideal.span
        ({algebraMap A (Chart g j) (g j)} : Set (Chart g j)) :=
      (centerIdeal_eq_span g j).le b.2
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hb
    refine ⟨a, Subtype.ext ?_⟩
    change a * algebraMap A (Chart g j) (g j) = (b : Chart g j)
    rw [mul_comm, ← ha]⟩

/-- The entire original module equivalence is exactly multiplication by the SAME original coefficient. -/
@[simp]
theorem centerLinearEquiv_coe (j : ι) (a : Chart g j) :
    (centerLinearEquiv g j a : Chart g j) = a * algebraMap A (Chart g j) (g j) := rfl

end EnvelopeProperty.ReesChart
