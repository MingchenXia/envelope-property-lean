import EnvelopeProperty.Char0.NativeBPWholeComparison
import EnvelopeProperty.Char0.NativeMultiplierProduct
import EnvelopeProperty.Char0.NativeAffineIdealDescent
import EnvelopeProperty.Char0.SequenceMultiplierKernel
import EnvelopeProperty.Char0.ValuativeMultiplierFunctoriality

/-! # Actual complex affine subadditivity of the full original all-DVR multiplier ideal -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.ComplexValuativeSubadditivity

open CategoryTheory AlgebraicGeometry BingWangEntropy SGPT.Okounkov
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open NativeAffineIdealWeight NativeMultiplierProduct
open scoped Topology

section Ring
variable {R : Type} [CommRing R] [IsDomain R] [Algebra ℂ R]

/-- The actual whole original BP rounded quotient coefficient kernel. -/
def originalBPKernel (n : ℕ) (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (I : Ideal R) (hI : I ≠ ⊥) (q : ℚ) : Ideal R :=
  letI := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  RoundedCanonicalModule.specPushedQuotientKernel (.of R) S.composite z hz
    ((specIdealSheaf I).comap S.composite)
    (affinePrincipalization_isIdealOfSncDivisor f n I hI) q

omit [Algebra ℂ R] in
private theorem product_ne_bot_ring (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I * J ≠ ⊥ := by
  intro h
  exact (not_or.mpr ⟨hI, hJ⟩) (Ideal.mul_eq_bot.mp h)

local instance ringAffine : IsAffineHom
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := isAffineHom_of_isAffine _
local instance ringTopology : TopologicalSpace
    (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticPointTopology _
local instance ringCharts (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    ChartedSpace (ComplexModel n)
      (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticTNChartedSpace _ n
local instance ringManifold (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))] :
    IsComplexManifold n
      (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  schemeAnalyticTN_isComplexManifold _ n

private theorem affineMultiplierIdeal_eq_originalBPKernel
    (n : ℕ) (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (I : Ideal R) (hI : I ≠ ⊥) {m : ℕ} (a : Fin m → R)
    (ha : Ideal.span (Set.range a) = I) (q : ℚ) (hq : (0 : ℝ) < q) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
    ∀ p : SchemeComplexPoint f,
      affineMultiplierIdeal f n a (q : ℝ) hq p =
        (originalBPKernel n z hz I hI q).map (nativeMap f n p) := by
  exact NativeBPWholeComparison.nativeMultiplierIdeal_eq_originalBP_kernel n z hz I hI a ha q hq

/-- Actual original whole BP kernels satisfy complex affine subadditivity
without a chosen fraction-field embedding or comparison hypothesis. -/
theorem originalBPKernel_mul_le
    (n : ℕ) (z : Fin n → R)
    (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) (hq : (0 : ℝ) < q) :
    originalBPKernel n z hz (I * J) (product_ne_bot_ring I J hI hJ) q ≤
      originalBPKernel n z hz I hI q * originalBPKernel n z hz J hJ q := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  let : Algebra.FiniteType ℂ R := finiteType_of_etale_coordinates z hz
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  obtain ⟨m, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  obtain ⟨k, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian J)
  change Ideal.span (Set.range a) = I at ha
  change Ideal.span (Set.range b) = J at hb
  have hab : Ideal.span (Set.range (productGenerators a b)) = I * J := by
    rw [span_productGenerators, ha, hb]
  apply (NativeAffineIdealDescent.ideal_le_mul_iff_nativeMap f n _ _ _).mpr
  intro p
  have hnative := affine_product_le_mul f n I J hI hJ a b ha hb (q : ℝ) hq p
  rw [affineMultiplierIdeal_eq_originalBPKernel n z hz (I * J)
      (product_ne_bot_ring I J hI hJ) (productGenerators a b) hab q hq p,
    affineMultiplierIdeal_eq_originalBPKernel n z hz I hI a ha q hq p,
    affineMultiplierIdeal_eq_originalBPKernel n z hz J hJ b hb q hq p] at hnative
  exact hnative
end Ring

variable {K : Type} [Field K] [Algebra ℂ K]
    (C : Subalgebra ℂ K) [IsFractionRing C K]

local instance baseAffine : IsAffineHom
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ C))) := isAffineHom_of_isAffine _
local instance baseTopology : TopologicalSpace
    (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ C)))) :=
  schemeAnalyticPointTopology _
local instance baseCharts (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ C)))] :
    ChartedSpace (ComplexModel n)
      (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ C)))) :=
  schemeAnalyticTNChartedSpace _ n
local instance baseManifold (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ C)))] :
    IsComplexManifold n
      (SchemeComplexPoint (Spec.map (CommRingCat.ofHom (algebraMap ℂ C)))) :=
  schemeAnalyticTN_isComplexManifold _ n

/-- The SAME entire native ideal is the extension of the FULL original all-DVR
valuative multiplier ideal, by the actual original BP and existing sequence theorem. -/
theorem nativeMultiplierIdeal_eq_valuativeMultiplierIdeal
    (n : ℕ) (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (I : Ideal C) (hI : I ≠ ⊥) {m : ℕ} (a : Fin m → C)
    (ha : Ideal.span (Set.range a) = I) (q : ℚ) (hq : (0 : ℝ) < q) :
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ C))
    ∀ p : SchemeComplexPoint f,
      affineMultiplierIdeal f n a (q : ℝ) hq p =
        (valuativeMultiplierIdeal C I hI q).map (nativeMap f n p) := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  intro f p
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let J := (specIdealSheaf I).comap S.composite
  let hJ := affinePrincipalization_isIdealOfSncDivisor f n I hI
  let : SmoothOfRelativeDimension n (S.composite ≫ f) :=
    affinePrincipalization_smoothOfRelativeDimension f n I hI
  let : IsIso (S.composite ∣_ (specIdealSheaf I).support.compl) :=
    affinePrincipalization_isIso_restrict f n I hI
  have hwhole := NativeBPWholeComparison.nativeMultiplierIdeal_eq_originalBP_kernel
    n z hz I hI a ha q hq p
  have hfull := RoundedCanonicalModule.specPushedQuotientKernel_eq_valuativeMultiplierIdeal_of_sequence
    C n I hI z hz S hJ q
  change affineMultiplierIdeal f n a (q : ℝ) hq p =
    (RoundedCanonicalModule.specPushedQuotientKernel (.of C) S.composite z hz J hJ q).map
      (nativeMap f n p) at hwhole
  exact hwhole.trans (congrArg (fun L : Ideal C => L.map (nativeMap f n p)) hfull)

omit [IsFractionRing C K] in
private theorem product_ne_bot (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I * J ≠ ⊥ := by
  intro h
  exact (not_or.mpr ⟨hI, hJ⟩) (Ideal.mul_eq_bot.mp h)

/-- FULL intrinsic all-DVR multiplier ideals on an actual original complex affine
integral chart satisfy subadditivity, with no comparison hypothesis or supplied generators. -/
theorem valuativeMultiplierIdeal_mul_le_of_pos
    (n : ℕ) (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) (hq : (0 : ℝ) < q) :
    valuativeMultiplierIdeal C (I * J) (product_ne_bot C I J hI hJ) q ≤
      valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q := by
  let := smoothOfRelativeDimension_of_etale_coordinates z hz
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ C))
  let : Algebra.FiniteType ℂ C := finiteType_of_etale_coordinates z hz
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing ℂ C
  obtain ⟨m, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  obtain ⟨k, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian J)
  change Ideal.span (Set.range a) = I at ha
  change Ideal.span (Set.range b) = J at hb
  have hab : Ideal.span (Set.range (productGenerators a b)) = I * J := by
    rw [span_productGenerators, ha, hb]
  apply (NativeAffineIdealDescent.ideal_le_mul_iff_nativeMap f n _ _ _).mpr
  intro p
  have hnative := affine_product_le_mul f n I J hI hJ a b ha hb (q : ℝ) hq p
  rw [nativeMultiplierIdeal_eq_valuativeMultiplierIdeal C n z hz (I * J)
      (product_ne_bot C I J hI hJ) (productGenerators a b) hab q hq p,
    nativeMultiplierIdeal_eq_valuativeMultiplierIdeal C n z hz I hI a ha q hq p,
    nativeMultiplierIdeal_eq_valuativeMultiplierIdeal C n z hz J hJ b hb q hq p] at hnative
  exact hnative

/-- All rational levels, including the unit-ideal nonpositive branch. -/
theorem valuativeMultiplierIdeal_mul_le
    (n : ℕ) (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (I J : Ideal C) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (q : ℚ) :
    valuativeMultiplierIdeal C (I * J) (product_ne_bot C I J hI hJ) q ≤
      valuativeMultiplierIdeal C I hI q * valuativeMultiplierIdeal C J hJ q := by
  by_cases hq : 0 < q
  · exact valuativeMultiplierIdeal_mul_le_of_pos C n z hz I J hI hJ q (by exact_mod_cast hq)
  · rw [valuativeMultiplierIdeal_eq_top_of_nonpos C I hI q (le_of_not_gt hq),
      valuativeMultiplierIdeal_eq_top_of_nonpos C J hJ q (le_of_not_gt hq), Ideal.top_mul]
    exact le_top

end EnvelopeProperty.Char0.ComplexValuativeSubadditivity
