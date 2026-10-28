import EnvelopeProperty.Potential.LinePolynomialComponent

/-! # Actual native inverse-disc functions produce the completed principal components -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] {m : ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)

/-- Actual original polynomial evaluation at the original hole inverse. -/
def inverseRationalPolynomial (j : Fin m) : K[X] →ₐ[K] U.RationalFunctions :=
  Polynomial.aeval (U.rationalHoleInverse j)

/-- The whole ORIGINAL inverse-coordinate point of every original point of the affinoid. -/
def holeInversePoint (j : Fin m) (x : U.carrier) : RelativeSpectrum (NormedField.valuation (K := K)) K[X] :=
  RelativeSpectrum.comap (U.inverseRationalPolynomial j) (U.rationalPoint x)

omit [IsAlgClosed K] in
theorem holeInversePoint_val_X (j : Fin m) (x : U.carrier) :
    val (U.holeInversePoint j x) X = (val x.1 (X-C (U.holeCenter j)))⁻¹ := by
  change U.rationalValue (U.inverseRationalPolynomial j X) x = _
  rw [inverseRationalPolynomial,Polynomial.aeval_X,U.rationalValue_holeInverse]

omit [IsAlgClosed K] in
theorem holeInversePoint_val_X_le (j : Fin m) (x : U.carrier) :
    val (U.holeInversePoint j x) X ≤ (U.holeRadius j)⁻¹ := by
  rw [U.holeInversePoint_val_X]
  exact (inv_le_inv₀ ((U.holeRadius_pos j).trans_le (x.2.2 j)) (U.holeRadius_pos j)).mpr (x.2.2 j)

omit [IsAlgClosed K] in
theorem holeInversePoint_boundary_linear (j : Fin m) (b : K) :
    val (U.holeInversePoint j ⟨U.holeBoundaryPoint j,U.holeGauss_mem j⟩) (X-C b) =
      max ((U.holeRadius j)⁻¹) (‖b‖₊) := by
  let x : U.carrier := ⟨U.holeBoundaryPoint j,U.holeGauss_mem j⟩
  let v : Valuation U.RationalFunctions ℝ≥0 := (U.rationalPoint x).1.val
  let c := algebraMap K U.RationalFunctions
  let d := algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j))
  have hc (a : K) : v (c a) = ‖a‖₊ := (U.rationalPoint x).2 a
  have hd : d*U.rationalHoleInverse j = 1 := U.holeCoordinate_mul_rationalHoleInverse j
  have hi : v (U.rationalHoleInverse j) = (U.holeRadius j)⁻¹ := by
    change U.rationalValue (U.rationalHoleInverse j) x = _
    rw [U.rationalValue_holeInverse]
    rw [show val x.1 (X-C (U.holeCenter j)) = U.holeRadius j from centeredGauss_val_X_sub_C _ _ _]
  change v (U.inverseRationalPolynomial j (X-C b)) = _
  rw [inverseRationalPolynomial,map_sub,Polynomial.aeval_X,Polynomial.aeval_C]
  change v (U.rationalHoleInverse j-c b) = _
  by_cases hb : b = 0
  · subst b
    simpa only [map_zero,sub_zero,nnnorm_zero,max_eq_left zero_le] using hi
  · have hbc : c b*c b⁻¹ = 1 := by rw [← map_mul,mul_inv_cancel₀ hb,map_one]
    have he : U.rationalHoleInverse j-c b = -c b*(d-c b⁻¹)*U.rationalHoleInverse j := by
      symm
      calc
        _ = (c b*c b⁻¹)*U.rationalHoleInverse j-c b*(d*U.rationalHoleInverse j) := by ring
        _ = _ := by rw [hbc,hd,one_mul,mul_one]
    have hs : v (d-c b⁻¹) = max (U.holeRadius j) (‖b‖₊)⁻¹ := by
      have hcoef : c b⁻¹ = algebraMap K[X] U.RationalFunctions (C b⁻¹) :=
        IsScalarTower.algebraMap_apply K K[X] U.RationalFunctions b⁻¹
      rw [hcoef]
      change v (algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j))-
        algebraMap K[X] U.RationalFunctions (C b⁻¹)) = _
      rw [← map_sub]
      change U.rationalValue (algebraMap K[X] U.RationalFunctions
        (X-C (U.holeCenter j)-C b⁻¹)) x = _
      rw [U.rationalValue_polynomial]
      have hpoly : X-C (U.holeCenter j)-C b⁻¹ = X-C (U.holeCenter j+b⁻¹) := by
        rw [map_add]
        ring
      rw [hpoly]
      change val (centeredGauss (self _) (U.holeCenter j) (U.holeRadius j)) _ = _
      rw [fc_centeredGauss_val_X_sub_C]
      simp only [sub_add_cancel_left,Valuation.map_neg,NormedField.valuation_apply,nnnorm_inv,max_comm]
    rw [he,map_mul,map_mul,Valuation.map_neg,hc,hs,hi,mul_max,max_mul]
    have hbv : ‖b‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hb
    have hr : U.holeRadius j ≠ 0 := (U.holeRadius_pos j).ne'
    have hwb : ‖b‖₊*((‖b‖₊)⁻¹*(U.holeRadius j)⁻¹) = (U.holeRadius j)⁻¹ := by
      rw [← mul_assoc,mul_inv_cancel₀ hbv,one_mul]
    simp only [mul_assoc,mul_inv_cancel₀ hr,mul_one,hwb,max_comm]

/-- The WHOLE original inverse-coordinate Gauss point is identified from actual original linear values. -/
theorem holeInversePoint_boundary_eq_gauss (j : Fin m) :
    U.holeInversePoint j ⟨U.holeBoundaryPoint j,U.holeGauss_mem j⟩ =
      gauss (self (NormedField.valuation (K := K))) (U.holeRadius j)⁻¹ := by
  apply fc_ext_linear
  intro b
  rw [U.holeInversePoint_boundary_linear]
  change max ((U.holeRadius j)⁻¹) ‖b‖₊ =
    gaussFun (NormedField.valuation (K := K)) (U.holeRadius j)⁻¹ (X-C b)
  rw [gaussFun_X_sub_C,NormedField.valuation_apply]

omit [IsAlgClosed K] in
theorem inverseRationalPolynomial_value_le (j : Fin m) (p : K[X]) (x : U.carrier) :
    U.rationalValue (U.inverseRationalPolynomial j p) x ≤
      gaussFun (NormedField.valuation (K := K)) (U.holeRadius j)⁻¹ p := by
  have hy : proj (U.holeInversePoint j x) = self (NormedField.valuation (K := K)) := by
    apply RelativeSpectrum.ext_val
    intro a
    exact (U.holeInversePoint j x).2 a
  exact val_le_gauss_val hy (U.holeInversePoint_val_X_le j x) p

theorem inverseRationalPolynomial_boundary_value (j : Fin m) (p : K[X]) :
    U.rationalValue (U.inverseRationalPolynomial j p) ⟨U.holeBoundaryPoint j,U.holeGauss_mem j⟩ =
      gaussFun (NormedField.valuation (K := K)) (U.holeRadius j)⁻¹ p := by
  change val (U.holeInversePoint j ⟨U.holeBoundaryPoint j,U.holeGauss_mem j⟩) p = _
  rw [U.holeInversePoint_boundary_eq_gauss]
  exact gauss_val_apply _ _ _

/-- EVERY original inverse polynomial has the exact native inverse-disc Gauss norm. -/
theorem nnnorm_inverseRationalPolynomial (j : Fin m) (p : K[X]) :
    ‖U.rationalMap (U.inverseRationalPolynomial j p)‖₊ =
      gaussFun (NormedField.valuation (K := K)) (U.holeRadius j)⁻¹ p := by
  let _ : Fintype U.boundary := U.rationalBoundaryFintype
  rw [U.nnnorm_rationalMap]
  apply le_antisymm
  · exact Finset.sup_le fun z _ => U.inverseRationalPolynomial_value_le j p ⟨z.1,U.boundary_subset z.2⟩
  · let z : U.boundary := ⟨U.holeBoundaryPoint j,U.holeBoundaryPoint_mem_boundary j⟩
    have hz := Finset.le_sup (f := fun y : U.boundary =>
      U.rationalValue (U.inverseRationalPolynomial j p) ⟨y.1,U.boundary_subset y.2⟩) (Finset.mem_univ z)
    exact (U.inverseRationalPolynomial_boundary_value j p).symm.trans_le hz

omit [IsAlgClosed K] in
/-- Positivity is DERIVED from the original hole radius. -/
theorem inverseRadius_pos (j : Fin m) : 0 < (U.holeRadius j)⁻¹ := inv_pos.mpr (U.holeRadius_pos j)

/-- Native original inverse Gauss polynomials evaluated in the actual affinoid algebra. -/
def inverseGaussPolynomialMap (j : Fin m) :
    GaussCompletion.PolynomialRing (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j) →+* U.AnalyticFunctions :=
  U.rationalMap.comp ((U.inverseRationalPolynomial j).toRingHom.comp
    (GaussCompletion.polynomialEquiv (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)).toRingHom)

theorem isometry_inverseGaussPolynomialMap (j : Fin m) : Isometry (U.inverseGaussPolynomialMap j) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro p
  exact congrArg NNReal.toReal
    ((U.nnnorm_inverseRationalPolynomial j
      (GaussCompletion.polynomialEquiv (U.holeRadius j)⁻¹ (U.inverseRadius_pos j) p)).trans
        (GaussCompletion.nnnorm_polynomial (U.holeRadius j)⁻¹ (U.inverseRadius_pos j) p).symm)

/-- The GENUINE original inverse-disc completion map into the WHOLE actual affinoid algebra. -/
def inverseGaussExtension (j : Fin m) :
    GaussCompletion.Ring (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j) →+* U.AnalyticFunctions :=
  Completion.extensionHom (U.inverseGaussPolynomialMap j) (U.isometry_inverseGaussPolynomialMap j).continuous

theorem inverseGaussExtension_polynomialMap (j : Fin m) (p : K[X]) :
    U.inverseGaussExtension j
      (GaussCompletion.polynomialMap (U.holeRadius j)⁻¹ (U.inverseRadius_pos j) p) =
        U.rationalMap (U.inverseRationalPolynomial j p) := by
  change U.inverseGaussExtension j
    ((GaussCompletion.polynomialEquiv (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)).symm p :
      GaussCompletion.Ring (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)) = _
  rw [inverseGaussExtension,Completion.extensionHom_coe]
  change U.rationalMap (U.inverseRationalPolynomial j
    (GaussCompletion.polynomialEquiv (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)
      ((GaussCompletion.polynomialEquiv (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)).symm p))) = _
  rw [RingEquiv.apply_symm_apply]

theorem continuous_inverseGaussExtension (j : Fin m) : Continuous (U.inverseGaussExtension j) :=
  Completion.continuous_extension

theorem nnnorm_inverseGaussExtension (j : Fin m)
    (f : GaussCompletion.Ring (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)) :
    ‖U.inverseGaussExtension j f‖₊ = ‖f‖₊ := by
  exact (GaussCompletion.denseRange_polynomialMap (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)).induction_on f
    (isClosed_eq (continuous_nnnorm.comp (U.continuous_inverseGaussExtension j)) continuous_nnnorm)
    (fun p => by rw [U.inverseGaussExtension_polynomialMap,U.nnnorm_inverseRationalPolynomial,
      GaussCompletion.nnnorm_polynomialMap])

theorem isometry_inverseGaussExtension (j : Fin m) : Isometry (U.inverseGaussExtension j) :=
  AddMonoidHomClass.isometry_of_norm _ fun f => congrArg NNReal.toReal (U.nnnorm_inverseGaussExtension j f)

theorem inverseGaussExtension_original_coefficient (j : Fin m) (a : K) :
    U.inverseGaussExtension j
      (algebraMap K (GaussCompletion.Ring (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)) a) =
        algebraMap K U.AnalyticFunctions a := by
  change U.inverseGaussExtension j
    (GaussCompletion.polynomialMap (U.holeRadius j)⁻¹ (U.inverseRadius_pos j) (C a)) = _
  rw [U.inverseGaussExtension_polynomialMap]
  change U.rationalMap (Polynomial.aeval (U.rationalHoleInverse j) (C a)) = _
  rw [Polynomial.aeval_C,U.rationalMap_original_coefficient]

/-- The actual inverse-disc map retains the ORIGINAL coefficient algebra. -/
def inverseGaussAlgHom (j : Fin m) :
    GaussCompletion.Ring (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j) →ₐ[K] U.AnalyticFunctions where
  __ := U.inverseGaussExtension j
  commutes' := U.inverseGaussExtension_original_coefficient j

/-- The finite ORIGINAL inverse polynomial belonging to an original proper numerator. -/
def inversePrincipalPolynomial (p : K[X]) (n : ℕ) : K[X] :=
  ∑ k ∈ Finset.range n, Polynomial.monomial (n-k) (p.coeff k)

omit [IsAlgClosed K] [IsUltrametricDist K] in
theorem inversePrincipalPolynomial_coeff_zero (p : K[X]) (n : ℕ) :
    (inversePrincipalPolynomial p n).coeff 0 = 0 := by
  classical
  simp only [inversePrincipalPolynomial,Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : n-k ≠ 0 := (Nat.sub_pos_of_lt (Finset.mem_range.mp hk)).ne'
  simp only [Polynomial.coeff_monomial,if_neg hkn]

omit [IsAlgClosed K] in
theorem holeCoordinate_pow_mul_inverse_pow (j : Fin m) (k n : ℕ) (hk : k ≤ n) :
    (algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j)))^k*(U.rationalHoleInverse j)^n =
      (U.rationalHoleInverse j)^(n-k) := by
  have he : n = k+(n-k) := (Nat.add_sub_of_le hk).symm
  conv_lhs => rw [he,pow_add]
  calc
    _ = ((algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j)))*U.rationalHoleInverse j)^k*
        (U.rationalHoleInverse j)^(n-k) := by rw [mul_pow]; ring
    _ = _ := by rw [U.holeCoordinate_mul_rationalHoleInverse,one_pow,one_mul]

omit [IsAlgClosed K] in
/-- Every actual ORIGINAL proper fraction is a constructed finite inverse polynomial with zero constant. -/
theorem properRationalPart_eq_inversePolynomial (p : K[X]) (j : Fin m) (n : ℕ) (hp : p.degree < n) :
    U.properRationalPart p j n = U.inverseRationalPolynomial j (inversePrincipalPolynomial p n) := by
  have ht : initialPolynomial p n = p := by
    apply Polynomial.ext
    intro k
    rw [initialPolynomial_coeff]
    split_ifs with hk
    · rfl
    · exact ((Polynomial.degree_lt_iff_coeff_zero _ _).mp hp k (le_of_not_gt hk)).symm
  have hC (a : K) : Polynomial.algEquivAevalXAddC (-U.holeCenter j) (C a) = C a :=
    (Polynomial.algEquivAevalXAddC (-U.holeCenter j)).commutes a
  have hX : Polynomial.algEquivAevalXAddC (-U.holeCenter j) X = X-C (U.holeCenter j) := by
    simp [Polynomial.algEquivAevalXAddC]
    ring
  calc
    U.properRationalPart p j n = U.properRationalPart (initialPolynomial p n) j n := congrArg (fun q => U.properRationalPart q j n) ht.symm
    _ = ∑ k ∈ Finset.range n, algebraMap K[X] U.RationalFunctions (C (p.coeff k))*
        (algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j)))^k*(U.rationalHoleInverse j)^n := by
      unfold properRationalPart initialPolynomial
      rw [map_sum,map_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,hC,hX,map_mul,map_pow]
    _ = ∑ k ∈ Finset.range n, algebraMap K U.RationalFunctions (p.coeff k)*
        (U.rationalHoleInverse j)^(n-k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_assoc,U.holeCoordinate_pow_mul_inverse_pow j k n (Finset.mem_range.mp hk).le]
      rw [IsScalarTower.algebraMap_apply K K[X] U.RationalFunctions]
      rfl
    _ = U.inverseRationalPolynomial j (inversePrincipalPolynomial p n) := by
      simp only [inverseRationalPolynomial,inversePrincipalPolynomial,map_sum,Polynomial.aeval_monomial]

/-- Every WHOLE actual completed principal component is produced by a unique ORIGINAL native inverse-disc function. -/
theorem exists_unique_native_principal_component (j : Fin m) (f : U.AnalyticFunctions) :
    ∃! g : GaussCompletion.Ring (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j),
      U.inverseGaussExtension j g = U.analyticComponent (some j) f := by
  have hclosed : IsClosed (Set.range (U.inverseGaussExtension j)) :=
    (U.isometry_inverseGaussExtension j).isClosedEmbedding.isClosed_range
  have hsub : U.rationalComponentSet (some j) ⊆ Set.range (U.inverseGaussExtension j) := by
    rintro g ⟨p,n,hp,rfl⟩
    refine ⟨GaussCompletion.polynomialMap (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)
      (inversePrincipalPolynomial p n),?_⟩
    rw [U.inverseGaussExtension_polynomialMap,← U.properRationalPart_eq_inversePolynomial p j n hp]
  have hg := closure_minimal hsub hclosed (U.analyticComponent_mem_closure (some j) f)
  obtain ⟨g,hg⟩ := hg
  exact ⟨g,hg,fun h hh => (U.isometry_inverseGaussExtension j).injective (hh.trans hg.symm)⟩

/-- The WHOLE native original disc/principal decomposition, with its exact native maximum norm. -/
theorem exists_native_gauss_decomposition (hr : 0 < U.radius) (f : U.AnalyticFunctions) :
    ∃ (g₀ : GaussCompletion.Ring (K := K) U.radius hr)
      (g : ∀ j, GaussCompletion.Ring (K := K) (U.holeRadius j)⁻¹ (U.inverseRadius_pos j)),
      U.outerGaussExtension hr g₀ = U.analyticComponent none f ∧
      (∀ j, U.inverseGaussExtension j (g j) = U.analyticComponent (some j) f) ∧
      f = U.outerGaussExtension hr g₀+∑ j, U.inverseGaussExtension j (g j) ∧
      ‖f‖₊ = max ‖g₀‖₊ (Finset.univ.sup fun j => ‖g j‖₊) := by
  obtain ⟨g₀,hg₀,_⟩ := U.exists_unique_native_polynomial_component hr f
  have hgs (j : Fin m) := (U.exists_unique_native_principal_component j f).exists
  choose g hg using hgs
  refine ⟨g₀,g,hg₀,hg,?_,?_⟩
  · simpa only [hg₀,hg] using U.analyticComponent_sum f
  · have hn := U.nnnorm_analyticComponents f
    rw [← hg₀,U.nnnorm_outerGaussExtension] at hn
    simp_rw [← hg,U.nnnorm_inverseGaussExtension] at hn
    exact hn
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
