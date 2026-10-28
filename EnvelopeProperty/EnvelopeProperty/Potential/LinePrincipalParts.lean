import EnvelopeProperty.Potential.LineAffinoidRestrictions
import EnvelopeProperty.Potential.LineDirichlet
import Mathlib.Algebra.Ring.GeomSum

/-! # Constructed finite inverses and sharp original-hole principal parts -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

/-- The original normalized polynomial error, with no analytic expansion data. -/
def finiteTaylorError (q : K[X]) : K[X] := 1-C (q.coeff 0)⁻¹*q

/-- An actual FINITE original polynomial inverse modulo a coordinate power. -/
def finiteTaylorInverse (q : K[X]) (n : ℕ) : K[X] :=
  C (q.coeff 0)⁻¹ * ∑ k ∈ Finset.range n, (finiteTaylorError q)^k

theorem finiteTaylorError_coeff_zero (q : K[X]) (hq : q.coeff 0 ≠ 0) :
    (finiteTaylorError q).coeff 0 = 0 := by
  simp [finiteTaylorError,hq]

theorem finiteTaylorInverse_mul (q : K[X]) (n : ℕ) :
    q*finiteTaylorInverse q n-1 = -(finiteTaylorError q)^n := by
  have hq : q*C (q.coeff 0)⁻¹ = 1-finiteTaylorError q := by
    unfold finiteTaylorError
    ring
  rw [finiteTaylorInverse,← mul_assoc,hq,mul_neg_geom_sum]
  ring

theorem pow_X_dvd_finiteTaylorInverse_error (q : K[X]) (hq : q.coeff 0 ≠ 0) (n : ℕ) :
    X^n ∣ q*finiteTaylorInverse q n-1 := by
  rw [finiteTaylorInverse_mul]
  apply dvd_neg.mpr
  exact pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr (finiteTaylorError_coeff_zero q hq)) n

/-- The finite geometric inverse has the DERIVED sharp original Gauss bound, including non-strict coefficient equality. -/
theorem gaussFun_finiteTaylorInverse_le (q : K[X]) (hq : q.coeff 0 ≠ 0)
    (r : ℝ≥0) (hqr : gaussFun w r q ≤ w (q.coeff 0)) (n : ℕ) :
    gaussFun w r (finiteTaylorInverse q n) ≤ (w (q.coeff 0))⁻¹ := by
  let v : Valuation K[X] ℝ≥0 := (gauss (self w) r).1.val
  have hv (p : K[X]) : v p = gaussFun w r p := gauss_val_apply _ _ _
  have hvC (a : K) : v (C a) = w a := (gauss (self w) r).2 a
  have hne : w (q.coeff 0) ≠ 0 := (_root_.map_ne_zero w).mpr hq
  have hscale : v (C (q.coeff 0)⁻¹*q) ≤ 1 := by
    rw [map_mul,hvC,map_inv₀,hv]
    exact (mul_le_mul' le_rfl hqr).trans_eq (inv_mul_cancel₀ hne)
  have hg : v (finiteTaylorError q) ≤ 1 := by
    exact (v.map_sub 1 (C (q.coeff 0)⁻¹*q)).trans (max_le (by simp) hscale)
  have hsum : v (∑ k ∈ Finset.range n, (finiteTaylorError q)^k) ≤ 1 := by
    apply v.map_sum_le
    intro k _
    rw [map_pow]
    exact pow_le_one₀ zero_le hg
  rw [← hv,finiteTaylorInverse,map_mul,hvC,map_inv₀]
  simpa only [mul_one] using mul_le_mul' (le_refl ((w (q.coeff 0))⁻¹)) hsum

/-- The actual finite ORIGINAL coefficient truncation below the specified pole order. -/
def initialPolynomial (p : K[X]) (n : ℕ) : K[X] :=
  ∑ k ∈ Finset.range n, Polynomial.monomial k (p.coeff k)

theorem initialPolynomial_coeff (p : K[X]) (n k : ℕ) :
    (initialPolynomial p n).coeff k = if k < n then p.coeff k else 0 := by
  classical
  simp [initialPolynomial,Polynomial.coeff_monomial]

theorem pow_X_dvd_sub_initialPolynomial (p : K[X]) (n : ℕ) :
    X^n ∣ p-initialPolynomial p n := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  simp only [Polynomial.coeff_sub,initialPolynomial_coeff,if_pos hk,sub_self]

theorem degree_initialPolynomial_lt (p : K[X]) (n : ℕ) :
    (initialPolynomial p n).degree < n := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  simp only [initialPolynomial_coeff,if_neg (not_lt_of_ge hk)]

theorem gaussFun_initialPolynomial_le (p : K[X]) (n : ℕ) (r : ℝ≥0) :
    gaussFun w r (initialPolynomial p n) ≤ gaussFun w r p := by
  apply Finset.sup_le
  intro k _
  rw [initialPolynomial_coeff]
  split_ifs
  · exact le_gaussFun w r p k
  · simp

/-- The actual finite principal numerator, formed from the ORIGINAL numerator and constructed finite inverse. -/
def principalNumerator (p q : K[X]) (n : ℕ) : K[X] :=
  initialPolynomial (p*finiteTaylorInverse q n) n

theorem principalNumerator_degree_lt (p q : K[X]) (n : ℕ) :
    (principalNumerator p q n).degree < n := degree_initialPolynomial_lt _ _

theorem pow_X_dvd_principalNumerator_error (p q : K[X]) (hq : q.coeff 0 ≠ 0) (n : ℕ) :
    X^n ∣ q*principalNumerator p q n-p := by
  have h₁ : X^n ∣ p*(q*finiteTaylorInverse q n-1) :=
    dvd_mul_of_dvd_right (pow_X_dvd_finiteTaylorInverse_error q hq n) p
  have h₂ : X^n ∣ q*(p*finiteTaylorInverse q n-principalNumerator p q n) :=
    dvd_mul_of_dvd_right (pow_X_dvd_sub_initialPolynomial (p*finiteTaylorInverse q n) n) q
  have he : q*principalNumerator p q n-p = p*(q*finiteTaylorInverse q n-1)-
      q*(p*finiteTaylorInverse q n-principalNumerator p q n) := by ring
  rw [he]
  exact dvd_sub h₁ h₂

/-- The original principal numerator has its DERIVED sharp Gauss bound from finite algebra alone. -/
theorem gaussFun_principalNumerator_le (p q : K[X]) (hq : q.coeff 0 ≠ 0)
    (r : ℝ≥0) (hqr : gaussFun w r q ≤ w (q.coeff 0)) (n : ℕ) :
    gaussFun w r (principalNumerator p q n) ≤ gaussFun w r p*(w (q.coeff 0))⁻¹ := by
  exact (gaussFun_initialPolynomial_le (p*finiteTaylorInverse q n) n r).trans
    ((gaussFun_mul w r p (finiteTaylorInverse q n)).le.trans
      (mul_le_mul' le_rfl (gaussFun_finiteTaylorInverse_le q hq r hqr n)))

/-- Proper polynomial fractions have nonincreasing actual radial Gauss values. -/
theorem gaussFun_div_pow_antitone (p : K[X]) (n : ℕ)
    (hp : ∀ k, n ≤ k → p.coeff k = 0) (r b : ℝ≥0) (hr : 0 < r) (hrb : r ≤ b) :
    gaussFun w b p / b^n ≤ gaussFun w r p / r^n := by
  have hb : 0 < b := hr.trans_le hrb
  apply (div_le_iff₀ (pow_pos hb n)).mpr
  apply Finset.sup_le
  intro k hk
  have hkn : k < n := by
    by_contra hbad
    exact (Polynomial.mem_support_iff.mp hk) (hp k (le_of_not_gt hbad))
  have hexp : k+(n-k) = n := by omega
  have hcross : b^k*r^n ≤ r^k*b^n := by
    calc
      b^k*r^n = (r^k*b^k)*r^(n-k) := by
        calc
          _ = b^k*(r^k*r^(n-k)) := by rw [← pow_add,hexp]
          _ = _ := by ring
      _ ≤ (r^k*b^k)*b^(n-k) := mul_le_mul' le_rfl (pow_le_pow_left' hrb _)
      _ = r^k*b^n := by rw [mul_assoc,← pow_add,hexp]
  have hmono : (w (p.coeff k)*b^k)/b^n ≤ (w (p.coeff k)*r^k)/r^n := by
    apply (div_le_div_iff₀ (pow_pos hb n) (pow_pos hr n)).mpr
    simpa only [mul_assoc] using mul_le_mul' (le_refl (w (p.coeff k))) hcross
  have hcoeff : (w (p.coeff k)*r^k)/r^n ≤ gaussFun w r p/r^n := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul' (le_gaussFun w r p k) le_rfl
  exact (div_le_iff₀ (pow_pos hb n)).mp (hmono.trans hcoeff)

/-- The original translated whole point obeys the genuine polynomial Gauss bound. -/
theorem val_inverseTranslate_le_gauss (a : K) (x : RelativeSpectrum w K[X]) (p : K[X]) :
    val x (Polynomial.algEquivAevalXAddC (-a) p) ≤ gaussFun w (val x (X-C a)) p := by
  let y := polynomialTranslation (-a) x
  have hy : proj y = self w := by
    apply RelativeSpectrum.ext_val
    intro c
    exact y.2 c
  have hX : val y X = val x (X-C a) := by
    change val x (Polynomial.algEquivAevalXAddC (-a) X) = _
    congr 1
    simp [Polynomial.algEquivAevalXAddC]
    ring
  exact val_le_gauss_val hy hX.le p

/-- Every ORIGINAL point outside the actual hole has the constructed proper-fraction boundary bound. -/
theorem properFraction_value_le (p : K[X]) (a : K) (n : ℕ)
    (hp : ∀ k, n ≤ k → p.coeff k = 0) (r : ℝ≥0) (hr : 0 < r)
    (x : RelativeSpectrum w K[X]) (hx : r ≤ val x (X-C a)) :
    val x (Polynomial.algEquivAevalXAddC (-a) p) / (val x (X-C a))^n ≤
      gaussFun w r p/r^n := by
  have hnum : val x (Polynomial.algEquivAevalXAddC (-a) p) / (val x (X-C a))^n ≤
      gaussFun w (val x (X-C a)) p / (val x (X-C a))^n := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul' (val_inverseTranslate_le_gauss a x p) le_rfl
  exact hnum.trans (gaussFun_div_pow_antitone p n hp r _ hr hx)

variable {m : ℕ} (U : FCStandardAffinoid w m)

/-- Distinctness of the ORIGINAL centers is derived from the actual positive disjoint open holes. -/
theorem holeCenter_injective : Function.Injective U.holeCenter := by
  intro i j hij
  by_contra hne
  have hd := U.holeRadius_le_center_distance i j hne
  rw [hij,sub_self,map_zero] at hd
  exact not_le_of_gt (U.holeRadius_pos j) hd

/-- The ORIGINAL complementary denominator, in the actual coordinate centered at hole j. -/
def holeLocalDenominator (j : Fin m) (n : ℕ) : K[X] :=
  (∏ i ∈ Finset.univ.erase j, (X-C (U.holeCenter i-U.holeCenter j)))^n

theorem holeLocalDenominator_coeff_zero (j : Fin m) (n : ℕ) :
    (U.holeLocalDenominator j n).coeff 0 =
      (∏ i ∈ Finset.univ.erase j, (U.holeCenter j-U.holeCenter i))^n := by
  change Polynomial.constantCoeff (U.holeLocalDenominator j n) = _
  unfold holeLocalDenominator
  rw [map_pow,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  change (X-C (U.holeCenter i-U.holeCenter j)).coeff 0 = _
  simp only [Polynomial.coeff_sub,Polynomial.coeff_X_zero,Polynomial.coeff_C_zero,zero_sub,neg_sub]

theorem holeLocalDenominator_coeff_zero_ne_zero (j : Fin m) (n : ℕ) :
    (U.holeLocalDenominator j n).coeff 0 ≠ 0 := by
  rw [U.holeLocalDenominator_coeff_zero]
  apply pow_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact sub_ne_zero.mpr fun he => (Finset.mem_erase.mp hi).1 (U.holeCenter_injective he).symm

/-- The needed coefficient bound is DERIVED from the original hole separation, including touching boundaries. -/
theorem gaussFun_holeLocalDenominator (j : Fin m) (n : ℕ) :
    gaussFun w (U.holeRadius j) (U.holeLocalDenominator j n) =
      w ((U.holeLocalDenominator j n).coeff 0) := by
  let v : Valuation K[X] ℝ≥0 := (gauss (self w) (U.holeRadius j)).1.val
  change v (U.holeLocalDenominator j n) = _
  rw [U.holeLocalDenominator_coeff_zero,holeLocalDenominator,map_pow,map_prod,map_pow,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hd := U.holeRadius_le_center_distance i j (Finset.mem_erase.mp hi).1
  change gaussFun w (U.holeRadius j) (X-C (U.holeCenter i-U.holeCenter j)) = _
  rw [gaussFun_X_sub_C,max_eq_right hd,
    show U.holeCenter j-U.holeCenter i = -(U.holeCenter i-U.holeCenter j) by ring,Valuation.map_neg]

theorem holeLocalDenominator_translate (j : Fin m) (n : ℕ) :
    Polynomial.algEquivAevalXAddC (U.holeCenter j) ((U.holeComplementPolynomial j)^n) =
      U.holeLocalDenominator j n := by
  unfold holeComplementPolynomial holeLocalDenominator
  rw [map_pow,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [Polynomial.algEquivAevalXAddC]
  ring

/-- The ACTUAL original finite principal numerator at each original hole. -/
def holePrincipalNumerator (A : K[X]) (j : Fin m) (n : ℕ) : K[X] :=
  principalNumerator (Polynomial.algEquivAevalXAddC (U.holeCenter j) A) (U.holeLocalDenominator j n) n

theorem holePrincipalNumerator_coeff_large (A : K[X]) (j : Fin m) (n k : ℕ) (hk : n ≤ k) :
    (U.holePrincipalNumerator A j n).coeff k = 0 := by
  simp only [holePrincipalNumerator,principalNumerator,initialPolynomial_coeff,if_neg (not_lt_of_ge hk)]

theorem holePrincipalNumerator_degree_lt (A : K[X]) (j : Fin m) (n : ℕ) :
    (U.holePrincipalNumerator A j n).degree < n := principalNumerator_degree_lt _ _ _

theorem gaussFun_holePrincipalNumerator_le (A : K[X]) (j : Fin m) (n : ℕ) :
    gaussFun w (U.holeRadius j) (U.holePrincipalNumerator A j n) ≤
      gaussFun w (U.holeRadius j) (Polynomial.algEquivAevalXAddC (U.holeCenter j) A)*
        (w ((U.holeLocalDenominator j n).coeff 0))⁻¹ :=
  gaussFun_principalNumerator_le _ _ (U.holeLocalDenominator_coeff_zero_ne_zero j n) _
    (U.gaussFun_holeLocalDenominator j n).le n

/-- The exact whole original proper fraction, in the literal original localized rational ring. -/
def holePrincipalPart (A : K[X]) (j : Fin m) (n : ℕ) : U.RationalFunctions :=
  algebraMap K[X] U.RationalFunctions
    (Polynomial.algEquivAevalXAddC (-U.holeCenter j) (U.holePrincipalNumerator A j n)) *
      (U.rationalHoleInverse j)^n

theorem rationalValue_holePrincipalPart (A : K[X]) (j : Fin m) (n : ℕ) (x : U.carrier) :
    U.rationalValue (U.holePrincipalPart A j n) x =
      val x.1 (Polynomial.algEquivAevalXAddC (-U.holeCenter j) (U.holePrincipalNumerator A j n)) /
        (val x.1 (X-C (U.holeCenter j)))^n := by
  change (U.rationalPoint x).1.val (_ * _) = _
  rw [map_mul,map_pow]
  change U.rationalValue (algebraMap K[X] U.RationalFunctions _) x *
    (U.rationalValue (U.rationalHoleInverse j) x)^n = _
  rw [U.rationalValue_polynomial,U.rationalValue_holeInverse,inv_pow,div_eq_mul_inv]

/-- The actual original fraction with a common power of the genuine hole product. -/
def commonRationalFraction (A : K[X]) (n : ℕ) : U.RationalFunctions :=
  IsLocalization.mk' U.RationalFunctions A
    (⟨U.denominatorPolynomial^n,n,rfl⟩ : Submonoid.powers U.denominatorPolynomial)

theorem rationalValue_commonFraction (A : K[X]) (n : ℕ) (x : U.carrier) :
    U.rationalValue (U.commonRationalFraction A n) x =
      val x.1 A/(val x.1 U.denominatorPolynomial)^n := U.rationalValue_mk' A n x

theorem rationalValue_commonFraction_holeBoundary (A : K[X]) (j : Fin m) (n : ℕ) :
    U.rationalValue (U.commonRationalFraction A n) ⟨U.holeBoundaryPoint j,U.holeGauss_mem j⟩ =
      gaussFun w (U.holeRadius j) (Polynomial.algEquivAevalXAddC (U.holeCenter j) A) /
        ((U.holeRadius j)^n*w ((U.holeLocalDenominator j n).coeff 0)) := by
  rw [U.rationalValue_commonFraction]
  have hcoord : val (U.holeBoundaryPoint j) (X-C (U.holeCenter j)) = U.holeRadius j :=
    centeredGauss_val_X_sub_C _ _ _
  have hother : val (U.holeBoundaryPoint j) ((U.holeComplementPolynomial j)^n) =
      w ((U.holeLocalDenominator j n).coeff 0) := by
    change val (centeredGauss (self w) _ _) _ = _
    rw [centeredGauss_val_apply,U.holeLocalDenominator_translate]
    exact U.gaussFun_holeLocalDenominator j n
  have hden : (val (U.holeBoundaryPoint j) U.denominatorPolynomial)^n =
      (U.holeRadius j)^n*w ((U.holeLocalDenominator j n).coeff 0) := by
    rw [← map_pow,← U.holeCoordinate_mul_complement j,mul_pow,map_mul,map_pow,hcoord,hother]
  rw [hden]
  congr 1

/-- The DERIVED sharp bound holds at EVERY actual point, including touching/coincident Gauss boundaries. -/
theorem rationalValue_holePrincipalPart_le (A : K[X]) (j : Fin m) (n : ℕ) (x : U.carrier) :
    U.rationalValue (U.holePrincipalPart A j n) x ≤
      U.rationalValue (U.commonRationalFraction A n) ⟨U.holeBoundaryPoint j,U.holeGauss_mem j⟩ := by
  rw [U.rationalValue_holePrincipalPart,U.rationalValue_commonFraction_holeBoundary]
  have hb := properFraction_value_le (U.holePrincipalNumerator A j n) (U.holeCenter j) n
    (U.holePrincipalNumerator_coeff_large A j n) (U.holeRadius j) (U.holeRadius_pos j) x.1 (x.2.2 j)
  apply hb.trans
  have hnum := mul_le_mul' (U.gaussFun_holePrincipalNumerator_le A j n)
    (le_refl (((U.holeRadius j)^n)⁻¹))
  simpa only [div_eq_mul_inv,mul_inv_rev,mul_assoc] using hnum

/-- Whole ORIGINAL proper-fraction congruence, with the finite inverse CONSTRUCTED from original hole data. -/
theorem holePrincipalNumerator_congruence (A : K[X]) (j : Fin m) (n : ℕ) :
    (X-C (U.holeCenter j))^n ∣
      (U.holeComplementPolynomial j)^n *
        Polynomial.algEquivAevalXAddC (-U.holeCenter j) (U.holePrincipalNumerator A j n)-A := by
  let e := Polynomial.algEquivAevalXAddC (U.holeCenter j)
  have h := pow_X_dvd_principalNumerator_error (e A) (U.holeLocalDenominator j n)
    (U.holeLocalDenominator_coeff_zero_ne_zero j n) n
  have hm := map_dvd e.symm.toRingHom h
  have hX : e.symm X = X-C (U.holeCenter j) := by
    rw [show e.symm = Polynomial.algEquivAevalXAddC (-U.holeCenter j) from
      Polynomial.algEquivAevalXAddC_symm _]
    simp [Polynomial.algEquivAevalXAddC]
    ring
  have hq : e.symm (U.holeLocalDenominator j n) = (U.holeComplementPolynomial j)^n := by
    rw [← U.holeLocalDenominator_translate]
    exact e.symm_apply_apply _
  change e.symm (X^n) ∣ e.symm (_*_-e A) at hm
  rw [map_pow,hX,map_sub,map_mul,hq,AlgEquiv.symm_apply_apply] at hm
  simpa only [e,Polynomial.algEquivAevalXAddC_symm,holePrincipalNumerator] using hm

/-- The whole original finite-boundary seminorm of the CONSTRUCTED principal part is contractive. -/
theorem nnnorm_holePrincipalPart_le (A : K[X]) (j : Fin m) (n : ℕ) :
    ‖U.normedRationalEquiv.symm (U.holePrincipalPart A j n)‖₊ ≤
      ‖U.normedRationalEquiv.symm (U.commonRationalFraction A n)‖₊ := by
  let _ : Fintype U.boundary := U.rationalBoundaryFintype
  let zj : U.boundary := ⟨U.holeBoundaryPoint j,U.holeBoundaryPoint_mem_boundary j⟩
  have hb : U.rationalValue (U.commonRationalFraction A n) ⟨zj.1,U.boundary_subset zj.2⟩ ≤
      ‖U.normedRationalEquiv.symm (U.commonRationalFraction A n)‖₊ := by
    rw [U.nnnorm_normedRationalFunctions,RingEquiv.apply_symm_apply]
    exact Finset.le_sup (f := fun z : U.boundary =>
      U.rationalValue (U.commonRationalFraction A n) ⟨z.1,U.boundary_subset z.2⟩) (Finset.mem_univ zj)
  rw [U.nnnorm_normedRationalFunctions,RingEquiv.apply_symm_apply]
  apply Finset.sup_le
  intro z _
  exact (U.rationalValue_holePrincipalPart_le A j n ⟨z.1,U.boundary_subset z.2⟩).trans hb
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
