import EnvelopeProperty.Potential.LineStandardAffinoid
import EnvelopeProperty.Berkovich.RationalUnitAllPointLocalMaximum
import EnvelopeProperty.Berkovich.SpectrumLocalization
import Mathlib.Topology.Connected.Clopen

/-! # Actual localized rational functions on standard affine-line affinoids -/
open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The actual product of all original hole coordinates. -/
def denominatorPolynomial : K[X] := ∏ j, (X-C (U.holeCenter j))

theorem denominatorPolynomial_ne_zero : U.denominatorPolynomial ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero _

theorem denominatorPolynomial_val_ne_zero (x : U.carrier) :
    val x.1 U.denominatorPolynomial ≠ 0 := by
  classical
  rw [denominatorPolynomial,map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact ne_of_gt ((U.holeRadius_pos j).trans_le (x.2.2 j))

/-- This literal localization is the polynomial algebra with all original hole coordinates inverted. -/
abbrev RationalFunctions := Localization.Away U.denominatorPolynomial

/-- The original point's unique valuation extension to the actual rational algebra. -/
def rationalPoint (x : U.carrier) : RelativeSpectrum w U.RationalFunctions :=
  RelativeSpectrum.Away.lift w U.RationalFunctions U.denominatorPolynomial x.1
    (U.denominatorPolynomial_val_ne_zero x)

/-- The actual rational-function value, at the same original polynomial point. -/
def rationalValue (f : U.RationalFunctions) (x : U.carrier) : ℝ≥0 :=
  (U.rationalPoint x).1.val f

theorem rationalValue_polynomial (p : K[X]) (x : U.carrier) :
    U.rationalValue (algebraMap K[X] U.RationalFunctions p) x = val x.1 p :=
  RelativeSpectrum.Away.lift_val_algebraMap w U.RationalFunctions U.denominatorPolynomial
    x.1 (U.denominatorPolynomial_val_ne_zero x) p

theorem rationalValue_mk' (p : K[X]) (n : ℕ) (x : U.carrier) :
    U.rationalValue (IsLocalization.mk' U.RationalFunctions p
      (⟨U.denominatorPolynomial^n,n,rfl⟩ : Submonoid.powers U.denominatorPolynomial)) x =
      val x.1 p / val x.1 U.denominatorPolynomial ^ n :=
  RelativeSpectrum.Away.lift_val_mk' w U.RationalFunctions U.denominatorPolynomial
    x.1 (U.denominatorPolynomial_val_ne_zero x) p n

theorem continuous_rationalValue (f : U.RationalFunctions) : Continuous (U.rationalValue f) := by
  obtain ⟨p,n,hf⟩ := Spectrum.Away.exists_eq_mk' U.RationalFunctions U.denominatorPolynomial f
  have he : U.rationalValue f = fun x => val x.1 p / val x.1 U.denominatorPolynomial ^ n := by
    funext x
    rw [hf,U.rationalValue_mk']
  rw [he]
  exact ((continuous_val_apply p).comp continuous_subtype_val).div₀
    (((continuous_val_apply U.denominatorPolynomial).comp continuous_subtype_val).pow n)
    (fun x => pow_ne_zero n (U.denominatorPolynomial_val_ne_zero x))

/-- Every actual rational function evaluates in the ORIGINAL point's completed residue field. -/
def rationalEvaluation (x : U.carrier) : U.RationalFunctions →+* x.1.1.H :=
  IsLocalization.lift (M := Submonoid.powers U.denominatorPolynomial) (g := x.1.1.toH) (by
    rintro ⟨_,n,rfl⟩
    simpa only [map_pow] using (isUnit_iff_ne_zero.mpr fun h =>
      U.denominatorPolynomial_val_ne_zero x
        ((Spectrum.toH_eq_zero_iff x.1.1 (b := U.denominatorPolynomial)).mp h)).pow n)

theorem rationalEvaluation_polynomial (x : U.carrier) (p : K[X]) :
    U.rationalEvaluation x (algebraMap K[X] U.RationalFunctions p) = x.1.1.toH p := by
  rw [rationalEvaluation,IsLocalization.lift_eq]

/-- Localization uniqueness compares every genuine residue-field evaluation, with no residue-field identification. -/
theorem nnnorm_rationalEvaluation (x : U.carrier) (f : U.RationalFunctions) :
    ‖U.rationalEvaluation x f‖₊ = U.rationalValue f x := by
  let z := Spectrum.comap (U.rationalEvaluation x)
    (Spectrum.ofValuation (NormedField.valuation (K := x.1.1.H)))
  have he : Spectrum.Away.comap U.RationalFunctions z = x.1.1 := by
    apply Spectrum.ext_val
    intro p
    change ‖U.rationalEvaluation x (algebraMap K[X] U.RationalFunctions p)‖₊ = x.1.1.val p
    rw [U.rationalEvaluation_polynomial,Spectrum.nnnorm_toH]
  have hz : (U.rationalPoint x).1 = z := by
    apply Spectrum.Away.comap_injective U.RationalFunctions U.denominatorPolynomial
    rw [he]
    exact Spectrum.Away.comap_lift U.RationalFunctions U.denominatorPolynomial x.1.1
      (U.denominatorPolynomial_val_ne_zero x)
  change z.val f = _
  rw [← hz]
  rfl

/-- The original ratio of two original polynomial values, defined on the whole original line. -/
def rationalRatio (p q : K[X]) (x : RelativeSpectrum w K[X]) : ℝ≥0 :=
  val x p / val x q

variable [IsAlgClosed K]

/-- The all-point rational-unit theorem gives local constancy of the SAME original positive ratio. -/
theorem rationalRatio_eventually_eq_of_isLocalMax (p q : K[X])
    (x : RelativeSpectrum w K[X]) (hx : val x (p*q) ≠ 0)
    (hmax : IsLocalMax (rationalRatio p q) x) :
    ∀ᶠ y in 𝓝 x, rationalRatio p q y = rationalRatio p q x := by
  classical
  let P : Unit → K[X] := fun _ => p
  let Q : Unit → K[X] := fun _ => q
  let I : Finset Unit := {()}
  have hI : I.Nonempty := by simp [I]
  let M := RationalUnitFamily.maxValue w P Q I hI (fun _ => 0) (fun _ _ => 1)
  have hpos (y : RelativeSpectrum w K[X]) (hy : val y (p*q) ≠ 0) :
      0 < (rationalRatio p q y : ℝ) := by
    have hpq : val y p ≠ 0 ∧ val y q ≠ 0 := by
      simpa only [map_mul,mul_ne_zero_iff] using hy
    exact_mod_cast div_pos (pos_iff_ne_zero.mpr hpq.1) (pos_iff_ne_zero.mpr hpq.2)
  have hM (y : RelativeSpectrum w K[X]) (hy : val y (p*q) ≠ 0) :
      M y = Real.log (rationalRatio p q y : ℝ) := by
    have hpq : val y p ≠ 0 ∧ val y q ≠ 0 := by
      simpa only [map_mul,mul_ne_zero_iff] using hy
    simp only [M,RationalUnitFamily.maxValue,I,Finset.sup'_singleton,
      RationalUnitFamily.affineValue,Finset.univ_unique,Finset.sum_singleton,P,Q,
      one_mul,zero_add,rationalUnitLog_eq w p q y hy,EReal.toReal_coe,
      rationalRealLog,polynomialRealLog,rationalRatio,NNReal.coe_div]
    exact (Real.log_div (by exact_mod_cast hpq.1) (by exact_mod_cast hpq.2)).symm
  have hN : ∀ᶠ y in 𝓝 x, val y (p*q) ≠ 0 :=
    (isOpen_compl_singleton.preimage (continuous_val_apply (p*q))).mem_nhds hx
  have hmaxM : IsLocalMax M x := by
    filter_upwards [hmax,hN] with y hy hyN
    rw [hM y hyN,hM x hx]
    exact Real.log_le_log (hpos y hyN) (by exact_mod_cast hy)
  have hp : ∀ j, P j ≠ 0 := by
    intro j hp
    apply hx
    simp only [P] at hp
    simp [hp]
  have hq : ∀ j, Q j ≠ 0 := by
    intro j hq
    apply hx
    simp only [Q] at hq
    simp [hq]
  obtain ⟨W,hWo,hxW,hW,hunits⟩ :=
    RationalUnitFamily.exists_open_maxValue_constant_of_isLocalMax_any_point w P Q hp hq
      I hI (fun _ => 0) (fun _ _ => 1) x (fun _ => hx) hmaxM
  filter_upwards [hWo.mem_nhds hxW] with y hy
  have hyN := hunits y hy ()
  have hl : Real.log (rationalRatio p q y : ℝ) = Real.log (rationalRatio p q x : ℝ) := by
    rw [← hM y hyN,← hM x hx]
    exact hW y hy
  have he := congrArg Real.exp hl
  rw [Real.exp_log (hpos y hyN),Real.exp_log (hpos x hx)] at he
  exact_mod_cast he

/-- Every original polynomial ratio with no denominator zero on U attains its whole maximum at an original Gauss boundary point. -/
theorem rationalRatio_exists_boundary_max (p q : K[X])
    (hq : ∀ x ∈ U.carrier, val x q ≠ 0) :
    ∃ z ∈ U.boundary, ∀ x ∈ U.carrier, rationalRatio p q x ≤ rationalRatio p q z := by
  let _ : CompactSpace U.carrier := isCompact_iff_compactSpace.mp U.isCompact_carrier
  let _ : ConnectedSpace U.carrier := isConnected_iff_connectedSpace.mp U.isConnected_carrier
  let f : U.carrier → ℝ≥0 := fun x => rationalRatio p q x.1
  have hf : Continuous f := ((continuous_val_apply p).comp continuous_subtype_val).div₀
    ((continuous_val_apply q).comp continuous_subtype_val) (fun x => hq x.1 x.2)
  have hne : (Set.univ : Set U.carrier).Nonempty :=
    ⟨⟨U.outerGauss,U.outerGauss_mem⟩,Set.mem_univ _⟩
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn hne hf.continuousOn
  have hmax : ∀ y : U.carrier, f y ≤ f x := fun y => hx (Set.mem_univ y)
  by_cases hzero : f x = 0
  · refine ⟨U.outerGauss,Set.mem_insert _ _,?_⟩
    intro y hy
    have hy0 : f ⟨y,hy⟩ = 0 := le_zero_iff.mp ((hmax ⟨y,hy⟩).trans_eq hzero)
    change f ⟨y,hy⟩ ≤ f ⟨U.outerGauss,U.outerGauss_mem⟩
    rw [hy0]
    exact zero_le
  by_cases hboundary : ∃ z : U.carrier, z.1 ∈ U.boundary ∧ f z = f x
  · obtain ⟨z,hz,hze⟩ := hboundary
    exact ⟨z.1,hz,fun y hy => (hmax ⟨y,hy⟩).trans_eq hze.symm⟩
  · let M : Set U.carrier := {y | f y = f x}
    have hclosed : IsClosed M := isClosed_eq hf continuous_const
    have hopen : IsOpen M := by
      apply isOpen_iff_mem_nhds.mpr
      intro z hz
      change f z = f x at hz
      have hzB : z.1 ∉ U.boundary := fun hB => hboundary ⟨z,hB,hz⟩
      have hzInt : z.1 ∈ interior U.carrier := by
        rw [U.interior_carrier]
        exact ⟨z.2,hzB⟩
      have hU : ∀ᶠ y in 𝓝 z.1, y ∈ interior U.carrier :=
        isOpen_interior.mem_nhds hzInt
      have hlocal : IsLocalMax (rationalRatio p q) z.1 := hU.mono fun y hy =>
        (hmax ⟨y,interior_subset hy⟩).trans_eq hz.symm
      have hzp : val z.1 p ≠ 0 := by
        intro hp
        have hfz : f z = 0 := by simp [f,rationalRatio,hp]
        exact hzero (hz.symm.trans hfz)
      have hunit : val z.1 (p*q) ≠ 0 := by
        rw [map_mul]
        exact mul_ne_zero hzp (hq z.1 z.2)
      have he := rationalRatio_eventually_eq_of_isLocalMax p q z.1 hunit hlocal
      have hs : Tendsto (fun y : U.carrier => y.1) (𝓝 z) (𝓝 z.1) :=
        continuous_subtype_val.tendsto z
      exact (hs.eventually he).mono fun y hy => hy.trans hz
    have hMuniv : M = Set.univ := (show IsClopen M from ⟨hclosed,hopen⟩).eq_univ ⟨x,rfl⟩
    have houter : (⟨U.outerGauss,U.outerGauss_mem⟩ : U.carrier) ∈ M := by
      rw [hMuniv]
      exact Set.mem_univ _
    exact False.elim (hboundary ⟨⟨U.outerGauss,U.outerGauss_mem⟩,Set.mem_insert _ _,houter⟩)

/-- Finite-boundary maximum modulus is proved for EVERY element of the original localized rational algebra. -/
theorem rationalValue_exists_boundary_max (f : U.RationalFunctions) :
    ∃ z : U.boundary, ∀ x : U.carrier,
      U.rationalValue f x ≤ U.rationalValue f ⟨z.1,U.boundary_subset z.2⟩ := by
  obtain ⟨p,n,hf⟩ := Spectrum.Away.exists_eq_mk' U.RationalFunctions U.denominatorPolynomial f
  have hq : ∀ x ∈ U.carrier, val x (U.denominatorPolynomial^n) ≠ 0 := by
    intro x hx
    rw [map_pow]
    exact pow_ne_zero n (U.denominatorPolynomial_val_ne_zero ⟨x,hx⟩)
  obtain ⟨z,hz,hmax⟩ := U.rationalRatio_exists_boundary_max p (U.denominatorPolynomial^n) hq
  refine ⟨⟨z,hz⟩,?_⟩
  intro x
  rw [hf,U.rationalValue_mk',U.rationalValue_mk']
  simpa only [rationalRatio,map_pow] using hmax x.1 x.2
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
