/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothCone

/-!
# The charts `D_{iρ} = T_{s_{iρ}}` of the punctured cone, their `p`-bases and Jacobians

Let `k` be a field of characteristic `p`, `X = V(I) ⊆ ℙᴹ` with cone ring `T = S[t]`
(`ProjSubvariety.ConeRing`) and `K = Frac T`. This file contains `def:sg-charts` and
`lem:sg-jacobians`(1),(2) of the blueprint chapter `smooth-general.tex` (`subsec:sg-cone`;
Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Theorem 3.1,
`thm:smooth-EP`).

The localizations `T_s`, `s ∈ T ∖ 0`, are realized as `T`-subalgebras of `K`
(`ProjSubvariety.awaySubalgebra`), so that all charts and all Jacobians live in the one field `K`;
`T_s` is a localization of `T` at `s` (`ProjSubvariety.isLocalization_awaySubalgebra`).

## Main definitions

* `ProjSubvariety.awaySubalgebra X s = T_s = {f ∈ K : f s^m ∈ T for some m}`.
* `ProjSubvariety.chartFamily X i u`: for a chart `A_i` and `u : σ → A_i`, the family
  `v = (t, x̄ᵢ, u)` of `K`, indexed like the `p`-basis `ζ = (u, Y, t)` of the chart model;
  `ProjSubvariety.chartFamilyAway`: the same family in `T_s`.
* `ProjSubvariety.ChartDatum X p` (`def:sg-charts`): a chart `A_i`, a form `h̃` with
  `h = h̃ / x̄ᵢ^e`, and `u ∈ A_i^n` which is a `p`-basis of `k(X)` and of `(A_i)_h`; its form
  `s = xᵢ h̃` (`ChartDatum.s`), chart `D = T_s` (`ChartDatum.D`), `p`-basis `v` (`ChartDatum.v`) and
  the Jacobian `J(z/v)` of a homogeneous family `z` (`ChartDatum.jac`).

## Main results

* `ProjSubvariety.isPBasis_chartFamily` (`lem:sg-pbasis-basics`(2),(4)): if `u` is a `p`-basis of
  `k(X) = Frac(A_i)`, then `v = (u, x̄ᵢ, t)` is a `p`-basis of `K`.
* `ProjSubvariety.isPBasis_chartFamilyAway` (`def:sg-charts`): if moreover `u` is a `p`-basis of
  `(A_i)_h`, `h = h̃ / x̄ᵢ^e`, and `xᵢ h̃ ∣ s`, then `v` is a `p`-basis of `T_s`; in particular of
  `D = T_{xᵢ h̃} = (A_i)_h[x̄ᵢ^{±1}][t]` (`ChartDatum.isPBasis_v`) and of `T_{s s'}`.
* `ChartDatum.jac_eq`, `ChartDatum.isBihom_jac` (`lem:sg-jacobians`(1)): `J(z/v) = c x̄ᵢ^n` with
  `c ∈ k(X)`, `n = dim X`, bihomogeneous of bidegree `(n, 0)`; `ChartDatum.jac_mem`,
  `ChartDatum.jac_ne_zero`.
* `ChartDatum.div_jac_mem` (`lem:sg-jacobians`(2)): `J/J' ∈ T_{s s'}`.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

open ProjBerk (quotChartMk QuotChartAlg)

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-! ### The localizations `T_s ⊆ K` -/

/-- The localization `T_s = {f ∈ K : f s^m ∈ T for some m}` of the cone ring at `s`, as a
`T`-subalgebra of `K = Frac T`. -/
def awaySubalgebra (s : X.ConeRing) : Subalgebra X.ConeRing (FractionRing X.ConeRing) where
  carrier := {f | ∃ (a : X.ConeRing) (m : ℕ),
    f * algebraMap X.ConeRing (FractionRing X.ConeRing) s ^ m =
      algebraMap X.ConeRing (FractionRing X.ConeRing) a}
  mul_mem' := by
    rintro f g ⟨a, m, ha⟩ ⟨b, n, hb⟩
    exact ⟨a * b, m + n, by rw [map_mul, ← ha, ← hb, pow_add]; ring⟩
  add_mem' := by
    rintro f g ⟨a, m, ha⟩ ⟨b, n, hb⟩
    refine ⟨a * s ^ n + b * s ^ m, m + n, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hb, pow_add]
    ring
  algebraMap_mem' r := ⟨r, 0, by rw [pow_zero, mul_one]⟩

variable {X}

theorem mem_awaySubalgebra {s : X.ConeRing} {f : FractionRing X.ConeRing} :
    f ∈ X.awaySubalgebra s ↔ ∃ (a : X.ConeRing) (m : ℕ),
      f * algebraMap X.ConeRing (FractionRing X.ConeRing) s ^ m =
        algebraMap X.ConeRing (FractionRing X.ConeRing) a :=
  Iff.rfl

theorem algebraMap_mem_awaySubalgebra (s r : X.ConeRing) :
    algebraMap X.ConeRing (FractionRing X.ConeRing) r ∈ X.awaySubalgebra s :=
  (X.awaySubalgebra s).algebraMap_mem r

theorem inv_mem_awaySubalgebra (s : X.ConeRing) :
    (algebraMap X.ConeRing (FractionRing X.ConeRing) s)⁻¹ ∈ X.awaySubalgebra s := by
  by_cases hs : s = 0
  · subst hs
    rw [map_zero, inv_zero]
    exact (X.awaySubalgebra 0).zero_mem
  · refine ⟨1, 1, ?_⟩
    rw [pow_one, map_one, inv_mul_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hs)]

theorem awaySubalgebra_le_of_dvd {s s' : X.ConeRing} (h : s ∣ s') :
    X.awaySubalgebra s ≤ X.awaySubalgebra s' := by
  obtain ⟨r, rfl⟩ := h
  rintro f ⟨a, m, ha⟩
  exact ⟨a * r ^ m, m, by rw [map_mul, mul_pow, ← mul_assoc, ha, map_mul, map_pow]⟩

/-- `T_s` is a localization of `T` at `s` (for `s ≠ 0`). -/
theorem isLocalization_awaySubalgebra {s : X.ConeRing} (hs : s ≠ 0) :
    IsLocalization.Away s (X.awaySubalgebra s) := by
  have hs' : algebraMap X.ConeRing (FractionRing X.ConeRing) s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hs
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, fun {x y} hxy => ?_⟩
  · rintro ⟨_, m, rfl⟩
    refine IsUnit.of_mul_eq_one (⟨(algebraMap X.ConeRing (FractionRing X.ConeRing) s)⁻¹ ^ m,
      (X.awaySubalgebra s).pow_mem (inv_mem_awaySubalgebra s) m⟩) ?_
    apply Subtype.ext
    change algebraMap X.ConeRing (FractionRing X.ConeRing) (s ^ m) *
      (algebraMap X.ConeRing (FractionRing X.ConeRing) s)⁻¹ ^ m = 1
    rw [map_pow, ← mul_pow, mul_inv_cancel₀ hs', one_pow]
  · rintro ⟨f, a, m, ha⟩
    refine ⟨(a, ⟨s ^ m, m, rfl⟩), Subtype.ext ?_⟩
    change f * algebraMap X.ConeRing (FractionRing X.ConeRing) (s ^ m) =
      algebraMap X.ConeRing (FractionRing X.ConeRing) a
    rw [map_pow, ha]
  · refine ⟨1, ?_⟩
    have : algebraMap X.ConeRing (FractionRing X.ConeRing) x =
        algebraMap X.ConeRing (FractionRing X.ConeRing) y := congrArg Subtype.val hxy
    rw [IsFractionRing.injective _ _ this]

instance charP_awaySubalgebra (p : ℕ) [Fact p.Prime] [CharP k p] (s : X.ConeRing) :
    CharP (X.awaySubalgebra s) p :=
  CharP.subring' (FractionRing X.ConeRing) p (X.awaySubalgebra s).toSubring

/-! ### `p`-bases of localizations from `p`-bases of `K` -/

section PBasis

open Cartier

variable (p : ℕ) [hp : Fact p.Prime]

/-- If every element of `A` is in the `B^p`-span of the monomials of a family `y` of a
localization `B` of `A`, then so is every element of `B`. -/
theorem surjective_pSum_of_isLocalization' {A B : Type*} [CommRing A] [CommRing B] [CharP B p]
    [Algebra A B] (N : Submonoid A) [IsLocalization N B] {σ : Type*} [Fintype σ] [DecidableEq σ]
    {y : σ → B} (h : ∀ r : A, algebraMap A B r ∈ AddMonoidHom.mrange (pSum p y)) :
    Function.Surjective (pSum p y) := by
  intro x
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective N x
  show ∃ c, pSum p y c = IsLocalization.mk' B a m
  set v := IsLocalization.mk' B (1 : A) m
  have hv : v * algebraMap A B m = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  have hp1 : p = p - 1 + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
  have hx : IsLocalization.mk' B a m = v ^ p * algebraMap A B (a * (m : A) ^ (p - 1)) := by
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    calc algebraMap A B a * v = algebraMap A B a * v * (v * algebraMap A B m) ^ (p - 1) := by
          rw [hv, one_pow, mul_one]
      _ = v ^ (p - 1 + 1) * algebraMap A B (a * (m : A) ^ (p - 1)) := by
          rw [map_mul, map_pow]; ring
      _ = _ := by rw [← hp1]
  rw [hx]
  exact pow_mul_mem_range_pSum p _ _ (h _)

/-- A family of a subring `R ⊆ K` of a field whose image is a `p`-basis of `K` and whose monomials
span `R` over `R^p` is a `p`-basis of `R`. -/
theorem isPBasis_of_isPBasis_val {K : Type*} [Field K] [CharP K p] {R : Type*} [CommRing R]
    [CharP R p] (φ : R →+* K) (hφ : Function.Injective φ) {σ : Type*} [Fintype σ]
    [DecidableEq σ] {y : σ → R} (hK : IsPBasis p (φ ∘ y)) (hs : Function.Surjective (pSum p y)) :
    IsPBasis p y := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, hs⟩
  have h1 : pSum p (φ ∘ y) (φ ∘ c) = 0 := by
    rw [← map_pSum, hc, map_zero]
  have h2 : φ ∘ c = 0 := hK.injective (h1.trans (map_zero _).symm)
  funext a
  exact hφ ((congr_fun h2 a).trans (map_zero φ).symm)

end PBasis

/-! ### The chart families `v = (u, x̄ᵢ, t)` -/

section ChartFamily

open Cartier

variable (X) (i : Fin (M + 1)) [Fact (MvPolynomial.X i ∉ X.ideal)]

/-- The chart family `v = (t, x̄ᵢ, u)` of `K` attached to `u : σ → A_i`, indexed like the
`p`-basis `ζ = (u, Y, t)` of the chart model (`none ↦ t`, `some none ↦ x̄ᵢ`,
`some (some l) ↦ uₗ`). -/
def chartFamily {σ : Type*} (u : σ → X.ChartAlg i) :
    Option (Option σ) → FractionRing X.ConeRing :=
  fun o => o.elim X.fracT fun o' => o'.elim (X.fracMk (MvPolynomial.X i)) fun l =>
    X.chartAlgToFrac i (u l)

variable {X i}

theorem chartFamily_eq_modelToFrac {σ : Type*} (u : σ → X.ChartAlg i) :
    X.chartFamily i u = X.modelToFrac i ∘ fun o : Option (Option σ) => o.elim Polynomial.X
      fun o' => Polynomial.C (o'.elim (LaurentPolynomial.T 1) fun l =>
        LaurentPolynomial.C (algebraMap (X.ChartAlg i) (X.ChartField i) (u l))) := by
  funext o
  rcases o with _ | _ | l
  · simp [chartFamily, modelToFrac_X]
  · have h := modelToFrac_monomial (X := X) (j := i) 1 1 0
    simp only [map_one, one_mul, pow_zero, mul_one, zpow_one] at h
    simp only [chartFamily, Option.elim_none, Option.elim_some, Function.comp_apply]
    rw [← h]
  · simp only [chartFamily, Option.elim_some, Function.comp_apply]
    rw [modelToFrac_C_C, chartFieldToFrac_algebraMap]

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- **`lem:sg-pbasis-basics`(2),(4)**: if `u` is a `p`-basis of `k(X) = Frac(A_i)`, the chart
family `v = (u, x̄ᵢ, t)` is a `p`-basis of `K = Frac T`. -/
theorem isPBasis_chartFamily {σ : Type*} [Fintype σ] [DecidableEq σ] {u : σ → X.ChartAlg i}
    (hu : IsPBasis p (algebraMap (X.ChartAlg i) (X.ChartField i) ∘ u)) :
    IsPBasis p (X.chartFamily i u) := by
  rw [chartFamily_eq_modelToFrac]
  exact X.isPBasis_modelToFrac_laurentFamily p i hu

end ChartFamily

/-! ### The charts `D = T_s` with `xᵢ h̃ ∣ s` and their `p`-bases (`def:sg-charts`) -/

variable (X) in
/-- The element `ā ∈ T` (a constant in `t`) of a polynomial `a ∈ R_M`. -/
def coneS (a : MvPolynomial (Fin (M + 1)) k) : X.ConeRing := Polynomial.C (X.coordMk a)

theorem algebraMap_coneS (a : MvPolynomial (Fin (M + 1)) k) :
    algebraMap X.ConeRing (FractionRing X.ConeRing) (X.coneS a) = X.fracMk a :=
  (fracMk_apply a).symm

theorem coneS_ne_zero {a : MvPolynomial (Fin (M + 1)) k} (ha : a ∉ X.ideal) : X.coneS a ≠ 0 := by
  rw [coneS, Ne, Polynomial.C_eq_zero, coordMk_eq_zero_iff]
  exact ha

theorem fracMk_mem_awaySubalgebra (s : X.ConeRing) (a : MvPolynomial (Fin (M + 1)) k) :
    X.fracMk a ∈ X.awaySubalgebra s := by
  rw [← algebraMap_coneS]
  exact algebraMap_mem_awaySubalgebra s _

theorem fracT_mem_awaySubalgebra (s : X.ConeRing) : X.fracT ∈ X.awaySubalgebra s :=
  algebraMap_mem_awaySubalgebra s _

section ChartAway

variable {i : Fin (M + 1)} [Fact (MvPolynomial.X i ∉ X.ideal)]

/-- `A_i ⊆ T_s` when `x̄ᵢ ∣ s`. -/
theorem chartAlgToFrac_mem_awaySubalgebra {s : X.ConeRing}
    (hs : X.coneS (MvPolynomial.X i) ∣ s) (a : X.ChartAlg i) :
    X.chartAlgToFrac i a ∈ X.awaySubalgebra s := by
  refine awaySubalgebra_le_of_dvd hs ?_
  obtain ⟨N, τ, hτ, rfl⟩ := exists_quotDehom_eq a
  refine ⟨X.coneS τ, N, ?_⟩
  rw [algebraMap_coneS, algebraMap_coneS, chartAlgToFrac_quotDehom_mul hτ]

/-- `h⁻¹ ∈ T_s` for `h = h̃ / x̄ᵢ^e` when `xᵢ h̃ ∣ s`. -/
theorem inv_chartAlgToFrac_mem_awaySubalgebra {s : X.ConeRing} {h : MvPolynomial (Fin (M + 1)) k}
    {e : ℕ} (hh : h.IsHomogeneous e) (hs : X.coneS (MvPolynomial.X i * h) ∣ s) :
    (X.chartAlgToFrac i (X.quotDehom i h))⁻¹ ∈ X.awaySubalgebra s := by
  refine awaySubalgebra_le_of_dvd hs ?_
  rw [chartAlgToFrac_quotDehom hh]
  by_cases h0 : X.fracMk h = 0
  · rw [h0, zero_div, inv_zero]
    exact Subalgebra.zero_mem _
  · refine ⟨X.coneS (MvPolynomial.X i ^ (e + 1)), 1, ?_⟩
    rw [algebraMap_coneS, algebraMap_coneS, map_mul, map_pow, pow_one, inv_div]
    have hx := fracMk_X_ne_zero (X := X) (j := i)
    field_simp
    ring

variable (X i) in
/-- The chart family `v = (t, x̄ᵢ, u)` as a family of `T_s` (for `x̄ᵢ ∣ s`). -/
def chartFamilyAway {σ : Type*} (u : σ → X.ChartAlg i) {s : X.ConeRing}
    (hs : X.coneS (MvPolynomial.X i) ∣ s) : Option (Option σ) → X.awaySubalgebra s :=
  fun o => ⟨X.chartFamily i u o, by
    rcases o with _ | _ | l
    · exact fracT_mem_awaySubalgebra s
    · exact fracMk_mem_awaySubalgebra s _
    · exact chartAlgToFrac_mem_awaySubalgebra hs (u l)⟩

theorem coe_chartFamilyAway {σ : Type*} (u : σ → X.ChartAlg i) {s : X.ConeRing}
    (hs : X.coneS (MvPolynomial.X i) ∣ s) (o : Option (Option σ)) :
    (X.chartFamilyAway i u hs o : FractionRing X.ConeRing) = X.chartFamily i u o :=
  rfl

omit [Fact (MvPolynomial.X i ∉ X.ideal)] in
theorem coneS_X_dvd {h : MvPolynomial (Fin (M + 1)) k} {s : X.ConeRing}
    (hs : X.coneS (MvPolynomial.X i * h) ∣ s) : X.coneS (MvPolynomial.X i) ∣ s :=
  dvd_trans ⟨X.coneS h, by simp only [coneS, map_mul]⟩ hs

open Cartier

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- **The chart `p`-bases** (`def:sg-charts`, `lem:sg-pbasis-basics`(3),(4)). Let `u` be a
`p`-basis of `k(X) = Frac(A_i)` and of `(A_i)_h`, `h = h̃ / x̄ᵢ^e`, and let `s ≠ 0` be divisible by
`xᵢ h̃` in `T`. Then `v = (u, x̄ᵢ, t)` is a `p`-basis of `T_s`. (For `s = xᵢ h̃` this is the chart
`D = T_s = (A_i)_h[x̄ᵢ^{±1}][t]`.) -/
theorem isPBasis_chartFamilyAway {σ : Type*} [Fintype σ] [DecidableEq σ] {u : σ → X.ChartAlg i}
    (hu : IsPBasis p (algebraMap (X.ChartAlg i) (X.ChartField i) ∘ u))
    {h : MvPolynomial (Fin (M + 1)) k} {e : ℕ} (hh : h.IsHomogeneous e)
    [CharP (Localization.Away (X.quotDehom i h)) p]
    (huh : IsPBasis p (algebraMap (X.ChartAlg i) (Localization.Away (X.quotDehom i h)) ∘ u))
    {s : X.ConeRing} (hs0 : s ≠ 0) (hs : X.coneS (MvPolynomial.X i * h) ∣ s) :
    IsPBasis p (X.chartFamilyAway i u (coneS_X_dvd hs)) := by
  have := isLocalization_awaySubalgebra (X := X) hs0
  set D := X.awaySubalgebra s
  set y := X.chartFamilyAway i u (coneS_X_dvd hs)
  refine isPBasis_of_isPBasis_val p D.val.toRingHom Subtype.val_injective
    (isPBasis_chartFamily p hu) ?_
  -- the `k`-subalgebra `∑_a D^p y^a`
  set Sub := pSumSubalgebra p y k
  have hy : ∀ o, y o ∈ Sub := fun o => by
    have : y o = mono y (Pi.single o 1) := by rw [mono_single, pow_one]
    rw [this]
    exact mono_mem_range_pSum p y _
  -- `A_i → T_s`
  let ψA : X.ChartAlg i →+* D := RingHom.codRestrict (X.chartAlgToFrac i : X.ChartAlg i →+* _)
    D (chartAlgToFrac_mem_awaySubalgebra (coneS_X_dvd hs))
  have hunit : IsUnit (ψA (X.quotDehom i h)) := by
    refine IsUnit.of_mul_eq_one (⟨_, inv_chartAlgToFrac_mem_awaySubalgebra hh hs⟩ : D) ?_
    apply Subtype.ext
    change X.chartAlgToFrac i (X.quotDehom i h) * (X.chartAlgToFrac i (X.quotDehom i h))⁻¹ = 1
    refine mul_inv_cancel₀ ?_
    intro h0
    have hsx : X.coneS (MvPolynomial.X i * h) ≠ 0 := fun h' => hs0 (by
      obtain ⟨r, rfl⟩ := hs
      rw [h', zero_mul])
    have hhI : h ∉ X.ideal := fun hI => hsx (by
      rw [coneS, Polynomial.C_eq_zero, coordMk_eq_zero_iff]
      exact X.ideal.mul_mem_left _ hI)
    rw [chartAlgToFrac_quotDehom hh, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact fracMk_ne_zero hhI h0
    · exact pow_ne_zero _ fracMk_X_ne_zero h0
  let ψh : Localization.Away (X.quotDehom i h) →+* D := IsLocalization.Away.lift _ hunit
  have hψh : ∀ a, ψh (algebraMap _ _ a) = ψA a := fun a => IsLocalization.Away.lift_eq _ hunit a
  -- `A_i` lands in `Sub`
  have hA : ∀ a : X.ChartAlg i, ψA a ∈ Sub := by
    intro a
    obtain ⟨c, hc⟩ := huh.surjective (algebraMap _ (Localization.Away (X.quotDehom i h)) a)
    have h1 : ψA a = pSum p (ψh ∘ algebraMap _ _ ∘ u) (ψh ∘ c) := by
      rw [← hψh, ← hc, map_pSum]
    rw [h1, pSum_apply]
    refine Sub.sum_mem fun b _ => Sub.mul_mem ?_ ?_
    · have := pow_mul_mem_range_pSum p y ((ψh ∘ c) b) (mono_mem_range_pSum p y 0)
      rwa [mono_zero, mul_one] at this
    · refine Sub.prod_mem fun l _ => Sub.pow_mem ?_ _
      have : (ψh ∘ algebraMap _ _ ∘ u) l = y (some (some l)) := by
        apply Subtype.ext
        simp only [Function.comp_apply, hψh]
        rfl
      rw [this]
      exact hy _
  -- the generators of `T` land in `Sub`
  have hxj : ∀ j, algebraMap X.ConeRing D (Polynomial.C (X.coordMk (MvPolynomial.X j))) ∈ Sub := by
    intro j
    have : algebraMap X.ConeRing D (Polynomial.C (X.coordMk (MvPolynomial.X j))) =
        ψA (X.quotDehom i (MvPolynomial.X j)) * y (some none) := by
      apply Subtype.ext
      change algebraMap X.ConeRing (FractionRing X.ConeRing)
        (Polynomial.C (X.coordMk (MvPolynomial.X j))) =
          X.chartAlgToFrac i (X.quotDehom i (MvPolynomial.X j)) * X.fracMk (MvPolynomial.X i)
      have h2 := chartAlgToFrac_quotDehom_mul (X := X) (j := i) (MvPolynomial.isHomogeneous_X k j)
      rw [pow_one] at h2
      rw [h2, fracMk_apply]
    rw [this]
    exact Sub.mul_mem (hA _) (hy _)
  have hT : ∀ r : X.ConeRing, algebraMap X.ConeRing D r ∈ Sub := by
    intro r
    obtain ⟨g, rfl⟩ := coneMk_surjective (X := X) r
    induction g using Polynomial.induction_on with
    | C a =>
      rw [coneMk_C]
      induction a using MvPolynomial.induction_on with
      | C κ =>
        have : algebraMap X.ConeRing D (Polynomial.C (X.coordMk (MvPolynomial.C κ))) =
            algebraMap k D κ := by
          rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Polynomial.algebraMap_apply,
            ← IsScalarTower.algebraMap_apply]
        rw [this]
        exact Sub.algebraMap_mem κ
      | add a b ha hb =>
        rw [map_add, Polynomial.C_add, map_add]
        exact Sub.add_mem ha hb
      | mul_X a j ha =>
        rw [map_mul, Polynomial.C_mul, map_mul]
        exact Sub.mul_mem ha (hxj j)
    | add f g hf hg =>
      rw [map_add, map_add]
      exact Sub.add_mem hf hg
    | monomial n a ha =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, coneMk_X]
      refine Sub.mul_mem ha ?_
      have : algebraMap X.ConeRing D Polynomial.X = y none := Subtype.ext rfl
      rw [this]
      exact hy none
  exact surjective_pSum_of_isLocalization' p (Submonoid.powers s) hT

end ChartAway

/-! ### Chart data (`def:sg-charts`) -/

section ChartDatum

open Cartier

variable (X) (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- A **chart datum** `(i, h̃, u)` (`def:sg-charts`): a chart `A_i` (`xᵢ ∉ I`), a form `h̃ ∉ I` of
degree `e` with `h = h̃ / x̄ᵢ^e ∈ A_i`, and `u ∈ A_i^n` (`n = dim X`) which is a `p`-basis of
`k(X) = Frac(A_i)` and of `(A_i)_h`. Its chart is `D = T_s`, `s = x̄ᵢ h̃`
(`ProjSubvariety.ChartDatum.D`), with the `p`-basis `v = (u, x̄ᵢ, t)`. -/
structure ChartDatum where
  /-- The index `i` of the chart `A_i`. -/
  i : Fin (M + 1)
  [fact : Fact (MvPolynomial.X i ∉ X.ideal)]
  /-- The form `h̃`, with `h = h̃ / x̄ᵢ^e`. -/
  h : MvPolynomial (Fin (M + 1)) k
  /-- The degree of `h̃`. -/
  e : ℕ
  isHomogeneous : h.IsHomogeneous e
  notMem : h ∉ X.ideal
  [charP : CharP (Localization.Away (X.quotDehom i h)) p]
  /-- The `p`-basis `u` of `(A_i)_h`. -/
  u : Fin X.dim → X.ChartAlg i
  isPBasis_field : IsPBasis p (algebraMap (X.ChartAlg i) (X.ChartField i) ∘ u)
  isPBasis_away : IsPBasis p (algebraMap (X.ChartAlg i) (Localization.Away (X.quotDehom i h)) ∘ u)

attribute [instance] ChartDatum.fact ChartDatum.charP

namespace ChartDatum

variable {X p} (C : X.ChartDatum p)

/-- The form `s = xᵢ h̃` of degree `e + 1` (`s_{iρ}` in `def:sg-charts`). -/
def form : MvPolynomial (Fin (M + 1)) k := MvPolynomial.X C.i * C.h

theorem form_isHomogeneous : C.form.IsHomogeneous (C.e + 1) := by
  have := (MvPolynomial.isHomogeneous_X k C.i).mul C.isHomogeneous
  rwa [add_comm 1 C.e] at this

theorem form_notMem : C.form ∉ X.ideal := fun h =>
  (X.isPrime.mem_or_mem h).elim (Fact.out : MvPolynomial.X C.i ∉ X.ideal) C.notMem

/-- `s = x̄ᵢ h̃ ∈ T`. -/
def s : X.ConeRing := X.coneS C.form

theorem s_ne_zero : C.s ≠ 0 := coneS_ne_zero C.form_notMem

theorem algebraMap_s : algebraMap X.ConeRing (FractionRing X.ConeRing) C.s = X.fracMk C.form :=
  algebraMap_coneS _

theorem algebraMap_s_ne_zero : algebraMap X.ConeRing (FractionRing X.ConeRing) C.s ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 C.s_ne_zero

/-- The chart `D = T_s = (A_i)_h[x̄ᵢ^{±1}][t] ⊆ K` (`def:sg-charts`). -/
abbrev D : Subalgebra X.ConeRing (FractionRing X.ConeRing) := X.awaySubalgebra C.s

instance isLocalization_D : IsLocalization.Away C.s C.D :=
  isLocalization_awaySubalgebra C.s_ne_zero

instance isNoetherianRing_D : IsNoetherianRing C.D :=
  IsLocalization.isNoetherianRing (Submonoid.powers C.s) C.D inferInstance

/-- The chart family `v = (t, x̄ᵢ, u)` of `K`. -/
def vK : Option (Option (Fin X.dim)) → FractionRing X.ConeRing := X.chartFamily C.i C.u

/-- `v` is a `p`-basis of `K`. -/
theorem isPBasis_vK : IsPBasis p C.vK := isPBasis_chartFamily p C.isPBasis_field

/-- The chart family `v = (t, x̄ᵢ, u)` as a family of `D`. -/
def v : Option (Option (Fin X.dim)) → C.D := X.chartFamilyAway C.i C.u (coneS_X_dvd dvd_rfl)

theorem coe_v (o : Option (Option (Fin X.dim))) : (C.v o : FractionRing X.ConeRing) = C.vK o :=
  rfl

variable [PerfectRing k p]

/-- **`v` is a `p`-basis of the chart `D`** (`def:sg-charts`). -/
theorem isPBasis_v : IsPBasis p C.v :=
  isPBasis_chartFamilyAway p C.isPBasis_field C.isHomogeneous C.isPBasis_away C.s_ne_zero dvd_rfl

/-- `v` is a `p`-basis of every `T_{s'}` with `s ∣ s'`, `s' ≠ 0` (e.g. `T_{s s'}`). -/
theorem isPBasis_away_of_dvd {s' : X.ConeRing} (hs0 : s' ≠ 0) (hs : C.s ∣ s') :
    IsPBasis p (X.chartFamilyAway C.i C.u (coneS_X_dvd hs)) :=
  isPBasis_chartFamilyAway p C.isPBasis_field C.isHomogeneous C.isPBasis_away hs0 hs

/-! #### The Jacobians `J = J(z/v)` (`def:sg-charts`, `lem:sg-jacobians`) -/

/-- The Jacobian `J(z/v) = det(∂zₐ/∂v_b) ∈ K` of the family `z = X.coneZ ι` with respect to the
chart `p`-basis `v` (`def:sg-charts`). -/
def jac (idx : Option (Fin X.dim) → Fin (M + 1)) : FractionRing X.ConeRing :=
  C.isPBasis_vK.jac (algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx)

theorem jac_congr {σ : Type*} [Fintype σ] [DecidableEq σ] {A : Type*} [CommRing A] [CharP A p]
    {y y' : σ → A} (hy : IsPBasis p y) (hy' : IsPBasis p y') (h : y = y') (w : σ → A) :
    hy.jac w = hy'.jac w := by
  subst h
  rfl

omit [PerfectRing k p] in
/-- **`lem:sg-jacobians`(1)**: `J(z/v) = c x̄ᵢ^n` with `c = det N ∈ k(X)`, `n = dim X`. -/
theorem jac_eq (idx : Option (Fin X.dim) → Fin (M + 1)) :
    C.jac idx = X.chartFieldToFrac C.i (coneJacMatrix C.isPBasis_field
        (fun o => algebraMap _ (X.ChartField C.i) (X.quotDehom C.i (MvPolynomial.X (idx o))))).det *
      X.fracMk (MvPolynomial.X C.i) ^ X.dim := by
  have hζK := C.isPBasis_field.isPBasis_algebraMap_laurentFamily (K := FractionRing X.ConeRing)
  have hjac := C.isPBasis_field.jac_algebraMap_coneFamily (K := FractionRing X.ConeRing)
    (fun o => algebraMap _ (X.ChartField C.i) (X.quotDehom C.i (MvPolynomial.X (idx o))))
  rw [jac, jac_congr C.isPBasis_vK hζK (chartFamily_eq_modelToFrac C.u),
    algebraMap_comp_coneZ idx C.i]
  refine hjac.trans ?_
  have h := modelToFrac_monomial (X := X) (j := C.i) ((coneJacMatrix C.isPBasis_field
    (fun o => algebraMap _ (X.ChartField C.i) (X.quotDehom C.i (MvPolynomial.X (idx o))))).det)
    (Fintype.card (Fin X.dim) : ℤ) 0
  rw [pow_zero, mul_one, pow_zero, mul_one, Fintype.card_fin, zpow_natCast] at h
  rw [Fintype.card_fin]
  exact h

omit [PerfectRing k p] in
/-- **`lem:sg-jacobians`(1)**: `J(z/v)` is bihomogeneous of bidegree `(n, 0)`, `n = dim X`. -/
theorem isBihom_jac (idx : Option (Fin X.dim) → Fin (M + 1)) : X.IsBihom (C.jac idx) X.dim 0 := by
  rw [C.jac_eq, isBihom_iff_chartModel (j := C.i)]
  refine ⟨(coneJacMatrix C.isPBasis_field
    (fun o => algebraMap _ (X.ChartField C.i) (X.quotDehom C.i (MvPolynomial.X (idx o))))).det, ?_⟩
  rw [modelToFrac_monomial, pow_zero, mul_one, zpow_natCast]

omit [PerfectRing k p] in
/-- `J(z/v) ≠ 0` when `z` is a `p`-basis of `K` (`lem:sg-jacobians`(1)). -/
theorem jac_ne_zero {idx : Option (Fin X.dim) → Fin (M + 1)}
    (hz : IsPBasis p (algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx)) :
    C.jac idx ≠ 0 :=
  (IsPBasis.isUnit_jac C.isPBasis_vK hz).ne_zero

/-- `J(z/v) ∈ D`: the derivations of the `p`-basis `v` of `D` preserve `D`, and `z ⊆ T ⊆ D`
(`lem:sg-jacobians`(1)). -/
theorem jac_mem (idx : Option (Fin X.dim) → Fin (M + 1)) : C.jac idx ∈ C.D := by
  have h := IsPBasis.jac_map (C.D.val : C.D →+* FractionRing X.ConeRing) C.isPBasis_v
    C.isPBasis_vK (algebraMap X.ConeRing C.D ∘ X.coneZ idx)
  have h' : C.jac idx = (C.D.val : C.D →+* FractionRing X.ConeRing)
      (C.isPBasis_v.jac (algebraMap X.ConeRing C.D ∘ X.coneZ idx)) := h
  rw [h']
  exact (C.isPBasis_v.jac _).2

/-- **`lem:sg-jacobians`(2)**: `J/J' = J(v'/v)` lies in `T_{s s'}` (the derivations of `v`, a
`p`-basis of `T_{s s'}`, preserve `T_{s s'}`); by symmetry `J/J'` is a unit there. -/
theorem div_jac_mem (C' : X.ChartDatum p) {idx : Option (Fin X.dim) → Fin (M + 1)}
    (hz : IsPBasis p (algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx)) :
    C.jac idx / C'.jac idx ∈ X.awaySubalgebra (C.s * C'.s) := by
  have hs0 : C.s * C'.s ≠ 0 := mul_ne_zero C.s_ne_zero C'.s_ne_zero
  have hv := C.isPBasis_away_of_dvd hs0 (dvd_mul_right _ _)
  have h1 := IsPBasis.jac_mul C.isPBasis_vK C'.isPBasis_vK
    (algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx)
  have h2 : C.jac idx / C'.jac idx = C.isPBasis_vK.jac C'.vK := by
    rw [div_eq_iff (C'.jac_ne_zero hz), jac, jac, h1, mul_comm]
  have h3 := IsPBasis.jac_map ((X.awaySubalgebra (C.s * C'.s)).val :
      X.awaySubalgebra (C.s * C'.s) →+* FractionRing X.ConeRing) hv C.isPBasis_vK
    (X.chartFamilyAway C'.i C'.u (coneS_X_dvd (dvd_mul_left C'.s C.s)))
  have h3' : C.isPBasis_vK.jac C'.vK = ((X.awaySubalgebra (C.s * C'.s)).val :
      X.awaySubalgebra (C.s * C'.s) →+* FractionRing X.ConeRing)
        (hv.jac (X.chartFamilyAway C'.i C'.u (coneS_X_dvd (dvd_mul_left C'.s C.s)))) := h3
  rw [h2, h3']
  exact (hv.jac _).2

end ChartDatum

end ChartDatum

end ProjSubvariety

end EnvelopeProperty
