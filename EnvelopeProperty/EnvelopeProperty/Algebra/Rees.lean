/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.NormalDVR
import EnvelopeProperty.Algebra.NormalizationFinite
import EnvelopeProperty.Algebra.RootableActionMinimalPrimes

/-!
# Rees valuation rings

Let `B` be a domain with fraction field `K` and let `I = (g_ℓ)_{ℓ ∈ ι}` be a finite family of
elements of `B`. For each `ℓ` with `g_ℓ ≠ 0` let `D_ℓ = B[g_i / g_ℓ : i ∈ ι] ⊆ K` be the affine
chart of the blowup of `I` and `E_ℓ` its integral closure in `K`. The *Rees valuation rings* of
`(I; g)` are the localizations `(E_ℓ)_P` at the minimal primes `P` of `g_ℓ E_ℓ`.

When `B` is a finitely generated domain over a perfect field `k`, every `E_ℓ` is a Noetherian
integrally closed domain (finiteness of normalization, `thm:bj-normalization-finite`), so the Rees
valuation rings form a finite set of discrete valuation rings containing `B` and essentially of
finite type over `k` (`lem:bj-dvr-minimal`). This is `def:bj-rees` of the blueprint (`bj22.tex`),
adapted from Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field*
(`bj22-trivval:defi:Rees`, `bj22-trivval:lem:CLT`, `bj22-trivval:lem:Shilov`), where Rees
valuations are defined through the normalized blowup of a flag ideal.

## Main results

* `EnvelopeProperty.valuation_le_pow_of_forall_dvd` (**`thm:bj-rees`**): the Rees valuations
  detect integral closure of powers against seminorms. If `w` is a multiplicative ultrametric
  seminorm on `B` (a `Valuation B ℝ≥0`) with `w ≤ 1` on `B` and `w (g ℓ) ≠ 0` for some `ℓ`, and
  `F ∈ B` satisfies `ord_V F ≥ r ord_V I` for every Rees valuation ring `V` (in divisibility
  form: `g_i ^ r ∣ F` in `V` for some `i`), then `w F ≤ max_ℓ w (g ℓ) ^ r`, which is
  `sup_{f ∈ I^r} w f` (`valuation_le_sup_pow_of_mem_span_pow`).
* `EnvelopeProperty.isDiscreteValuationRing_reesValuationRing`,
  `EnvelopeProperty.finite_reesIndex`, `EnvelopeProperty.essFiniteType_reesValuationRing`,
  `EnvelopeProperty.algebraMap_reesValuationRing_injective`: the Rees valuation rings form a
  finite family of discrete valuation rings `B ⊆ V ⊆ K`, essentially of finite type over `k`.
* `EnvelopeProperty.algebraMap_dvd_reesValuationRing`: `ord_V I = ord_V g_ℓ` for `V` attached to
  the chart `ℓ`.
* `EnvelopeProperty.isNoetherianRing_reesNormalChart`: the charts `E_ℓ` are Noetherian over a
  perfect field.
* **`lem:bj-rees-invariant`** (`B = A[t]`, `g_ℓ = h_ℓ t^{e_ℓ}`, `t^N ∈ I`, `k` algebraically
  closed): `EnvelopeProperty.not_isUnit_algebraMap_X_reesValuationRing`,
  `EnvelopeProperty.algebraMap_X_mem_maximalIdeal_reesValuationRing` and
  `EnvelopeProperty.addVal_X_pos_reesValuationRing` (`ord_V t > 0`), and
  `EnvelopeProperty.addVal_reesValuationRing_eq_inf` (`ord_V (∑ f_λ t^λ) = min_λ (ord_V f_λ +
  λ ord_V t)`), via the torus action `t ↦ c t` (`EnvelopeProperty.comap_torusAutE_eq_self`: it fixes
  the minimal primes of `g_ℓ E_ℓ`) and a Vandermonde argument
  (`EnvelopeProperty.algebraMap_dvd_algebraMap_C_coeff_mul_X_pow`).

## Implementation notes

* The Rees valuation rings are subalgebras `V` of `K` over `B`, indexed by the type
  `ReesIndex K g` of triples `(ℓ, P)` with `g ℓ ≠ 0` and `P` a minimal prime of `g_ℓ E_ℓ`. The
  blueprint assumes all `g_ℓ ≠ 0`; charts with `g_ℓ = 0` are simply omitted here. In
  `thm:bj-rees` only the chart where `w (g ℓ)` is maximal (hence nonzero) is used.
* The algebraic part only needs the charts `E_ℓ` to be Noetherian; this is an instance argument
  `[∀ ℓ, IsNoetherianRing (reesNormalChart K g ℓ)]`, discharged over a perfect field by
  `isNoetherianRing_reesNormalChart`.
* Hypotheses `ord_V F ≥ r ord_V I` are phrased by divisibility in `V`; `exists_dvd_iff_addVal_le`
  translates them to `IsDiscreteValuationRing.addVal`.
-/

open scoped NNReal nonZeroDivisors Polynomial

open IsLocalRing

noncomputable section

namespace EnvelopeProperty

/-! ### An integral equation estimate -/

/-- If `f` is a root of a monic polynomial whose coefficients have valuation `≤ 1`, then
`v f ≤ 1` (the ultrametric inequality). -/
theorem valuation_le_one_of_monic_eval₂_eq_zero {R A : Type*} [CommRing R] [CommRing A]
    (v : Valuation A ℝ≥0) (ψ : R →+* A) {p : Polynomial R} (hp : p.Monic) {f : A}
    (hf : p.eval₂ ψ f = 0) (hc : ∀ i < p.natDegree, v (ψ (p.coeff i)) ≤ 1) : v f ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  have hvf : 0 < v f := lt_trans one_pos hlt
  have heq : f ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i := by
    have h := hf
    rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at h
    exact eq_neg_of_add_eq_zero_left h
  have hlt' : v (∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i) < v f ^ p.natDegree := by
    refine v.map_sum_lt (pow_ne_zero _ hvf.ne') fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [v.map_mul, v.map_pow]
    calc v (ψ (p.coeff i)) * v f ^ i ≤ 1 * v f ^ i :=
          mul_le_mul_of_nonneg_right (hc i hi') zero_le
      _ < v f ^ (p.natDegree - i) * v f ^ i :=
          mul_lt_mul_of_pos_right (one_lt_pow₀ hlt (by omega)) (pow_pos hvf _)
      _ = v f ^ p.natDegree := by rw [← pow_add, Nat.sub_add_cancel hi'.le]
  have h2 : v (f ^ p.natDegree) = v (∑ i ∈ Finset.range p.natDegree, ψ (p.coeff i) * f ^ i) := by
    rw [heq, Valuation.map_neg]
  rw [v.map_pow] at h2
  rw [← h2] at hlt'
  exact lt_irrefl _ hlt'

/-! ### The charts of the blowup and their normalizations -/

section Charts

variable {B : Type*} [CommRing B] (K : Type*) [Field K] [Algebra B K]
  {ι : Type*} (g : ι → B)

/-- The affine chart `D_ℓ = B[g_i / g_ℓ : i ∈ ι] ⊆ K` of the blowup of `(g_i)_i`. -/
def reesChart (ℓ : ι) : Subalgebra B K :=
  Algebra.adjoin B (Set.range fun i => algebraMap B K (g i) / algebraMap B K (g ℓ))

/-- The normalization `E_ℓ` of the chart `D_ℓ`: the integral closure of `D_ℓ` in `K`. -/
def reesNormalChart (ℓ : ι) : Subalgebra B K :=
  (integralClosure (reesChart K g ℓ) K).restrictScalars B

variable {K g}

/-- The generators `g_i / g_ℓ` lie in the chart `D_ℓ`. -/
theorem div_mem_reesChart (i ℓ : ι) :
    algebraMap B K (g i) / algebraMap B K (g ℓ) ∈ reesChart K g ℓ :=
  Algebra.subset_adjoin ⟨i, rfl⟩

/-- `z ∈ E_ℓ` if and only if `z` is integral over `D_ℓ`. -/
theorem mem_reesNormalChart_iff {ℓ : ι} {z : K} :
    z ∈ reesNormalChart K g ℓ ↔ IsIntegral (reesChart K g ℓ) z :=
  Iff.rfl

/-- `D_ℓ ⊆ E_ℓ`. -/
theorem reesChart_le_reesNormalChart (ℓ : ι) : reesChart K g ℓ ≤ reesNormalChart K g ℓ :=
  fun z hz => isIntegral_algebraMap (R := reesChart K g ℓ) (x := ⟨z, hz⟩)

variable (K g) [IsFractionRing B K]

/-- The normalized charts `E_ℓ` are integrally closed. -/
instance isIntegrallyClosed_reesNormalChart (ℓ : ι) :
    IsIntegrallyClosed (reesNormalChart K g ℓ) :=
  isIntegrallyClosed_integralClosure (reesChart K g ℓ) K

/-- Over a perfect field `k`, the normalized charts `E_ℓ` of a finitely generated `k`-domain are
Noetherian (`thm:bj-normalization-finite`). -/
theorem isNoetherianRing_reesNormalChart (k : Type*) [Field k] [PerfectField k] [Algebra k B]
    [Algebra.FiniteType k B] [Algebra k K] [IsScalarTower k B K] [Finite ι] (ℓ : ι) :
    IsNoetherianRing (reesNormalChart K g ℓ) := by
  have : IsDomain B := (IsFractionRing.injective B K).isDomain
  have : Algebra.FiniteType B (reesChart K g ℓ) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  have : Algebra.FiniteType k (reesChart K g ℓ) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact isNoetherianRing_integralClosure k (reesChart K g ℓ) K

/-- Over a perfect field `k`, the normalized charts `E_ℓ` of a finitely generated `k`-domain are
finitely generated `k`-algebras. -/
theorem finiteType_reesNormalChart (k : Type*) [Field k] [PerfectField k] [Algebra k B]
    [Algebra.FiniteType k B] [Algebra k K] [IsScalarTower k B K] [Finite ι] (ℓ : ι) :
    Algebra.FiniteType k (reesNormalChart K g ℓ) := by
  have : IsDomain B := (IsFractionRing.injective B K).isDomain
  have : Algebra.FiniteType B (reesChart K g ℓ) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  have : Algebra.FiniteType k (reesChart K g ℓ) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact finiteType_integralClosure k (reesChart K g ℓ) K

end Charts

/-! ### Rees valuation rings -/

section ReesValuationRings

variable {B : Type*} [CommRing B] (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
  {ι : Type*} (g : ι → B)

/-- The index type of the Rees valuation rings of `(g_i)_i`: pairs `(ℓ, P)` with `g ℓ ≠ 0` and
`P` a minimal prime of `g_ℓ E_ℓ` (`def:bj-rees`). -/
structure ReesIndex where
  /-- The chart. -/
  idx : ι
  /-- The minimal prime of `g_ℓ E_ℓ`. -/
  ideal : Ideal (reesNormalChart K g idx)
  /-- The generator `g_ℓ` of the chart is nonzero. -/
  ne_zero : g idx ≠ 0
  /-- `P` is a minimal prime of `g_ℓ E_ℓ`. -/
  mem_minimalPrimes :
    ideal ∈ (Ideal.span {algebraMap B (reesNormalChart K g idx) (g idx)}).minimalPrimes

variable {K g}

/-- The ideal of a Rees index is prime. -/
instance ReesIndex.isPrime (x : ReesIndex K g) : x.ideal.IsPrime :=
  x.mem_minimalPrimes.1.1

variable (K g)

/-- The Rees valuation ring `V = (E_ℓ)_P ⊆ K` attached to `x = (ℓ, P)` (`def:bj-rees`). -/
def reesValuationRing (x : ReesIndex K g) : Subalgebra B K :=
  (Localization.subalgebra.ofField K x.ideal.primeCompl
    x.ideal.primeCompl_le_nonZeroDivisors).restrictScalars B

variable {K g}

/-- The elements of `V = (E_ℓ)_P` are the fractions `a / s` with `a, s ∈ E_ℓ`, `s ∉ P`. -/
theorem mem_reesValuationRing {x : ReesIndex K g} {z : K} :
    z ∈ reesValuationRing K g x ↔
      ∃ (a s : reesNormalChart K g x.idx) (_ : s ∉ x.ideal), z = a * (s : K)⁻¹ :=
  Iff.rfl

/-- `E_ℓ ⊆ V`. -/
theorem reesNormalChart_le_reesValuationRing (x : ReesIndex K g) :
    reesNormalChart K g x.idx ≤ reesValuationRing K g x := fun z hz =>
  mem_reesValuationRing.2 ⟨⟨z, hz⟩, 1, x.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2, by simp⟩

/-- `D_ℓ ⊆ V`. -/
theorem reesChart_le_reesValuationRing (x : ReesIndex K g) :
    reesChart K g x.idx ≤ reesValuationRing K g x :=
  (reesChart_le_reesNormalChart x.idx).trans (reesNormalChart_le_reesValuationRing x)

/-- `B ⊆ V`: the structure map `B → V` is injective. -/
theorem algebraMap_reesValuationRing_injective (x : ReesIndex K g) :
    Function.Injective (algebraMap B (reesValuationRing K g x)) := by
  intro a b hab
  apply IsFractionRing.injective B K
  exact congrArg Subtype.val hab

/-- `g_ℓ` divides every `g_i` in a Rees valuation ring attached to the chart `ℓ`: the order of
`I` along `V` is that of `g_ℓ` (`def:bj-rees`). -/
theorem algebraMap_dvd_reesValuationRing (x : ReesIndex K g) (i : ι) :
    algebraMap B (reesValuationRing K g x) (g x.idx) ∣
      algebraMap B (reesValuationRing K g x) (g i) := by
  refine ⟨⟨_, reesChart_le_reesValuationRing x (div_mem_reesChart i x.idx)⟩, ?_⟩
  apply Subtype.ext
  have h0 : algebraMap B K (g x.idx) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).2 x.ne_zero
  change algebraMap B K (g i) = algebraMap B K (g x.idx) *
    (algebraMap B K (g i) / algebraMap B K (g x.idx))
  rw [mul_div_cancel₀ _ h0]

/-- **`lem:bj-dvr-minimal`, applied to `def:bj-rees`.** Each Rees valuation ring is a discrete
valuation ring (if the chart `E_ℓ` is Noetherian). -/
instance isDiscreteValuationRing_reesValuationRing (x : ReesIndex K g)
    [IsNoetherianRing (reesNormalChart K g x.idx)] :
    IsDiscreteValuationRing (reesValuationRing K g x) := by
  have hh : algebraMap B (reesNormalChart K g x.idx) (g x.idx) ≠ 0 := by
    intro h
    apply x.ne_zero
    apply IsFractionRing.injective B K
    rw [map_zero]
    exact congrArg Subtype.val h
  have : IsDiscreteValuationRing (Localization.AtPrime x.ideal) :=
    isDiscreteValuationRing_localization_of_mem_minimalPrimes hh x.mem_minimalPrimes
  let e := IsLocalization.algEquiv x.ideal.primeCompl (Localization.AtPrime x.ideal)
    (Localization.subalgebra.ofField K x.ideal.primeCompl x.ideal.primeCompl_le_nonZeroDivisors)
  have : IsDiscreteValuationRing (Localization.subalgebra.ofField K x.ideal.primeCompl
      x.ideal.primeCompl_le_nonZeroDivisors) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  exact this

omit [IsFractionRing B K] in
/-- There are finitely many Rees valuation rings. -/
theorem finite_reesIndex [Finite ι] [∀ ℓ, IsNoetherianRing (reesNormalChart K g ℓ)] :
    Finite (ReesIndex K g) := by
  have (ℓ : ι) : Finite
      (Ideal.span {algebraMap B (reesNormalChart K g ℓ) (g ℓ)}).minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).to_subtype
  refine Finite.of_injective (β := Σ ℓ : ι,
    (Ideal.span {algebraMap B (reesNormalChart K g ℓ) (g ℓ)}).minimalPrimes)
    (fun x => ⟨x.idx, x.ideal, x.mem_minimalPrimes⟩) ?_
  rintro ⟨ℓ, P, h, hP⟩ ⟨ℓ', P', h', hP'⟩ hxy
  simp only [Sigma.mk.injEq] at hxy
  obtain ⟨rfl, hPP⟩ := hxy
  simp only [heq_eq_eq, Subtype.mk.injEq] at hPP
  subst hPP
  rfl

/-- Over a perfect field, the Rees valuation rings of a finitely generated domain are essentially
of finite type. -/
theorem essFiniteType_reesValuationRing (k : Type*) [Field k] [PerfectField k] [Algebra k B]
    [Algebra.FiniteType k B] [Algebra k K] [IsScalarTower k B K] [Finite ι]
    (x : ReesIndex K g) : Algebra.EssFiniteType k (reesValuationRing K g x) := by
  have := finiteType_reesNormalChart K g k x.idx
  have : Algebra.EssFiniteType (reesNormalChart K g x.idx)
      (Localization.subalgebra.ofField K x.ideal.primeCompl
        x.ideal.primeCompl_le_nonZeroDivisors) :=
    Algebra.EssFiniteType.of_isLocalization _ x.ideal.primeCompl
  have : Algebra.EssFiniteType k (Localization.subalgebra.ofField K x.ideal.primeCompl
      x.ideal.primeCompl_le_nonZeroDivisors) :=
    Algebra.EssFiniteType.comp k (reesNormalChart K g x.idx) _
  exact this

/-- In a Rees valuation ring `V` attached to the chart `ℓ`, `ord_V F ≥ r ord_V I` (that is,
`g_i ^ r ∣ F` for some `i`) if and only if `r ord_V g_ℓ ≤ ord_V F`. -/
theorem exists_dvd_iff_addVal_le (x : ReesIndex K g)
    [IsNoetherianRing (reesNormalChart K g x.idx)] (F : B) (r : ℕ) :
    (∃ i, algebraMap B (reesValuationRing K g x) (g i) ^ r ∣
        algebraMap B (reesValuationRing K g x) F) ↔
      r • IsDiscreteValuationRing.addVal (reesValuationRing K g x)
          (algebraMap B (reesValuationRing K g x) (g x.idx)) ≤
        IsDiscreteValuationRing.addVal (reesValuationRing K g x)
          (algebraMap B (reesValuationRing K g x) F) := by
  rw [← AddValuation.map_pow, IsDiscreteValuationRing.addVal_le_iff_dvd]
  refine ⟨fun ⟨i, hi⟩ => (pow_dvd_pow_of_dvd (algebraMap_dvd_reesValuationRing x i) r).trans hi,
    fun h => ⟨x.idx, h⟩⟩

/-! ### Rees valuations detect integral closure (`thm:bj-rees`) -/

/-- **Divisibility step of `thm:bj-rees`.** If `g_ℓ ^ r ∣ F` in every Rees valuation ring of the
chart `ℓ`, then `F / g_ℓ ^ r ∈ E_ℓ` (`lem:bj-dvr-minimal`). -/
theorem div_pow_mem_reesNormalChart {ℓ : ι} [IsNoetherianRing (reesNormalChart K g ℓ)]
    (hℓ : g ℓ ≠ 0) {F : B} {r : ℕ}
    (hF : ∀ x : ReesIndex K g, x.idx = ℓ →
      algebraMap B (reesValuationRing K g x) (g x.idx) ^ r ∣
        algebraMap B (reesValuationRing K g x) F) :
    algebraMap B K F / algebraMap B K (g ℓ) ^ r ∈ reesNormalChart K g ℓ := by
  set E := reesNormalChart K g ℓ
  have h0 : algebraMap B K (g ℓ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).2 hℓ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [pow_zero, div_one]; exact Subalgebra.algebraMap_mem _ _
  have hh : algebraMap B E (g ℓ) ^ r ≠ 0 := by
    refine pow_ne_zero _ fun h => h0 ?_
    exact congrArg Subtype.val h
  have key : algebraMap B E F ∈ Ideal.span {algebraMap B E (g ℓ) ^ r} := by
    rw [mem_span_singleton_iff_forall_minimalPrimes hh]
    intro P hP
    rw [minimalPrimes_span_singleton_pow _ hr.ne'] at hP
    let x : ReesIndex K g := ⟨ℓ, P, hℓ, hP⟩
    obtain ⟨v, hv⟩ := hF x rfl
    obtain ⟨a, s, hs, hvas⟩ := mem_reesValuationRing.1 v.2
    refine ⟨s, hs, Ideal.mem_span_singleton'.2 ⟨a, ?_⟩⟩
    have hv' : algebraMap B K F = algebraMap B K (g ℓ) ^ r * (v : K) := congrArg Subtype.val hv
    have hs0 : (s : K) ≠ 0 := fun h => hs (by
      rw [show s = 0 from Subtype.ext h]; exact Ideal.zero_mem _)
    apply Subtype.ext
    change (a : K) * algebraMap B K (g ℓ) ^ r = (s : K) * algebraMap B K F
    rw [hv', hvas]
    field_simp
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 key
  have hc' : (c : K) * algebraMap B K (g ℓ) ^ r = algebraMap B K F := congrArg Subtype.val hc
  rw [← hc', mul_div_cancel_right₀ _ (pow_ne_zero _ h0)]
  exact c.2

/-- **`thm:bj-rees`, chart form.** Let `w` be a multiplicative ultrametric seminorm on `B`, `≤ 1`
on `B`, and let `ℓ` be such that `w (g ℓ) ≠ 0` is maximal among the `w (g i)`. If `g_ℓ ^ r ∣ F`
in every Rees valuation ring of the chart `ℓ`, then `w F ≤ w (g ℓ) ^ r`. -/
theorem valuation_le_pow_of_forall_dvd_chart {ℓ : ι} [IsNoetherianRing (reesNormalChart K g ℓ)]
    (w : Valuation B ℝ≥0) (hw : ∀ b, w b ≤ 1) (hmax : ∀ i, w (g i) ≤ w (g ℓ))
    (hℓ0 : w (g ℓ) ≠ 0) {F : B} {r : ℕ}
    (hF : ∀ x : ReesIndex K g, x.idx = ℓ →
      algebraMap B (reesValuationRing K g x) (g x.idx) ^ r ∣
        algebraMap B (reesValuationRing K g x) F) :
    w F ≤ w (g ℓ) ^ r := by
  have hℓ : g ℓ ≠ 0 := fun h => hℓ0 (by rw [h, map_zero])
  have hz := div_pow_mem_reesNormalChart hℓ hF
  have hS : Submonoid.powers (g ℓ) ≤ B⁰ :=
    have : IsDomain B := (IsFractionRing.injective B K).isDomain
    powers_le_nonZeroDivisors_of_noZeroDivisors hℓ
  -- The localization `B[1/g_ℓ] ⊆ K` and the extension `w'` of `w` to it.
  set S := Localization.subalgebra.ofField K (Submonoid.powers (g ℓ)) hS
  have hS' : Submonoid.powers (g ℓ) ≤ w.supp.primeCompl := by
    rintro _ ⟨n, rfl⟩
    change g ℓ ^ n ∉ w.supp
    rw [Valuation.mem_supp_iff, map_pow]
    exact pow_ne_zero _ hℓ0
  set w' := w.extendToLocalization hS' S
  have h0 : algebraMap B K (g ℓ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).2 hℓ
  -- `w' (b / g_ℓ ^ n) = w b / w g_ℓ ^ n`.
  have hw' : ∀ (y : S) (b : B) (n : ℕ), (y : K) * algebraMap B K (g ℓ) ^ n = algebraMap B K b →
      w' y * w (g ℓ) ^ n = w b := by
    intro y b n hy
    have : y * algebraMap B S (g ℓ ^ n) = algebraMap B S b := by
      apply Subtype.ext
      change (y : K) * algebraMap B K (g ℓ ^ n) = algebraMap B K b
      rw [map_pow, hy]
    rw [← map_pow, ← Valuation.extendToLocalization_apply_map_apply w hS' S, ← map_mul, this,
      Valuation.extendToLocalization_apply_map_apply]
  have hmemS : ∀ (b : B) (n : ℕ), algebraMap B K b / algebraMap B K (g ℓ) ^ n ∈ S := fun b n =>
    ⟨b, g ℓ ^ n, ⟨n, rfl⟩, by rw [div_eq_mul_inv, map_pow]⟩
  -- `D_ℓ ⊆ B[1/g_ℓ]` and `w' ≤ 1` on `D_ℓ`.
  have hD : ∀ d ∈ reesChart K g ℓ, ∃ hd : d ∈ S, w' ⟨d, hd⟩ ≤ 1 := by
    intro d hd
    induction hd using Algebra.adjoin_induction with
    | mem d hd =>
      obtain ⟨i, rfl⟩ := hd
      have hmem := hmemS (g i) 1
      rw [pow_one] at hmem
      refine ⟨hmem, ?_⟩
      have := hw' ⟨_, hmem⟩ (g i) 1 (by
        change algebraMap B K (g i) / algebraMap B K (g ℓ) * algebraMap B K (g ℓ) ^ 1 = _
        rw [pow_one, div_mul_cancel₀ _ h0])
      rw [pow_one] at this
      have hpos : 0 < w (g ℓ) := pos_iff_ne_zero.2 hℓ0
      by_contra hlt
      rw [not_le] at hlt
      have := mul_lt_mul_of_pos_right hlt hpos
      rw [one_mul] at this
      exact absurd (hmax i) (not_le.2 (by linarith))
    | algebraMap b =>
      refine ⟨S.algebraMap_mem b, ?_⟩
      have : (⟨algebraMap B K b, S.algebraMap_mem b⟩ : S) = algebraMap B S b := rfl
      rw [this, Valuation.extendToLocalization_apply_map_apply]
      exact hw b
    | add d e _ _ hd he =>
      obtain ⟨hd, hd1⟩ := hd
      obtain ⟨he, he1⟩ := he
      refine ⟨S.add_mem hd he, ?_⟩
      have : (⟨d + e, S.add_mem hd he⟩ : S) = ⟨d, hd⟩ + ⟨e, he⟩ := rfl
      rw [this]
      exact (w'.map_add _ _).trans (max_le hd1 he1)
    | mul d e _ _ hd he =>
      obtain ⟨hd, hd1⟩ := hd
      obtain ⟨he, he1⟩ := he
      refine ⟨S.mul_mem hd he, ?_⟩
      have : (⟨d * e, S.mul_mem hd he⟩ : S) = ⟨d, hd⟩ * ⟨e, he⟩ := rfl
      rw [this, map_mul]
      exact mul_le_one' hd1 he1
  have hDS : reesChart K g ℓ ≤ S := fun d hd => (hD d hd).1
  set ψ : reesChart K g ℓ →+* S := (Subalgebra.inclusion hDS).toRingHom
  set z' : S := ⟨_, hmemS F r⟩
  obtain ⟨p, hpm, hpe⟩ := (mem_reesNormalChart_iff.1 hz)
  have heval : p.eval₂ ψ z' = 0 := by
    apply Subtype.val_injective
    have := Polynomial.hom_eval₂ p ψ (S.val : S →+* K) z'
    rw [ZeroMemClass.coe_zero, ← hpe]
    exact this
  have hz1 : w' z' ≤ 1 :=
    valuation_le_one_of_monic_eval₂_eq_zero w' ψ hpm heval fun i _ => (hD _ (p.coeff i).2).2
  have := hw' z' F r (by
    change algebraMap B K F / algebraMap B K (g ℓ) ^ r * algebraMap B K (g ℓ) ^ r = _
    rw [div_mul_cancel₀ _ (pow_ne_zero _ h0)])
  rw [← this]
  calc w' z' * w (g ℓ) ^ r ≤ 1 * w (g ℓ) ^ r := mul_le_mul_of_nonneg_right hz1 zero_le
    _ = w (g ℓ) ^ r := one_mul _

/-- **`thm:bj-rees` (Rees valuations detect integral closure).** Let `w` be a multiplicative
ultrametric seminorm on `B` with `w ≤ 1` on `B` and `w (g i) ≠ 0` for some `i`. If
`ord_V F ≥ r ord_V I` for every Rees valuation ring `V` (that is, `g_i ^ r ∣ F` in `V` for some
`i`), then `w F ≤ w (g ℓ) ^ r` for every `ℓ` maximizing `w (g ℓ)`. -/
theorem valuation_le_pow_of_forall_dvd [∀ ℓ, IsNoetherianRing (reesNormalChart K g ℓ)]
    (w : Valuation B ℝ≥0) (hw : ∀ b, w b ≤ 1) (hg : ∃ i, w (g i) ≠ 0) {F : B} {r : ℕ}
    (hF : ∀ x : ReesIndex K g, ∃ i, algebraMap B (reesValuationRing K g x) (g i) ^ r ∣
      algebraMap B (reesValuationRing K g x) F)
    {ℓ : ι} (hmax : ∀ i, w (g i) ≤ w (g ℓ)) :
    w F ≤ w (g ℓ) ^ r := by
  obtain ⟨i, hi⟩ := hg
  have hℓ0 : w (g ℓ) ≠ 0 := fun h => hi (le_antisymm ((hmax i).trans h.le) zero_le)
  refine valuation_le_pow_of_forall_dvd_chart (K := K) w hw hmax hℓ0 fun x _ => ?_
  obtain ⟨j, hj⟩ := hF x
  exact (pow_dvd_pow_of_dvd (algebraMap_dvd_reesValuationRing x j) r).trans hj

/-- **`thm:bj-rees`, maximum form.** Under the hypotheses of `valuation_le_pow_of_forall_dvd`,
`w F ≤ (max_i w (g i)) ^ r`. -/
theorem valuation_le_sup_pow_of_forall_dvd [Fintype ι]
    [∀ ℓ, IsNoetherianRing (reesNormalChart K g ℓ)]
    (w : Valuation B ℝ≥0) (hw : ∀ b, w b ≤ 1) (hg : ∃ i, w (g i) ≠ 0) {F : B} {r : ℕ}
    (hF : ∀ x : ReesIndex K g, ∃ i, algebraMap B (reesValuationRing K g x) (g i) ^ r ∣
      algebraMap B (reesValuationRing K g x) F) :
    w F ≤ (Finset.univ.sup fun i => w (g i)) ^ r := by
  obtain ⟨i₀, hi₀⟩ := hg
  obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_max_image Finset.univ (fun i => w (g i))
    ⟨i₀, Finset.mem_univ _⟩
  have hsup : (Finset.univ.sup fun i => w (g i)) = w (g ℓ) :=
    le_antisymm (Finset.sup_le fun i _ => hℓ i (Finset.mem_univ _))
      (Finset.le_sup (f := fun i => w (g i)) (Finset.mem_univ ℓ))
  rw [hsup]
  exact valuation_le_pow_of_forall_dvd w hw ⟨i₀, hi₀⟩ hF fun i => hℓ i (Finset.mem_univ _)

end ReesValuationRings

/-- If `w ≤ 1` on `B`, then `w f ≤ (max_i w (g i)) ^ r` for `f ∈ I ^ r`, `I = (g_i)_i`. -/
theorem valuation_le_sup_pow_of_mem_span_pow {B : Type*} [CommRing B] {ι : Type*} [Fintype ι]
    (g : ι → B) (w : Valuation B ℝ≥0) (hw : ∀ b, w b ≤ 1) {r : ℕ} {f : B}
    (hf : f ∈ Ideal.span (Set.range g) ^ r) : w f ≤ (Finset.univ.sup fun i => w (g i)) ^ r := by
  set M := Finset.univ.sup fun i => w (g i)
  have hI : ∀ b ∈ Ideal.span (Set.range g), w b ≤ M := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      exact Finset.le_sup (f := fun i => w (g i)) (Finset.mem_univ i)
    | zero => rw [map_zero]; exact zero_le
    | add a b _ _ ha hb => exact w.map_add_le ha hb
    | smul c b _ hb =>
      rw [smul_eq_mul, map_mul]
      calc w c * w b ≤ 1 * M := mul_le_mul' (hw c) hb
        _ = M := one_mul M
  induction r generalizing f with
  | zero => rw [pow_zero]; exact hw f
  | succ r ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => w.map_add_le ha hb)
    rw [map_mul, pow_succ]
    exact mul_le_mul' (ih ha) (hI b hb)

/-- The last equality of `thm:bj-rees`: if `w ≤ 1` on `B`, then
`sup_{f ∈ I^r} w f = (max_i w (g i)) ^ r`, and the supremum is attained. -/
theorem isGreatest_valuation_span_pow {B : Type*} [CommRing B] {ι : Type*} [Fintype ι]
    (g : ι → B) (w : Valuation B ℝ≥0) (hw : ∀ b, w b ≤ 1) (r : ℕ) :
    IsGreatest (w '' (Ideal.span (Set.range g) ^ r : Ideal B))
      ((Finset.univ.sup fun i => w (g i)) ^ r) := by
  refine ⟨?_, ?_⟩
  · rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Finset.univ_eq_empty, Finset.sup_empty]
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [pow_zero, pow_zero, Ideal.one_eq_top]
        exact ⟨1, Submodule.mem_top, map_one w⟩
      · exact ⟨0, Ideal.zero_mem _, by rw [map_zero, bot_eq_zero', zero_pow hr.ne']⟩
    · obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_max_image Finset.univ (fun i => w (g i))
        Finset.univ_nonempty
      have hsup : (Finset.univ.sup fun i => w (g i)) = w (g ℓ) :=
        le_antisymm (Finset.sup_le fun i _ => hℓ i (Finset.mem_univ _))
          (Finset.le_sup (f := fun i => w (g i)) (Finset.mem_univ ℓ))
      exact ⟨g ℓ ^ r, Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self ℓ)) r,
        by rw [map_pow, hsup]⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact valuation_le_sup_pow_of_mem_span_pow g w hw hf

/-! ### The torus action on `A[t]` -/

section Torus

open Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

private theorem torus_comp_aux (a b : k) (hab : a * b = 1) :
    (C (algebraMap k A a) * X).comp (C (algebraMap k A b) * X) = (X : A[X]) := by
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, ← map_mul, hab, map_one, C_1, one_mul]

variable (A) in
/-- The torus automorphism `t ↦ c t` of `A[t]`, for `c ∈ kˣ`. -/
def torusAut (c : kˣ) : A[X] ≃ₐ[A] A[X] :=
  algEquivOfCompEqX (C (algebraMap k A c) * X) (C (algebraMap k A ↑c⁻¹) * X)
    (torus_comp_aux _ _ c.mul_inv) (torus_comp_aux _ _ c.inv_mul)

/-- `torusAut c f = f(c t)`. -/
theorem torusAut_apply (c : kˣ) (f : A[X]) :
    torusAut A c f = f.comp (C (algebraMap k A c) * X) := by
  simp [torusAut, comp_eq_aeval]

/-- The torus multiplies the coefficient of `t ^ n` by `c ^ n`. -/
theorem coeff_torusAut (c : kˣ) (f : A[X]) (n : ℕ) :
    (torusAut A c f).coeff n = f.coeff n * algebraMap k A ((c : k) ^ n) := by
  rw [torusAut_apply, comp_C_mul_X_coeff, map_pow]

/-- `torusAut` is an action of `kˣ`. -/
theorem torusAut_mul_apply (c d : kˣ) (f : A[X]) :
    torusAut A (c * d) f = torusAut A c (torusAut A d f) := by
  ext n
  simp only [coeff_torusAut, Units.val_mul, mul_pow, map_mul, mul_assoc]
  ring

/-- `torusAut 1` is the identity. -/
theorem torusAut_one_apply (f : A[X]) : torusAut A (1 : kˣ) f = f := by
  ext n
  simp [coeff_torusAut]

/-- The torus acts on a monomial `a t ^ n` by the scalar `c ^ n`. -/
theorem torusAut_C_mul_X_pow (c : kˣ) (a : A) (n : ℕ) :
    torusAut A c (C a * X ^ n) = C (algebraMap k A ((c : k) ^ n)) * (C a * X ^ n) := by
  ext m
  rw [coeff_torusAut, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; ring
  · simp

variable {K : Type*} [Field K] [Algebra A[X] K] [IsFractionRing A[X] K]

variable (A K) in
/-- The extension of the torus automorphism `torusAut c` to the fraction field `K` of `A[t]`. -/
def torusAutK (c : kˣ) : K ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv (torusAut A c : A[X] ≃ₐ[A] A[X]).toRingEquiv

/-- `torusAutK c` extends `torusAut c`. -/
theorem torusAutK_algebraMap (c : kˣ) (f : A[X]) :
    torusAutK A K c (algebraMap A[X] K f) = algebraMap A[X] K (torusAut A c f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ f

/-- `torusAutK` is an action of `kˣ`. -/
theorem torusAutK_mul_apply (c d : kˣ) (y : K) :
    torusAutK A K (c * d) y = torusAutK A K c (torusAutK A K d y) := by
  have : (torusAutK A K (c * d) : K →+* K) =
      (torusAutK A K c : K →+* K).comp (torusAutK A K d : K →+* K) := by
    refine IsLocalization.ringHom_ext A[X]⁰ (RingHom.ext fun f => ?_)
    simp [torusAutK_algebraMap, torusAut_mul_apply]
  exact congrArg (fun φ : K →+* K => φ y) this

/-- `torusAutK 1` is the identity. -/
theorem torusAutK_one_apply (y : K) : torusAutK A K (1 : kˣ) y = y := by
  have : (torusAutK A K (1 : kˣ) : K →+* K) = RingHom.id K := by
    refine IsLocalization.ringHom_ext A[X]⁰ (RingHom.ext fun f => ?_)
    simp [torusAutK_algebraMap, torusAut_one_apply]
  exact congrArg (fun φ : K →+* K => φ y) this

/-- `torusAutK c⁻¹` is inverse to `torusAutK c`. -/
theorem torusAutK_inv_apply (c : kˣ) (y : K) : torusAutK A K c⁻¹ (torusAutK A K c y) = y := by
  rw [← torusAutK_mul_apply, inv_mul_cancel, torusAutK_one_apply]

/-- `torusAutK c⁻¹` is inverse to `torusAutK c`. -/
theorem torusAutK_apply_inv (c : kˣ) (y : K) : torusAutK A K c (torusAutK A K c⁻¹ y) = y := by
  rw [← torusAutK_mul_apply, mul_inv_cancel, torusAutK_one_apply]

/-- The restriction of the torus action to a subring `S ⊆ K` stable under it. -/
def torusAutRestrict (S : Subalgebra A[X] K) (hS : ∀ (c : kˣ), ∀ y ∈ S, torusAutK A K c y ∈ S)
    (c : kˣ) : S ≃+* S where
  toFun y := ⟨torusAutK A K c y.1, hS c y.1 y.2⟩
  invFun y := ⟨torusAutK A K c⁻¹ y.1, hS c⁻¹ y.1 y.2⟩
  left_inv y := Subtype.ext (torusAutK_inv_apply c y.1)
  right_inv y := Subtype.ext (torusAutK_apply_inv c y.1)
  map_mul' y z := Subtype.ext (map_mul (torusAutK A K c) y.1 z.1)
  map_add' y z := Subtype.ext (map_add (torusAutK A K c) y.1 z.1)

/-- `torusAutRestrict` is the restriction of `torusAutK`. -/
theorem coe_torusAutRestrict (S : Subalgebra A[X] K)
    (hS : ∀ (c : kˣ), ∀ y ∈ S, torusAutK A K c y ∈ S) (c : kˣ) (y : S) :
    (torusAutRestrict S hS c y : K) = torusAutK A K c y.1 :=
  rfl

end Torus

/-! ### Torus invariance of the Rees valuations (`lem:bj-rees-invariant`) -/

/-- A ring automorphism of a discrete valuation ring preserves the additive valuation. -/
theorem addVal_ringEquiv_apply {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (φ : R ≃+* R) (y : R) :
    IsDiscreteValuationRing.addVal R (φ y) = IsDiscreteValuationRing.addVal R y := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl,
    IsDiscreteValuationRing.addVal_def _ (Units.map (φ : R →* R) u) (hϖ.map φ) n
      (by rw [map_mul, map_pow]; rfl)]

section Invariance

open Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  {K : Type*} [Field K] [Algebra A[X] K] [IsFractionRing A[X] K]
  {ι : Type*} {g : ι → A[X]}

/-- The torus multiplies a bihomogeneous element `a t^n` by `c ^ n`. -/
theorem exists_torusAut_eq_mul (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (c : kˣ)
    (i : ι) : ∃ u : kˣ, torusAut A c (g i) = C (algebraMap k A u) * g i := by
  obtain ⟨a, n, hi⟩ := hg i
  exact ⟨c ^ n, by rw [hi, torusAut_C_mul_X_pow, Units.val_pow_eq_pow_val]⟩

omit [IsFractionRing A[X] K] in
/-- The constants `c ∈ kˣ` are units in `K`. -/
theorem algebraMap_C_algebraMap_mul_inv (u : kˣ) :
    algebraMap A[X] K (C (algebraMap k A u)) * algebraMap A[X] K (C (algebraMap k A ↑u⁻¹)) = 1 := by
  rw [← map_mul, ← C_mul, ← map_mul, u.mul_inv, map_one, C_1, map_one]

/-- The charts `D_ℓ` are stable under the torus. -/
theorem torusAutK_mem_reesChart (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (ℓ : ι)
    (c : kˣ) : ∀ y ∈ reesChart K g ℓ, torusAutK A K c y ∈ reesChart K g ℓ := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨u, hu⟩ := exists_torusAut_eq_mul hg c i
    obtain ⟨v, hv⟩ := exists_torusAut_eq_mul hg c ℓ
    have hinv := algebraMap_C_algebraMap_mul_inv (A := A) (K := K) v
    have key : torusAutK A K c (algebraMap A[X] K (g i) / algebraMap A[X] K (g ℓ)) =
        algebraMap A[X] K (C (algebraMap k A u) * C (algebraMap k A ↑v⁻¹)) *
          (algebraMap A[X] K (g i) / algebraMap A[X] K (g ℓ)) := by
      rw [map_div₀, torusAutK_algebraMap, torusAutK_algebraMap, hu, hv, map_mul, map_mul, map_mul,
        div_eq_mul_inv, div_eq_mul_inv, mul_inv,
        inv_eq_of_mul_eq_one_right hinv]
      ring
    rw [key]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (div_mem_reesChart i ℓ)
  | algebraMap f =>
    rw [torusAutK_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ hy hz

/-- The normalized charts `E_ℓ` are stable under the torus. -/
theorem torusAutK_mem_reesNormalChart (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n)
    (ℓ : ι) (c : kˣ) : ∀ y ∈ reesNormalChart K g ℓ, torusAutK A K c y ∈ reesNormalChart K g ℓ := by
  intro y hy
  rw [mem_reesNormalChart_iff] at hy ⊢
  exact IsIntegral.map_of_comp_eq
    (torusAutRestrict (reesChart K g ℓ) (torusAutK_mem_reesChart hg ℓ) c : _ →+* _)
    (torusAutK A K c : K →+* K) (RingHom.ext fun _ => rfl) hy

variable (K) in
/-- The torus action on the normalized chart `E_ℓ`. -/
def torusAutE (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (ℓ : ι) (c : kˣ) :
    reesNormalChart K g ℓ ≃+* reesNormalChart K g ℓ :=
  torusAutRestrict (reesNormalChart K g ℓ) (torusAutK_mem_reesNormalChart hg ℓ) c

/-- `torusAutE` is the restriction of `torusAutK`. -/
theorem coe_torusAutE (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (ℓ : ι) (c : kˣ)
    (y : reesNormalChart K g ℓ) : (torusAutE K hg ℓ c y : K) = torusAutK A K c y.1 :=
  rfl

/-- `torusAutE` is an action of `kˣ`. -/
theorem torusAutE_comp (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (ℓ : ι) (c d : kˣ) :
    (torusAutE K hg ℓ d : reesNormalChart K g ℓ →+* reesNormalChart K g ℓ).comp
      (torusAutE K hg ℓ c : reesNormalChart K g ℓ →+* reesNormalChart K g ℓ) =
      (torusAutE K hg ℓ (d * c) : reesNormalChart K g ℓ →+* reesNormalChart K g ℓ) :=
  RingHom.ext fun y => Subtype.ext (torusAutK_mul_apply d c y.1).symm

/-- `torusAutE 1` is the identity. -/
theorem torusAutE_one (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (ℓ : ι) :
    (torusAutE K hg ℓ (1 : kˣ) : reesNormalChart K g ℓ →+* reesNormalChart K g ℓ) =
      RingHom.id _ :=
  RingHom.ext fun y => Subtype.ext (torusAutK_one_apply y.1)

/-- The torus preserves the ideal `g_ℓ E_ℓ`. -/
theorem comap_torusAutE_span (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (ℓ : ι)
    (c : kˣ) :
    (Ideal.span {algebraMap A[X] (reesNormalChart K g ℓ) (g ℓ)}).comap
      (torusAutE K hg ℓ c : reesNormalChart K g ℓ →+* reesNormalChart K g ℓ) =
      Ideal.span {algebraMap A[X] (reesNormalChart K g ℓ) (g ℓ)} := by
  set gE := algebraMap A[X] (reesNormalChart K g ℓ) (g ℓ)
  have hdvd : ∀ (d : kˣ) (y : reesNormalChart K g ℓ), gE ∣ y → gE ∣ torusAutE K hg ℓ d y := by
    rintro d y ⟨z, rfl⟩
    obtain ⟨u, hu⟩ := exists_torusAut_eq_mul hg d ℓ
    have : torusAutE K hg ℓ d gE = algebraMap A[X] (reesNormalChart K g ℓ)
        (C (algebraMap k A u)) * gE := by
      apply Subtype.ext
      change torusAutK A K d (algebraMap A[X] K (g ℓ)) =
        algebraMap A[X] K (C (algebraMap k A u)) * algebraMap A[X] K (g ℓ)
      rw [torusAutK_algebraMap, hu, map_mul]
    rw [map_mul, this, mul_assoc]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  ext y
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  refine ⟨fun h => ?_, hdvd c y⟩
  have := hdvd c⁻¹ (torusAutE K hg ℓ c y) h
  rwa [show torusAutE K hg ℓ c⁻¹ (torusAutE K hg ℓ c y) = y from
    Subtype.ext (torusAutK_inv_apply c y.1)] at this

/-- **Key step of `lem:bj-rees-invariant`.** Over an algebraically closed field, the torus fixes
every minimal prime of `g_ℓ E_ℓ`: it permutes this finite set, and `kˣ` is divisible. -/
theorem comap_torusAutE_eq_self [IsAlgClosed k] (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n)
    (ℓ : ι) [IsNoetherianRing (reesNormalChart K g ℓ)] (c : kˣ) {P : Ideal (reesNormalChart K g ℓ)}
    (hP : P ∈ (Ideal.span {algebraMap A[X] (reesNormalChart K g ℓ) (g ℓ)}).minimalPrimes) :
    P.comap (torusAutE K hg ℓ c : reesNormalChart K g ℓ →+* reesNormalChart K g ℓ) = P := by
  classical
  let ρ : kˣ →* RingAut (reesNormalChart K g ℓ) :=
    { toFun := torusAutE K hg ℓ
      map_one' := RingEquiv.ext fun y => Subtype.ext (by
        change torusAutK A K (1 : kˣ) (y : K) = (y : K)
        exact torusAutK_one_apply _)
      map_mul' := fun c d => RingEquiv.ext fun y => Subtype.ext (by
        change torusAutK A K (c * d) (y : K) =
          torusAutK A K c (torusAutK A K d (y : K))
        exact torusAutK_mul_apply c d _) }
  let : RootableBy kˣ ℕ := rootableByOfPowLeftSurj _ _ fun {n} hn c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : k) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact c.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hz
  exact minimalPrime_comap_eq_self_of_rootable_action ρ
    (Ideal.span {algebraMap A[X] (reesNormalChart K g ℓ) (g ℓ)})
    (fun d => comap_torusAutE_span hg ℓ d) hP c

/-- The Rees valuation rings are stable under the torus (`lem:bj-rees-invariant`). -/
theorem torusAutK_mem_reesValuationRing [IsAlgClosed k]
    (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (x : ReesIndex K g)
    [IsNoetherianRing (reesNormalChart K g x.idx)] (c : kˣ) :
    ∀ y ∈ reesValuationRing K g x, torusAutK A K c y ∈ reesValuationRing K g x := by
  intro y hy
  obtain ⟨a, s, hs, rfl⟩ := mem_reesValuationRing.1 hy
  refine mem_reesValuationRing.2 ⟨torusAutE K hg x.idx c a, torusAutE K hg x.idx c s, ?_, ?_⟩
  · intro h
    apply hs
    have := comap_torusAutE_eq_self hg x.idx c x.mem_minimalPrimes
    rw [← this]
    exact h
  · rw [map_mul, map_inv₀, coe_torusAutE, coe_torusAutE]

/-- The torus acts on a Rees valuation ring `V` by ring automorphisms, so it preserves `ord_V`:
`f ∣ f(c t)` in `V` for `f ∈ A[t]`. -/
theorem algebraMap_dvd_algebraMap_torusAut [IsAlgClosed k]
    (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (x : ReesIndex K g)
    [IsNoetherianRing (reesNormalChart K g x.idx)] (c : kˣ) (f : A[X]) :
    algebraMap A[X] (reesValuationRing K g x) f ∣
      algebraMap A[X] (reesValuationRing K g x) (torusAut A c f) := by
  set φ := torusAutRestrict (reesValuationRing K g x) (torusAutK_mem_reesValuationRing hg x) c
  have : φ (algebraMap A[X] (reesValuationRing K g x) f) =
      algebraMap A[X] (reesValuationRing K g x) (torusAut A c f) :=
    Subtype.ext (torusAutK_algebraMap c f)
  rw [← this, ← IsDiscreteValuationRing.addVal_le_iff_dvd, addVal_ringEquiv_apply]

omit [Algebra k A] in
/-- An algebraically closed field has infinitely many units. -/
theorem infinite_units_of_isAlgClosed [IsAlgClosed k] : Infinite kˣ := by
  have : Infinite ↥(({0} : Set k)ᶜ) := (Set.finite_singleton (0 : k)).infinite_compl.to_subtype
  exact Infinite.of_injective (fun x : ↥(({0} : Set k)ᶜ) => Units.mk0 x.1 x.2)
    fun x y hxy => Subtype.ext (congrArg Units.val hxy)

variable (k) in
/-- **Vandermonde step of `lem:bj-rees-invariant`.** Each homogeneous component `f_m t^m` of
`f ∈ A[t]` is a `k`-linear combination of the `f(μ_i t)`, so `f ∣ f_m t^m` in every Rees valuation
ring: `ord_V (f_m t^m) ≥ ord_V f`. -/
theorem algebraMap_dvd_algebraMap_C_coeff_mul_X_pow [IsAlgClosed k]
    (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (x : ReesIndex K g)
    [IsNoetherianRing (reesNormalChart K g x.idx)] (f : A[X]) (m : ℕ) :
    algebraMap A[X] (reesValuationRing K g x) f ∣
      algebraMap A[X] (reesValuationRing K g x) (C (f.coeff m) * X ^ m) := by
  rcases lt_or_ge f.natDegree m with hm | hm
  · rw [coeff_eq_zero_of_natDegree_lt hm, map_zero, zero_mul, map_zero]
    exact dvd_zero _
  -- Distinct nodes `μ_0, …, μ_L ∈ kˣ`, `L = deg f`.
  have := infinite_units_of_isAlgClosed (k := k)
  set n := f.natDegree + 1
  let μ : Fin n ↪ kˣ := Fin.valEmbedding.trans (Infinite.natEmbedding kˣ)
  set ν : Fin n → k := fun i => (μ i : k)
  have hν : Function.Injective ν := fun i j hij => μ.injective (Units.ext hij)
  set Vd := Matrix.vandermonde ν
  have hdet : IsUnit Vd.det := isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hν)
  have hAV : Vd⁻¹ * Vd = 1 := Matrix.nonsing_inv_mul Vd hdet
  set m' : Fin n := ⟨m, Nat.lt_succ_of_le hm⟩
  -- `f_m t^m = ∑_i a_{m i} f(μ_i t)` with `(a_{m i}) = (Vandermonde)⁻¹`.
  have key : C (f.coeff m) * X ^ m =
      ∑ i, C (algebraMap k A (Vd⁻¹ m' i)) * torusAut A (μ i) f := by
    ext j
    rw [coeff_C_mul_X_pow, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_torusAut]
    have hsum : ∑ i, algebraMap k A (Vd⁻¹ m' i) * (f.coeff j * algebraMap k A (ν i ^ j)) =
        f.coeff j * algebraMap k A (∑ i, Vd⁻¹ m' i * ν i ^ j) := by
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      ring
    change _ = ∑ i, algebraMap k A (Vd⁻¹ m' i) * (f.coeff j * algebraMap k A (ν i ^ j))
    rw [hsum]
    rcases lt_or_ge f.natDegree j with hj | hj
    · rw [coeff_eq_zero_of_natDegree_lt hj, zero_mul, if_neg (by omega)]
    · have : ∑ i, Vd⁻¹ m' i * ν i ^ j = (Vd⁻¹ * Vd) m' ⟨j, Nat.lt_succ_of_le hj⟩ := by
        rw [Matrix.mul_apply]
        rfl
      rw [this, hAV, Matrix.one_apply]
      by_cases hjm : j = m
      · subst hjm
        rw [if_pos rfl, if_pos rfl, map_one, mul_one]
      · rw [if_neg hjm, if_neg (fun h => hjm (congrArg Fin.val h).symm), map_zero, mul_zero]
  rw [key, map_sum]
  refine Finset.dvd_sum fun i _ => ?_
  rw [map_mul]
  exact Dvd.dvd.mul_left (algebraMap_dvd_algebraMap_torusAut hg x (μ i) f) _

/-- **`lem:bj-rees-invariant`, first part.** If `t^N ∈ I`, then `t` is not a unit in any Rees
valuation ring: `ord_V t > 0`. -/
theorem not_isUnit_algebraMap_X_reesValuationRing (hN : ∃ N : ℕ, X ^ N ∈ Ideal.span (Set.range g))
    (x : ReesIndex K g) : ¬IsUnit (algebraMap A[X] (reesValuationRing K g x) X) := by
  obtain ⟨N, hN⟩ := hN
  set E := reesNormalChart K g x.idx
  have h0 : algebraMap A[X] K (g x.idx) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A[X] K)).2 x.ne_zero
  -- `I E_ℓ = g_ℓ E_ℓ ⊆ P`, so `t ∈ P`.
  have hI : Ideal.span (Set.range g) ≤
      (Ideal.span {algebraMap A[X] E (g x.idx)}).comap (algebraMap A[X] E) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨⟨_, reesChart_le_reesNormalChart x.idx (div_mem_reesChart i x.idx)⟩, ?_⟩
    apply Subtype.ext
    change algebraMap A[X] K (g i) / algebraMap A[X] K (g x.idx) * algebraMap A[X] K (g x.idx) =
      algebraMap A[X] K (g i)
    rw [div_mul_cancel₀ _ h0]
  have hXP : algebraMap A[X] E X ∈ x.ideal := by
    refine x.isPrime.mem_of_pow_mem N ?_
    rw [← map_pow]
    exact x.mem_minimalPrimes.1.2 (hI hN)
  rintro ⟨u, hu⟩
  obtain ⟨a, s, hs, hv⟩ := mem_reesValuationRing.1 (u⁻¹ : (reesValuationRing K g x)ˣ).1.2
  have hs0 : (s : K) ≠ 0 := fun h => hs (by
    rw [show s = 0 from Subtype.ext h]; exact Ideal.zero_mem _)
  have h1 : algebraMap A[X] K X * ((a : K) * (s : K)⁻¹) = 1 := by
    rw [← hv]
    have := congrArg Subtype.val u.mul_inv
    rw [hu] at this
    exact this
  have h2 : algebraMap A[X] E X * a = s := by
    apply Subtype.ext
    change algebraMap A[X] K X * (a : K) = (s : K)
    field_simp at h1
    exact h1
  exact hs (h2 ▸ Ideal.mul_mem_right _ _ hXP)

/-- **`lem:bj-rees-invariant`, first part.** If `t^N ∈ I`, then `t` lies in the maximal ideal of
every Rees valuation ring. -/
theorem algebraMap_X_mem_maximalIdeal_reesValuationRing
    (hN : ∃ N : ℕ, X ^ N ∈ Ideal.span (Set.range g)) (x : ReesIndex K g)
    [IsNoetherianRing (reesNormalChart K g x.idx)] :
    algebraMap A[X] (reesValuationRing K g x) X ∈ maximalIdeal (reesValuationRing K g x) :=
  (mem_maximalIdeal _).2 (not_isUnit_algebraMap_X_reesValuationRing hN x)

/-- **`lem:bj-rees-invariant`, first part, valuative form.** If `t^N ∈ I`, then `ord_V t > 0`. -/
theorem addVal_X_pos_reesValuationRing (hN : ∃ N : ℕ, X ^ N ∈ Ideal.span (Set.range g))
    (x : ReesIndex K g) [IsNoetherianRing (reesNormalChart K g x.idx)] :
    0 < IsDiscreteValuationRing.addVal (reesValuationRing K g x)
      (algebraMap A[X] (reesValuationRing K g x) X) := by
  refine pos_iff_ne_zero.2 fun h => not_isUnit_algebraMap_X_reesValuationRing hN x ?_
  rwa [IsDiscreteValuationRing.addVal_eq_zero_iff] at h

variable (k) in
/-- **`lem:bj-rees-invariant`, second part.** Over an algebraically closed field, for bihomogeneous
generators `g_i = a_i t^{n_i}`, every Rees valuation is monomial in `t`:
`ord_V (∑_λ f_λ t^λ) = min_λ (ord_V f_λ + λ ord_V t)`. -/
theorem addVal_reesValuationRing_eq_inf [IsAlgClosed k]
    (hg : ∀ i, ∃ (a : A) (n : ℕ), g i = C a * X ^ n) (x : ReesIndex K g)
    [IsNoetherianRing (reesNormalChart K g x.idx)] (f : A[X]) :
    IsDiscreteValuationRing.addVal (reesValuationRing K g x)
        (algebraMap A[X] (reesValuationRing K g x) f) =
      f.support.inf fun n =>
        IsDiscreteValuationRing.addVal (reesValuationRing K g x)
            (algebraMap A[X] (reesValuationRing K g x) (C (f.coeff n))) +
          n • IsDiscreteValuationRing.addVal (reesValuationRing K g x)
            (algebraMap A[X] (reesValuationRing K g x) X) := by
  set v := IsDiscreteValuationRing.addVal (reesValuationRing K g x)
  set φ := algebraMap A[X] (reesValuationRing K g x)
  have hterm : ∀ n, v (φ (C (f.coeff n) * X ^ n)) = v (φ (C (f.coeff n))) + n • v (φ X) := by
    intro n
    rw [map_mul, map_pow, AddValuation.map_mul, AddValuation.map_pow]
  refine le_antisymm (Finset.le_inf fun n _ => ?_) ?_
  · rw [← hterm, IsDiscreteValuationRing.addVal_le_iff_dvd]
    exact algebraMap_dvd_algebraMap_C_coeff_mul_X_pow k hg x f n
  · conv_rhs => rw [f.as_sum_support_C_mul_X_pow, map_sum]
    refine AddValuation.map_le_sum v fun n hn => ?_
    rw [hterm]
    exact Finset.inf_le hn

end Invariance

end EnvelopeProperty
