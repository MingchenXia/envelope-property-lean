/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Subvariety
import EnvelopeProperty.Projective.Divisorial

/-!
# The affine cone over `X × 𝔸¹` and its charts

Let `k` be a field and `X = V(I) ⊆ ℙᴹ` a projective subvariety (`EnvelopeProperty.ProjSubvariety`),
with `R_M = k[x₀, …, x_M]`, homogeneous coordinate ring `S = R_M / I` and the coordinate ring
`T = S[t]` of the affine cone over `X × 𝔸¹`. This file contains the purely algebraic part of the
blueprint chapter `smooth-general.tex` used for the proof of Fang–Han–Xia, *The envelope property
for unibranch projective varieties*, Theorem 3.1 (`thm:smooth-EP`) on smooth `X`: the cone ring and
saturation of `conv:sg-setting`, and the charts of the punctured cone, `lem:sg-cone-charts`(1),(2).
The analytic part (Gauss points, divisorial points) is in
`EnvelopeProperty.Projective.SubvarietyGauss`.

## Main definitions

* `ProjSubvariety.CoordRing X = S = R_M / I` (a type synonym with transported instances: the
  instances of polynomial rings over the quotient `R_M / I` unify very slowly otherwise),
  `ProjSubvariety.coordMk : R_M → S`, `ProjSubvariety.ConeRing X = T = S[t]`,
  `ProjSubvariety.coneMk : R_M[t] → T`.
* `ProjSubvariety.coneIrrelevant X = 𝔪₊ T` and `ProjSubvariety.saturation X 𝔟 = 𝔟^sat =
  {f : 𝔪₊^r f ⊆ 𝔟 for some r}` (`conv:sg-setting`).
* `ProjSubvariety.tAdicDVR X = T_{(t)}`, a `BirationalDVR k X.ConeRing`.
* For `j : Fin (M + 1)`: the chart algebra `A_j = X.ChartAlg j` (a type synonym of
  `ProjBerk.QuotChartAlg I xⱼ 1`), `B_j = X.ChartRing j = A_j[t]`, `X.ChartPoly j = B_j[Y]`,
  `X.ChartLaurent j = B_j[Y, Y⁻¹]`, `X.coneX j = x̄ⱼ ∈ T`, `X.ConeAway j = T_{x̄ⱼ}`; the
  dehomogenization `X.quotDehom j : R_M → A_j` (`xᵢ ↦ x̄ᵢ / x̄ⱼ`, `τ ↦ τ̄ / x̄ⱼ^N` on forms of
  degree `N`), the expansion `X.coneToChartPoly j : R_M[t] → B_j[Y]` (`xᵢ ↦ (x̄ᵢ / x̄ⱼ) Y`,
  `t ↦ t`) and its factorization `X.coneTChartPoly j : T → B_j[Y]`, the map
  `X.chartPolyToAway j : B_j[Y] → T_{x̄ⱼ}` (`Y ↦ x̄ⱼ`), and
  `X.chartPolyToFrac j : B_j[Y] → Frac T`.
* `ProjSubvariety.chartDVR X j V`: for a discrete valuation ring `B_j ⊆ V ⊆ Frac B_j`, the
  discrete valuation ring `V[x̄ⱼ]_{m_V V[x̄ⱼ]} ⊆ Frac T` (`lem:bj-gauss-dvr`), birational to `T`.

## Main results

* **`lem:sg-cone-charts`(1)**: `ProjSubvariety.coneChartEquiv X j : B_j[Y, Y⁻¹] ≃ₐ[k] T_{x̄ⱼ}`,
  the inclusion on `A_j`, `t ↦ t`, `Y ↦ x̄ⱼ` (`ProjSubvariety.coneChartEquiv_algebraMap`), with
  inverse `x̄ᵢ ↦ (x̄ᵢ / x̄ⱼ) Y` (`ProjSubvariety.coneAwayToLaurent`).
* **`lem:sg-cone-charts`(2)**: `T` is a domain (instance), and for `xⱼ ∉ I`, `x̄ⱼ` is transcendental
  over `Frac B_j ⊆ Frac T` (`ProjSubvariety.chartPolyToFrac_injective`,
  `ProjSubvariety.gaussToFrac_injective`); `ḡ = ∑_c (g_c / x̄ⱼ^c) x̄ⱼ^c`
  (`ProjSubvariety.chartPolyToFrac_coneToChartPoly`); `trdeg_k Frac T = trdeg_k k(X) + 2`
  (`ProjSubvariety.trdeg_fractionRing_coneRing`, from `trdeg_localization_eq` and
  `trdeg_polynomial_eq_add_one`).
* `ProjSubvariety.exists_pow_mul_saturation_le`: `𝔪₊^r 𝔟^sat ⊆ 𝔟` for some `r`.
* `ProjSubvariety.tAdicDVR_ord`: `ord_{(t)} = ` order of vanishing in `t`.
* `ProjSubvariety.chartDVR_ord`: the Gauss formula `ord_{R'}(ḡ) = min_c ord_V(η(g)_c)`.

## Deviations from the blueprint

* `lem:sg-cone-charts`(1) is stated with `B_j[Y][Y⁻¹] = A_j[t][Y, Y⁻¹]` instead of
  `A_j[Y, Y⁻¹][t]`; the matching of the bigradings is not formalized. In (2), the algebraic
  independence of `x̄ⱼ, t` over `k(X)` is formalized as the injectivity of `A_j[t][Y] → Frac T`
  (and of `V[Y] → Frac T` for `B_j ⊆ V ⊆ Frac B_j`), and `Frac T = k(X)(x̄ⱼ, t)` through the
  transcendence degree count; the equality of fields itself is not stated. Part (3) is not part of
  this file.
-/

open scoped NNReal ENNReal Topology Polynomial

open IsDiscreteValuationRing

noncomputable section

namespace EnvelopeProperty

open ProjBerk (quotChartMk QuotChartAlg)

universe u

/-! ### Transcendence degrees of localizations and polynomial rings -/

section Trdeg

variable {k : Type u} [Field k]

/-- A localization at non-zero-divisors has the same transcendence degree. -/
theorem trdeg_localization_eq {R S : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S] (N : Submonoid R)
    (hN : N ≤ nonZeroDivisors R) [IsLocalization N S] :
    Algebra.trdeg k S = Algebra.trdeg k R := by
  have : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors (M := N) (S := S) hN
  have : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).2 (IsLocalization.injective S hN)
  have : Algebra.IsAlgebraic R S := IsLocalization.isAlgebraic S N
  have h := trdeg_add_eq k R (A := S)
  rw [trdeg_eq_zero (R := R) (A := S), add_zero] at h
  exact h.symm

/-- `trdeg_k R[t] = trdeg_k R + 1` for a domain `R`. -/
theorem trdeg_polynomial_eq_add_one (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] :
    Algebra.trdeg k R[X] = Algebra.trdeg k R + 1 := by
  have : FaithfulSMul R R[X] :=
    (faithfulSMul_iff_algebraMap_injective R R[X]).2 Polynomial.C_injective
  have h := trdeg_add_eq k R (A := R[X])
  rw [Polynomial.trdeg_of_isDomain] at h
  exact h.symm

end Trdeg

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-! ### The cone ring `T = S[t]` -/

/-- The homogeneous coordinate ring `S = R_M / I` of `X`. It is a type synonym (a `def`, with its
instances transported) rather than an `abbrev`: unification of the instances of the polynomial
ring over the quotient `R_M / I` is otherwise very slow. -/
def CoordRing : Type u := MvPolynomial (Fin (M + 1)) k ⧸ X.ideal

instance : CommRing X.CoordRing :=
  inferInstanceAs (CommRing (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal))

instance : Algebra k X.CoordRing :=
  inferInstanceAs (Algebra k (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal))

instance : IsDomain X.CoordRing :=
  inferInstanceAs (IsDomain (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal))

instance : IsNoetherianRing X.CoordRing :=
  inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal))

/-- The quotient map `R_M → S = R_M / I`, `f ↦ f̄`. -/
def coordMk : MvPolynomial (Fin (M + 1)) k →ₐ[k] X.CoordRing := Ideal.Quotient.mkₐ k X.ideal

instance : Algebra.FiniteType k X.CoordRing :=
  Algebra.FiniteType.of_surjective X.coordMk Ideal.Quotient.mk_surjective

/-- The coordinate ring `T = S[t]`, `S = R_M / I`, of the affine cone over `X × 𝔸¹`
(`conv:sg-setting`). -/
abbrev ConeRing : Type u := Polynomial X.CoordRing

instance : Algebra.FiniteType k X.ConeRing :=
  Algebra.FiniteType.trans (S := X.CoordRing) inferInstance inferInstance

instance : Algebra.EssFiniteType k X.ConeRing := inferInstance

/-- The quotient map `R_M[t] → T = (R_M / I)[t]`, `g ↦ ḡ`. -/
def coneMk : (MvPolynomial (Fin (M + 1)) k)[X] →ₐ[k] X.ConeRing :=
  Polynomial.mapAlgHom X.coordMk

variable {X}

theorem coordMk_surjective : Function.Surjective X.coordMk := Ideal.Quotient.mk_surjective

theorem coordMk_eq_zero_iff {f : MvPolynomial (Fin (M + 1)) k} : X.coordMk f = 0 ↔ f ∈ X.ideal :=
  Ideal.Quotient.eq_zero_iff_mem

variable (X) in
/-- The map `S → B` induced by an algebra map `f : R_M → B` vanishing on `I`. -/
def coordLift {B : Type*} [CommRing B] [Algebra k B] (f : MvPolynomial (Fin (M + 1)) k →ₐ[k] B)
    (hf : ∀ a ∈ X.ideal, f a = 0) : X.CoordRing →ₐ[k] B :=
  Ideal.Quotient.liftₐ X.ideal f hf

@[simp]
theorem coordLift_coordMk {B : Type*} [CommRing B] [Algebra k B]
    (f : MvPolynomial (Fin (M + 1)) k →ₐ[k] B) (hf : ∀ a ∈ X.ideal, f a = 0)
    (a : MvPolynomial (Fin (M + 1)) k) : X.coordLift f hf (X.coordMk a) = f a :=
  rfl

theorem coeff_coneMk (g : (MvPolynomial (Fin (M + 1)) k)[X]) (ℓ : ℕ) :
    (X.coneMk g).coeff ℓ = X.coordMk (g.coeff ℓ) := by
  simp [coneMk]

@[simp]
theorem coneMk_C (s : MvPolynomial (Fin (M + 1)) k) :
    X.coneMk (Polynomial.C s) = Polynomial.C (X.coordMk s) := by
  simp [coneMk]

@[simp]
theorem coneMk_X : X.coneMk (Polynomial.X : (MvPolynomial (Fin (M + 1)) k)[X]) = Polynomial.X := by
  simp [coneMk]

theorem coneMk_surjective : Function.Surjective X.coneMk :=
  Polynomial.map_surjective _ coordMk_surjective

theorem coneMk_eq_zero_iff {g : (MvPolynomial (Fin (M + 1)) k)[X]} :
    X.coneMk g = 0 ↔ ∀ ℓ, g.coeff ℓ ∈ X.ideal := by
  rw [Polynomial.ext_iff]
  simp only [coeff_coneMk, Polynomial.coeff_zero, coordMk_eq_zero_iff]

variable (X) in
/-- The irrelevant ideal `𝔪₊ T = (x̄₀, …, x̄_M) T` of the cone ring. -/
def coneIrrelevant : Ideal X.ConeRing :=
  Ideal.span (Set.range fun i => Polynomial.C (X.coordMk (MvPolynomial.X i)))

variable (X) in
/-- The **saturation** `𝔟^sat = {f ∈ T : 𝔪₊^r f ⊆ 𝔟 for some r}` of an ideal `𝔟 ⊆ T`
(`conv:sg-setting`). -/
def saturation (𝔟 : Ideal X.ConeRing) : Ideal X.ConeRing :=
  ⨆ r : ℕ, 𝔟.colon ((X.coneIrrelevant ^ r : Ideal X.ConeRing) : Set X.ConeRing)

theorem colon_pow_mono (𝔟 : Ideal X.ConeRing) : Monotone fun r : ℕ =>
    𝔟.colon ((X.coneIrrelevant ^ r : Ideal X.ConeRing) : Set X.ConeRing) := fun _ _ hrr' =>
  Submodule.colon_mono le_rfl (Ideal.pow_le_pow_right hrr')

theorem mem_saturation_iff {𝔟 : Ideal X.ConeRing} {f : X.ConeRing} :
    f ∈ X.saturation 𝔟 ↔ ∃ r : ℕ, ∀ a ∈ X.coneIrrelevant ^ r, a * f ∈ 𝔟 := by
  rw [saturation, Submodule.mem_iSup_of_directed _ (colon_pow_mono 𝔟).directed_le]
  refine exists_congr fun r => ?_
  rw [Submodule.mem_colon]
  refine forall₂_congr fun a _ => ?_
  show f * a ∈ 𝔟 ↔ a * f ∈ 𝔟
  rw [mul_comm]

theorem le_saturation (𝔟 : Ideal X.ConeRing) : 𝔟 ≤ X.saturation 𝔟 := fun _ hf =>
  mem_saturation_iff.2 ⟨0, fun a _ => 𝔟.mul_mem_left a hf⟩

/-- `𝔪₊^r 𝔟^sat ⊆ 𝔟` for some `r` (`T` is Noetherian). -/
theorem exists_pow_mul_saturation_le (𝔟 : Ideal X.ConeRing) :
    ∃ r : ℕ, X.coneIrrelevant ^ r * X.saturation 𝔟 ≤ 𝔟 := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (X.saturation 𝔟) : (X.saturation 𝔟).FG)
  choose! r hr using fun f (hf : f ∈ G) =>
    mem_saturation_iff.1 (hG ▸ Ideal.subset_span hf : f ∈ X.saturation 𝔟)
  refine ⟨G.sup r, ?_⟩
  rw [← hG, Ideal.mul_le]
  intro a ha f hf
  change f ∈ Submodule.span X.ConeRing (G : Set X.ConeRing) at hf
  obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hf
  rw [Finset.mul_sum]
  refine Ideal.sum_mem _ fun g hg => ?_
  rw [smul_eq_mul, show a * (c g * g) = c g * (a * g) by ring]
  refine 𝔟.mul_mem_left _ (hr g hg a ?_)
  exact Ideal.pow_le_pow_right (Finset.le_sup hg) ha

/-! ### The `t`-adic discrete valuation ring -/

instance : (Ideal.span {(Polynomial.X : X.ConeRing)}).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X

variable (X) in
/-- The discrete valuation ring `T_{(t)} ⊆ Frac T` of the `t`-adic valuation. -/
def tAdicDVR : BirationalDVR k X.ConeRing where
  ring := atPrimeRange (P := Ideal.span {Polynomial.X})
    (IsScalarTower.toAlgHom k _ (FractionRing X.ConeRing)) (IsFractionRing.injective _ _)
  isDVR := isDiscreteValuationRing_atPrimeRange _ _ rfl Polynomial.X_ne_zero
  essFiniteType := essFiniteType_atPrimeRange _ _
  algebraMap_mem g := mem_atPrimeRange _ _ g

theorem tAdicDVR_ord_X_pow_mul (m : ℕ) {q : X.ConeRing} (hq : q.coeff 0 ≠ 0) :
    (X.tAdicDVR).ord (Polynomial.X ^ m * q) = m := by
  have hq' : ¬ (Polynomial.X : X.ConeRing) ∣ q := by rw [Polynomial.X_dvd_iff]; exact hq
  have : IsDiscreteValuationRing (atPrimeRange (P := Ideal.span {Polynomial.X})
      (IsScalarTower.toAlgHom k _ (FractionRing X.ConeRing))
      (IsFractionRing.injective _ _)) := (X.tAdicDVR).isDVR
  exact addVal_atPrimeRange _ _ rfl Polynomial.X_ne_zero m hq'

/-- `ord_{(t)}(f)` is the order of vanishing of `f` in `t`. -/
theorem tAdicDVR_ord {f : X.ConeRing} (hf : f ≠ 0) :
    (X.tAdicDVR).ord f = f.natTrailingDegree := by
  obtain ⟨q, hq⟩ : Polynomial.X ^ f.natTrailingDegree ∣ f :=
    Polynomial.X_pow_dvd_iff.2 fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 ≠ 0 := by
    have h := Polynomial.coeff_X_pow_mul q f.natTrailingDegree 0
    rw [zero_add, ← hq] at h
    rw [← h]
    exact mt Polynomial.trailingCoeff_eq_zero.1 hf
  conv_lhs => rw [hq]
  exact tAdicDVR_ord_X_pow_mul _ hq0

/-! ### The charts of the punctured cone (`lem:sg-cone-charts`) -/

section Charts

variable (X) (j : Fin (M + 1))

/-- The chart algebra `A_j = S_{(x̄ⱼ)}` of `X` (`lem:wu-proj-chart`): a type synonym (a `def`,
with transported instances) of the quotient chart algebra `ProjBerk.QuotChartAlg I xⱼ 1`. -/
def ChartAlg : Type u := QuotChartAlg X.ideal (MvPolynomial.X j) 1

instance : CommRing (X.ChartAlg j) :=
  inferInstanceAs (CommRing (QuotChartAlg X.ideal (MvPolynomial.X j) 1))

instance : Algebra k (X.ChartAlg j) :=
  inferInstanceAs (Algebra k (QuotChartAlg X.ideal (MvPolynomial.X j) 1))

instance : Algebra.FiniteType k (X.ChartAlg j) :=
  ProjBerk.finiteType_quotChartAlg (MvPolynomial.isHomogeneous_X k j)

instance [h : Fact (MvPolynomial.X j ∉ X.ideal)] : IsDomain (X.ChartAlg j) :=
  ProjBerk.isDomain_quotChartAlg h.out

/-- The chart ring `B_j = A_j[t]`. -/
abbrev ChartRing : Type u := Polynomial (X.ChartAlg j)

/-- The polynomial ring `B_j[Y]`, `Y` standing for `x̄ⱼ`. -/
abbrev ChartPoly : Type u := Polynomial (X.ChartRing j)

/-- The quotient map `(R_M)_{(xⱼ)} → A_j`. -/
def chartQuot :
    ProjBerk.chartAlg (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) 1 →ₐ[k] X.ChartAlg j :=
  Ideal.Quotient.mkₐ k _

/-- The **dehomogenization** `δⱼ : R_M → A_j`, `xᵢ ↦ x̄ᵢ / x̄ⱼ`; on a form `τ` of degree `N` it is
`τ̄ / x̄ⱼ^N` (`quotDehom_of_isHomogeneous`). -/
def quotDehom : MvPolynomial (Fin (M + 1)) k →ₐ[k] X.ChartAlg j :=
  (X.chartQuot j).comp (MvPolynomial.aeval fun i =>
    ProjBerk.chartMk (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) 1 1 (MvPolynomial.X i))

variable {X j}

theorem quotDehom_of_isHomogeneous {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous N) :
    X.quotDehom j τ = X.chartQuot j (ProjBerk.chartMk (MvPolynomial.X j) 1 N τ) := by
  rw [quotDehom, AlgHom.comp_apply, ProjBerk.aeval_chartMk_X hτ]

@[simp]
theorem quotDehom_X_self : X.quotDehom j (MvPolynomial.X j) = 1 := by
  rw [quotDehom_of_isHomogeneous (MvPolynomial.isHomogeneous_X k j)]
  have h := ProjBerk.chartMk_pow_self (σ := (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k))
    (MvPolynomial.isHomogeneous_X k j) 1
  rw [pow_one] at h
  rw [h, map_one]

theorem chartQuot_eq_zero_iff
    {a : ProjBerk.chartAlg (MvPolynomial.X j : MvPolynomial (Fin (M + 1)) k) 1} :
    X.chartQuot j a = 0 ↔ a ∈ ProjBerk.chartIdeal X.ideal (MvPolynomial.X j) 1 :=
  Ideal.Quotient.eq_zero_iff_mem

/-- `δⱼ` vanishes on `I`. -/
theorem quotDehom_eq_zero_of_mem {f : MvPolynomial (Fin (M + 1)) k} (hf : f ∈ X.ideal) :
    X.quotDehom j f = 0 := by
  rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [quotDehom_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous c f),
    chartQuot_eq_zero_iff]
  exact ProjBerk.chartMk_mem_chartIdeal
    (by rw [mul_one]; exact MvPolynomial.homogeneousComponent_isHomogeneous c f)
    (X.isHomogeneousIdeal f hf c)

/-- For `xⱼ ∉ I` and a form `τ`, `τ̄ / x̄ⱼ^N = 0` iff `τ ∈ I`. -/
theorem quotDehom_eq_zero_iff [Fact (MvPolynomial.X j ∉ X.ideal)] {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous N) :
    X.quotDehom j τ = 0 ↔ τ ∈ X.ideal := by
  rw [quotDehom_of_isHomogeneous hτ]
  exact ProjBerk.quotChartMk_eq_zero_iff Fact.out (by rw [mul_one]; exact hτ)

/-- Every element of `A_j` is `τ̄ / x̄ⱼ^N` for a form `τ` of degree `N`. -/
theorem exists_quotDehom_eq (b : X.ChartAlg j) :
    ∃ (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k), τ.IsHomogeneous N ∧ X.quotDehom j τ = b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := ProjBerk.chartIdeal X.ideal (MvPolynomial.X j) 1) b
  obtain ⟨N, τ, hτ, rfl⟩ := ProjBerk.exists_eq_chartMk (MvPolynomial.isHomogeneous_X k j) a
  rw [mul_one] at hτ
  exact ⟨N, τ, hτ, quotDehom_of_isHomogeneous hτ⟩

theorem quotDehom_surjective : Function.Surjective (X.quotDehom j) := fun b =>
  let ⟨_, τ, _, h⟩ := exists_quotDehom_eq b
  ⟨τ, h⟩

/-- Algebra maps out of `A_j` agree if they agree on the `x̄ᵢ / x̄ⱼ`. -/
theorem chartAlg_algHom_ext {B : Type*} [Semiring B] [Algebra k B] {f g : X.ChartAlg j →ₐ[k] B}
    (h : ∀ i, f (X.quotDehom j (MvPolynomial.X i)) = g (X.quotDehom j (MvPolynomial.X i))) :
    f = g := by
  have h' : f.comp (X.quotDehom j) = g.comp (X.quotDehom j) :=
    MvPolynomial.algHom_ext fun i => h i
  refine AlgHom.ext fun b => ?_
  obtain ⟨τ, rfl⟩ := quotDehom_surjective b
  exact congrArg (fun φ : MvPolynomial (Fin (M + 1)) k →ₐ[k] B => φ τ) h'

/-- Algebra maps out of `S = R_M / I` agree if they agree on the `x̄ᵢ`. -/
theorem coordRing_algHom_ext {B : Type*} [Semiring B] [Algebra k B] {f g : X.CoordRing →ₐ[k] B}
    (h : ∀ i, f (X.coordMk (MvPolynomial.X i)) = g (X.coordMk (MvPolynomial.X i))) : f = g := by
  have h' : f.comp X.coordMk = g.comp X.coordMk := MvPolynomial.algHom_ext fun i => h i
  refine AlgHom.ext fun b => ?_
  obtain ⟨τ, rfl⟩ := coordMk_surjective b
  exact congrArg (fun φ : MvPolynomial (Fin (M + 1)) k →ₐ[k] B => φ τ) h'

/-! #### The expansion `R_M[t] → B_j[Y]` -/

variable (X j) in
/-- The expansion `η : R_M[t] → B_j[Y]`, `xᵢ ↦ (x̄ᵢ / x̄ⱼ) Y`, `t ↦ t`: an element is written in the
chart coordinates, `Y` standing for `x̄ⱼ`. -/
def coneToChartPoly : (MvPolynomial (Fin (M + 1)) k)[X] →ₐ[k] X.ChartPoly j :=
  Polynomial.aevalTower (MvPolynomial.aeval fun i =>
    (Polynomial.C (Polynomial.C (X.quotDehom j (MvPolynomial.X i))) * Polynomial.X :
      X.ChartPoly j)) (Polynomial.C Polynomial.X)

theorem coneToChartPoly_C_X (i : Fin (M + 1)) :
    X.coneToChartPoly j (Polynomial.C (MvPolynomial.X i)) =
      Polynomial.C (Polynomial.C (X.quotDehom j (MvPolynomial.X i))) * Polynomial.X := by
  rw [coneToChartPoly, Polynomial.aevalTower_C, MvPolynomial.aeval_X]

theorem coneToChartPoly_X :
    X.coneToChartPoly j Polynomial.X = Polynomial.C Polynomial.X := by
  rw [coneToChartPoly, Polynomial.aevalTower_X]

theorem coneToChartPoly_C_X_self :
    X.coneToChartPoly j (Polynomial.C (MvPolynomial.X j)) = Polynomial.X := by
  rw [coneToChartPoly_C_X, quotDehom_X_self, map_one, map_one, one_mul]

theorem coneToChartPoly_C_monomial (β : Fin (M + 1) →₀ ℕ) (a : k) :
    X.coneToChartPoly j (Polynomial.C (MvPolynomial.monomial β a)) =
      Polynomial.C (Polynomial.C (X.quotDehom j (MvPolynomial.monomial β a))) *
        Polynomial.X ^ β.degree := by
  rw [coneToChartPoly, Polynomial.aevalTower_C, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  conv_rhs => rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, ← MvPolynomial.algebraMap_eq,
    AlgHom.commutes, Polynomial.algebraMap_apply]
  have hp : ∀ i, (Polynomial.C (Polynomial.C (X.quotDehom j (MvPolynomial.X i))) *
      Polynomial.X : X.ChartPoly j) ^ β i =
      Polynomial.C (Polynomial.C (X.quotDehom j (MvPolynomial.X i))) ^ β i *
        Polynomial.X ^ β i := fun i => by ring
  simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]
  ring

/-- `η(s) = ∑_c δⱼ(s_c) Y^c` for `s ∈ R_M`. -/
theorem coeff_coneToChartPoly_C (s : MvPolynomial (Fin (M + 1)) k) (c : ℕ) :
    (X.coneToChartPoly j (Polynomial.C s)).coeff c =
      Polynomial.C (X.quotDehom j (MvPolynomial.homogeneousComponent c s)) := by
  induction s using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]
  | monomial β a =>
    rw [coneToChartPoly_C_monomial, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl)]
    split_ifs <;> simp

/-- The coefficients of `η(g)`: `(η(g)_c)_ℓ = δⱼ((g_ℓ)_c)`. -/
theorem coeff_coeff_coneToChartPoly (g : (MvPolynomial (Fin (M + 1)) k)[X]) (c ℓ : ℕ) :
    ((X.coneToChartPoly j g).coeff c).coeff ℓ =
      X.quotDehom j (MvPolynomial.homogeneousComponent c (g.coeff ℓ)) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial m s =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, coneToChartPoly_X,
      ← Polynomial.C_pow, Polynomial.coeff_mul_C, coeff_coneToChartPoly_C,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp

/-- `η` vanishes on `I[t]`. -/
theorem coneToChartPoly_eq_zero {g : (MvPolynomial (Fin (M + 1)) k)[X]} (hg : X.coneMk g = 0) :
    X.coneToChartPoly j g = 0 := by
  refine Polynomial.ext fun c => Polynomial.ext fun ℓ => ?_
  rw [coeff_coeff_coneToChartPoly,
    quotDehom_eq_zero_of_mem (X.isHomogeneousIdeal _ (coneMk_eq_zero_iff.1 hg ℓ) c)]
  simp

variable (X j) in
/-- The expansion `T → B_j[Y]` induced by `η`. -/
def coneTChartPoly : X.ConeRing →ₐ[k] X.ChartPoly j :=
  Polynomial.aevalTower (R := X.CoordRing) (X.coordLift
    ((X.coneToChartPoly j).comp Polynomial.CAlgHom) fun f hf =>
      coneToChartPoly_eq_zero (by
        change X.coneMk (Polynomial.C f) = 0
        rw [coneMk_C, Polynomial.C_eq_zero, coordMk_eq_zero_iff]
        exact hf))
    (Polynomial.C Polynomial.X)

theorem coneTChartPoly_coneMk (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    X.coneTChartPoly j (X.coneMk g) = X.coneToChartPoly j g := by
  have h : (X.coneTChartPoly j).comp X.coneMk = X.coneToChartPoly j := by
    refine Polynomial.algHom_ext' (AlgHom.ext fun s => ?_) ?_
    · simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, coneMk_C]
      simp only [coneTChartPoly, Polynomial.aevalTower_C]
      rfl
    · simp only [AlgHom.comp_apply, coneMk_X]
      simp only [coneTChartPoly, Polynomial.aevalTower_X, coneToChartPoly_X]
  exact congrArg (fun φ : (MvPolynomial (Fin (M + 1)) k)[X] →ₐ[k] X.ChartPoly j => φ g) h

/-! #### The localization `T_{x̄ⱼ}` and the inverse map -/

variable (X j) in
/-- `x̄ⱼ ∈ T`. -/
def coneX : X.ConeRing := X.coneMk (Polynomial.C (MvPolynomial.X j))

variable (X j) in
/-- The localization `T_{x̄ⱼ}`. -/
abbrev ConeAway : Type u := Localization.Away (X.coneX j)

variable (X j) in
/-- The localization `B_j[Y, Y⁻¹]`. -/
abbrev ChartLaurent : Type u := Localization.Away (Polynomial.X : X.ChartPoly j)

theorem coneTChartPoly_coneX : X.coneTChartPoly j (X.coneX j) = Polynomial.X := by
  rw [coneX, coneTChartPoly_coneMk, coneToChartPoly_C_X_self]

variable (X j) in
/-- `R_M → T_{x̄ⱼ}`, `f ↦ f̄`. -/
def coneAwayMk : MvPolynomial (Fin (M + 1)) k →ₐ[k] X.ConeAway j :=
  (IsScalarTower.toAlgHom k X.ConeRing (X.ConeAway j)).comp (X.coneMk.comp Polynomial.CAlgHom)

theorem coneAwayMk_apply (f : MvPolynomial (Fin (M + 1)) k) :
    X.coneAwayMk j f = algebraMap X.ConeRing (X.ConeAway j) (X.coneMk (Polynomial.C f)) :=
  rfl

theorem isUnit_coneAwayMk_X : IsUnit (X.coneAwayMk j (MvPolynomial.X j)) :=
  IsLocalization.Away.algebraMap_isUnit (X.coneX j)

variable (X j) in
/-- The inclusion `A_j → T_{x̄ⱼ}`, `τ̄ / x̄ⱼ^N ↦ τ̄ / x̄ⱼ^N`. -/
def chartAlgToAway : X.ChartAlg j →ₐ[k] X.ConeAway j :=
  ProjBerk.quotChartLift X.ideal (MvPolynomial.X j) 1 (X.coneAwayMk j)
    (fun f hf => by
      rw [coneAwayMk_apply, coneMk_C, (coordMk_eq_zero_iff.2 hf), Polynomial.C_0, map_zero])
    isUnit_coneAwayMk_X

theorem chartAlgToAway_quotDehom_X_mul (i : Fin (M + 1)) :
    X.chartAlgToAway j (X.quotDehom j (MvPolynomial.X i)) * X.coneAwayMk j (MvPolynomial.X j) =
      X.coneAwayMk j (MvPolynomial.X i) := by
  have h := ProjBerk.quotChartLift_quotChartMk_mul_pow (I := X.ideal)
    (σ := MvPolynomial.X j) (d := 1) (X.coneAwayMk j) (fun f hf => by
      rw [coneAwayMk_apply, coneMk_C, (coordMk_eq_zero_iff.2 hf), Polynomial.C_0, map_zero])
    isUnit_coneAwayMk_X 1 (MvPolynomial.X i)
  rw [pow_one, MvPolynomial.homogeneousComponent_eq_self
    (by rw [mul_one]; exact MvPolynomial.isHomogeneous_X k i)] at h
  rw [quotDehom_of_isHomogeneous (MvPolynomial.isHomogeneous_X k i)]
  exact h

variable (X j) in
/-- `B_j = A_j[t] → T_{x̄ⱼ}`. -/
def chartRingToAway : X.ChartRing j →ₐ[k] X.ConeAway j :=
  Polynomial.aevalTower (X.chartAlgToAway j) (algebraMap X.ConeRing (X.ConeAway j) Polynomial.X)

variable (X j) in
/-- `B_j[Y] → T_{x̄ⱼ}`, `Y ↦ x̄ⱼ`. -/
def chartPolyToAway : X.ChartPoly j →ₐ[k] X.ConeAway j :=
  Polynomial.aevalTower (X.chartRingToAway j) (algebraMap X.ConeRing (X.ConeAway j) (X.coneX j))

@[simp]
theorem chartPolyToAway_C_C (a : X.ChartAlg j) :
    X.chartPolyToAway j (Polynomial.C (Polynomial.C a)) = X.chartAlgToAway j a := by
  rw [chartPolyToAway, Polynomial.aevalTower_C, chartRingToAway, Polynomial.aevalTower_C]

@[simp]
theorem chartPolyToAway_C_X :
    X.chartPolyToAway j (Polynomial.C Polynomial.X) =
      algebraMap X.ConeRing (X.ConeAway j) Polynomial.X := by
  rw [chartPolyToAway, Polynomial.aevalTower_C, chartRingToAway, Polynomial.aevalTower_X]

@[simp]
theorem chartPolyToAway_X :
    X.chartPolyToAway j Polynomial.X = algebraMap X.ConeRing (X.ConeAway j) (X.coneX j) := by
  rw [chartPolyToAway, Polynomial.aevalTower_X]

variable (X j) in
/-- The inverse `T_{x̄ⱼ} → B_j[Y, Y⁻¹]`, `x̄ᵢ ↦ (x̄ᵢ / x̄ⱼ) Y`, `t ↦ t`. -/
def coneAwayToLaurent : X.ConeAway j →ₐ[k] X.ChartLaurent j :=
  IsLocalization.Away.liftAlgHom (X.coneX j)
    (f := (IsScalarTower.toAlgHom k (X.ChartPoly j) (X.ChartLaurent j)).comp (X.coneTChartPoly j))
    (by
      rw [AlgHom.comp_apply, coneTChartPoly_coneX, IsScalarTower.coe_toAlgHom']
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem coneAwayToLaurent_algebraMap (t : X.ConeRing) :
    X.coneAwayToLaurent j (algebraMap X.ConeRing (X.ConeAway j) t) =
      algebraMap (X.ChartPoly j) (X.ChartLaurent j) (X.coneTChartPoly j t) := by
  rw [coneAwayToLaurent, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

theorem coneAwayToLaurent_coneAwayMk (f : MvPolynomial (Fin (M + 1)) k) :
    X.coneAwayToLaurent j (X.coneAwayMk j f) =
      algebraMap (X.ChartPoly j) (X.ChartLaurent j) (X.coneToChartPoly j (Polynomial.C f)) := by
  rw [coneAwayMk_apply, coneAwayToLaurent_algebraMap, coneTChartPoly_coneMk]

/-- The composite `B_j[Y] → T_{x̄ⱼ} → B_j[Y, Y⁻¹]` is the localization map. -/
theorem coneAwayToLaurent_comp_chartPolyToAway :
    (X.coneAwayToLaurent j).comp (X.chartPolyToAway j) =
      IsScalarTower.toAlgHom k (X.ChartPoly j) (X.ChartLaurent j) := by
  have hu : IsUnit (algebraMap (X.ChartPoly j) (X.ChartLaurent j) Polynomial.X) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hY : X.coneAwayToLaurent j (X.coneAwayMk j (MvPolynomial.X j)) =
      algebraMap (X.ChartPoly j) (X.ChartLaurent j) Polynomial.X := by
    rw [coneAwayToLaurent_coneAwayMk, coneToChartPoly_C_X_self]
  refine Polynomial.algHom_ext' (Polynomial.algHom_ext' (chartAlg_algHom_ext fun i => ?_) ?_) ?_
  · simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, chartPolyToAway_C_C,
      IsScalarTower.coe_toAlgHom']
    refine hu.mul_right_cancel ?_
    rw [← hY, ← map_mul, chartAlgToAway_quotDehom_X_mul, coneAwayToLaurent_coneAwayMk,
      coneToChartPoly_C_X, map_mul, hY]
  · simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, chartPolyToAway_C_X,
      IsScalarTower.coe_toAlgHom', coneAwayToLaurent_algebraMap]
    rw [← coneMk_X, coneTChartPoly_coneMk, coneToChartPoly_X]
  · simp only [AlgHom.comp_apply, chartPolyToAway_X, IsScalarTower.coe_toAlgHom',
      coneAwayToLaurent_algebraMap, coneTChartPoly_coneX]

/-- The composite `T → B_j[Y] → T_{x̄ⱼ}` is the localization map:
`ḡ = ∑_c (g_c / x̄ⱼ^c) x̄ⱼ^c`. -/
theorem chartPolyToAway_comp_coneTChartPoly :
    (X.chartPolyToAway j).comp (X.coneTChartPoly j) =
      IsScalarTower.toAlgHom k X.ConeRing (X.ConeAway j) := by
  refine Polynomial.algHom_ext' (coordRing_algHom_ext fun i => ?_) ?_
  · simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, IsScalarTower.coe_toAlgHom']
    rw [← coneMk_C, coneTChartPoly_coneMk, coneToChartPoly_C_X, map_mul, chartPolyToAway_C_C,
      chartPolyToAway_X]
    exact chartAlgToAway_quotDehom_X_mul i
  · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← coneMk_X, coneTChartPoly_coneMk, coneToChartPoly_X, chartPolyToAway_C_X, coneMk_X]

theorem chartPolyToAway_coneToChartPoly (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    X.chartPolyToAway j (X.coneToChartPoly j g) =
      algebraMap X.ConeRing (X.ConeAway j) (X.coneMk g) := by
  rw [← coneTChartPoly_coneMk]
  exact congrArg (fun φ : X.ConeRing →ₐ[k] X.ConeAway j => φ (X.coneMk g))
    chartPolyToAway_comp_coneTChartPoly

theorem chartPolyToAway_injective : Function.Injective (X.chartPolyToAway j) := by
  have h : Function.Injective ((X.coneAwayToLaurent j).comp (X.chartPolyToAway j)) := by
    rw [coneAwayToLaurent_comp_chartPolyToAway]
    exact IsLocalization.injective (M := Submonoid.powers (Polynomial.X : X.ChartPoly j))
      (S := X.ChartLaurent j) (Submonoid.powers_le.2 Polynomial.X_mem_nonzeroDivisors)
  rw [AlgHom.coe_comp] at h
  exact Function.Injective.of_comp h

variable (X j) in
/-- `B_j[Y, Y⁻¹] → T_{x̄ⱼ}`, the extension of `B_j[Y] → T_{x̄ⱼ}`. -/
def laurentToConeAway : X.ChartLaurent j →ₐ[k] X.ConeAway j :=
  IsLocalization.Away.liftAlgHom (Polynomial.X : X.ChartPoly j) (f := X.chartPolyToAway j)
    (by rw [chartPolyToAway_X]; exact IsLocalization.Away.algebraMap_isUnit _)

theorem laurentToConeAway_algebraMap (p : X.ChartPoly j) :
    X.laurentToConeAway j (algebraMap (X.ChartPoly j) (X.ChartLaurent j) p) =
      X.chartPolyToAway j p := by
  rw [laurentToConeAway, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

variable (X j) in
/-- **`lem:sg-cone-charts`(1)**: `B_j[Y, Y⁻¹] = A_j[t][Y, Y⁻¹] ≃ T_{x̄ⱼ}`, by the inclusion on
`A_j`, `t ↦ t` and `Y ↦ x̄ⱼ`. -/
def coneChartEquiv : X.ChartLaurent j ≃ₐ[k] X.ConeAway j :=
  AlgEquiv.ofAlgHom (X.laurentToConeAway j) (X.coneAwayToLaurent j)
    (by
      refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
        (Submonoid.powers (X.coneX j)) (RingHom.ext fun t => ?_))
      simp only [RingHom.coe_comp, AlgHom.coe_toRingHom, Function.comp_apply, AlgHom.coe_comp,
        AlgHom.coe_id, id_eq, coneAwayToLaurent_algebraMap, laurentToConeAway_algebraMap]
      exact congrArg (fun φ : X.ConeRing →ₐ[k] X.ConeAway j => φ t)
        chartPolyToAway_comp_coneTChartPoly)
    (by
      refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
        (Submonoid.powers (Polynomial.X : X.ChartPoly j)) (RingHom.ext fun p => ?_))
      simp only [RingHom.coe_comp, AlgHom.coe_toRingHom, Function.comp_apply, AlgHom.coe_comp,
        AlgHom.coe_id, id_eq, laurentToConeAway_algebraMap]
      exact congrArg (fun φ : X.ChartPoly j →ₐ[k] X.ChartLaurent j => φ p)
        coneAwayToLaurent_comp_chartPolyToAway)

theorem coneChartEquiv_algebraMap (p : X.ChartPoly j) :
    X.coneChartEquiv j (algebraMap (X.ChartPoly j) (X.ChartLaurent j) p) =
      X.chartPolyToAway j p :=
  laurentToConeAway_algebraMap p

/-! #### Embedding in `Frac T` (`lem:sg-cone-charts`(2)) -/

variable [Fact (MvPolynomial.X j ∉ X.ideal)]

theorem coneX_ne_zero : X.coneX j ≠ 0 := by
  rw [coneX, coneMk_C, Ne, Polynomial.C_eq_zero, coordMk_eq_zero_iff]
  exact Fact.out

variable (X j) in
/-- `T_{x̄ⱼ} → Frac T`. -/
def coneAwayToFrac : X.ConeAway j →ₐ[k] FractionRing X.ConeRing :=
  IsLocalization.Away.liftAlgHom (X.coneX j)
    (f := IsScalarTower.toAlgHom k X.ConeRing (FractionRing X.ConeRing))
    (isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (coneX_ne_zero (X := X) (j := j))))

theorem coneAwayToFrac_algebraMap (t : X.ConeRing) :
    X.coneAwayToFrac j (algebraMap X.ConeRing (X.ConeAway j) t) =
      algebraMap X.ConeRing (FractionRing X.ConeRing) t := by
  rw [coneAwayToFrac, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

theorem coneAwayToFrac_injective : Function.Injective (X.coneAwayToFrac j) := by
  rw [coneAwayToFrac, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift,
    IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (X.ConeAway j)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (coneX_ne_zero (X := X) (j := j)))).eq_iff]
  exact ⟨fun h => h ▸ rfl, fun h => IsFractionRing.injective _ _ h⟩

variable (X j) in
/-- `B_j[Y] → Frac T`, `Y ↦ x̄ⱼ`. -/
def chartPolyToFrac : X.ChartPoly j →ₐ[k] FractionRing X.ConeRing :=
  (X.coneAwayToFrac j).comp (X.chartPolyToAway j)

/-- **`lem:sg-cone-charts`(2)**: `B_j[Y] → Frac T`, `Y ↦ x̄ⱼ`, is injective. -/
theorem chartPolyToFrac_injective : Function.Injective (X.chartPolyToFrac j) := by
  rw [chartPolyToFrac, AlgHom.coe_comp]
  exact coneAwayToFrac_injective.comp chartPolyToAway_injective

/-- `ḡ = ∑_c (g_c / x̄ⱼ^c) x̄ⱼ^c` in `Frac T`. -/
theorem chartPolyToFrac_coneToChartPoly (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    X.chartPolyToFrac j (X.coneToChartPoly j g) =
      algebraMap X.ConeRing (FractionRing X.ConeRing) (X.coneMk g) := by
  rw [chartPolyToFrac, AlgHom.comp_apply, chartPolyToAway_coneToChartPoly,
    coneAwayToFrac_algebraMap]

variable (X j) in
/-- `B_j → Frac T`. -/
def chartRingToFrac : X.ChartRing j →ₐ[k] FractionRing X.ConeRing :=
  (X.chartPolyToFrac j).comp Polynomial.CAlgHom

theorem chartRingToFrac_injective : Function.Injective (X.chartRingToFrac j) := by
  rw [chartRingToFrac, AlgHom.coe_comp]
  exact chartPolyToFrac_injective.comp Polynomial.C_injective

variable (X j) in
/-- The embedding of function fields `Frac B_j → Frac T`. -/
def chartFracToFrac : FractionRing (X.ChartRing j) →ₐ[k] FractionRing X.ConeRing :=
  IsFractionRing.liftAlgHom (chartRingToFrac_injective (X := X) (j := j))

theorem chartFracToFrac_algebraMap (b : X.ChartRing j) :
    X.chartFracToFrac j (algebraMap _ _ b) = X.chartRingToFrac j b := by
  rw [chartFracToFrac, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

/-- `V[Y] → Frac T`, `Y ↦ x̄ⱼ`, for `B_j ⊆ V ⊆ Frac B_j`. -/
def gaussToFrac (V : BirationalDVR k (X.ChartRing j)) :
    V.ring[X] →ₐ[k] FractionRing X.ConeRing :=
  Polynomial.aevalTower ((X.chartFracToFrac j).comp V.ring.val)
    (algebraMap X.ConeRing _ (X.coneX j))

theorem gaussToFrac_map (V : BirationalDVR k (X.ChartRing j)) (p : X.ChartPoly j) :
    gaussToFrac V (p.map V.toRing) = X.chartPolyToFrac j p := by
  have h : (gaussToFrac V).comp (Polynomial.mapAlgHom V.toRing) = X.chartPolyToFrac j := by
    refine Polynomial.algHom_ext' (AlgHom.ext fun b => ?_) ?_
    · simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Polynomial.coe_mapAlgHom,
        Polynomial.map_C]
      rw [gaussToFrac, Polynomial.aevalTower_C, AlgHom.comp_apply, Subalgebra.coe_val,
        BirationalDVR.coe_toRing_ringHom, chartFracToFrac_algebraMap, chartRingToFrac,
        AlgHom.comp_apply, Polynomial.CAlgHom_apply]
    · simp only [AlgHom.comp_apply, Polynomial.coe_mapAlgHom, Polynomial.map_X]
      rw [gaussToFrac, Polynomial.aevalTower_X, chartPolyToFrac, AlgHom.comp_apply,
        chartPolyToAway_X, coneAwayToFrac_algebraMap]
  exact congrArg (fun φ : X.ChartPoly j →ₐ[k] FractionRing X.ConeRing => φ p) h

/-- **`lem:sg-cone-charts`(2)**, Gauss form: `x̄ⱼ` is transcendental over `V ⊆ Frac B_j`. -/
theorem gaussToFrac_injective (V : BirationalDVR k (X.ChartRing j)) :
    Function.Injective (gaussToFrac V) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (X.ChartRing j))
    (p.support.image fun c => (p.coeff c : FractionRing (X.ChartRing j)))
  have hb : ∀ c, ∃ b : X.ChartRing j, algebraMap _ (FractionRing (X.ChartRing j)) b =
      (d : X.ChartRing j) • (p.coeff c : FractionRing (X.ChartRing j)) := by
    intro c
    by_cases hc : c ∈ p.support
    · exact hd _ (Finset.mem_image_of_mem _ hc)
    · exact ⟨0, by
        rw [Polynomial.notMem_support_iff.1 hc, map_zero, ZeroMemClass.coe_zero]
        exact (smul_zero (A := FractionRing (X.ChartRing j)) (d : X.ChartRing j)).symm⟩
  choose b hb using hb
  set q : X.ChartPoly j := ∑ c ∈ p.support, Polynomial.monomial c (b c) with hq_def
  have hq : q.map V.toRing = Polynomial.C (V.toRing d) * p := by
    ext c : 1
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul, hq_def, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hc
    · apply Subtype.ext
      rw [BirationalDVR.coe_toRing_ringHom, hb c, Subalgebra.coe_mul, BirationalDVR.coe_toRing]
      exact Algebra.smul_def (d : X.ChartRing j)
        ((p.coeff c : V.ring) : FractionRing (X.ChartRing j))
    · rw [Polynomial.notMem_support_iff.1 hc, mul_zero, map_zero]
  have h1 : X.chartPolyToFrac j q = 0 := by
    rw [← gaussToFrac_map, hq, map_mul, hp, mul_zero]
  have hq0 : q = 0 := chartPolyToFrac_injective (h1.trans (map_zero _).symm)
  have h2 : Polynomial.C (V.toRing d) * p = 0 := by rw [← hq, hq0, Polynomial.map_zero]
  refine (mul_eq_zero.1 h2).resolve_left ?_
  rw [Polynomial.C_eq_zero, map_eq_zero_iff _ V.toRing_injective]
  exact nonZeroDivisors.ne_zero d.2

theorem gaussToFrac_coneToChartPoly (V : BirationalDVR k (X.ChartRing j))
    (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    gaussToFrac V ((X.coneToChartPoly j g).map V.toRing) =
      algebraMap X.ConeRing _ (X.coneMk g) := by
  rw [gaussToFrac_map, chartPolyToFrac_coneToChartPoly]

variable (X j) in
/-- **`lem:sg-cone-charts`(2)**, transcendence degree: `trdeg_k Frac T = trdeg_k k(X) + 2`, with
`k(X) = Frac A_j`. (Through `T ⊆ T_{x̄ⱼ} ≅ B_j[Y, Y⁻¹]` and `B_j[Y] = A_j[t][Y]`.) -/
theorem trdeg_fractionRing_coneRing :
    Algebra.trdeg k (FractionRing X.ConeRing) =
      Algebra.trdeg k (FractionRing (X.ChartAlg j)) + 2 := by
  rw [trdeg_localization_eq (S := FractionRing X.ConeRing) (nonZeroDivisors X.ConeRing) le_rfl,
    trdeg_localization_eq (S := FractionRing (X.ChartAlg j)) (nonZeroDivisors (X.ChartAlg j))
      le_rfl,
    ← trdeg_localization_eq (S := X.ConeAway j) (Submonoid.powers (X.coneX j))
      (powers_le_nonZeroDivisors_of_noZeroDivisors coneX_ne_zero),
    ← (X.coneChartEquiv j).trdeg_eq,
    trdeg_localization_eq (S := X.ChartLaurent j) (Submonoid.powers (Polynomial.X : X.ChartPoly j))
      (Submonoid.powers_le.2 Polynomial.X_mem_nonzeroDivisors),
    trdeg_polynomial_eq_add_one, trdeg_polynomial_eq_add_one, add_assoc, one_add_one_eq_two]

variable (X j) in
/-- The discrete valuation ring `R' = V[x̄ⱼ]_{m_V V[x̄ⱼ]} ⊆ Frac T` attached to a discrete valuation
ring `B_j ⊆ V ⊆ Frac B_j` (proof of `lem:sg-div-points`(2), via `lem:bj-gauss-dvr`). -/
def chartDVR (V : BirationalDVR k (X.ChartRing j)) : BirationalDVR k X.ConeRing :=
  haveI : Algebra.EssFiniteType k V.ring[X] := Algebra.EssFiniteType.comp k V.ring V.ring[X]
  { ring := atPrimeRange
      (P := Ideal.map (Polynomial.C : V.ring →+* V.ring[X]) (IsLocalRing.maximalIdeal V.ring))
      (gaussToFrac V) (gaussToFrac_injective V)
    isDVR := RingEquivClass.isDiscreteValuationRing (atPrimeEquiv _ _)
    essFiniteType := essFiniteType_atPrimeRange _ _
    algebraMap_mem := fun t => by
      obtain ⟨g, rfl⟩ := coneMk_surjective t
      rw [← gaussToFrac_coneToChartPoly V g]
      exact mem_atPrimeRange _ _ _ }

/-- The Gauss formula `ord_{R'}(ḡ) = min_c ord_V(η(g)_c)`. -/
theorem chartDVR_ord (V : BirationalDVR k (X.ChartRing j))
    (g : (MvPolynomial (Fin (M + 1)) k)[X]) :
    (X.chartDVR j V).ord (X.coneMk g) = (X.coneToChartPoly j g).support.inf
      fun c => V.ord ((X.coneToChartPoly j g).coeff c) := by
  have : IsDiscreteValuationRing (atPrimeRange
      (P := Ideal.map (Polynomial.C : V.ring →+* V.ring[X]) (IsLocalRing.maximalIdeal V.ring))
      (gaussToFrac V) (gaussToFrac_injective V)) := (X.chartDVR j V).isDVR
  have h : (X.chartDVR j V).toRing (X.coneMk g) =
      ⟨gaussToFrac V ((X.coneToChartPoly j g).map V.toRing), mem_atPrimeRange _ _ _⟩ :=
    Subtype.ext (gaussToFrac_coneToChartPoly V g).symm
  rw [BirationalDVR.ord, h]
  erw [addVal_atPrimeRange_eq]
  rw [addVal_gaussDVR, Polynomial.support_map_of_injective
    (f := (V.toRing : X.ChartRing j →+* V.ring)) _ V.toRing_injective]
  simp only [Polynomial.coeff_map]
  rfl

end Charts

end ProjSubvariety

end EnvelopeProperty
