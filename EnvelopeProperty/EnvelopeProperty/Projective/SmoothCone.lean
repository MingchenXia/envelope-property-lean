/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SmoothConeLaurent
import EnvelopeProperty.Projective.SubvarietyCone
import EnvelopeProperty.Projective.SubvarietyNormal
import EnvelopeProperty.Algebra.NormalDVR

/-!
# The cone over a projectively normal variety: bigrading, chart models, homogeneous `p`-basis

Let `k` be a field, `X = V(I) ⊆ ℙᴹ` a projective subvariety (`EnvelopeProperty.ProjSubvariety`),
`S = R_M / I` and `T = S[t]` the coordinate ring of the affine cone over `X × 𝔸¹`
(`ProjSubvariety.ConeRing`), with fraction field `K = Frac T`. This file contains the first part
of the subsection `subsec:sg-cone` of the blueprint chapter `smooth-general.tex` (test ideals on
the punctured cone, for Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Theorem 3.1, `thm:smooth-EP`, on smooth `X`): the bigrading of `K`, the chart models
`A_j[Y, Y⁻¹][t] ⊆ Frac(A_j)[Y, Y⁻¹][t] ⊆ K` (`lem:sg-cone-charts`), projective normality
(`lem:sg-proj-normal-sat`) and the homogeneous `p`-basis (`lem:sg-homog-pbasis`).

## Main definitions

* `ProjSubvariety.HasSmoothCharts X`: every chart algebra `A_i`, `xᵢ ∉ I`, is smooth over `k`
  (`conv:sg-setting`).
* `ProjSubvariety.dim X = trdeg_k Frac(T) - 2`; it is `trdeg_k k(X)` for the function field
  `k(X) = Frac(A_j)` of every chart (`ProjSubvariety.trdeg_chartField_eq_dim`).
* `ProjSubvariety.fracMk X : R_M → K`, `a ↦ ā`, and `ProjSubvariety.fracT X = t ∈ K`.
* `ProjSubvariety.IsBihom X f b λ` (`conv:sg-setting`): `f ∈ K` is bihomogeneous of bidegree
  `(b, λ) ∈ ℤ × ℕ`, i.e. `f = (ā / ā') t^λ` for forms `a`, `a' ∉ I` with `deg a - deg a' = b`.
  The bigrading is put into these explicit fractions (no graded-algebra instances).
* For `xⱼ ∉ I`: `X.ChartField j = Frac(A_j)`, `X.ChartModel j = Frac(A_j)[Y, Y⁻¹][t]`
  (`(LaurentPolynomial _)[X]`), the embedding `X.modelToFrac j` (`Y ↦ x̄ⱼ`, `t ↦ t`) and the
  instances `X.modelAlgebra j`, `ProjSubvariety.isFractionRing_chartModel`: `K` is a fraction field
  of the chart model.
* `ProjSubvariety.coneZ X ι`: the family `z = (t, x̄_{ι(o)})_o` of `T`.

## Main results

* `ProjSubvariety.exists_eq_coneMk_of_isBihom`: an element of `T` that is bihomogeneous of
  bidegree `(b, λ)` in `K` is `s̄ t^λ` for a form `s` of degree `b`.
* `ProjSubvariety.isBihom_iff_chartModel` (`lem:sg-cone-charts`(1), bigraded form): `f` is
  bihomogeneous of bidegree `(b, λ)` iff `f = c x̄ⱼ^b t^λ` with `c ∈ k(X) = Frac(A_j)`.
* `ProjSubvariety.modelToFrac_injective` (`lem:sg-cone-charts`(2)): `x̄ⱼ`, `t` are algebraically
  independent over `k(X)`.
* `ProjSubvariety.smooth_coneAway` (`lem:sg-cone-charts`(3)): `T_{x̄ⱼ}` is smooth if `A_j` is.
* `ProjSubvariety.dvd_of_forall_dvd_mul_pow`,
  `ProjSubvariety.exists_eq_algebraMap_of_forall_mul_pow` (`lem:sg-proj-normal-sat`): for `X` projectively normal of dimension `≥ 1`,
  `⋂_{xᵢ ∉ I} S_{x̄ᵢ} = S` and `⋂_{xᵢ ∉ I} T_{x̄ᵢ} = T` in `K`.
* `ProjSubvariety.exists_isPBasis_chartField` (`lem:sg-homog-pbasis`(1), field part),
  `ProjSubvariety.exists_isPBasis_coneZ` (`lem:sg-homog-pbasis`(1)): `z = (x̄_{i₀}, …, x̄_{iₙ}, t)`
  is a `p`-basis of `K`; `ProjSubvariety.IsBihom.traceIter_coneZ` (`lem:sg-homog-pbasis`(2)):
  `Φ^e_z` maps bidegree `(b, λ)` to `((b - (n + 1)(Q - 1))/Q, (λ - (Q - 1))/Q)` or to `0`.

## Deviations from the blueprint

* `lem:sg-cone-charts`(1) is formalized by SG2 as `B_j[Y, Y⁻¹] ≅ T_{x̄ⱼ}`
  (`ProjSubvariety.coneChartEquiv`); the bigraded identification is used here in the form
  `isBihom_iff_chartModel` over the function field, and `K = Frac(Frac(A_j)[Y, Y⁻¹][t])`.
* `lem:sg-homog-pbasis`(1) is proved through the chart model of an arbitrary chart and the
  Jacobian criterion (`EnvelopeProperty.Cartier.IsPBasis.of_isUnit_jac`) instead of `ζ = (w, Y, t)`
  for `Y = x̄ᵢ₀` only; (2) uses `J(z/ζ) = det N · Y^n` with `det N ∈ k(X)^×`, not `±Y^n`.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty

open ProjBerk (quotChartMk QuotChartAlg)

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-! ### Smooth charts and dimension -/

/-- `X = V(I)` has **smooth charts** if every chart algebra `A_i = S_{(x̄ᵢ)}`, `xᵢ ∉ I`, is a
smooth `k`-algebra (`conv:sg-setting`). -/
def HasSmoothCharts : Prop :=
  ∀ i, MvPolynomial.X i ∉ X.ideal → Algebra.Smooth k (QuotChartAlg X.ideal (MvPolynomial.X i) 1)

/-- The **dimension** `n = trdeg_k Frac(T) - 2` of `X`, `T = S[t]` the cone ring. In
characteristic `p` it is the transcendence degree of the function field `k(X) = Frac(A_j)` of every
chart (`trdeg_chartField_eq_dim`). -/
def dim : ℕ := (Algebra.trdeg k (FractionRing X.ConeRing)).toNat - 2

/-! ### Forms in `Frac T` -/

/-- The class `ā ∈ K = Frac T` of `a ∈ R_M`. -/
def fracMk : MvPolynomial (Fin (M + 1)) k →ₐ[k] FractionRing X.ConeRing :=
  (IsScalarTower.toAlgHom k X.ConeRing (FractionRing X.ConeRing)).comp
    (X.coneMk.comp Polynomial.CAlgHom)

/-- `t ∈ K = Frac T`. -/
def fracT : FractionRing X.ConeRing :=
  algebraMap X.ConeRing (FractionRing X.ConeRing) Polynomial.X

variable {X}

theorem fracMk_apply (a : MvPolynomial (Fin (M + 1)) k) :
    X.fracMk a = algebraMap X.ConeRing (FractionRing X.ConeRing) (Polynomial.C (X.coordMk a)) := by
  simp [fracMk, coneMk_C]

theorem fracMk_eq_zero_iff {a : MvPolynomial (Fin (M + 1)) k} : X.fracMk a = 0 ↔ a ∈ X.ideal := by
  rw [fracMk_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _), Polynomial.C_eq_zero,
    coordMk_eq_zero_iff]

theorem fracMk_ne_zero {a : MvPolynomial (Fin (M + 1)) k} (ha : a ∉ X.ideal) : X.fracMk a ≠ 0 :=
  fun h => ha (fracMk_eq_zero_iff.1 h)

theorem fracT_ne_zero : X.fracT ≠ 0 := by
  rw [fracT, Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact Polynomial.X_ne_zero

theorem algebraMap_coneMk_C_mul_X_pow (a : MvPolynomial (Fin (M + 1)) k) (l : ℕ) :
    algebraMap X.ConeRing (FractionRing X.ConeRing) (X.coneMk (Polynomial.C a * Polynomial.X ^ l)) =
      X.fracMk a * X.fracT ^ l := by
  rw [map_mul, map_pow, coneMk_C, coneMk_X, map_mul, map_pow, fracMk_apply, fracT]

/-! ### Bihomogeneous elements of `Frac T` -/

variable (X) in
/-- `f ∈ K = Frac T` is **bihomogeneous of bidegree `(b, λ)`** (`conv:sg-setting`):
`f = (ā / ā') t^λ` for forms `a` of degree `d` and `a' ∉ I` of degree `d'` with `d - d' = b`.
Here `deg x̄ᵢ = (1, 0)`, `deg t = (0, 1)`; `0` is bihomogeneous of every bidegree. -/
def IsBihom (f : FractionRing X.ConeRing) (b : ℤ) (l : ℕ) : Prop :=
  ∃ (a a' : MvPolynomial (Fin (M + 1)) k) (d d' : ℕ), a.IsHomogeneous d ∧ a'.IsHomogeneous d' ∧
    a' ∉ X.ideal ∧ (d : ℤ) - d' = b ∧ f = X.fracMk a / X.fracMk a' * X.fracT ^ l

theorem isBihom_zero (b : ℤ) (l : ℕ) : X.IsBihom 0 b l := by
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  rcases le_or_gt 0 b with hb | hb
  · refine ⟨0, 1, b.toNat, 0, MvPolynomial.isHomogeneous_zero _ _ _,
      MvPolynomial.isHomogeneous_one _ _, fun h => ?_, by omega, by simp⟩
    exact (Ideal.ne_top_iff_one _).1 X.isPrime.ne_top h
  · refine ⟨0, MvPolynomial.X j ^ (-b).toNat, 0, (-b).toNat,
      MvPolynomial.isHomogeneous_zero _ _ _, MvPolynomial.isHomogeneous_X_pow _ _,
      fun h => hj (X.isPrime.mem_of_pow_mem _ h), by omega, by simp⟩

/-- A form `a` of degree `d` times `t^λ` is bihomogeneous of bidegree `(d, λ)`. -/
theorem isBihom_fracMk_mul {a : MvPolynomial (Fin (M + 1)) k} {d : ℕ} (ha : a.IsHomogeneous d)
    (l : ℕ) : X.IsBihom (X.fracMk a * X.fracT ^ l) d l :=
  ⟨a, 1, d, 0, ha, MvPolynomial.isHomogeneous_one _ _,
    fun h => (Ideal.ne_top_iff_one _).1 X.isPrime.ne_top h, by simp, by simp⟩

/-- `s̄ t^λ ∈ T` is bihomogeneous of bidegree `(d, λ)` for a form `s` of degree `d`. -/
theorem isBihom_algebraMap_coneMk {a : MvPolynomial (Fin (M + 1)) k} {d : ℕ}
    (ha : a.IsHomogeneous d) (l : ℕ) :
    X.IsBihom (algebraMap X.ConeRing (FractionRing X.ConeRing)
      (X.coneMk (Polynomial.C a * Polynomial.X ^ l))) d l := by
  rw [algebraMap_coneMk_C_mul_X_pow]
  exact isBihom_fracMk_mul ha l

theorem IsBihom.mul {f g : FractionRing X.ConeRing} {b c : ℤ} {l m : ℕ} (hf : X.IsBihom f b l)
    (hg : X.IsBihom g c m) : X.IsBihom (f * g) (b + c) (l + m) := by
  obtain ⟨a, a', d, d', ha, ha', ha'I, hd, rfl⟩ := hf
  obtain ⟨e, e', r, r', he, he', he'I, hr, rfl⟩ := hg
  refine ⟨a * e, a' * e', d + r, d' + r', ha.mul he, ha'.mul he',
    fun h => (X.isPrime.mem_or_mem h).elim ha'I he'I, by push_cast; omega, ?_⟩
  rw [map_mul, map_mul, pow_add]
  field_simp

theorem IsBihom.pow {f : FractionRing X.ConeRing} {b : ℤ} {l : ℕ} (hf : X.IsBihom f b l) (r : ℕ) :
    X.IsBihom (f ^ r) (r * b) (r * l) := by
  induction r with
  | zero =>
    simpa using isBihom_fracMk_mul (X := X) (MvPolynomial.isHomogeneous_one _ _) 0
  | succ r ih =>
    rw [pow_succ]
    convert ih.mul hf using 1 <;> push_cast <;> ring

theorem IsBihom.add {f g : FractionRing X.ConeRing} {b : ℤ} {l : ℕ} (hf : X.IsBihom f b l)
    (hg : X.IsBihom g b l) : X.IsBihom (f + g) b l := by
  obtain ⟨a, a', d, d', ha, ha', ha'I, hd, rfl⟩ := hf
  obtain ⟨e, e', r, r', he, he', he'I, hr, rfl⟩ := hg
  have hdeg : d + r' = r + d' := by omega
  refine ⟨a * e' + e * a', a' * e', d + r', d' + r', (ha.mul he').add (hdeg ▸ he.mul ha'),
    ha'.mul he', fun h => (X.isPrime.mem_or_mem h).elim ha'I he'I, by push_cast; omega, ?_⟩
  have h1 := fracMk_ne_zero ha'I
  have h2 := fracMk_ne_zero he'I
  rw [map_add, map_mul, map_mul, map_mul]
  field_simp

theorem IsBihom.neg {f : FractionRing X.ConeRing} {b : ℤ} {l : ℕ} (hf : X.IsBihom f b l) :
    X.IsBihom (-f) b l := by
  obtain ⟨a, a', d, d', ha, ha', ha'I, hd, rfl⟩ := hf
  refine ⟨-a, a', d, d', ha.neg, ha', ha'I, hd, ?_⟩
  rw [map_neg]
  ring

theorem IsBihom.inv {f : FractionRing X.ConeRing} {b : ℤ} (hf : X.IsBihom f b 0) :
    X.IsBihom f⁻¹ (-b) 0 := by
  obtain ⟨a, a', d, d', ha, ha', ha'I, hd, rfl⟩ := hf
  by_cases haI : a ∈ X.ideal
  · rw [fracMk_eq_zero_iff.2 haI, zero_div, zero_mul, inv_zero]
    exact isBihom_zero _ _
  · exact ⟨a', a, d', d, ha', ha, haI, by omega, by simp⟩

/-- **Bihomogeneous elements of `T`** (`conv:sg-setting`): if `f ∈ T` is bihomogeneous of bidegree
`(b, λ)` in `K`, then `f = s̄ t^λ` for a form `s` of degree `b` (`s = 0` if `b < 0`). -/
theorem exists_eq_coneMk_of_isBihom {f : X.ConeRing} {b : ℤ} {l : ℕ}
    (hf : X.IsBihom (algebraMap X.ConeRing (FractionRing X.ConeRing) f) b l) :
    ∃ s : MvPolynomial (Fin (M + 1)) k, s.IsHomogeneous b.toNat ∧
      f = X.coneMk (Polynomial.C s * Polynomial.X ^ l) := by
  obtain ⟨a, a', d, d', ha, ha', ha'I, hd, hfa⟩ := hf
  have ha'0 := fracMk_ne_zero ha'I
  -- `f ā' = ā t^λ` in `T`
  have h1 : f * Polynomial.C (X.coordMk a') = Polynomial.C (X.coordMk a) * Polynomial.X ^ l := by
    apply IsFractionRing.injective X.ConeRing (FractionRing X.ConeRing)
    rw [map_mul, hfa, map_mul, map_pow, ← fracMk_apply, ← fracMk_apply, ← fracT]
    field_simp
  have hs0 : X.coordMk a' ≠ 0 := fun h => ha'I (coordMk_eq_zero_iff.1 h)
  -- the coefficients of `f`
  have hcoeff : ∀ m, f.coeff m * X.coordMk a' = if m = l then X.coordMk a else 0 := by
    intro m
    have := congrArg (fun q => Polynomial.coeff q m) h1
    simpa [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul_X_pow, eq_comm] using this
  obtain ⟨F, hF⟩ := coordMk_surjective (X := X) (f.coeff l)
  have hFa : a' * F - a ∈ X.ideal := by
    rw [← coordMk_eq_zero_iff, map_sub, map_mul, hF, mul_comm, hcoeff l, if_pos rfl, sub_self]
  have hfC : f = Polynomial.C (f.coeff l) * Polynomial.X ^ l := by
    ext m
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with hm
    · rw [hm]
    · have := hcoeff m
      rw [if_neg hm] at this
      exact (mul_eq_zero.1 this).resolve_right hs0
  by_cases hb : 0 ≤ b
  · refine ⟨MvPolynomial.homogeneousComponent b.toNat F,
      MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
    have h2 := sub_homogeneousComponent_mem_of_mul_sub_mem X.isHomogeneousIdeal ha' ha'I ha hFa
      (c := b.toNat) (by omega)
    rw [← coordMk_eq_zero_iff, map_sub, sub_eq_zero, hF] at h2
    rw [hfC, h2, coneMk]
    simp
  · refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, ?_⟩
    have h2 : F ∈ X.ideal := mem_of_forall_homogeneousComponent_mem fun c =>
      homogeneousComponent_mem_of_mul_sub_mem X.isHomogeneousIdeal ha' ha'I ha hFa (by omega)
    rw [← coordMk_eq_zero_iff, hF] at h2
    rw [hfC, h2]
    simp

/-! ### The chart models `Frac(A_j)[Y, Y⁻¹][t] ⊆ K` (`lem:sg-cone-charts`) -/

section ChartModel

variable (X) (j : Fin (M + 1)) [Fact (MvPolynomial.X j ∉ X.ideal)]

/-- The function field `k(X) = Frac(A_j)` of `X`, seen through the chart `A_j`. -/
abbrev ChartField : Type u := FractionRing (X.ChartAlg j)

/-- The **chart model** `Frac(A_j)[Y, Y⁻¹][t]`, bigraded by `deg Y = (1, 0)`, `deg t = (0, 1)`. -/
abbrev ChartModel : Type u := (LaurentPolynomial (X.ChartField j))[X]

/-- The embedding `A_j → K`, `τ̄ / x̄ⱼ^N ↦ τ̄ / x̄ⱼ^N`. -/
def chartAlgToFrac : X.ChartAlg j →ₐ[k] FractionRing X.ConeRing :=
  (X.coneAwayToFrac j).comp (X.chartAlgToAway j)

variable {X j}

theorem chartAlgToFrac_eq (a : X.ChartAlg j) :
    X.chartAlgToFrac j a = X.chartPolyToFrac j (Polynomial.C (Polynomial.C a)) := by
  simp [chartAlgToFrac, chartPolyToFrac, chartPolyToAway_C_C]

theorem chartAlgToFrac_injective : Function.Injective (X.chartAlgToFrac j) := by
  intro a b h
  rw [chartAlgToFrac_eq, chartAlgToFrac_eq] at h
  exact Polynomial.C_injective (Polynomial.C_injective (chartPolyToFrac_injective h))

theorem fracMk_X_ne_zero : X.fracMk (MvPolynomial.X j) ≠ 0 := fracMk_ne_zero Fact.out

theorem coneAwayToFrac_coneAwayMk (f : MvPolynomial (Fin (M + 1)) k) :
    X.coneAwayToFrac j (X.coneAwayMk j f) = X.fracMk f := by
  rw [coneAwayMk_apply, coneAwayToFrac_algebraMap]
  rfl

/-- `δⱼ(τ) x̄ⱼ^N = τ̄` in `K` for a form `τ` of degree `N`. -/
theorem chartAlgToFrac_quotDehom_mul {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous N) :
    X.chartAlgToFrac j (X.quotDehom j τ) * X.fracMk (MvPolynomial.X j) ^ N = X.fracMk τ := by
  have h := ProjBerk.quotChartLift_quotChartMk_mul_pow (I := X.ideal)
    (σ := MvPolynomial.X j) (d := 1) (X.coneAwayMk j) (fun f hf => by
      rw [coneAwayMk_apply, coneMk_C, (coordMk_eq_zero_iff.2 hf), Polynomial.C_0, map_zero])
    isUnit_coneAwayMk_X N τ
  rw [mul_one, MvPolynomial.homogeneousComponent_eq_self hτ] at h
  have h3 : X.chartAlgToAway j (X.quotDehom j τ) * X.coneAwayMk j (MvPolynomial.X j) ^ N =
      X.coneAwayMk j τ := by
    rw [quotDehom_of_isHomogeneous hτ]
    exact h
  have h4 := congrArg (X.coneAwayToFrac j) h3
  rwa [map_mul, map_pow, coneAwayToFrac_coneAwayMk, coneAwayToFrac_coneAwayMk] at h4

theorem chartAlgToFrac_quotDehom {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous N) :
    X.chartAlgToFrac j (X.quotDehom j τ) = X.fracMk τ / X.fracMk (MvPolynomial.X j) ^ N := by
  rw [eq_div_iff (pow_ne_zero _ fracMk_X_ne_zero), chartAlgToFrac_quotDehom_mul hτ]

variable (X j) in
/-- The embedding of function fields `Frac(A_j) → K`. -/
def chartFieldToFrac : X.ChartField j →ₐ[k] FractionRing X.ConeRing :=
  IsFractionRing.liftAlgHom (K := X.ChartField j) (chartAlgToFrac_injective (X := X) (j := j))

theorem chartFieldToFrac_algebraMap (a : X.ChartAlg j) :
    X.chartFieldToFrac j (algebraMap (X.ChartAlg j) (X.ChartField j) a) = X.chartAlgToFrac j a := by
  rw [chartFieldToFrac, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem chartFieldToFrac_injective : Function.Injective (X.chartFieldToFrac j) :=
  (X.chartFieldToFrac j : X.ChartField j →+* FractionRing X.ConeRing).injective

variable (X j) in
/-- `x̄ⱼ` as a unit of `K`. -/
def coneXUnit : (FractionRing X.ConeRing)ˣ :=
  Units.mk0 (X.fracMk (MvPolynomial.X j)) fracMk_X_ne_zero

variable (X j) in
/-- `Frac(A_j)[Y, Y⁻¹] → K`, `Y ↦ x̄ⱼ`. -/
def laurentToFrac : LaurentPolynomial (X.ChartField j) →+* FractionRing X.ConeRing :=
  LaurentPolynomial.eval₂ (X.chartFieldToFrac j : X.ChartField j →+* FractionRing X.ConeRing)
    (X.coneXUnit j)

variable (X j) in
/-- **The chart model** `Frac(A_j)[Y, Y⁻¹][t] → K`, `Y ↦ x̄ⱼ`, `t ↦ t` (`lem:sg-cone-charts`). -/
def modelToFrac : X.ChartModel j →+* FractionRing X.ConeRing :=
  Polynomial.eval₂RingHom (X.laurentToFrac j) X.fracT

theorem modelToFrac_monomial (c : X.ChartField j) (b : ℤ) (l : ℕ) :
    X.modelToFrac j (Polynomial.C (LaurentPolynomial.C c * LaurentPolynomial.T b) *
        Polynomial.X ^ l) =
      X.chartFieldToFrac j c * X.fracMk (MvPolynomial.X j) ^ b * X.fracT ^ l := by
  simp only [modelToFrac, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow, laurentToFrac, LaurentPolynomial.eval₂_C_mul_T,
    Units.val_zpow_eq_zpow_val, coneXUnit, Units.val_mk0]
  rfl

theorem modelToFrac_C_C (c : X.ChartField j) :
    X.modelToFrac j (Polynomial.C (LaurentPolynomial.C c)) = X.chartFieldToFrac j c := by
  have h := modelToFrac_monomial (X := X) (j := j) c 0 0
  simpa using h

theorem modelToFrac_X : X.modelToFrac j Polynomial.X = X.fracT := by
  simp [modelToFrac]

variable (X j) in
/-- `B_j[Y] = A_j[t][Y] → Frac(A_j)[Y, Y⁻¹][t]`, the identity on `A_j`, `t ↦ t`, `Y ↦ Y`. -/
def chartPolyToModel : X.ChartPoly j →+* X.ChartModel j :=
  Polynomial.eval₂RingHom (R := X.ChartRing j) (S := X.ChartModel j)
    (Polynomial.eval₂RingHom (R := X.ChartAlg j) (S := X.ChartModel j)
      ((Polynomial.C : LaurentPolynomial (X.ChartField j) →+* X.ChartModel j).comp
        ((LaurentPolynomial.C : X.ChartField j →+* LaurentPolynomial (X.ChartField j)).comp
          (algebraMap (X.ChartAlg j) (X.ChartField j)))) (Polynomial.X : X.ChartModel j))
    (Polynomial.C (LaurentPolynomial.T 1) : X.ChartModel j)

theorem modelToFrac_comp_chartPolyToModel :
    (X.modelToFrac j).comp (X.chartPolyToModel j) =
      (X.chartPolyToFrac j : X.ChartPoly j →+* FractionRing X.ConeRing) := by
  refine Polynomial.ringHom_ext (fun q => ?_) ?_
  · have h : ((X.modelToFrac j).comp (X.chartPolyToModel j)).comp Polynomial.C =
        (X.chartPolyToFrac j : X.ChartPoly j →+* FractionRing X.ConeRing).comp Polynomial.C := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, chartPolyToModel,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.coe_coe]
        rw [modelToFrac_C_C, chartFieldToFrac_algebraMap, chartAlgToFrac_eq]
      · simp only [RingHom.coe_comp, Function.comp_apply, chartPolyToModel,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, RingHom.coe_coe]
        rw [modelToFrac_X, chartPolyToFrac, AlgHom.comp_apply, chartPolyToAway_C_X,
          coneAwayToFrac_algebraMap]
        rfl
    exact congrArg (fun φ : X.ChartRing j →+* FractionRing X.ConeRing => φ q) h
  · simp only [RingHom.coe_comp, Function.comp_apply, chartPolyToModel,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.coe_coe]
    rw [chartPolyToFrac, AlgHom.comp_apply, chartPolyToAway_X, coneAwayToFrac_algebraMap]
    have h := modelToFrac_monomial (X := X) (j := j) 1 1 0
    simp only [map_one, one_mul, pow_zero, mul_one, zpow_one] at h
    rw [h, coneX, fracMk_apply, coneMk_C]

theorem modelToFrac_chartPolyToModel (q : X.ChartPoly j) :
    X.modelToFrac j (X.chartPolyToModel j q) = X.chartPolyToFrac j q :=
  congrArg (fun φ : X.ChartPoly j →+* FractionRing X.ConeRing => φ q)
    modelToFrac_comp_chartPolyToModel

/-- **Clearing denominators** in the chart model: every `f` satisfies `ψ(h) f = ψ(g)` for some
`h, g ∈ A_j[t][Y]` with `ψ(h) ≠ 0`, `ψ = chartPolyToModel`. -/
theorem exists_mul_eq_chartPolyToModel (f : X.ChartModel j) :
    ∃ h g : X.ChartPoly j, X.chartPolyToModel j h ≠ 0 ∧
      X.chartPolyToModel j h * f = X.chartPolyToModel j g := by
  set ψ := X.chartPolyToModel j
  let P : X.ChartModel j → Prop := fun f => ∃ h g : X.ChartPoly j, ψ h ≠ 0 ∧ ψ h * f = ψ g
  have hadd : ∀ f₁ f₂, P f₁ → P f₂ → P (f₁ + f₂) := by
    rintro f₁ f₂ ⟨h₁, g₁, hh₁, e₁⟩ ⟨h₂, g₂, hh₂, e₂⟩
    refine ⟨h₁ * h₂, h₂ * g₁ + h₁ * g₂, by rw [map_mul]; exact mul_ne_zero hh₁ hh₂, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
    ring
  have hψC : ∀ a : X.ChartAlg j, ψ (Polynomial.C (Polynomial.C a)) =
      Polynomial.C (LaurentPolynomial.C (algebraMap (X.ChartAlg j) (X.ChartField j) a)) := by
    intro a
    simp [ψ, chartPolyToModel]
  have hψt : ψ (Polynomial.C Polynomial.X) = Polynomial.X := by simp [ψ, chartPolyToModel]
  have hψY : ψ Polynomial.X = Polynomial.C (LaurentPolynomial.T 1) := by
    simp [ψ, chartPolyToModel]
  have hmono : ∀ (c : X.ChartField j) (b : ℤ) (l : ℕ),
      P (Polynomial.C (LaurentPolynomial.C c * LaurentPolynomial.T b) * Polynomial.X ^ l) := by
    intro c b l
    obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := X.ChartAlg j) c
    have ha'0 : algebraMap (X.ChartAlg j) (X.ChartField j) a' ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha'
    refine ⟨Polynomial.C (Polynomial.C a') * Polynomial.X ^ b.natAbs,
      Polynomial.C (Polynomial.C a * Polynomial.X ^ l) * Polynomial.X ^ (b.natAbs + b).toNat,
      ?_, ?_⟩
    · rw [map_mul, map_pow, hψC, hψY]
      refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
      · rw [Ne, Polynomial.C_eq_zero, map_eq_zero_iff _
          (LaurentPolynomial.C : X.ChartField j →+* LaurentPolynomial (X.ChartField j)).injective]
        exact ha'0
      · rw [Ne, Polynomial.C_eq_zero]
        exact (LaurentPolynomial.isUnit_T 1).ne_zero
    · have hnb : ((b.natAbs + b).toNat : ℤ) = b.natAbs + b := Int.toNat_of_nonneg (by omega)
      set α := algebraMap (X.ChartAlg j) (X.ChartField j) a
      set α' := algebraMap (X.ChartAlg j) (X.ChartField j) a'
      have e1 : ψ (Polynomial.C (Polynomial.C a') * Polynomial.X ^ b.natAbs) =
          Polynomial.C (LaurentPolynomial.C α') * Polynomial.C (LaurentPolynomial.T b.natAbs) := by
        rw [map_mul, map_pow, hψC, hψY, ← map_pow, LaurentPolynomial.T_pow, mul_one]
      have e2 : ψ (Polynomial.C (Polynomial.C a * Polynomial.X ^ l) *
          Polynomial.X ^ (b.natAbs + b).toNat) =
          Polynomial.C (LaurentPolynomial.C α) * Polynomial.X ^ l *
            Polynomial.C (LaurentPolynomial.T (b.natAbs + b)) := by
        simp only [map_mul, map_pow, hψC, hψt, hψY]
        rw [← map_pow, LaurentPolynomial.T_pow, mul_one, hnb]
      rw [e1, e2, LaurentPolynomial.T_add]
      have hc : (Polynomial.C (LaurentPolynomial.C α) : X.ChartModel j) =
          Polynomial.C (LaurentPolynomial.C α') * Polynomial.C (LaurentPolynomial.C (α / α')) := by
        rw [← map_mul, ← map_mul, mul_div_cancel₀ _ ha'0]
      rw [hc]
      simp only [map_mul]
      ring
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ => exact hadd f₁ f₂ h₁ h₂
  | monomial l q =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    induction q using LaurentPolynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ =>
      rw [map_add, add_mul]
      exact hadd _ _ h₁ h₂
    | C_mul_T b c => exact hmono c b l

/-- **`lem:sg-cone-charts`(2)**: `Frac(A_j)[Y, Y⁻¹][t] → K` is injective, i.e. `x̄ⱼ` and `t` are
algebraically independent over `k(X) = Frac(A_j)`. -/
theorem modelToFrac_injective : Function.Injective (X.modelToFrac j) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  obtain ⟨h, g, hh, hg⟩ := exists_mul_eq_chartPolyToModel f
  have h1 : X.chartPolyToFrac j g = 0 := by
    rw [← modelToFrac_chartPolyToModel, ← hg, map_mul, hf, mul_zero]
  have hg0 : g = 0 := chartPolyToFrac_injective (h1.trans (map_zero _).symm)
  rw [hg0, map_zero] at hg
  exact (mul_eq_zero.1 hg).resolve_left hh

variable (X j) in
/-- `T → Frac(A_j)[Y, Y⁻¹][t]`, `ḡ ↦ ∑_c (g_c / x̄ⱼ^c) Y^c`. -/
def coneToModel : X.ConeRing →+* X.ChartModel j :=
  (X.chartPolyToModel j).comp (X.coneTChartPoly j : X.ConeRing →+* X.ChartPoly j)

theorem modelToFrac_coneToModel (f : X.ConeRing) :
    X.modelToFrac j (X.coneToModel j f) = algebraMap X.ConeRing (FractionRing X.ConeRing) f := by
  obtain ⟨g, rfl⟩ := coneMk_surjective (X := X) f
  rw [coneToModel, RingHom.comp_apply, modelToFrac_chartPolyToModel, RingHom.coe_coe,
    coneTChartPoly_coneMk, chartPolyToFrac_coneToChartPoly]

variable (X j) in
/-- `K` as an algebra over the chart model `Frac(A_j)[Y, Y⁻¹][t]` (through `modelToFrac`). -/
instance modelAlgebra : Algebra (X.ChartModel j) (FractionRing X.ConeRing) :=
  (X.modelToFrac j).toAlgebra

/-- **`K = Frac T` is a fraction field of the chart model** `Frac(A_j)[Y, Y⁻¹][t]`. -/
instance isFractionRing_chartModel :
    IsFractionRing (X.ChartModel j) (FractionRing X.ConeRing) := by
  have hf : FaithfulSMul (X.ChartModel j) (FractionRing X.ConeRing) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 modelToFrac_injective
  have hsurj : ∀ z : FractionRing X.ConeRing, ∃ x y : X.ChartModel j,
      z = X.modelToFrac j x / X.modelToFrac j y := by
    intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.ConeRing) z
    exact ⟨X.coneToModel j a, X.coneToModel j b, by
      rw [modelToFrac_coneToModel, modelToFrac_coneToModel]⟩
  exact @IsFractionRing.of_field (X.ChartModel j) _ (FractionRing X.ConeRing) _ _ hf hsurj

/-- **Bihomogeneous elements in the chart model** (`lem:sg-cone-charts`(1),(2)): `f ∈ K` is
bihomogeneous of bidegree `(b, λ)` iff `f = c x̄ⱼ^b t^λ` for some `c ∈ k(X) = Frac(A_j)`. -/
theorem isBihom_iff_chartModel {f : FractionRing X.ConeRing} {b : ℤ} {l : ℕ} :
    X.IsBihom f b l ↔ ∃ c : X.ChartField j, f = X.modelToFrac j
      (Polynomial.C (LaurentPolynomial.C c * LaurentPolynomial.T b) * Polynomial.X ^ l) := by
  simp_rw [modelToFrac_monomial]
  have hx := fracMk_X_ne_zero (X := X) (j := j)
  constructor
  · rintro ⟨a, a', d, d', ha, ha', ha'I, hd, rfl⟩
    have ha'0 := fracMk_ne_zero ha'I
    refine ⟨algebraMap _ _ (X.quotDehom j a) / algebraMap _ _ (X.quotDehom j a'), ?_⟩
    rw [map_div₀, chartFieldToFrac_algebraMap, chartFieldToFrac_algebraMap,
      chartAlgToFrac_quotDehom ha, chartAlgToFrac_quotDehom ha', ← hd, zpow_sub₀ hx,
      zpow_natCast, zpow_natCast]
    field_simp
  · rintro ⟨c, rfl⟩
    obtain ⟨α, α', hα', rfl⟩ := IsFractionRing.div_surjective (A := X.ChartAlg j) c
    obtain ⟨N, τ, hτ, rfl⟩ := exists_quotDehom_eq α
    obtain ⟨N', τ', hτ', rfl⟩ := exists_quotDehom_eq α'
    have hτ'I : τ' ∉ X.ideal := fun h => by
      rw [quotDehom_eq_zero_of_mem h] at hα'
      exact zero_notMem_nonZeroDivisors hα'
    have hτ'0 := fracMk_ne_zero hτ'I
    refine ⟨τ * MvPolynomial.X j ^ (N' + b.toNat), τ' * MvPolynomial.X j ^ (N + (-b).toNat),
      N + (N' + b.toNat), N' + (N + (-b).toNat), hτ.mul (MvPolynomial.isHomogeneous_X_pow _ _),
      hτ'.mul (MvPolynomial.isHomogeneous_X_pow _ _),
      fun h => (X.isPrime.mem_or_mem h).elim hτ'I fun h' => (Fact.out : MvPolynomial.X j ∉ X.ideal)
        (X.isPrime.mem_of_pow_mem _ h'), by omega, ?_⟩
    rw [map_div₀, chartFieldToFrac_algebraMap, chartFieldToFrac_algebraMap,
      chartAlgToFrac_quotDehom hτ, chartAlgToFrac_quotDehom hτ', map_mul, map_mul, map_pow,
      map_pow]
    have hb : X.fracMk (MvPolynomial.X j) ^ b =
        X.fracMk (MvPolynomial.X j) ^ b.toNat / X.fracMk (MvPolynomial.X j) ^ (-b).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hx]
      congr 1
      omega
    rw [hb]
    field_simp
    ring

/-- `x̄ᵢ = (x̄ᵢ / x̄ⱼ) x̄ⱼ` in the chart model. -/
theorem modelToFrac_quotDehom_X (i : Fin (M + 1)) :
    X.modelToFrac j (Polynomial.C (LaurentPolynomial.C
        (algebraMap _ (X.ChartField j) (X.quotDehom j (MvPolynomial.X i))) *
          LaurentPolynomial.T 1)) = X.fracMk (MvPolynomial.X i) := by
  have h := modelToFrac_monomial (X := X) (j := j)
    (algebraMap _ (X.ChartField j) (X.quotDehom j (MvPolynomial.X i))) 1 0
  rw [pow_zero, mul_one, pow_zero, mul_one, zpow_one, chartFieldToFrac_algebraMap] at h
  have h2 := chartAlgToFrac_quotDehom_mul (X := X) (j := j) (MvPolynomial.isHomogeneous_X k i)
  rw [pow_one] at h2
  rw [h, h2]

/-- `trdeg_k Frac(A_j) < ℵ₀`. -/
theorem trdeg_chartField_lt_aleph0 : Algebra.trdeg k (X.ChartField j) < Cardinal.aleph0 := by
  rw [trdeg_localization_eq (S := X.ChartField j) (nonZeroDivisors (X.ChartAlg j)) le_rfl]
  exact trdeg_lt_aleph0_of_finiteType

/-- **The dimension of `X`** is the transcendence degree of its function field `k(X) = Frac(A_j)`
(`lem:sg-cone-charts`(2): `trdeg_k Frac T = trdeg_k k(X) + 2`). -/
theorem trdeg_chartField_eq_dim : Algebra.trdeg k (X.ChartField j) = X.dim := by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 (trdeg_chartField_lt_aleph0 (X := X) (j := j))
  have h := X.trdeg_fractionRing_coneRing j
  rw [dim, h, hn]
  norm_cast

/-! ### Projective normality and the punctured cone (`lem:sg-proj-normal-sat`) -/

section ProjNormal

/-- In dimension `n ≥ 1` the chart algebra `A_j` is not a field (a field of finite type over `k` is
finite over `k`, Zariski's lemma, so its transcendence degree vanishes). -/
theorem not_isField_chartAlg (hn : 1 ≤ X.dim) : ¬ IsField (X.ChartAlg j) := by
  intro hF
  let _ := hF.toField
  have : Module.Finite k (X.ChartAlg j) := finite_of_finite_type_of_isJacobsonRing k (X.ChartAlg j)
  have : Algebra.IsAlgebraic k (X.ChartAlg j) := Algebra.IsIntegral.isAlgebraic
  have h0 : Algebra.trdeg k (X.ChartAlg j) = 0 := trdeg_eq_zero
  rw [← trdeg_localization_eq (S := X.ChartField j) (nonZeroDivisors (X.ChartAlg j)) le_rfl,
    trdeg_chartField_eq_dim] at h0
  norm_cast at h0
  omega

variable (X j) in
/-- The map `S → (A_j/𝔫)[t][Y]`, `x̄ᵢ ↦ (x̄ᵢ / x̄ⱼ mod 𝔫) Y`, for an ideal `𝔫 ⊆ A_j`; its kernel is
the homogeneous prime ideal of the cone over the point `𝔫` (proof of `lem:sg-proj-normal-sat`). -/
def coordToPointLine (𝔫 : Ideal (X.ChartAlg j)) :
    X.CoordRing →+* Polynomial (Polynomial (X.ChartAlg j ⧸ 𝔫)) :=
  (Polynomial.mapRingHom (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔫))).comp
    ((X.coneTChartPoly j : X.ConeRing →+* X.ChartPoly j).comp Polynomial.C)

omit [Fact (MvPolynomial.X j ∉ X.ideal)] in
theorem coordToPointLine_coordMk (𝔫 : Ideal (X.ChartAlg j)) (F : MvPolynomial (Fin (M + 1)) k)
    (c ℓ : ℕ) :
    ((X.coordToPointLine j 𝔫 (X.coordMk F)).coeff c).coeff ℓ =
      Ideal.Quotient.mk 𝔫 (X.quotDehom j (MvPolynomial.homogeneousComponent c
        ((Polynomial.C F : (MvPolynomial (Fin (M + 1)) k)[X]).coeff ℓ))) := by
  simp only [coordToPointLine, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [← coneMk_C, coneTChartPoly_coneMk, coeff_coeff_coneToChartPoly]

omit [Fact (MvPolynomial.X j ∉ X.ideal)] in
theorem coordToPointLine_eq_zero_iff (𝔫 : Ideal (X.ChartAlg j)) (F : MvPolynomial (Fin (M + 1)) k) :
    X.coordToPointLine j 𝔫 (X.coordMk F) = 0 ↔
      ∀ c, X.quotDehom j (MvPolynomial.homogeneousComponent c F) ∈ 𝔫 := by
  constructor
  · intro h c
    have := coordToPointLine_coordMk (X := X) (j := j) 𝔫 F c 0
    rw [h, Polynomial.coeff_zero, Polynomial.coeff_zero, Polynomial.coeff_C_zero, eq_comm,
      Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · intro h
    refine Polynomial.ext fun c => Polynomial.ext fun ℓ => ?_
    rw [coordToPointLine_coordMk, Polynomial.coeff_zero, Polynomial.coeff_zero,
      Ideal.Quotient.eq_zero_iff_mem, Polynomial.coeff_C]
    split_ifs
    · exact h c
    · rw [map_zero, map_zero]
      exact 𝔫.zero_mem

/-- The prime `𝔭 = ker(S → (A_j/𝔫)[t][Y])` attached to a nonzero maximal ideal `𝔫` of `A_j`:
`0 ≠ 𝔭 ⊆ 𝔪₊`, `x̄ⱼ ∉ 𝔭` (proof of `lem:sg-proj-normal-sat`). -/
theorem exists_prime_lt_irrelevant (hn : 1 ≤ X.dim) :
    ∃ 𝔭 : Ideal X.CoordRing, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ X.coordMk (MvPolynomial.X j) ∉ 𝔭 ∧
      𝔭 ≤ Ideal.span (Set.range fun i => X.coordMk (MvPolynomial.X i)) := by
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal (X.ChartAlg j)
  have h𝔫0 : 𝔫 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔫 (not_isField_chartAlg hn)
  have : 𝔫.IsMaximal := h𝔫
  refine ⟨RingHom.ker (X.coordToPointLine j 𝔫), RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · obtain ⟨α, hα𝔫, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔫0
    obtain ⟨N, τ, hτ, rfl⟩ := exists_quotDehom_eq α
    intro hbot
    have hmem : X.coordMk τ ∈ RingHom.ker (X.coordToPointLine j 𝔫) := by
      rw [RingHom.mem_ker, coordToPointLine_eq_zero_iff]
      intro c
      rw [MvPolynomial.homogeneousComponent_of_mem hτ]
      split_ifs
      · exact hα𝔫
      · rw [map_zero]; exact 𝔫.zero_mem
    rw [hbot, Ideal.mem_bot, coordMk_eq_zero_iff] at hmem
    exact hα0 (quotDehom_eq_zero_of_mem hmem)
  · rw [RingHom.mem_ker, coordToPointLine_eq_zero_iff]
    intro h
    have h1 := h 1
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_X k j), if_pos rfl,
      quotDehom_X_self] at h1
    exact h𝔫.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · intro f hf
    obtain ⟨F, rfl⟩ := coordMk_surjective (X := X) f
    rw [RingHom.mem_ker, coordToPointLine_eq_zero_iff] at hf
    have h0 := hf 0
    rw [MvPolynomial.homogeneousComponent_zero] at h0
    have hκ : MvPolynomial.coeff 0 F = 0 := by
      by_contra hκ
      have : X.quotDehom j (MvPolynomial.C (MvPolynomial.coeff 0 F)) ∈ 𝔫 := h0
      rw [MvPolynomial.C_eq_smul_one, map_smul, map_one, Algebra.smul_def, mul_one] at this
      exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ this ((isUnit_iff_ne_zero.2 hκ).map _))
    have hF : F ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin (M + 1)))) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra h'
      push Not at h'
      have hm0 : m = 0 := Finsupp.ext fun i => h' i (Set.mem_univ i)
      rw [hm0, MvPolynomial.mem_support_iff] at hm
      exact hm hκ
    have := Ideal.mem_map_of_mem (X.coordMk : MvPolynomial (Fin (M + 1)) k →+* X.CoordRing) hF
    rw [Ideal.map_span, ← Set.image_comp, Set.image_univ] at this
    exact this

variable (X) in
/-- **`lem:sg-proj-normal-sat` for `S`.** Let `X` be projectively normal of dimension `n ≥ 1`,
`xⱼ ∉ I` and `g ∈ S`. If `x̄ⱼ^N ∣ g x̄ᵢ^{mᵢ}` for every `i` with `xᵢ ∉ I`, then `x̄ⱼ^N ∣ g`: an
element
of `⋂ᵢ S_{x̄ᵢ}` lies in `S`. -/
theorem dvd_of_forall_dvd_mul_pow (hX : X.IsProjNormal) (hn : 1 ≤ X.dim) {N : ℕ}
    {g : X.CoordRing}
    (hg : ∀ i, MvPolynomial.X i ∉ X.ideal →
      ∃ m : ℕ, X.coordMk (MvPolynomial.X j) ^ N ∣ g * X.coordMk (MvPolynomial.X i) ^ m) :
    X.coordMk (MvPolynomial.X j) ^ N ∣ g := by
  have : IsIntegrallyClosed X.CoordRing := hX
  have hxj : X.coordMk (MvPolynomial.X j) ≠ 0 := fun h =>
    (Fact.out : MvPolynomial.X j ∉ X.ideal) (coordMk_eq_zero_iff.1 h)
  have hh : X.coordMk (MvPolynomial.X j) ^ N ≠ 0 := pow_ne_zero _ hxj
  rw [← Ideal.mem_span_singleton, mem_span_singleton_iff_forall_minimalPrimes hh]
  intro P hP
  have hPp : P.IsPrime := hP.1.1
  by_cases hall : ∀ i, MvPolynomial.X i ∉ X.ideal → X.coordMk (MvPolynomial.X i) ∈ P
  · exfalso
    obtain ⟨𝔭, h𝔭p, h𝔭0, hj𝔭, h𝔭m⟩ := exists_prime_lt_irrelevant (X := X) (j := j) hn
    have hmP : Ideal.span (Set.range fun i => X.coordMk (MvPolynomial.X i)) ≤ P := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hi : MvPolynomial.X i ∈ X.ideal
      · change X.coordMk (MvPolynomial.X i) ∈ P
        rw [coordMk_eq_zero_iff.2 hi]
        exact P.zero_mem
      · exact hall i hi
    have h𝔭P : 𝔭 ≤ P := h𝔭m.trans hmP
    have := isDiscreteValuationRing_localization_of_mem_minimalPrimes hh hP
    let R := Localization.AtPrime P
    have hdisj : Disjoint (P.primeCompl : Set X.CoordRing) 𝔭 := by
      rw [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
        Set.disjoint_compl_left_iff_subset]
      exact h𝔭P
    have h𝔭R : (𝔭.map (algebraMap X.CoordRing R)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl R 𝔭 h𝔭p hdisj
    have hinj : Function.Injective (algebraMap X.CoordRing R) :=
      IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
    have h𝔭R0 : 𝔭.map (algebraMap X.CoordRing R) ≠ ⊥ := by
      intro h0
      obtain ⟨x, hx𝔭, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭0
      have : algebraMap X.CoordRing R x ∈ 𝔭.map (algebraMap X.CoordRing R) :=
        Ideal.mem_map_of_mem _ hx𝔭
      rw [h0, Ideal.mem_bot, map_eq_zero_iff _ hinj] at this
      exact hx0 this
    have hmax : 𝔭.map (algebraMap X.CoordRing R) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (h𝔭R.isMaximal h𝔭R0)
    have h1 := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl R h𝔭p hdisj
    rw [hmax, IsLocalization.AtPrime.under_maximalIdeal R P] at h1
    exact hj𝔭 (h1 ▸ hall j Fact.out)
  · push Not at hall
    obtain ⟨i, hi, hiP⟩ := hall
    obtain ⟨m, hm⟩ := hg i hi
    refine ⟨X.coordMk (MvPolynomial.X i) ^ m, fun h => hiP (hPp.mem_of_pow_mem _ h), ?_⟩
    rw [Ideal.mem_span_singleton, mul_comm]
    exact hm

end ProjNormal

omit [Fact (MvPolynomial.X j ∉ X.ideal)] in
/-- **`lem:sg-cone-charts`(3)**: if the chart algebra `A_j` is smooth over `k`, so is
`T_{x̄ⱼ} ≅ A_j[t][Y, Y⁻¹]` (polynomial algebras, localizations and composites of smooth algebras
are smooth). -/
theorem smooth_coneAway (h : Algebra.Smooth k (QuotChartAlg X.ideal (MvPolynomial.X j) 1)) :
    Algebra.Smooth k (X.ConeAway j) := by
  have : Algebra.Smooth k (X.ChartAlg j) := h
  have : Algebra.Smooth (X.ChartAlg j) (X.ChartRing j) := {}
  have : Algebra.Smooth k (X.ChartRing j) := .comp k (X.ChartAlg j) _
  have : Algebra.Smooth (X.ChartRing j) (X.ChartPoly j) := {}
  have : Algebra.Smooth k (X.ChartPoly j) := .comp k (X.ChartRing j) _
  have : Algebra.Smooth (X.ChartPoly j) (X.ChartLaurent j) :=
    .of_isLocalization_Away (Polynomial.X : X.ChartPoly j)
  have : Algebra.Smooth k (X.ChartLaurent j) := .comp k (X.ChartPoly j) _
  exact .of_equiv (X.coneChartEquiv j)

end ChartModel

variable (X) in
/-- **`lem:sg-proj-normal-sat`.** Let `X` be projectively normal of dimension `n ≥ 1`. Then
`⋂_{xᵢ ∉ I} T_{x̄ᵢ} = T` inside `K = Frac T`: if `f ∈ K` and every `f x̄ᵢ^{mᵢ}`, `xᵢ ∉ I`, lies in
`T`, then `f ∈ T` (coefficientwise in `t` from `dvd_of_forall_dvd_mul_pow`). -/
theorem exists_eq_algebraMap_of_forall_mul_pow (hX : X.IsProjNormal) (hn : 1 ≤ X.dim)
    {f : FractionRing X.ConeRing}
    (hf : ∀ i, MvPolynomial.X i ∉ X.ideal → ∃ (a : X.ConeRing) (m : ℕ),
      f * X.fracMk (MvPolynomial.X i) ^ m = algebraMap X.ConeRing (FractionRing X.ConeRing) a) :
    ∃ a : X.ConeRing, f = algebraMap X.ConeRing (FractionRing X.ConeRing) a := by
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  have : Fact (MvPolynomial.X j ∉ X.ideal) := ⟨hj⟩
  obtain ⟨a₀, N, ha₀⟩ := hf j hj
  have hdvd : Polynomial.C (X.coordMk (MvPolynomial.X j) ^ N) ∣ a₀ := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro ℓ
    refine dvd_of_forall_dvd_mul_pow X (j := j) hX hn fun i hi => ?_
    obtain ⟨a, m, ha⟩ := hf i hi
    refine ⟨m, a.coeff ℓ, ?_⟩
    have h1 : a₀ * Polynomial.C (X.coordMk (MvPolynomial.X i) ^ m) =
        a * Polynomial.C (X.coordMk (MvPolynomial.X j) ^ N) := by
      apply IsFractionRing.injective X.ConeRing (FractionRing X.ConeRing)
      rw [map_mul, map_mul, ← ha₀, ← ha, Polynomial.C_pow, Polynomial.C_pow, map_pow, map_pow,
        ← fracMk_apply, ← fracMk_apply]
      ring
    have h2 := congrArg (fun q => Polynomial.coeff q ℓ) h1
    simp only [Polynomial.coeff_mul_C] at h2
    rw [h2, mul_comm]
  obtain ⟨a, rfl⟩ := hdvd
  refine ⟨a, ?_⟩
  have hx : X.fracMk (MvPolynomial.X j) ^ N ≠ 0 := pow_ne_zero _ fracMk_X_ne_zero
  apply mul_right_cancel₀ hx
  rw [ha₀, map_mul, mul_comm, Polynomial.C_pow, map_pow, fracMk_apply]

/-! ### The cone family `z = (t, x̄_{ι(o)})` -/

variable (X) in
/-- The family `z = (t, x̄_{ι(o)})_o` of bihomogeneous elements of `T`, indexed like the `p`-basis
`ζ = (u, Y, t)` of a chart model: `none ↦ t`, `some o ↦ x̄_{ι(o)}`. For `ι(none) = i₀` and suitable
`ι(some l) = i_l` it is the homogeneous `p`-basis `(x̄_{i₀}, …, x̄_{iₙ}, t)` of
`lem:sg-homog-pbasis`. -/
def coneZ {σ : Type*} (idx : Option σ → Fin (M + 1)) : Option (Option σ) → X.ConeRing :=
  fun o => o.elim Polynomial.X fun o' => Polynomial.C (X.coordMk (MvPolynomial.X (idx o')))

theorem coneZ_none {σ : Type*} (idx : Option σ → Fin (M + 1)) : X.coneZ idx none = Polynomial.X :=
  rfl

theorem coneZ_some {σ : Type*} (idx : Option σ → Fin (M + 1)) (o : Option σ) :
    X.coneZ idx (some o) = Polynomial.C (X.coordMk (MvPolynomial.X (idx o))) :=
  rfl

/-- The elements of `z` are bihomogeneous: `deg t = (0, 1)`, `deg x̄ᵢ = (1, 0)`. -/
theorem isBihom_coneZ {σ : Type*} (idx : Option σ → Fin (M + 1)) (o : Option (Option σ)) :
    X.IsBihom (algebraMap X.ConeRing (FractionRing X.ConeRing) (X.coneZ idx o))
      (o.elim 0 fun _ => 1) (o.elim 1 fun _ => 0) := by
  rcases o with _ | o
  · have h := isBihom_fracMk_mul (X := X) (MvPolynomial.isHomogeneous_one _ _) 1
    simpa [coneZ, fracT] using h
  · have h := isBihom_fracMk_mul (X := X) (MvPolynomial.isHomogeneous_X k (idx o)) 0
    simpa [coneZ, fracMk_apply] using h

/-- In every chart model, `z = (t, (x̄_{ι(o)} / x̄ⱼ) Y)`. -/
theorem algebraMap_comp_coneZ {σ : Type*} (idx : Option σ → Fin (M + 1)) (j : Fin (M + 1))
    [Fact (MvPolynomial.X j ∉ X.ideal)] :
    algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx =
      X.modelToFrac j ∘ Cartier.coneFamily
        (fun o => algebraMap _ (X.ChartField j) (X.quotDehom j (MvPolynomial.X (idx o)))) := by
  funext o
  rcases o with _ | o
  · simp [coneZ, Cartier.coneFamily, modelToFrac_X, fracT]
  · simp only [Function.comp_apply, coneZ, Cartier.coneFamily, Option.elim_some]
    rw [modelToFrac_quotDehom_X, fracMk_apply]

/-! ### Characteristic `p`: the homogeneous `p`-basis (`lem:sg-homog-pbasis`) -/

section CharP

open Cartier

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p]

instance charP_coordRing_of_charP : CharP X.CoordRing p :=
  charP_of_injective_ringHom (algebraMap k X.CoordRing).injective p

instance charP_chartAlg_of_charP {j : Fin (M + 1)} [Fact (MvPolynomial.X j ∉ X.ideal)] :
    CharP (X.ChartAlg j) p :=
  charP_of_injective_ringHom (algebraMap k (X.ChartAlg j)).injective p

omit hp [CharP k p] in
theorem essFiniteType_chartField (j : Fin (M + 1)) [Fact (MvPolynomial.X j ∉ X.ideal)] :
    Algebra.EssFiniteType k (X.ChartField j) := by
  have : Algebra.EssFiniteType (X.ChartAlg j) (X.ChartField j) :=
    .of_isLocalization _ (nonZeroDivisors _)
  exact .comp k (X.ChartAlg j) _

/-- **`lem:sg-homog-pbasis`(1), the field part**: `k(X) = Frac(A_j)` has a `p`-basis
`w = (x̄_{i₁}/x̄ⱼ, …, x̄_{iₙ}/x̄ⱼ)` of `n = dim X` elements chosen among the field generators
`x̄ᵢ / x̄ⱼ` (`lem:sg-field-pbasis`). -/
theorem exists_isPBasis_chartField [PerfectRing k p] (j : Fin (M + 1))
    [Fact (MvPolynomial.X j ∉ X.ideal)] :
    ∃ idx : Fin X.dim → Fin (M + 1), IsPBasis p
      (fun l => algebraMap (X.ChartAlg j) (X.ChartField j)
        (X.quotDehom j (MvPolynomial.X (idx l)))) := by
  have := essFiniteType_chartField (X := X) j
  set φ : MvPolynomial (Fin (M + 1)) k →ₐ[k] X.ChartField j :=
    (IsScalarTower.toAlgHom k (X.ChartAlg j) (X.ChartField j)).comp (X.quotDehom j) with hφ
  have hS : IntermediateField.adjoin k (Set.range (φ ∘ MvPolynomial.X)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    have hA : ∀ a : X.ChartAlg j, algebraMap _ (X.ChartField j) a ∈
        IntermediateField.adjoin k (Set.range (φ ∘ MvPolynomial.X)) := by
      intro a
      obtain ⟨τ, rfl⟩ := quotDehom_surjective (X := X) (j := j) a
      have h1 : φ τ ∈ Algebra.adjoin k (Set.range (φ ∘ MvPolynomial.X)) := by
        rw [Algebra.adjoin_range_eq_range_aeval, ← MvPolynomial.aeval_unique φ]
        exact ⟨τ, rfl⟩
      exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.ChartAlg j) c
    exact IntermediateField.div_mem _ (hA a) (hA b)
  obtain ⟨w, hwS, hw⟩ := exists_isPBasis_of_adjoin_eq_top_of_trdeg (p := p) k (X.ChartField j)
    (trdeg_chartField_eq_dim (X := X) (j := j)) _ hS
  choose idx hidx using hwS
  refine ⟨idx, ?_⟩
  have e : (fun l => algebraMap (X.ChartAlg j) (X.ChartField j)
      (X.quotDehom j (MvPolynomial.X (idx l)))) = w := funext fun l => hidx l
  rw [e]
  exact hw

/-- `ζ = (w, x̄ⱼ, t)` is a `p`-basis of `K = Frac T` for a `p`-basis `w` of `k(X) = Frac(A_j)`
(`lem:sg-homog-pbasis`(1), `lem:sg-pbasis-basics`(2),(4)). -/
theorem isPBasis_modelToFrac_laurentFamily (j : Fin (M + 1)) [Fact (MvPolynomial.X j ∉ X.ideal)]
    {σ : Type*} [Fintype σ] [DecidableEq σ] {w : σ → X.ChartField j} (hw : IsPBasis p w) :
    IsPBasis p (X.modelToFrac j ∘ fun o : Option (Option σ) => o.elim Polynomial.X fun o' =>
      Polynomial.C (o'.elim (LaurentPolynomial.T 1) fun i => LaurentPolynomial.C (w i))) := by
  exact hw.isPBasis_algebraMap_laurentFamily

/-- **`lem:sg-homog-pbasis`(1)**: for `xᵢ₀ ∉ I` there are `i₁, …, iₙ` (`n = dim X`) such that
`z = (x̄ᵢ₀, x̄ᵢ₁, …, x̄ᵢₙ, t)` (`X.coneZ idx`, `idx none = i₀`) is a `p`-basis of `K = Frac T`. -/
theorem exists_isPBasis_coneZ [PerfectRing k p] (i₀ : Fin (M + 1))
    (hi₀ : MvPolynomial.X i₀ ∉ X.ideal) :
    ∃ idx : Option (Fin X.dim) → Fin (M + 1), idx none = i₀ ∧
      IsPBasis p (algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx) := by
  have : Fact (MvPolynomial.X i₀ ∉ X.ideal) := ⟨hi₀⟩
  obtain ⟨idx', hu⟩ := exists_isPBasis_chartField (X := X) p i₀
  set idx : Option (Fin X.dim) → Fin (M + 1) := fun o => o.elim i₀ idx' with hidx
  set g : Option (Fin X.dim) → X.ChartField i₀ :=
    fun o => algebraMap _ (X.ChartField i₀) (X.quotDehom i₀ (MvPolynomial.X (idx o))) with hg
  have hdet : (coneJacMatrix hu g).det = 1 := by
    have hg0 : g none = 1 := by simp [hg, hidx, quotDehom_X_self]
    rw [det_option_of_row_none_eq_zero _ (fun m => by
      simp only [coneJacMatrix, Matrix.of_apply, Option.elim_some, hg0,
        Derivation.map_one_eq_zero])]
    have h2 : (Matrix.of fun l m => coneJacMatrix hu g (some l) (some m)) = 1 := by
      ext l m
      simp only [coneJacMatrix, Matrix.of_apply, Option.elim_some, Matrix.one_apply]
      exact (hu.pderiv_self m l).trans (by simp [eq_comm])
    simp only [coneJacMatrix, Matrix.of_apply, Option.elim_none, hg0] at h2 ⊢
    rw [h2, Matrix.det_one, mul_one]
  refine ⟨idx, rfl, ?_⟩
  have h := hu.isPBasis_algebraMap_coneFamily (K := FractionRing X.ConeRing) g
    (by rw [hdet]; exact one_ne_zero)
  rw [algebraMap_comp_coneZ (X := X) idx i₀]
  exact h

/-- **`lem:sg-homog-pbasis`(2)**: if `z = X.coneZ ι` is a `p`-basis of `K` (with `n = dim X`) and
`f ∈ K` is bihomogeneous of bidegree `(b, λ)`, then `Φ^e_z(f)` is `0` or bihomogeneous of bidegree
`(b', λ')` with `Q b' = b - (n + 1)(Q - 1)` and `Q λ' = λ - (Q - 1)`, `Q = p^e`. -/
theorem IsBihom.traceIter_coneZ [PerfectRing k p] {idx : Option (Fin X.dim) → Fin (M + 1)}
    (hz : IsPBasis p (algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx)) (e : ℕ)
    {f : FractionRing X.ConeRing} {b : ℤ} {l : ℕ} (hf : X.IsBihom f b l) :
    hz.traceIter e f = 0 ∨ ∃ (b' : ℤ) (l' : ℕ),
      (p : ℤ) ^ e * b' + (X.dim + 1) * ((p : ℤ) ^ e - 1) = b ∧ p ^ e * l' + (p ^ e - 1) = l ∧
        X.IsBihom (hz.traceIter e f) b' l' := by
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  have : Fact (MvPolynomial.X j ∉ X.ideal) := ⟨hj⟩
  obtain ⟨idx', hu⟩ := exists_isPBasis_chartField (X := X) p j
  set g : Option (Fin X.dim) → X.ChartField j :=
    fun o => algebraMap _ (X.ChartField j) (X.quotDehom j (MvPolynomial.X (idx o))) with hg
  have hfam : algebraMap X.ConeRing (FractionRing X.ConeRing) ∘ X.coneZ idx =
      X.modelToFrac j ∘ coneFamily g :=
    algebraMap_comp_coneZ (X := X) idx j
  have hd : (coneJacMatrix hu g).det ≠ 0 := by
    intro h0
    have hz' : IsPBasis p (X.modelToFrac j ∘ coneFamily g) := hfam ▸ hz
    have hζ := hu.isPBasis_algebraMap_laurentFamily (K := FractionRing X.ConeRing)
    have hu' := IsPBasis.isUnit_jac hζ hz'
    have e : hζ.jac (X.modelToFrac j ∘ coneFamily g) =
        X.modelToFrac j (Polynomial.C (LaurentPolynomial.C (coneJacMatrix hu g).det *
          LaurentPolynomial.T (Fintype.card (Fin X.dim) : ℤ))) :=
      hu.jac_algebraMap_coneFamily g
    rw [e, h0] at hu'
    simp at hu'
  rw [hz.traceIter_congr (hu.isPBasis_algebraMap_coneFamily g hd) hfam]
  obtain ⟨c, rfl⟩ := (isBihom_iff_chartModel (X := X) (j := j)).1 hf
  rcases hu.exists_traceIter_algebraMap_coneFamily_eq (K := FractionRing X.ConeRing) g hd e c b l
    with h | ⟨c', b', l', hb, hl, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨b', l', by simpa using hb, hl, ?_⟩
    have h' : (hu.isPBasis_algebraMap_coneFamily (K := FractionRing X.ConeRing) g hd).traceIter e
        (X.modelToFrac j (Polynomial.C (LaurentPolynomial.C c * LaurentPolynomial.T b) *
          Polynomial.X ^ l)) = X.modelToFrac j
            (Polynomial.C (LaurentPolynomial.C c' * LaurentPolynomial.T b') * Polynomial.X ^ l') :=
      h
    rw [h']
    exact (isBihom_iff_chartModel (X := X) (j := j)).2 ⟨c', rfl⟩

end CharP

end ProjSubvariety

end EnvelopeProperty
