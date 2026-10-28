/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BridgePSH
import EnvelopeProperty.Projective.SmoothEPCharZeroImport

/-!
# The envelope property of smooth models (FHX Theorem 3.1 on models)

This file implements the blueprint nodes `thm:gl-smooth-ep` and `cor:gl-smooth-ep-nef`
(`global.tex`, subsection `subsec:gl-model`) and `cor:sg-smooth-model` (`smooth-general.tex`) for
the formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX, revision `832e086`), Theorem 3.1 (`thm:smooth-EP`): *every nef class of a smooth projective
variety has the envelope property*, in the model of `sec:global` (smooth models,
`MultiModel.IsSmooth`, `def:gl-smooth`) and for the classes `θ ∈ ℝ^r_{≥0}`.

## Main results

* `MultiModel.hasEnvelopeProperty_of_isSmooth` (**`thm:gl-smooth-ep` = `cor:sg-smooth-model`**):
  for `k` algebraically closed and a smooth model `𝒳` of rank `1`, every `t ≥ 0` has the envelope
  property; unconditional in characteristic `p > 0`, and resting on the imported
  `SmoothEnvelopeCharZero k` (`thm:import-sg-ep-char0`) in characteristic `0`, through the
  hypothesis `h₀ : ∀ [CharZero k], SmoothEnvelopeCharZero k` of
  `ProjSubvariety.hasEnvelopeProperty_of_smooth` (`thm:sg-ep`, lanes SG7/SG9).
* `MultiModel.hasEnvelopeProperty_of_isSmooth_of_nonneg` (**`cor:gl-smooth-ep-nef`**): for a
  smooth model of rank `r ≥ 1`, every `θ ∈ ℝ^r_{≥0}` has the envelope property.

## The proof of `cor:sg-smooth-model`

(a) `𝒳 ↦ 𝒳^ν` (`MultiModel.normalization`): `EP_𝒳(t) ↔ EP_{𝒳^ν}(t)`
(`hasEnvelopeProperty_normalization_iff`), and `𝒳^ν` has the same chart algebras
(`MultiModel.chartAlg_normalization`), so it is smooth (`MultiModel.IsSmooth.normalization`).
`S_0 = k` (`MultiModel.exists_algebraMap_eq_of_mem_piece_zero`).

(b) Some Veronese model `𝒳^ν_(e)` is generated in degree `1`
(`MultiModel.exists_degOnePres_veronese`, from `lem:wu-veronese`, `exists_veronese_generated`,
transported along `K[U] ≅ K[X]`, `MultiModel.finOnePolyEquiv`), and it is normal
(`isNormal_veronese`); a presentation `w_0, …, w_N` gives a projectively normal
`V(I) ⊆ ℙ^N` (`DegOnePres.isProjNormal_toProjSubvariety_iff`) with
`EP_{V(I)}(t') ↔ EP_{𝒳^ν_(e)}(t')` for `t' ≥ 0` (`lem:gl-bridge-psh`(1),
`EnvelopeProperty.Global.BridgePSH`) and `EP_{𝒳^ν_(e)}(t') ↔ EP_{𝒳^ν}(e t')` (`lem:gl-veronese`).

(c) `V(I)` has smooth charts (`DegOnePres.hasSmoothCharts_of_isSmooth`). Its chart at `x_i`
is `S_{(w_i)} = {g / w_i^n : g ∈ S_{n e}}` (`MultiModel.homLocAlg`,
`DegOnePres.chartAlg_recoord_eq`, `DegOnePres.quotChartAlgEquiv`). The elements `z_j^e / w_i`
generate its unit ideal (`DegOnePres.span_chartDen_div_eq_top`: no point of its analytification
is a common zero, since every point of `𝒳^ν_(e)^an ≅ 𝒳^{ν,an}` has some `|z_j| = 1`), and the
localization of `S_{(w_i)}` at `z_j^e / w_i` is `S_{(w_i z_j^e)}`, the localization of the
smooth chart `A_j = S_{(z_j^e)}` at `w_i / z_j^e` (`MultiModel.homLocAlg_mul_localization`,
`MultiModel.chartAlg_eq_homLocAlg`). Smoothness is local on such a cover
(`MultiModel.smooth_homLocAlg_of_span`, Mathlib's `RingHom.Smooth.ofLocalizationSpanTarget`).

(d) `thm:sg-ep` (`ProjSubvariety.hasEnvelopeProperty_of_smooth`) gives `EP_{V(I)}(t / e)`.

## Deviations from the blueprint

* (c) covers `S_{(w_i)}` by the localizations at `z_j^e / w_i` (charts `j` of `𝒳`) instead of
  the `z^β / w_i`, `β ∈ Mon(e)`; the unit ideal property is proved with points
  (`Berk.span_eq_top_of_forall_exists_val_ne_zero`) instead of the integral equation of `w_i`
  over `k[z]`, and the localization is identified in one step with a localization of `A_j`.
* `cor:gl-smooth-ep-nef` (`MultiModel.IsSmooth.veronese`): the chart of `𝒳_(a)` at `z̃^β` is
  covered by its localizations at the `z̃_j^a / z̃^β` (all charts `j`), instead of being
  identified with a single localization of a chart `A_j` with `j` in the support of `β`; it is
  integrally closed because it coincides with the corresponding chart of the normal model
  `𝒳^ν_(a)` (`MultiModel.homLocAlg_normalization_eq`, by patching along the same cover).
-/

open scoped NNReal ENNReal Topology

open Topology Filter MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Localizations inside a field -/

section SubalgebraLocalization

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]

/-- If `R ≤ L` are `k`-subalgebras of a field, `s ∈ R` is nonzero with `s⁻¹ ∈ L`, and every
element of `L` lies in `R` after multiplication by a power of `s`, then `L = R[s⁻¹]` is the
localization of `R` away from `s` (for the inclusion `R → L`). -/
theorem subalgebra_isLocalizationAway_of_inv_mem {R L : Subalgebra k K} (hRL : R ≤ L) (s : R)
    (hs : (s : K) ≠ 0) (hinv : (s : K)⁻¹ ∈ L) (hsurj : ∀ x ∈ L, ∃ n : ℕ, x * (s : K) ^ n ∈ R) :
    letI := (Subalgebra.inclusion hRL).toRingHom.toAlgebra
    IsLocalization.Away s L := by
  let := (Subalgebra.inclusion hRL).toRingHom.toAlgebra
  show IsLocalization (Submonoid.powers s) L
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩)
    exact mul_inv_cancel₀ hs
  · intro z
    obtain ⟨n, hn⟩ := hsurj z.1 z.2
    exact ⟨(⟨_, hn⟩, ⟨s ^ n, n, rfl⟩), Subtype.ext rfl⟩
  · intro x y hxy
    exact ⟨1, by rw [Subalgebra.inclusion_injective hRL hxy]⟩

/-- **Smoothness of `R[s⁻¹]`**: in the situation of `subalgebra_isLocalizationAway_of_inv_mem`,
if `R` is a smooth `k`-algebra, so is `L`. -/
theorem subalgebra_smooth_of_inv_mem {R L : Subalgebra k K} (hRL : R ≤ L) (s : R)
    (hs : (s : K) ≠ 0) (hinv : (s : K)⁻¹ ∈ L) (hsurj : ∀ x ∈ L, ∃ n : ℕ, x * (s : K) ^ n ∈ R)
    [Algebra.Smooth k R] : Algebra.Smooth k L := by
  let := (Subalgebra.inclusion hRL).toRingHom.toAlgebra
  have := subalgebra_isLocalizationAway_of_inv_mem hRL s hs hinv hsurj
  have : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Smooth R L := Algebra.Smooth.of_isLocalization_Away s
  exact Algebra.Smooth.comp k R L

/-- In the situation of `subalgebra_isLocalizationAway_of_inv_mem`, `Localization.Away s ≅ L`, so
`Localization.Away s` is smooth over `k` if `L` is. -/
theorem subalgebra_smooth_localizationAway_of_inv_mem {R L : Subalgebra k K} (hRL : R ≤ L) (s : R)
    (hs : (s : K) ≠ 0) (hinv : (s : K)⁻¹ ∈ L) (hsurj : ∀ x ∈ L, ∃ n : ℕ, x * (s : K) ^ n ∈ R)
    [Algebra.Smooth k L] : Algebra.Smooth k (Localization.Away s) := by
  let := (Subalgebra.inclusion hRL).toRingHom.toAlgebra
  have := subalgebra_isLocalizationAway_of_inv_mem hRL s hs hinv hsurj
  have : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers s) L (Localization.Away s)).restrictScalars k)

/-- **Patching** along a cover by principal open sets: if `s_i ∈ R` generate the unit ideal of a
`k`-subalgebra `R` of a field and `x s_i^{n_i} ∈ R` for every `i`, then `x ∈ R`. -/
theorem subalgebra_mem_of_span_eq_top {R : Subalgebra k K} {ι : Type*} [Fintype ι] {s : ι → R}
    (hspan : Ideal.span (Set.range s) = ⊤) {x : K} (hx : ∀ i, ∃ n : ℕ, x * (s i : K) ^ n ∈ R) :
    x ∈ R := by
  classical
  choose n hn using hx
  set M := Finset.univ.sup n
  have hM : ∀ i, x * (s i : K) ^ M ∈ R := fun i => by
    have hle : n i ≤ M := Finset.le_sup (Finset.mem_univ i)
    rw [← Nat.add_sub_cancel' hle, pow_add, ← mul_assoc]
    exact R.mul_mem (hn i) (R.pow_mem (s i).2 _)
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => s i ^ M) := by
    rw [show (Set.range fun i => s i ^ M) = (fun y : R => y ^ M) '' Set.range s from
      (Set.range_comp (fun y : R => y ^ M) s), Ideal.span_pow_eq_top _ hspan]
    trivial
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  have e : x = ∑ i, (c i : K) * (x * (s i : K) ^ M) := by
    have h2 := congrArg (fun y : R => (y : K)) hc
    push_cast at h2
    calc x = x * ∑ i, (c i : K) * (s i : K) ^ M := by rw [h2, mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact R.sum_mem fun i _ => R.mul_mem (c i).2 (hM i)

end SubalgebraLocalization

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

/-! ### Degree-zero localizations of `S` -/

section HomLoc

variable (X : MultiModel k K r)

/-- The **degree-zero localization** `S_{(h)} = {g / h^n : n ∈ ℕ, g ∈ S_{n a}} ⊆ K` of `S` at a
homogeneous element `h T^a` (the coordinate ring of the affine open set `D_+(h T^a)`). -/
def homLocAlg (h : K) (a : Fin r →₀ ℕ) : Subalgebra k K :=
  Algebra.adjoin k {x | ∃ (n : ℕ) (g : K), g ∈ X.piece (n • a) ∧ x = g / h ^ n}

variable {X} {h h' g : K} {a : Fin r →₀ ℕ}

/-- `g / h^n ∈ S_{(h)}` for `g ∈ S_{n a}`. -/
theorem div_pow_mem_homLocAlg {n : ℕ} (hg : g ∈ X.piece (n • a)) :
    g / h ^ n ∈ X.homLocAlg h a :=
  Algebra.subset_adjoin ⟨n, g, hg, rfl⟩

/-- `g / h ∈ S_{(h)}` for `g ∈ S_a`. -/
theorem div_mem_homLocAlg (hg : g ∈ X.piece a) : g / h ∈ X.homLocAlg h a := by
  have := div_pow_mem_homLocAlg (X := X) (h := h) (n := 1) (by rwa [one_smul])
  rwa [pow_one] at this

/-- For `0 ≠ h ∈ S_a`, the elements of `S_{(h)}` are the fractions `g / h^n`, `g ∈ S_{n a}`. -/
theorem mem_homLocAlg_iff (hh : h ∈ X.piece a) (h0 : h ≠ 0) {x : K} :
    x ∈ X.homLocAlg h a ↔ ∃ (n : ℕ) (g : K), g ∈ X.piece (n • a) ∧ x = g / h ^ n := by
  refine ⟨fun hx => ?_, fun ⟨n, g, hg, hx⟩ => hx ▸ div_pow_mem_homLocAlg hg⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap c =>
    exact ⟨0, algebraMap k K c, by rw [zero_smul]; exact X.algebraMap_mem_piece_zero c,
      by rw [pow_zero, div_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, g, hg, rfl⟩ := hx
    obtain ⟨m, g', hg', rfl⟩ := hy
    refine ⟨n + m, g * h ^ m + g' * h ^ n, Submodule.add_mem _ ?_ ?_, ?_⟩
    · rw [add_nsmul]; exact mul_mem_piece hg (pow_mem_piece hh m)
    · rw [add_nsmul, add_comm (n • a)]; exact mul_mem_piece hg' (pow_mem_piece hh n)
    · rw [div_add_div _ _ (pow_ne_zero n h0) (pow_ne_zero m h0), pow_add]
      ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, g, hg, rfl⟩ := hx
    obtain ⟨m, g', hg', rfl⟩ := hy
    refine ⟨n + m, g * g', ?_, by rw [pow_add, mul_div_mul_comm]⟩
    rw [add_nsmul]; exact mul_mem_piece hg hg'

/-- `z̃_j^{n a} = (z̃_j^a)^n`. -/
theorem chartDen_nsmul (j : X.ChartIndex) (n : ℕ) (a : Fin r →₀ ℕ) :
    X.chartDen j (n • a) = X.chartDen j a ^ n := by
  induction n with
  | zero => rw [zero_smul, chartDen_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, chartDen_add, ih, pow_succ]

/-- **Charts as degree-zero localizations**: for a positive `a ∈ ℕ^r`, the chart algebra `A_j` is
`S_{(z̃_j^a)}`. -/
theorem chartAlg_eq_homLocAlg {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (ha : ∀ c, 0 < a c) : X.chartAlg j = X.homLocAlg (X.chartDen j a) a := by
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨b, f, hf, rfl⟩ := (mem_chartAlg_iff hj).1 hx
    set n := ∑ c, b c
    have hle : b ≤ n • a := le_sum_nsmul ha b
    have hmem : f * X.chartDen j (n • a - b) ∈ X.piece (n • a) := by
      have := mul_mem_piece hf (X.chartDen_mem_piece j (n • a - b))
      rwa [add_tsub_cancel_of_le hle] at this
    have e : f / X.chartDen j b = f * X.chartDen j (n • a - b) / X.chartDen j a ^ n := by
      rw [← chartDen_nsmul, ← add_tsub_cancel_of_le hle, chartDen_add, add_tsub_cancel_left,
        mul_div_mul_right _ _ (chartDen_ne_zero hj _)]
    rw [e]
    exact div_pow_mem_homLocAlg hmem
  · rintro _ ⟨n, g, hg, rfl⟩
    rw [← chartDen_nsmul]
    exact div_chartDen_mem_chartAlg hg

/-- `S_{(h)} ⊆ S_{(h h')}`: `g / h^n = g h'^n / (h h')^n`. -/
theorem homLocAlg_le_mul (hh' : h' ∈ X.piece a) (h0' : h' ≠ 0) :
    X.homLocAlg h a ≤ X.homLocAlg (h * h') (a + a) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨n, g, hg, rfl⟩
  have e : g / h ^ n = g * h' ^ n / (h * h') ^ n := by
    rw [mul_pow, mul_div_mul_right _ _ (pow_ne_zero n h0')]
  rw [e]
  refine div_pow_mem_homLocAlg ?_
  rw [nsmul_add]
  exact mul_mem_piece hg (pow_mem_piece hh' n)

/-- **`S_{(h h')} = S_{(h)}[(h' / h)⁻¹]`** for nonzero `h, h' ∈ S_a`: the hypotheses of
`subalgebra_isLocalizationAway_of_inv_mem`. -/
theorem homLocAlg_mul_localization (hh : h ∈ X.piece a) (h0 : h ≠ 0) (hh' : h' ∈ X.piece a)
    (h0' : h' ≠ 0) :
    ((h' / h)⁻¹ ∈ X.homLocAlg (h * h') (a + a)) ∧
      ∀ x ∈ X.homLocAlg (h * h') (a + a), ∃ n : ℕ, x * (h' / h) ^ n ∈ X.homLocAlg h a := by
  have hhh' : h * h' ∈ X.piece (a + a) := mul_mem_piece hh hh'
  refine ⟨?_, fun x hx => ?_⟩
  · have e : (h' / h)⁻¹ = h * h / (h * h') ^ 1 := by
      rw [inv_div, pow_one, mul_div_mul_left _ _ h0]
    rw [e]
    exact div_pow_mem_homLocAlg (by rw [one_smul]; exact mul_mem_piece hh hh)
  · obtain ⟨n, g, hg, rfl⟩ := (mem_homLocAlg_iff hhh' (mul_ne_zero h0 h0')).1 hx
    refine ⟨n, ?_⟩
    have e : g / (h * h') ^ n * (h' / h) ^ n = g / h ^ (n + n) := by
      rw [div_pow, mul_pow, pow_add, div_mul_div_comm,
        show h ^ n * h' ^ n * h ^ n = h ^ n * h ^ n * h' ^ n by ring,
        mul_div_mul_right _ _ (pow_ne_zero _ h0')]
    rw [e]
    refine div_pow_mem_homLocAlg ?_
    rwa [add_nsmul, ← nsmul_add]

/-- **Smoothness is local on a cover by degree-zero localizations.** Let `h, g_i ∈ S_a` be nonzero
with `S_{(g_i)}` smooth over `k`, and suppose that the `g_i / h` generate the unit ideal of
`S_{(h)}`. Then `S_{(h)}` is smooth over `k`: its localization at `g_i / h` is
`S_{(h g_i)} = S_{(g_i)}[(h / g_i)⁻¹]`. -/
theorem smooth_homLocAlg_of_span (hh : h ∈ X.piece a) (h0 : h ≠ 0) {ι : Type*} {g : ι → K}
    (hg : ∀ i, g i ∈ X.piece a) (hg0 : ∀ i, g i ≠ 0)
    (hsm : ∀ i, Algebra.Smooth k (X.homLocAlg (g i) a))
    (hspan : Ideal.span (Set.range fun i =>
      (⟨g i / h, div_mem_homLocAlg (hg i)⟩ : X.homLocAlg h a)) = ⊤) :
    Algebra.Smooth k (X.homLocAlg h a) := by
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.Smooth.ofLocalizationSpanTarget (algebraMap k (X.homLocAlg h a)) _ hspan ?_
  rintro ⟨_, i, rfl⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.smooth_algebraMap]
  have hL : Algebra.Smooth k (X.homLocAlg (h * g i) (a + a)) := by
    have := hsm i
    obtain ⟨hinv, hsurj⟩ := homLocAlg_mul_localization (hg i) (hg0 i) hh h0
    have h1 := subalgebra_smooth_of_inv_mem (homLocAlg_le_mul hh h0)
      ⟨h / g i, div_mem_homLocAlg hh⟩ (div_ne_zero h0 (hg0 i)) hinv hsurj
    rw [mul_comm]
    exact h1
  obtain ⟨hinv, hsurj⟩ := homLocAlg_mul_localization hh h0 (hg i) (hg0 i)
  exact subalgebra_smooth_localizationAway_of_inv_mem (homLocAlg_le_mul (hg i) (hg0 i))
    ⟨g i / h, div_mem_homLocAlg (hg i)⟩ (div_ne_zero (hg0 i) h0) hinv hsurj

end HomLoc

/-! ### The normalization of a smooth model -/

section Normalization

variable [Infinite k] [PerfectField k] {X : MultiModel k K r}

/-- **Charts of the normalization** (`cor:sg-smooth-model`(a)): if `A_j` is integrally closed, the
chart algebra of `𝒳^ν` at `j` is `A_j`; it contains `A_j`, is integral over it (the
dehomogenization of an integral equation over `S`) and lies in `K = Frac A_j`. -/
theorem chartAlg_normalization {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (hX : IsIntegrallyClosed (X.chartAlg j)) : X.normalization.chartAlg j = X.chartAlg j := by
  refine le_antisymm (fun y hy => ?_) (Subalgebra.map_mono X.le_normalization_S)
  obtain ⟨p, hp, rfl⟩ := Subalgebra.mem_map.1 hy
  have hint : IsIntegral X.S p := mem_normalization_S.1 hp
  let δ : X.S →+* X.chartAlg j :=
    ((X.dehom j).comp X.S.val).toRingHom.codRestrict _ fun p => Subalgebra.mem_map.2 ⟨p.1, p.2, rfl⟩
  have h1 : IsIntegral (X.chartAlg j) (X.dehom j p) :=
    IsIntegral.map_of_comp_eq δ (X.dehom j).toRingHom (RingHom.ext fun _ => rfl) hint
  have := isFractionRing_chartAlg hj
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  change X.dehom j p ∈ X.chartAlg j
  rw [← hz]
  exact z.2

/-- **The normalization of a smooth model is smooth**, with the same chart algebras. -/
theorem IsSmooth.normalization (hX : X.IsSmooth) : X.normalization.IsSmooth := fun j hj => by
  have hj' : ∀ c, X.coord c (j c) ≠ 0 := hj
  have e := chartAlg_normalization hj' (hX.isIntegrallyClosed hj')
  have := hX.smooth hj'
  exact ⟨Algebra.Smooth.of_equiv (Subalgebra.equivOfEq _ _ e.symm),
    isIntegrallyClosed_chartAlg hj X.isNormal_normalization⟩

end Normalization

/-! ### Charts of Segre–Veronese models and of presentations -/

section Veronese

variable [NeZero r] {Y : MultiModel k K r} {a : Fin r →₀ ℕ} (ha : ∀ c, 0 < a c)

/-- Degree-zero localizations of `𝒳_(a)` in degree `1` are those of `𝒳` in degree `a`. -/
theorem homLocAlg_veronese (g : K) :
    (Y.veronese ha).homLocAlg g (Finsupp.single 0 1) = Y.homLocAlg g a := by
  unfold homLocAlg
  congr 1
  ext x
  refine exists_congr fun n => exists_congr fun f => and_congr_left' ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one, Y.mem_veronese_piece_iff ha]

/-- `z̃_j^a ∈ S_(a)` lies in degree `1`. -/
theorem chartDen_mem_veronese_piece (j : Y.ChartIndex) :
    Y.chartDen j a ∈ (Y.veronese ha).piece (Finsupp.single 0 1) := by
  rw [Y.mem_veronese_piece_iff ha, one_smul]
  exact Y.chartDen_mem_piece j a

/-- Every point of `𝒳_(a)^an` has `|z̃_j^a U| = 1` for some chart `j` of `𝒳` with all
`f^{(c)}_{j_c} ≠ 0` (`lem:gl-charts`(3) through `𝒳_(a)^an ≅ 𝒳^an`). -/
theorem exists_val_chartDen_veronese_eq_one (v : (Y.veronese ha).an) :
    ∃ j : Y.ChartIndex, ∃ _ : ∀ c, Y.coord c (j c) ≠ 0,
      v.1.val ((Y.veronese ha).ofPiece (chartDen_mem_veronese_piece ha j)) = 1 := by
  set v₂ := (Y.veroneseHomeomorph ha).symm v
  obtain ⟨j, hj, hv⟩ := Y.exists_chartIndex v₂
  refine ⟨j, hj, ?_⟩
  have e : v = Y.veroneseAnMap ha v₂ := by
    rw [← veroneseHomeomorph_apply, Homeomorph.apply_symm_apply]
  rw [e, veroneseAnMap_val_ofPiece]
  have e2 : Y.ofPiece ((Y.mem_veronese_piece_iff' ha).1 (chartDen_mem_veronese_piece ha j)) =
      Y.chartMono j a :=
    Y.ofPiece_congr _ _ (by rw [Finsupp.single_eq_same, one_smul]) rfl
  rw [e2, val_chartMono]
  exact Finset.prod_eq_one fun c _ => by rw [hv c, one_pow]

/-- **Charts of the Segre–Veronese model**: `A_β(𝒳_(a)) = S_{(z̃^β)}` (degree `a`). -/
theorem chartAlg_veronese_eq {β : (Y.veronese ha).ChartIndex}
    (hβ : ∀ c, (Y.veronese ha).coord c (β c) ≠ 0) :
    (Y.veronese ha).chartAlg β =
      Y.homLocAlg ((Y.veronese ha).chartDen β (Finsupp.single 0 1)) a := by
  rw [chartAlg_eq_homLocAlg hβ (a := Finsupp.single 0 1) fun c => by
    obtain rfl := Fin.fin_one_eq_zero c; simp, homLocAlg_veronese]

/-- The elements `z̃_j^a / z̃^β` (charts `j` of `𝒳`) generate the unit ideal of the chart algebra
`S_{(z̃^β)}` of `𝒳_(a)`: no point of its analytification is a common zero. -/
theorem span_chartDen_div_veronese_eq_top {β : (Y.veronese ha).ChartIndex}
    (hβ : ∀ c, (Y.veronese ha).coord c (β c) ≠ 0) :
    Ideal.span (Set.range fun j : {j : Y.ChartIndex // ∀ c, Y.coord c (j c) ≠ 0} =>
      (⟨Y.chartDen j.1 a / (Y.veronese ha).chartDen β (Finsupp.single 0 1),
        div_mem_homLocAlg (Y.chartDen_mem_piece j.1 a)⟩ :
          Y.homLocAlg ((Y.veronese ha).chartDen β (Finsupp.single 0 1)) a)) = ⊤ := by
  have e := chartAlg_veronese_eq ha hβ
  apply Berk.span_eq_top_of_forall_exists_val_ne_zero (k := k)
  intro y
  set y' : Berk k ((Y.veronese ha).chartAlg β) := Berk.comap (Subalgebra.equivOfEq _ _ e).toAlgHom y
  obtain ⟨j, hj, hv⟩ := exists_val_chartDen_veronese_eq_one ha ((Y.veronese ha).chartInv β hβ y')
  refine ⟨_, ⟨⟨j, hj⟩, rfl⟩, fun h0 => ?_⟩
  have h1 := (Y.veronese ha).chartInv_val_ofPiece hβ y' (chartDen_mem_veronese_piece ha j)
  rw [hv] at h1
  have h2 : y'.val ⟨Y.chartDen j a / (Y.veronese ha).chartDen β (Finsupp.single 0 1),
      div_chartDen_mem_chartAlg (chartDen_mem_veronese_piece ha j)⟩ = 0 := h0
  rw [h2, zero_div] at h1
  exact one_ne_zero h1

omit [NeZero r] in
include ha in
/-- The degree-zero localizations of `𝒳` and of its normalization coincide on a cover: if the
charts `A_j` of `𝒳` are integrally closed and the `z̃_j^a / h` generate the unit ideal of
`S_{(h)}`, then `S^ν_{(h)} = S_{(h)}` (an element `g / h^n` of `S^ν_{(h)}` becomes an element of
`S_{(h)}` after multiplication by a power of each `z̃_j^a / h`, since `A_j(𝒳^ν) = A_j(𝒳)`). -/
theorem homLocAlg_normalization_eq [Infinite k] [PerfectField k]
    (hY : ∀ j : Y.ChartIndex, (∀ c, Y.coord c (j c) ≠ 0) → IsIntegrallyClosed (Y.chartAlg j))
    {h : K}
    (hspan : Ideal.span (Set.range fun j : {j : Y.ChartIndex // ∀ c, Y.coord c (j c) ≠ 0} =>
      (⟨Y.chartDen j.1 a / h, div_mem_homLocAlg (Y.chartDen_mem_piece j.1 a)⟩ :
        Y.homLocAlg h a)) = ⊤) :
    Y.normalization.homLocAlg h a = Y.homLocAlg h a := by
  classical
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨n, g, hg, rfl⟩
    refine subalgebra_mem_of_span_eq_top hspan ?_
    rintro ⟨j, hj⟩
    have hmem : g / Y.chartDen j (n • a) ∈ Y.chartAlg j := by
      rw [← chartAlg_normalization hj (hY j hj)]
      exact div_chartDen_mem_chartAlg hg
    obtain ⟨b, g', hg', he⟩ := (mem_chartAlg_iff hj).1 hmem
    set m := ∑ c, b c
    have hle : b ≤ m • a := le_sum_nsmul ha b
    refine ⟨m, ?_⟩
    have hD : ∀ d, Y.chartDen j d ≠ 0 := chartDen_ne_zero hj
    have key : g * Y.chartDen j (m • a) =
        g' * Y.chartDen j (n • a) * Y.chartDen j (m • a - b) := by
      have h1 : g * Y.chartDen j b = g' * Y.chartDen j (n • a) := by
        rw [div_eq_div_iff (hD _) (hD _)] at he
        exact he
      rw [← add_tsub_cancel_of_le hle, chartDen_add, add_tsub_cancel_left, ← mul_assoc, h1]
    have hmem' : g * Y.chartDen j (m • a) ∈ Y.piece ((n + m) • a) := by
      rw [key]
      have := mul_mem_piece (mul_mem_piece hg' (Y.chartDen_mem_piece j (n • a)))
        (Y.chartDen_mem_piece j (m • a - b))
      rwa [add_comm b, add_assoc, add_tsub_cancel_of_le hle, ← add_nsmul] at this
    have e : g / h ^ n * (Y.chartDen j a / h) ^ m = g * Y.chartDen j (m • a) / h ^ (n + m) := by
      rw [chartDen_nsmul, div_pow, pow_add]
      ring
    change g / h ^ n * (Y.chartDen j a / h) ^ m ∈ Y.homLocAlg h a
    rw [e]
    exact div_pow_mem_homLocAlg hmem'
  · rintro _ ⟨n, g, hg, rfl⟩
    exact div_pow_mem_homLocAlg (Y.le_normalization_S hg)

/-- **Smooth Segre–Veronese models** (`cor:gl-smooth-ep-nef`, G3 pending item 3): if `𝒳` is
smooth, so is `𝒳_(a)`. The chart `S_{(z̃^β)}` is covered by the localizations
`S_{(z̃^β z̃_j^a)}` of the smooth charts `A_j = S_{(z̃_j^a)}` of `𝒳`, and it is the corresponding
chart of the normal model `𝒳^ν_(a)` (`homLocAlg_normalization_eq`), hence integrally closed. -/
theorem IsSmooth.veronese [Infinite k] [PerfectField k] (hX : Y.IsSmooth) :
    (Y.veronese ha).IsSmooth := by
  intro β hβ
  have hmem : (Y.veronese ha).chartDen β (Finsupp.single 0 1) ∈ Y.piece a := by
    have := (Y.veronese ha).chartDen_mem_piece β (Finsupp.single 0 1)
    rwa [Y.mem_veronese_piece_iff ha, one_smul] at this
  have hspan := span_chartDen_div_veronese_eq_top ha hβ
  refine ⟨?_, ?_⟩
  · have := smooth_homLocAlg_of_span hmem (chartDen_ne_zero hβ _)
      (g := fun j : {j : Y.ChartIndex // ∀ c, Y.coord c (j c) ≠ 0} => Y.chartDen j.1 a)
      (fun j => Y.chartDen_mem_piece j.1 a) (fun j => chartDen_ne_zero j.2 a)
      (fun j => by
        have := hX.smooth j.2
        exact Algebra.Smooth.of_equiv (Subalgebra.equivOfEq _ _ (chartAlg_eq_homLocAlg j.2 ha)))
      hspan
    exact Algebra.Smooth.of_equiv (Subalgebra.equivOfEq _ _ (chartAlg_veronese_eq ha hβ).symm)
  · have hβ' : ∀ c, (Y.normalization.veronese ha).coord c (β c) ≠ 0 := hβ
    have h1 : IsIntegrallyClosed ((Y.normalization.veronese ha).chartAlg β) :=
      isIntegrallyClosed_chartAlg hβ'
        (Y.normalization.isNormal_veronese (ha := ha) Y.isNormal_normalization)
    have e : (Y.normalization.veronese ha).chartAlg β = (Y.veronese ha).chartAlg β := by
      rw [chartAlg_veronese_eq ha hβ', chartAlg_veronese_eq ha hβ]
      exact homLocAlg_normalization_eq ha (fun j hj => hX.isIntegrallyClosed hj) hspan
    exact IsIntegrallyClosed.of_equiv (Subalgebra.equivOfEq _ _ e).toRingEquiv

end Veronese

namespace DegOnePres

variable {X : MultiModel k K 1} {N : ℕ} (P : DegOnePres X N)

/-- **Charts of a presentation**: the chart algebra of `(K, S, w)` at `w_i ≠ 0` is
`S_{(w_i)} = {g / w_i^n : g ∈ S_n}`. -/
theorem chartAlg_recoord_eq {i : Fin (N + 1)} (hi : P.w i ≠ 0) :
    P.recoord.chartAlg (P.chartIndex i) = X.homLocAlg (P.w i) (Finsupp.single 0 1) := by
  rw [chartAlg_eq_homLocAlg (P.coord_chartIndex_ne_zero hi) (a := Finsupp.single 0 1) fun c => by
    obtain rfl := Fin.fin_one_eq_zero c; simp, P.chartDen_chartIndex i 1, pow_one]
  rfl

/-- **Smooth charts of `V(I)`** (`cor:sg-smooth-model`(c)): if every `S_{(w_i)}`, `w_i ≠ 0`, is a
smooth `k`-algebra, then `V(I)` has smooth charts (`A_{x_i} / I_{(x_i)} ≅ S_{(w_i)}`). -/
theorem hasSmoothCharts_toProjSubvariety
    (h : ∀ i, P.w i ≠ 0 → Algebra.Smooth k (X.homLocAlg (P.w i) (Finsupp.single 0 1))) :
    P.toProjSubvariety.HasSmoothCharts := by
  intro i hi
  have hw := (P.X_notMem_ideal_iff i).1 hi
  have := h i hw
  have : Algebra.Smooth k (P.recoord.chartAlg (P.chartIndex i)) :=
    Algebra.Smooth.of_equiv (Subalgebra.equivOfEq _ _ (P.chartAlg_recoord_eq hw).symm)
  exact Algebra.Smooth.of_equiv (P.quotChartAlgEquiv i hw).symm

end DegOnePres

section VeronesePres

variable [NeZero r] {Y : MultiModel k K r} {a : Fin r →₀ ℕ} {ha : ∀ c, 0 < a c} {N : ℕ}
  (P : DegOnePres (Y.veronese ha) N)

include P in
/-- The generators `w_i ∈ (S_(a))_1` of a presentation of `𝒳_(a)` lie in `S_a`. -/
theorem DegOnePres.w_mem_piece (i : Fin (N + 1)) : P.w i ∈ Y.piece a := by
  have := P.mem i
  rwa [Y.mem_veronese_piece_iff ha, one_smul] at this

/-- For a presentation `w` of `𝒳_(a)` in degree `1` and `w_i ≠ 0`, the elements `z̃_j^a / w_i`
generate the unit ideal of `S_{(w_i)}`: a point of its analytification is a point of the chart
`w_i ≠ 0` of `(K, S_(a), w)^an ≅ 𝒳_(a)^an ≅ 𝒳^an`, where some `|z̃_j^a U|` is `1`. -/
theorem DegOnePres.span_chartDen_div_eq_top {i : Fin (N + 1)} (hi : P.w i ≠ 0) :
    Ideal.span (Set.range fun j : {j : Y.ChartIndex // ∀ c, Y.coord c (j c) ≠ 0} =>
      (⟨Y.chartDen j.1 a / P.w i, div_mem_homLocAlg (Y.chartDen_mem_piece j.1 a)⟩ :
        Y.homLocAlg (P.w i) a)) = ⊤ := by
  have e : P.recoord.chartAlg (P.chartIndex i) = Y.homLocAlg (P.w i) a :=
    (P.chartAlg_recoord_eq hi).trans (homLocAlg_veronese ha _)
  apply Berk.span_eq_top_of_forall_exists_val_ne_zero (k := k)
  intro y
  set y' : Berk k (P.recoord.chartAlg (P.chartIndex i)) :=
    Berk.comap (Subalgebra.equivOfEq _ _ e).toAlgHom y
  set v := P.recoord.chartInv (P.chartIndex i) (P.coord_chartIndex_ne_zero hi) y'
  obtain ⟨j, hj, hv⟩ := exists_val_chartDen_veronese_eq_one ha (P.recoordHomeomorph v)
  refine ⟨_, ⟨⟨j, hj⟩, rfl⟩, fun h0 => ?_⟩
  have h1 := P.recoord.chartInv_val_ofPiece (P.coord_chartIndex_ne_zero hi) y'
    (chartDen_mem_veronese_piece ha j)
  have hv' : v.1.val (P.recoord.ofPiece (chartDen_mem_veronese_piece ha j)) = 1 := hv
  rw [hv'] at h1
  have h2 : y'.val ⟨Y.chartDen j a / P.recoord.chartDen (P.chartIndex i) (Finsupp.single 0 1),
      div_chartDen_mem_chartAlg (chartDen_mem_veronese_piece ha j)⟩ = 0 := by
    change y.val ⟨_, _⟩ = 0
    convert h0 using 3
    change Y.chartDen j a / P.recoord.chartDen (P.chartIndex i) (Finsupp.single 0 1) =
      Y.chartDen j a / P.w i
    rw [P.chartDen_chartIndex i 1, pow_one]
  rw [h2, zero_div] at h1
  exact one_ne_zero h1

/-- **The charts `S_{(w_i)}` of a presentation of `𝒳_(a)` are smooth** if `𝒳` is smooth: they
are covered by the localizations `S_{(w_i z̃_j^a)}` of the smooth charts `A_j = S_{(z̃_j^a)}`. -/
theorem DegOnePres.smooth_homLocAlg (hX : Y.IsSmooth) {i : Fin (N + 1)} (hi : P.w i ≠ 0) :
    Algebra.Smooth k (Y.homLocAlg (P.w i) a) :=
  smooth_homLocAlg_of_span (P.w_mem_piece i) hi
    (g := fun j : {j : Y.ChartIndex // ∀ c, Y.coord c (j c) ≠ 0} => Y.chartDen j.1 a)
    (fun j => Y.chartDen_mem_piece j.1 a) (fun j => chartDen_ne_zero j.2 a)
    (fun j => by
      have := hX.smooth j.2
      exact Algebra.Smooth.of_equiv (Subalgebra.equivOfEq _ _ (chartAlg_eq_homLocAlg j.2 ha)))
    (P.span_chartDen_div_eq_top hi)

/-- **`V(I)` has smooth charts** for a presentation of the Segre–Veronese model of a smooth
model. -/
theorem DegOnePres.hasSmoothCharts_of_isSmooth (hX : Y.IsSmooth) :
    P.toProjSubvariety.HasSmoothCharts :=
  P.hasSmoothCharts_toProjSubvariety fun i hi => by
    have := P.smooth_homLocAlg hX hi
    exact Algebra.Smooth.of_equiv (Subalgebra.equivOfEq _ _ (homLocAlg_veronese ha _).symm)

end VeronesePres

/-! ### Veronese models generated in degree 1 -/

section DegreeZero

/-- **`S_0 = k`** for `k` algebraically closed (`cor:sg-smooth-model`(a)): an element of `S_0` is
integral over `k[z]`, so (taking constant coefficients) algebraic over `k`. -/
theorem exists_algebraMap_eq_of_mem_piece_zero [IsAlgClosed k] (X : MultiModel k K r) {f : K}
    (hf : f ∈ X.piece 0) : ∃ c : k, algebraMap k K c = f := by
  have hint : IsIntegral X.coordAlg (monomial 0 f) := X.isIntegral_coordAlg hf
  let ψ : MvPolynomial (Fin r) K →ₐ[k] K := (aeval fun _ => (0 : K)).restrictScalars k
  have hle : X.coordAlg ≤ (⊥ : Subalgebra k K).comap ψ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    have h0 : ψ (X.coordMono i) = 0 := by
      simp [ψ, coordMono, aeval_monomial]
    change ψ (X.coordMono i) ∈ (⊥ : Subalgebra k K)
    rw [h0]
    exact Subalgebra.zero_mem _
  let φ : X.coordAlg →ₐ[k] k := (Algebra.botEquiv k K).toAlgHom.comp
    ((ψ.comp X.coordAlg.val).codRestrict ⊥ fun x => hle x.2)
  have hbot : ∀ b : (⊥ : Subalgebra k K), algebraMap k K (Algebra.botEquiv k K b) = b := by
    intro b
    conv_rhs => rw [← (Algebra.botEquiv k K).symm_apply_apply b]
    rw [Algebra.botEquiv_symm_apply]
    rfl
  have hφ : (algebraMap k K).comp (φ : X.coordAlg →+* k) =
      (ψ : MvPolynomial (Fin r) K →+* K).comp (algebraMap X.coordAlg (MvPolynomial (Fin r) K)) :=
    RingHom.ext fun x => hbot _
  have h1 := IsIntegral.map_of_comp_eq (φ : X.coordAlg →+* k) (ψ : MvPolynomial (Fin r) K →+* K)
    hφ hint
  have hψ : (ψ : MvPolynomial (Fin r) K →+* K) (monomial 0 f) = f := by
    simp [ψ]
  rw [hψ] at h1
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible h1)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 (Polynomial.natDegree_eq_of_degree_eq_some hdeg)
  exact ⟨c, hc⟩

end DegreeZero

section VeroneseGenerated

variable (k) in
/-- The isomorphism `K[U] ≅ K[X]` of the rank-one coordinate ring with polynomials in one
variable, which carries `S` to a graded subalgebra of `K[X]` (`Algebra/Veronese`). -/
abbrev finOnePolyEquiv : MvPolynomial (Fin 1) K ≃ₐ[k] Polynomial K :=
  (MvPolynomial.uniqueAlgEquiv K (Fin 1)).restrictScalars k

/-- `finOnePolyEquiv (f U^u) = f X^u`. -/
theorem finOnePolyEquiv_monomial (u : Fin 1 →₀ ℕ) (f : K) :
    finOnePolyEquiv k (monomial u f) = Polynomial.monomial (u 0) f := by
  rw [AlgEquiv.restrictScalars_apply, MvPolynomial.uniqueAlgEquiv_monomial]
  rfl

/-- **`lem:wu-veronese` for rank-one models** (`cor:sg-smooth-model`(b)): for `k` algebraically
closed, some Veronese model `𝒳_(e)` is generated in degree `1`, i.e. has a presentation
`w_0, …, w_N ∈ S_e` with `S_(e) = k[w_0 U, …, w_N U]`. -/
theorem exists_degOnePres_veronese [IsAlgClosed k] (Y : MultiModel k K 1) :
    ∃ (e : ℕ) (ha : ∀ c, 0 < (Finsupp.single (0 : Fin 1) e) c) (N : ℕ),
      Nonempty (DegOnePres (Y.veronese ha) N) := by
  classical
  let φ : MvPolynomial (Fin 1) K ≃ₐ[k] Polynomial K := finOnePolyEquiv k
  have hφ : ∀ (u : Fin 1 →₀ ℕ) (f : K), φ (monomial u f) = Polynomial.monomial (u 0) f :=
    finOnePolyEquiv_monomial
  let B : Subalgebra k (Polynomial K) := Y.S.map φ.toAlgHom
  have hmemB : ∀ p, p ∈ B ↔ φ.symm p ∈ Y.S := fun p => by
    refine ⟨fun hp => ?_, fun hp => ⟨φ.symm p, hp, φ.apply_symm_apply p⟩⟩
    obtain ⟨q, hq, rfl⟩ := Subalgebra.mem_map.1 hp
    change φ.symm (φ q) ∈ Y.S
    rwa [φ.symm_apply_apply]
  have hmonB : ∀ (d : ℕ) (f : K),
      Polynomial.monomial d f ∈ B ↔ f ∈ Y.piece (Finsupp.single 0 d) := by
    intro d f
    rw [hmemB, mem_piece]
    have : φ.symm (Polynomial.monomial d f) = monomial (Finsupp.single 0 d) f := by
      rw [AlgEquiv.symm_apply_eq, hφ, Finsupp.single_eq_same]
    rw [this]
  have hcoeff : ∀ (q : MvPolynomial (Fin 1) K) (d : ℕ),
      (φ q).coeff d = q.coeff (Finsupp.single 0 d) := by
    intro q d
    rw [AlgEquiv.restrictScalars_apply, MvPolynomial.coeff_uniqueAlgEquiv]
    rfl
  have hB : IsTGraded B := by
    intro p hp d
    rw [homogComp_apply, hmonB]
    obtain ⟨q, hq, rfl⟩ := Subalgebra.mem_map.1 hp
    change (φ q).coeff d ∈ _
    rw [hcoeff]
    exact Y.isGraded q hq _
  have hfg : B.FG := Y.fg.map _
  have h0 : ∀ f : K, Polynomial.C f ∈ B → ∃ c : k, algebraMap k K c = f := by
    intro f hf
    rw [← Polynomial.monomial_zero_left, hmonB, Finsupp.single_zero] at hf
    exact Y.exists_algebraMap_eq_of_mem_piece_zero hf
  obtain ⟨e, he, -, hver⟩ := exists_veronese_generated hB hfg h0
  have hfd : FiniteDimensional k (gradedPiece B e) := by
    obtain ⟨r', b, d, hd, hb, hadj⟩ := exists_homog_generators hB hfg h0
    rw [← hadj]
    exact finiteDimensional_gradedPiece_adjoin hb hd e
  have ha : ∀ c, 0 < (Finsupp.single (0 : Fin 1) e) c := fun c => by
    obtain rfl := Fin.fin_one_eq_zero c
    rw [Finsupp.single_eq_same]
    exact he
  let bs := Module.finBasis k (gradedPiece B e)
  let n := Module.finrank k (gradedPiece B e)
  let w : Fin (n + 1) → K := Fin.cons 0 fun i => (bs i : Polynomial K).coeff e
  have hbs : ∀ i, (bs i : Polynomial K) = Polynomial.monomial e ((bs i : Polynomial K).coeff e) :=
    fun i => (bs i).2.2.eq_monomial
  have hwmem : ∀ i : Fin n, (bs i : Polynomial K).coeff e ∈ Y.piece (Finsupp.single 0 e) := by
    intro i
    rw [← hmonB, ← hbs]
    exact (bs i).2.1
  have hmem : ∀ i, w i ∈ (Y.veronese ha).piece (Finsupp.single 0 1) := by
    intro i
    rw [Y.mem_veronese_piece_iff ha, one_smul]
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Submodule.zero_mem _
    · exact hwmem i
  refine ⟨e, ha, n, ⟨⟨w, hmem, le_antisymm ?_ ?_⟩⟩⟩
  · exact Algebra.adjoin_le (Set.range_subset_iff.2 fun i => hmem i)
  · set A' := Algebra.adjoin k (Set.range fun i =>
      (monomial (Finsupp.single 0 1) (w i) : MvPolynomial (Fin 1) K))
    let ψ : MvPolynomial (Fin 1) K →ₐ[k] Polynomial K :=
      φ.toAlgHom.comp (veroneseHom k (Finsupp.single 0 e))
    have hψ : ∀ (m : ℕ) (g : K),
        ψ (monomial (Finsupp.single 0 m) g) = Polynomial.monomial (m * e) g := by
      intro m g
      change φ (veroneseHom k _ (monomial _ g)) = _
      rw [veroneseHom_monomial_single, hφ, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul]
    have hψinj : Function.Injective ψ :=
      φ.injective.comp (veroneseHom_injective (k := k) (ne_zero_of_pos ha))
    have hgen : (gradedPiece B e : Set (Polynomial K)) ⊆ A'.map ψ := by
      intro x hx
      have hbasis : ∀ i, (bs i : Polynomial K) ∈ A'.map ψ := fun i =>
        ⟨monomial (Finsupp.single 0 1) (w i.succ), Algebra.subset_adjoin ⟨i.succ, rfl⟩, by
          change ψ _ = _
          rw [hψ, one_mul, hbs i]
          rfl⟩
      have e1 : x = ∑ i, bs.repr ⟨x, hx⟩ i • (bs i : Polynomial K) := by
        have := congrArg Subtype.val (bs.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simpa using this.symm
      rw [e1]
      exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hbasis i) _
    have hadj : Algebra.adjoin k (gradedPiece B e : Set (Polynomial K)) ≤ A'.map ψ :=
      Algebra.adjoin_le hgen
    intro p hp
    rw [p.as_sum]
    refine Subalgebra.sum_mem _ fun u _ => ?_
    have hu := (Y.veronese ha).isGraded p hp u
    rw [fin_one_eq_single u] at hu ⊢
    have hu' : p.coeff (Finsupp.single 0 (u 0)) ∈ Y.piece (Finsupp.single 0 (u 0 * e)) := by
      have := (Y.mem_veronese_piece_iff ha).1 hu
      rwa [Finsupp.smul_single, smul_eq_mul] at this
    have h1 : Polynomial.monomial (u 0 * e) (p.coeff (Finsupp.single 0 (u 0))) ∈
        EnvelopeProperty.veronese B e := by
      refine ⟨(hmonB _ _).2 hu', fun m hm => ?_⟩
      rw [Polynomial.coeff_monomial, if_neg]
      rintro rfl
      exact hm (dvd_mul_left e _)
    rw [hver] at h1
    obtain ⟨q, hq, hq'⟩ := Subalgebra.mem_map.1 (hadj h1)
    change ψ q = _ at hq'
    rw [← hψ] at hq'
    rw [← hψinj hq']
    exact hq

end VeroneseGenerated

/-! ### The envelope property of smooth models -/

section SmoothEP

/-- **The envelope property of smooth models of rank one** (**`thm:gl-smooth-ep`** =
**`cor:sg-smooth-model`**; FHX Theorem 3.1, `thm:smooth-EP`, for the classes `t O(1)`): let `k` be
algebraically closed and `𝒳` a smooth model of rank `1`. Then every `t ≥ 0` has the envelope
property on `𝒳`. In characteristic `p > 0` this is unconditional; in characteristic `0` it rests on
the imported `SmoothEnvelopeCharZero k` (`thm:import-sg-ep-char0`), which `h₀` provides (in
positive characteristic `h₀` holds vacuously).

Proof (`cor:sg-smooth-model`): (a) pass to the normalization `𝒳^ν`, which has the same (smooth)
charts; (b) a Veronese model `𝒳^ν_(e)` is generated in degree `1` by `w_0, …, w_N ∈ S^ν_e`, and is
normal, so `V(I) ⊆ ℙ^N` is projectively normal; (c) the charts `S^ν_{(w_i)}` of `V(I)` are covered
by the localizations `S^ν_{(w_i z_j^e)}` of the smooth charts `A_j`, hence smooth; (d) the
envelope property of `V(I)` (`thm:sg-ep`) transfers back along the bridge (`lem:gl-bridge-psh`(1))
and the Veronese model (`lem:gl-veronese`). -/
theorem hasEnvelopeProperty_of_isSmooth [IsAlgClosed k]
    (h₀ : ∀ [CharZero k], SmoothEnvelopeCharZero k) {X : MultiModel k K 1} (hX : X.IsSmooth)
    {t : ℝ} (ht : 0 ≤ t) : X.HasEnvelopeProperty fun _ => t := by
  -- (a) the normalization
  rw [← hasEnvelopeProperty_normalization_iff fun j hj => hX.isIntegrallyClosed hj]
  have hY : X.normalization.IsSmooth := hX.normalization
  have hYN : X.normalization.IsNormal := X.isNormal_normalization
  -- (b) a Veronese model generated in degree `1`
  obtain ⟨e, ha, N, ⟨P⟩⟩ := X.normalization.exists_degOnePres_veronese
  have he : (0 : ℝ) < e := by
    have := ha 0
    rw [Finsupp.single_eq_same] at this
    exact_mod_cast this
  have hV : P.toProjSubvariety.IsProjNormal :=
    P.isProjNormal_toProjSubvariety_iff.2 (X.normalization.isNormal_veronese (ha := ha) hYN)
  -- (c) smooth charts
  have hs : P.toProjSubvariety.HasSmoothCharts := P.hasSmoothCharts_of_isSmooth hY
  -- (d) Theorem 3.1 on `V(I)`
  have hEP := ProjSubvariety.hasEnvelopeProperty_of_smooth h₀ P.toProjSubvariety hV hs (t / e)
  have h1 := (P.hasEnvelopeProperty_toProjSubvariety_iff hV (div_nonneg ht he.le)).1 hEP
  have h2 := (X.normalization.hasEnvelopeProperty_veronese_iff ha).1 h1
  convert h2 using 2 with c
  obtain rfl := Fin.fin_one_eq_zero c
  rw [Finsupp.single_eq_same, div_mul_cancel₀ _ he.ne']

/-- **The envelope property of smooth models** (**`cor:gl-smooth-ep-nef`**): let `k` be
algebraically closed and `𝒳` a smooth model of rank `r ≥ 1`. Then every `θ ∈ ℝ^r_{≥0}` has the
envelope property on `𝒳` (in characteristic `0` from the imported `SmoothEnvelopeCharZero k`).

Proof: by `lem:gl-ep-basic`(1),(2) it suffices to treat positive `a ∈ ℕ^r`; the Segre–Veronese
model `𝒳_(a)` is smooth (`IsSmooth.veronese`), so `EP_𝒳(a) ↔ EP_{𝒳_(a)}(1)` (`lem:gl-veronese`)
holds by `hasEnvelopeProperty_of_isSmooth`. -/
theorem hasEnvelopeProperty_of_isSmooth_of_nonneg [IsAlgClosed k] [NeZero r]
    (h₀ : ∀ [CharZero k], SmoothEnvelopeCharZero k) {X : MultiModel k K r} (hX : X.IsSmooth)
    {θ : Fin r → ℝ} (hθ : 0 ≤ θ) : X.HasEnvelopeProperty θ := by
  refine hasEnvelopeProperty_of_forall_rat_gt (X.mem_nefCone_of_nonneg hθ)
    fun q hq => ?_
  have hqpos : ∀ c, (0 : ℚ) < q c := fun c => by
    have h : (0 : ℝ) < q c := lt_of_le_of_lt (hθ c) (hq c)
    exact_mod_cast h
  have hq0 : 0 ≤ q := fun c => (hqpos c).le
  obtain ⟨m, hm, d, hd⟩ := exists_nat_mul_rat_vec_eq_nat_of_nonneg hq0
  set a : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  have had : ∀ c, a c = d c := fun c => rfl
  have ha : ∀ c, 0 < a c := fun c => by
    have h2 : (0 : ℚ) < d c := by rw [hd c]; exact mul_pos (by exact_mod_cast hm) (hqpos c)
    rw [had c]
    exact_mod_cast h2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hqa : (fun c => (q c : ℝ)) = (m : ℝ)⁻¹ • fun c => (a c : ℝ) := by
    funext c
    have := hd c
    rw [Pi.smul_apply, smul_eq_mul, had c]
    have h' : ((d c : ℚ) : ℝ) = (m : ℝ) * (q c : ℝ) := by exact_mod_cast this
    rw [show ((d c : ℕ) : ℝ) = ((d c : ℚ) : ℝ) by norm_cast, h', ← mul_assoc,
      inv_mul_cancel₀ hm'.ne', one_mul]
  rw [hqa, hasEnvelopeProperty_smul_iff (X.mem_nefCone_of_nonneg fun c => by positivity)
    (inv_pos.2 hm')]
  have h1 := hasEnvelopeProperty_of_isSmooth h₀ (hX.veronese ha) zero_le_one
  have h2 := (X.hasEnvelopeProperty_veronese_iff ha).1 h1
  simpa using h2

end SmoothEP

end MultiModel

end EnvelopeProperty
