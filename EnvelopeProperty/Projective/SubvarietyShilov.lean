/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyGauss

/-!
# The Shilov boundary lemma on `X = V(I)`

Let `k` be an algebraically closed field with the trivial absolute value and `X = V(I) ⊆ ℙᴹ` a
projective subvariety (`EnvelopeProperty.ProjSubvariety`), with homogeneous coordinate ring
`S = R_M / I`, cone ring `T = S[t]` and charts `A_j = S_{(x̄ⱼ)}`, `B_j = A_j[t]` for `xⱼ ∉ I`
(`EnvelopeProperty.Projective.SubvarietyCone`). This file proves the Shilov boundary lemma of
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22,
Shilov), on `X`, following the blueprint chapter `smooth-general.tex` (subsection
`subsec:sg-comparison`, nodes `lem:sg-rees-invariant`, `lem:sg-finite-fs`, `lem:sg-shilov`); the
finite set `Σ` consists of `⋆` and the divisorial points attached to the Rees valuations of the
ideals `𝔦^{(j)}` of the charts `B_j` (`Algebra/Rees.lean`, `thm:bj-rees`, `lem:bj-rees-invariant`)
by `lem:sg-div-points`(2). It is the input of the divisorial comparison theorem on `X`
(`EnvelopeProperty.Projective.SubvarietyComparison`), used in Fang–Han–Xia, *The envelope property
for unibranch projective varieties*, Theorem 3.1 (`thm:smooth-EP`).

The proof is the one of `EnvelopeProperty.Projective.ComparisonShilov` for `ℙⁿ`, with the polynomial
charts `k[y][t]` replaced by the quotient charts `B_j` and the dehomogenization `dehom` by
`X.quotDehom j : R_M → A_j`.

## Main results

* `ProjSubvariety.X_mem_radical_span_sup`, `ProjSubvariety.exists_X_pow_mem_span_sup`
  (`lem:sg-finite-fs`, first claim): if forms `sᵢ` have no common zero on `X^an`, then every `xⱼ`
  lies in the radical of `(sᵢ) + I`, so `xⱼ^E ∈ (sᵢ) + I` (the point `ProjBerk.primePoint` of a
  homogeneous prime containing `(sᵢ) + I` lies in `X^an`).
* `ProjSubvariety.X_pow_mem_span_dehomGen` (`lem:sg-finite-fs`, last claim): `t^N ∈ 𝔦^{(j)} =
  (gᵢ^{(j)})` in every chart, `gᵢ = sᵢ t^{eᵢ}`, `gᵢ^{(j)} = δⱼ(gᵢ)` (`ProjSubvariety.dehomGen`).
* `ProjSubvariety.reesDVR_torus`, `ProjSubvariety.reesOrdX_pos` (**`lem:sg-rees-invariant`**,
  applied to `𝔦^{(j)}`): the Rees valuations are monomial in `t`, with `ord_V(t) > 0`;
  `ProjSubvariety.isDivisorial_reesPoint`: the points `v_V` are divisorial.
* `ProjSubvariety.exists_finset_shilov_core`, `ProjSubvariety.exists_finset_shilov_coneSup`: the
  comparison on `Σ` propagates to `X^an` (Rees valuations detect integral closure, applied to the
  seminorm `w = ProjSubvariety.chartGauss` on `B_j`).
* `ProjSubvariety.IsFinFS.exists_coneSup` (`lem:sg-finite-fs`): a finite Fubini–Study function on
  `X^an` is `K⁻¹ (φ_𝔦 + Z)` with `φ_𝔦 = max_i log|sᵢ t^{eᵢ}|_{σ(·)}` and forms `sᵢ` of one degree
  without common zero on `X^an`.
* **`lem:sg-shilov`**: `ProjSubvariety.IsFinFS.exists_finset_le_of_le` (comparison form) and
  `ProjSubvariety.IsFinFS.exists_finset_iSup_sub_eq`: for `ψ ∈ 𝓗_fin(X, b)` there is a finite set
  `Σ ⊆ X^div` containing `⋆` with `sup_{X^an} (φ - ψ) = max_Σ (φ - ψ)` for every `a ∈ ℚ` and every
  Fubini–Study function `φ` of class `a` with rational weights.

## Deviations from the blueprint

The same as in `EnvelopeProperty.Projective.ComparisonShilov`: `lem:sg-shilov` is proved in
comparison form first (so that the rationality of `max_Σ (φ - ψ)` is not needed); the normal form of
`ψ` subtracts the largest integral weight instead of normalizing `max λᵢ = 0`; the seminorm `w` on
`B_j` is the Gauss point of radius `e⁻¹` over the chart image `ι_{xⱼ}(v)` (`X.chartMap`), which
agrees with `f ↦ |F|_{σ(v)}` of the blueprint on dehomogenized elements. `lem:sg-finite-fs` is used
in the form "`xⱼ^E ∈ (sᵢ) + I` for all `j`" (equivalent to `𝔪₊^e ⊆ (s̄ᵢ) S`), which gives
`t^N ∈ 𝔦^{(j)}` directly in `B_j`.
-/

open scoped NNReal ENNReal Topology Polynomial

open IsDiscreteValuationRing

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace EnvelopeProperty

open ProjBerk (gaussExt logAbs gaussRadius coneGen coneSup)

universe u

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-! ### Chart indices -/

variable (X) in
/-- The indices `j` of the charts `xⱼ ∉ I` of `X`. -/
abbrev ChartIdx : Type := {j : Fin (M + 1) // MvPolynomial.X j ∉ X.ideal}

instance (j : X.ChartIdx) : Fact (MvPolynomial.X j.1 ∉ X.ideal) := ⟨j.2⟩

instance (j : Fin (M + 1)) : Algebra.FiniteType k (X.ChartRing j) :=
  Algebra.FiniteType.trans (S := X.ChartAlg j) inferInstance inferInstance

/-! ### Common zeros of forms on `X^an` (`lem:sg-finite-fs`) -/

/-- **`lem:sg-finite-fs`, first claim**: if forms `sᵢ` have no common zero on `X^an`, then every
`xⱼ` lies in the radical of `(sᵢ) + I`. Otherwise a prime `P ⊇ (sᵢ) + I` with `xⱼ ∉ P` has a
homogeneous core `P*` with the same properties, and the trivial semivaluation of `P*`
(`ProjBerk.primePoint`) is a common zero of the `sᵢ` in `X^an`. -/
theorem X_mem_radical_span_sup {ι : Type*} {s : ι → MvPolynomial (Fin (M + 1)) k}
    (hs : ∀ i, ∃ d, (s i).IsHomogeneous d) (hz : ∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0)
    (j : Fin (M + 1)) :
    MvPolynomial.X j ∈ (Ideal.span (Set.range s) ⊔ X.ideal).radical := by
  by_contra h
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf] at h
  push Not at h
  obtain ⟨J, ⟨hIJ, hJ⟩, hjJ⟩ := h
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (M + 1)) k
  have hspan : (Ideal.span (Set.range s)).IsHomogeneous 𝒜 := by
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨d, hd⟩ := hs i
    exact ⟨d, (MvPolynomial.mem_homogeneousSubmodule d _).2 hd⟩
  have hI : (Ideal.span (Set.range s) ⊔ X.ideal).IsHomogeneous 𝒜 :=
    hspan.sup ((isHomogeneousIdeal_iff_isHomogeneous _).1 X.isHomogeneousIdeal)
  have hp : ((Ideal.homogeneousCore 𝒜 J).toIdeal).IsPrime := hJ.homogeneousCore
  have hIp : Ideal.span (Set.range s) ⊔ X.ideal ≤ (Ideal.homogeneousCore 𝒜 J).toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hIJ
  have hjp : MvPolynomial.X j ∉ (Ideal.homogeneousCore 𝒜 J).toIdeal := fun h' =>
    hjJ (Ideal.toIdeal_homogeneousCore_le 𝒜 J h')
  have hmem : ProjBerk.primePoint _ hjp ∈ X.an := by
    refine (ProjBerk.mem_zeroLocus_iff X.isHomogeneousIdeal).2 fun D f hf hfI => ?_
    exact ProjBerk.primePoint_val_of_mem _ hjp hf (hIp (Ideal.mem_sup_right hfI))
  obtain ⟨i, hi⟩ := hz ⟨_, hmem⟩
  obtain ⟨d, hd⟩ := hs i
  exact hi (ProjBerk.primePoint_val_of_mem _ hjp hd
    (hIp (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))))

/-- **`lem:sg-finite-fs`, first claim, power form**: if forms `sᵢ` have no common zero on `X^an`,
then `xⱼ^E ∈ (sᵢ) + I` for some `E` and all `j`, i.e. `𝔪₊^{(M+1)E} ⊆ (s̄ᵢ) S`. -/
theorem exists_X_pow_mem_span_sup {ι : Type*} {s : ι → MvPolynomial (Fin (M + 1)) k}
    (hs : ∀ i, ∃ d, (s i).IsHomogeneous d) (hz : ∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0) :
    ∃ E : ℕ, ∀ j : Fin (M + 1), MvPolynomial.X j ^ E ∈ Ideal.span (Set.range s) ⊔ X.ideal := by
  choose E hE using fun j => (X_mem_radical_span_sup hs hz j : ∃ E : ℕ, _)
  refine ⟨Finset.univ.sup E, fun j => ?_⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup (f := E) (Finset.mem_univ j)), pow_add]
  exact Ideal.mul_mem_left _ _ (hE j)

/-! ### The chart seminorm -/

section ChartGauss

theorem val_X_ne_zero_of_eq_one {v : X.an} {j : Fin (M + 1)}
    (hv : v.1.1.val (MvPolynomial.X j) = 1) : (v : ProjBerk k M).1.val (MvPolynomial.X j) ≠ 0 := by
  rw [hv]
  exact one_ne_zero

/-- The image `ι_{xⱼ}(v) ∈ (Spec A_j)^an` of `v` in the chart `xⱼ ≠ 0`. -/
def chartPt (v : X.an) (j : Fin (M + 1)) (hv : v.1.1.val (MvPolynomial.X j) ≠ 0) :
    Berk k (X.ChartAlg j) :=
  X.chartMap (MvPolynomial.X j) 1 v hv

theorem chartPt_val_quotDehom {v : X.an} {j : Fin (M + 1)}
    (hv : v.1.1.val (MvPolynomial.X j) ≠ 0) {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous N) :
    (chartPt v j hv).val (X.quotDehom j τ) =
      v.1.1.val τ / v.1.1.val (MvPolynomial.X j) ^ N := by
  rw [quotDehom_of_isHomogeneous hτ]
  exact chartMap_val_quotChartMk v hv (by rw [mul_one]; exact hτ)

/-- For `v` with `|xⱼ|_v = 1`, the Gauss point of radius `e⁻¹` over the chart image of `v`: a
multiplicative seminorm on `B_j = A_j[t]` with `|G^{(j)}| = |G|_{σ(v)}` (`chartGauss_val_map`). -/
def chartGauss (v : X.an) (j : Fin (M + 1)) (hv : v.1.1.val (MvPolynomial.X j) = 1) :
    Berk k (X.ChartRing j) :=
  Berk.gauss (chartPt v j (val_X_ne_zero_of_eq_one hv)) gaussRadius

/-- `w(G^{(j)}) = |G|_{σ(v)}` for `G ∈ R_M[t]` whose `t`-coefficients are forms of one degree. -/
theorem chartGauss_val_map {v : X.an} {j : Fin (M + 1)} (hv : v.1.1.val (MvPolynomial.X j) = 1)
    {c : ℕ} {G : (MvPolynomial (Fin (M + 1)) k)[X]} (hG : ∀ ℓ, (G.coeff ℓ).IsHomogeneous c) :
    (chartGauss v j hv).val (G.map (X.quotDehom j).toRingHom) = (gaussExt v.1).val G := by
  rw [chartGauss, Berk.gauss_val_eq_sup_of_subset _ _ _ (Polynomial.support_map_subset _ G),
    ProjBerk.gaussExt_val_apply]
  refine Finset.sup_congr rfl fun ℓ _ => ?_
  rw [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    chartPt_val_quotDehom _ (hG ℓ), hv, one_pow, div_one]

/-- The chart seminorm is `≤ 1` on `B_j`. -/
theorem chartGauss_val_le_one {v : X.an} {j : Fin (M + 1)}
    (hv : v.1.1.val (MvPolynomial.X j) = 1) (F : X.ChartRing j) :
    (chartGauss v j hv).val F ≤ 1 := by
  rw [chartGauss, Berk.gauss_val_le_iff]
  intro ℓ
  obtain ⟨N, τ, hτ, hτF⟩ := exists_quotDehom_eq (F.coeff ℓ)
  rw [← hτF, chartPt_val_quotDehom _ hτ, hv, one_pow, div_one]
  calc v.1.1.val τ * gaussRadius ^ ℓ ≤ 1 * 1 ^ ℓ := by
        gcongr
        · exact ProjBerk.val_le_one v.1 τ
        · exact ProjBerk.gaussRadius_le_one
    _ = 1 := by simp

end ChartGauss

/-! ### Bihomogeneous generators and their dehomogenizations -/

section Generators

variable {ι : Type*} (s : ι → MvPolynomial (Fin (M + 1)) k) (e : ι → ℕ)

variable (X) in
/-- The dehomogenized generators `gᵢ^{(j)} = δⱼ(sᵢ t^{eᵢ}) ∈ B_j` of `𝔦^{(j)}`. -/
def dehomGen (j : Fin (M + 1)) (i : ι) : X.ChartRing j :=
  (coneGen s e i).map (X.quotDehom j).toRingHom

theorem dehomGen_eq (j : Fin (M + 1)) (i : ι) :
    X.dehomGen s e j i = Polynomial.C (X.quotDehom j (s i)) * Polynomial.X ^ (e i) := by
  simp [dehomGen, coneGen, Polynomial.map_mul, Polynomial.map_pow]

/-- **`lem:sg-finite-fs`, `t^N ∈ 𝔦^{(j)}`**: if the forms `sᵢ` have no common zero on `X^an`, then
`t^N ∈ 𝔦^{(j)} = (gᵢ^{(j)})` for `N = max_i eᵢ` in every chart `j`. -/
theorem X_pow_mem_span_dehomGen [Fintype ι] (hs : ∀ i, ∃ d, (s i).IsHomogeneous d)
    (hz : ∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0) (j : Fin (M + 1)) :
    ∃ N : ℕ, (Polynomial.X : X.ChartRing j) ^ N ∈ Ideal.span (Set.range (X.dehomGen s e j)) := by
  obtain ⟨E, hE⟩ := X_mem_radical_span_sup hs hz j
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hE
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
  set N := Finset.univ.sup e
  refine ⟨N, Ideal.mem_span_range_iff_exists_fun.2
    ⟨fun i => Polynomial.C (X.quotDehom j (c i)) * Polynomial.X ^ (N - e i), ?_⟩⟩
  have h1 : ∑ i, X.quotDehom j (c i) * X.quotDehom j (s i) = 1 := by
    simp_rw [← map_mul]
    rw [← map_sum, hc]
    have := congrArg (X.quotDehom j) hab
    rw [map_add, quotDehom_eq_zero_of_mem hb, add_zero, map_pow, quotDehom_X_self,
      one_pow] at this
    exact this
  calc ∑ i, Polynomial.C (X.quotDehom j (c i)) * Polynomial.X ^ (N - e i) * X.dehomGen s e j i
      = ∑ i, Polynomial.C (X.quotDehom j (c i) * X.quotDehom j (s i)) * Polynomial.X ^ N := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hX : (Polynomial.X : X.ChartRing j) ^ (N - e i) * Polynomial.X ^ e i =
            Polynomial.X ^ N := by
          rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ i))]
        rw [dehomGen_eq, Polynomial.C_mul, ← hX]
        ring
    _ = Polynomial.X ^ N := by
        rw [← Finset.sum_mul, ← map_sum, h1, Polynomial.C_1, one_mul]

end Generators

/-! ### Rees valuations of `𝔦^{(j)}` and their divisorial points -/

section Rees

variable [IsAlgClosed k] {ι : Type*} [Fintype ι] (s : ι → MvPolynomial (Fin (M + 1)) k)
  (e : ι → ℕ)

variable (X) in
/-- The fraction field `Frac B_j` of the chart ring. -/
abbrev ChartFrac (j : X.ChartIdx) : Type u := FractionRing (X.ChartRing j.1)

/-- The normalized charts of the blowup of `𝔦^{(j)}` are Noetherian (finiteness of
normalization). -/
theorem isNoetherianRing_reesNormalChart_dehomGen (j : X.ChartIdx) (ℓ : ι) :
    IsNoetherianRing (reesNormalChart (X.ChartFrac j) (X.dehomGen s e j.1) ℓ) :=
  isNoetherianRing_reesNormalChart (X.ChartFrac j) (X.dehomGen s e j.1) k ℓ

attribute [local instance] isNoetherianRing_reesNormalChart_dehomGen

theorem finite_reesIndex_dehomGen (j : X.ChartIdx) :
    Finite (ReesIndex (X.ChartFrac j) (X.dehomGen s e j.1)) :=
  finite_reesIndex

attribute [local instance] finite_reesIndex_dehomGen

/-- The Rees valuation ring `V` of `(𝔦^{(j)}; g^{(j)})` attached to `x`, as a discrete valuation
ring birational to `B_j`, essentially of finite type over `k` (`def:bj-rees`). -/
def reesDVR (j : X.ChartIdx) (x : ReesIndex (X.ChartFrac j) (X.dehomGen s e j.1)) :
    BirationalDVR k (X.ChartRing j.1) :=
  haveI := essFiniteType_reesValuationRing k x
  BirationalDVR.ofSubalgebra (reesValuationRing _ _ x)

theorem reesDVR_ord (j : X.ChartIdx) (x : ReesIndex (X.ChartFrac j) (X.dehomGen s e j.1))
    (b : X.ChartRing j.1) :
    (reesDVR s e j x).ord b = addVal (reesValuationRing _ _ x) (algebraMap _ _ b) :=
  rfl

/-- `b = ord_V(t)` as a natural number. -/
def reesOrdX (j : X.ChartIdx) (x : ReesIndex (X.ChartFrac j) (X.dehomGen s e j.1)) : ℕ :=
  ((reesDVR s e j x).ord Polynomial.X).toNat

/-- The divisorial point `v_V ∈ X^an` attached to a Rees valuation ring `V` of `𝔦^{(j)}`
(`lem:sg-div-points`(2)). -/
def reesPoint (j : X.ChartIdx) (x : ReesIndex (X.ChartFrac j) (X.dehomGen s e j.1)) : X.an :=
  X.chartDivPoint j.1 (reesDVR s e j x) (reesOrdX s e j x)

variable (j : X.ChartIdx) (x : ReesIndex (X.ChartFrac j) (X.dehomGen s e j.1))

theorem coe_reesOrdX : ((reesOrdX s e j x : ℕ) : ℕ∞) = (reesDVR s e j x).ord Polynomial.X :=
  ENat.natCast_toNat ((reesDVR s e j x).ord_eq_top_iff.not.2 Polynomial.X_ne_zero)

/-- `ord_V(t) > 0` (**`lem:sg-rees-invariant`**), using `t^N ∈ 𝔦^{(j)}`. -/
theorem reesOrdX_pos
    (hN : ∃ N : ℕ, (Polynomial.X : X.ChartRing j.1) ^ N ∈
      Ideal.span (Set.range (X.dehomGen s e j.1))) :
    0 < reesOrdX s e j x := by
  have h := addVal_X_pos_reesValuationRing hN x
  rw [← reesDVR_ord, ← coe_reesOrdX] at h
  exact_mod_cast h

/-- **`lem:sg-rees-invariant`** (torus invariance of the Rees valuations):
`ord_V(∑_ℓ f_ℓ t^ℓ) = min_ℓ (ord_V(f_ℓ) + ℓ ord_V(t))`. -/
theorem reesDVR_torus (F : X.ChartRing j.1) :
    (reesDVR s e j x).ord F = F.support.inf fun ℓ =>
      (reesDVR s e j x).ord (Polynomial.C (F.coeff ℓ)) +
        ((ℓ * reesOrdX s e j x : ℕ) : ℕ∞) := by
  have hg : ∀ i, ∃ (a : X.ChartAlg j.1) (m : ℕ),
      X.dehomGen s e j.1 i = Polynomial.C a * Polynomial.X ^ m :=
    fun i => ⟨_, _, dehomGen_eq s e j.1 i⟩
  rw [reesDVR_ord, addVal_reesValuationRing_eq_inf k hg x F]
  refine Finset.inf_congr rfl fun ℓ _ => ?_
  rw [← reesDVR_ord, ← reesDVR_ord, ← coe_reesOrdX, Nat.cast_mul, nsmul_eq_mul]

variable {s e j}

/-- The points `v_V` are divisorial (`lem:sg-div-points`(2)). -/
theorem isDivisorial_reesPoint
    (hN : ∃ N : ℕ, (Polynomial.X : X.ChartRing j.1) ^ N ∈
      Ideal.span (Set.range (X.dehomGen s e j.1))) :
    X.IsDivisorial (reesPoint s e j x) :=
  isDivisorial_chartDivPoint _ _ (reesOrdX_pos s e j x hN) (reesDVR_torus s e j x)

/-- `|G|_{σ(v_V)} = e^{-ord_V(G^{(j)})/b}` for `G ∈ R_M[t]` whose `t`-coefficients are forms of
one degree. -/
theorem gaussExt_reesPoint_val
    (hN : ∃ N : ℕ, (Polynomial.X : X.ChartRing j.1) ^ N ∈
      Ideal.span (Set.range (X.dehomGen s e j.1)))
    {c : ℕ} {G : (MvPolynomial (Fin (M + 1)) k)[X]} (hG : ∀ ℓ, (G.coeff ℓ).IsHomogeneous c) :
    (gaussExt (reesPoint s e j x : ProjBerk k M)).val G =
      expOrd (expNeg (reesOrdX s e j x : ℝ)⁻¹)
        ((reesDVR s e j x).ord (G.map (X.quotDehom j.1).toRingHom)) := by
  have hb := reesOrdX_pos s e j x hN
  have h := logAbs_gaussExt_chartDivPoint (reesDVR s e j x) (reesOrdX s e j x) hb
    (reesDVR_torus s e j x) hG
  rw [Berk.logAbs, ← log_expOrd_expNeg (inv_pos.2 (Nat.cast_pos.2 hb))] at h
  exact ENNReal.coe_injective (ENNReal.log_injective h)

/-- At a point `v_V ∈ Σ`, the inequality `|F|_{σ(v_V)} ≤ ‖𝔦‖_{σ(v_V)}^r` says
`ord_V(F^{(j)}) ≥ r ord_V(𝔦^{(j)})`, i.e. `(gᵢ^{(j)})^r ∣ F^{(j)}` in `V` for some `i`. -/
theorem exists_dvd_of_le_reesPoint {d : ℕ} (hs : ∀ i, (s i).IsHomogeneous d) [Nonempty ι]
    (hN : ∃ N : ℕ, (Polynomial.X : X.ChartRing j.1) ^ N ∈
      Ideal.span (Set.range (X.dehomGen s e j.1)))
    {c : ℕ} {F : (MvPolynomial (Fin (M + 1)) k)[X]} (hF : ∀ ℓ, (F.coeff ℓ).IsHomogeneous c)
    {r : ℕ}
    (h : (gaussExt (reesPoint s e j x : ProjBerk k M)).val F ≤
      (Finset.univ.sup fun i => (gaussExt (reesPoint s e j x : ProjBerk k M)).val
        (coneGen s e i)) ^ r) :
    ∃ i, algebraMap (X.ChartRing j.1)
        (reesValuationRing (X.ChartFrac j) (X.dehomGen s e j.1) x) (X.dehomGen s e j.1 i) ^ r ∣
      algebraMap (X.ChartRing j.1) (reesValuationRing (X.ChartFrac j) (X.dehomGen s e j.1) x)
        (F.map (X.quotDehom j.1).toRingHom) := by
  set V := reesDVR s e j x
  set q := expNeg ((reesOrdX s e j x : ℝ)⁻¹)
  have hb := reesOrdX_pos s e j x hN
  have hq0 : 0 < q := zero_lt_expNeg _
  have hq1 : q < 1 := expNeg_lt_one_of_pos (inv_pos.2 (Nat.cast_pos.2 hb))
  have hg : ∀ i, (gaussExt (reesPoint s e j x : ProjBerk k M)).val (coneGen s e i) =
      expOrd q (V.ord (X.dehomGen s e j.1 i)) := fun i =>
    gaussExt_reesPoint_val x hN (ProjBerk.isHomogeneous_coeff_coneGen s e hs i)
  rw [gaussExt_reesPoint_val x hN hF] at h
  simp only [hg] at h
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i => V.ord (X.dehomGen s e j.1 i)) Finset.univ_nonempty
  have hsup : (Finset.univ.sup fun i => expOrd q (V.ord (X.dehomGen s e j.1 i))) =
      expOrd q (V.ord (X.dehomGen s e j.1 i₀)) :=
    le_antisymm (Finset.sup_le fun i _ => expOrd_antitone hq1.le (hi₀ i (Finset.mem_univ i)))
      (Finset.le_sup (f := fun i => expOrd q (V.ord (X.dehomGen s e j.1 i))) (Finset.mem_univ i₀))
  rw [hsup, ← expOrd_nsmul] at h
  have hle := le_of_expOrd_le hq0 hq1 h
  refine ⟨i₀, ?_⟩
  rw [← map_pow, ← addVal_le_iff_dvd, map_pow, addVal_pow]
  exact hle

variable (s e) in
/-- **The Shilov boundary on `X`, core form** (`lem:sg-shilov`): for forms `sᵢ` of degree `d`
without common zero on `X^an` and `eᵢ ∈ ℕ`, let `gᵢ = sᵢ t^{eᵢ}`. There is a finite set `Σ` of
divisorial points of `X`, containing `⋆`, such that for every `F ∈ R_M[t]` whose `t`-coefficients
are forms of one degree and every `r ∈ ℕ`: if `|F|_{σ(w)} ≤ max_i |gᵢ|_{σ(w)}^r` for all `w ∈ Σ`,
then `|F|_{σ(v)} ≤ max_i |gᵢ|_{σ(v)}^r` for all `v ∈ X^an`. -/
theorem exists_finset_shilov_core {d : ℕ} (hs : ∀ i, (s i).IsHomogeneous d)
    (hz : ∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (c : ℕ) (F : (MvPolynomial (Fin (M + 1)) k)[X]), (∀ ℓ, (F.coeff ℓ).IsHomogeneous c) →
        ∀ r : ℕ, (∀ w ∈ S, (gaussExt w.1).val F ≤
          (Finset.univ.sup fun i => (gaussExt w.1).val (coneGen s e i)) ^ r) →
        ∀ v : X.an, (gaussExt v.1).val F ≤
          (Finset.univ.sup fun i => (gaussExt v.1).val (coneGen s e i)) ^ r := by
  have hN : ∀ j : X.ChartIdx, ∃ N : ℕ, (Polynomial.X : X.ChartRing j.1) ^ N ∈
      Ideal.span (Set.range (X.dehomGen s e j.1)) := fun j =>
    X_pow_mem_span_dehomGen s e (fun i => ⟨d, hs i⟩) hz j.1
  have : Nonempty ι := let ⟨i, _⟩ := hz X.triv; ⟨i⟩
  have hfin : (insert X.triv (⋃ j : X.ChartIdx, Set.range (reesPoint s e j)) :
      Set X.an).Finite :=
    (Set.finite_iUnion fun j => Set.finite_range _).insert _
  have hmem : ∀ (j : X.ChartIdx) x, reesPoint s e j x ∈ hfin.toFinset := fun j x =>
    hfin.mem_toFinset.2 (Or.inr (Set.mem_iUnion.2 ⟨j, x, rfl⟩))
  refine ⟨hfin.toFinset, hfin.mem_toFinset.2 (Or.inl rfl), fun w hw => ?_,
    fun c F hF r h v => ?_⟩
  · rcases hfin.mem_toFinset.1 hw with rfl | hw
    · exact isDivisorial_triv X
    · obtain ⟨j, x, rfl⟩ := Set.mem_iUnion.1 hw
      exact isDivisorial_reesPoint x (hN j)
  · obtain ⟨j₀, hj⟩ := ProjBerk.exists_val_X_eq_one v.1
    have hjI : MvPolynomial.X j₀ ∉ X.ideal :=
      notMem_ideal_of_val_ne_zero (val_X_ne_zero_of_eq_one hj)
    have : Fact (MvPolynomial.X j₀ ∉ X.ideal) := ⟨hjI⟩
    have : ∀ ℓ, IsNoetherianRing
        (reesNormalChart (FractionRing (X.ChartRing j₀)) (X.dehomGen s e j₀) ℓ) := fun ℓ =>
      isNoetherianRing_reesNormalChart (FractionRing (X.ChartRing j₀)) (X.dehomGen s e j₀) k ℓ
    have hwg : ∀ i, (chartGauss v j₀ hj).val (X.dehomGen s e j₀ i) =
        (gaussExt v.1).val (coneGen s e i) := fun i =>
      chartGauss_val_map hj (ProjBerk.isHomogeneous_coeff_coneGen s e hs i)
    have key := valuation_le_sup_pow_of_forall_dvd (K := FractionRing (X.ChartRing j₀))
      (g := X.dehomGen s e j₀)
      (chartGauss v j₀ hj).val (chartGauss_val_le_one hj) (by
        obtain ⟨i, hi⟩ := hz v
        refine ⟨i, ?_⟩
        rw [hwg, ProjBerk.gaussExt_val_coneGen]
        exact mul_ne_zero hi (pow_ne_zero _ ProjBerk.gaussRadius_ne_zero))
      (F := F.map (X.quotDehom j₀).toRingHom) (r := r)
      fun x => exists_dvd_of_le_reesPoint (j := ⟨j₀, hjI⟩) x hs (hN ⟨j₀, hjI⟩) hF
        (h _ (hmem ⟨j₀, hjI⟩ x))
    rw [chartGauss_val_map hj hF] at key
    simpa only [hwg] using key

end Rees

/-! ### The logarithmic form -/

section ConeSup

variable {ι : Type*} [Fintype ι] (s : ι → MvPolynomial (Fin (M + 1)) k) (e : ι → ℕ)

/-- **The Shilov boundary on `X`, single-term form**: with `Σ` as in `exists_finset_shilov_core`,
for a form `σ`, `z ∈ ℤ` and `r ∈ ℕ`, `log|σ| + z ≤ r φ_𝔦` on `Σ` implies it on `X^an`. -/
theorem exists_finset_shilov_coneSup [IsAlgClosed k] {d : ℕ} (hs : ∀ i, (s i).IsHomogeneous d)
    (hz : ∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (c : ℕ) (σ : MvPolynomial (Fin (M + 1)) k), σ.IsHomogeneous c → ∀ (z : ℤ) (r : ℕ),
        (∀ w ∈ S, logAbs σ w.1 + ((z : ℝ) : EReal) ≤ ((r : ℝ) : EReal) * coneSup s e w.1) →
        ∀ v : X.an, logAbs σ v.1 + ((z : ℝ) : EReal) ≤ ((r : ℝ) : EReal) * coneSup s e v.1 := by
  obtain ⟨S, hS, hSdiv, hcore⟩ := exists_finset_shilov_core s e hs hz
  refine ⟨S, hS, hSdiv, fun c σ hσ z r h v => ?_⟩
  by_cases hσI : σ ∈ X.ideal
  · rw [(ProjBerk.logAbs_eq_bot_iff σ v.1).2 (v.2 σ hσI), EReal.bot_add]
    exact bot_le
  -- evaluation at `⋆ ∈ Σ` gives `z ≤ 0`
  have hz0 : z ≤ 0 := by
    have h1 := h X.triv hS
    rw [X.logAbs_triv_of_notMem hσI, zero_add] at h1
    have h2 : ((r : ℝ) : EReal) * coneSup s e (X.triv : ProjBerk k M) ≤ 0 := by
      have := ProjBerk.ereal_coe_mul_monotone (Nat.cast_nonneg r)
        (ProjBerk.coneSup_le_zero s e (X.triv : ProjBerk k M))
      simpa only [mul_zero] using this
    have h3 : ((z : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := h1.trans h2
    exact_mod_cast EReal.coe_le_coe_iff.1 h3
  set a := z.natAbs
  have hza : ((z : ℝ) : EReal) = -((a : ℕ) : EReal) := by
    have h1 : ((a : ℕ) : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hz0
    have h2 : (z : ℝ) = -((a : ℕ) : ℝ) := by
      have := congrArg (fun m : ℤ => (m : ℝ)) h1
      push_cast at this
      linarith
    rw [h2, EReal.coe_neg]
    rfl
  -- `log|σ| + z = log|σ t^{-z}|_{σ(·)}`
  have key : ∀ w : ProjBerk k M, logAbs σ w + ((z : ℝ) : EReal) =
      Berk.logAbs (Polynomial.C σ * Polynomial.X ^ a) (gaussExt w) := fun w => by
    rw [ProjBerk.logAbs_C_mul_X_pow_gaussExt, hza, sub_eq_add_neg]
  have hF : ∀ ℓ, ((Polynomial.C σ * Polynomial.X ^ a :
      (MvPolynomial (Fin (M + 1)) k)[X]).coeff ℓ).IsHomogeneous c := fun ℓ => by
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · exact hσ
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  rw [key, ProjBerk.logAbs_le_mul_coneSup_iff]
  refine hcore c _ hF r (fun w hw => ?_) v
  rw [← ProjBerk.logAbs_le_mul_coneSup_iff, ← key]
  exact h w hw

end ConeSup

/-! ### Normal form of finite Fubini–Study functions on `X` (`lem:sg-finite-fs`) -/

/-- **Normal form of a finite Fubini–Study function on `X`** (`lem:sg-finite-fs`): after clearing
the denominators of the weights and subtracting the largest one, `ψ ∈ 𝓗_fin(X, b)` is
`K⁻¹ (φ_𝔦 + Z)` on `X^an`, with `K ∈ ℤ_{>0}`, `Z ∈ ℤ` and `φ_𝔦 = max_i log|sᵢ t^{eᵢ}|_{σ(·)}`
(`ProjBerk.coneSup`) for forms `sᵢ` of one degree without common zero on `X^an`, and `eᵢ ∈ ℕ`. -/
theorem IsFinFS.exists_coneSup {b : ℚ} {ψ : X.an → EReal} (hψ : X.IsFinFS b ψ) :
    ∃ (ι : Type u) (_ : Fintype ι) (s : ι → MvPolynomial (Fin (M + 1)) k) (d : ℕ) (e : ι → ℕ)
      (K : ℕ) (Z : ℤ), 0 < K ∧ (∀ i, (s i).IsHomogeneous d) ∧
        (∀ v : X.an, ∃ i, v.1.1.val (s i) ≠ 0) ∧
        ∀ v : X.an, ψ v = (((K : ℝ)⁻¹ : ℝ) : EReal) * (coneSup s e v.1 + ((Z : ℝ) : EReal)) := by
  obtain ⟨D, hD, hfin, hψD⟩ := hψ
  obtain ⟨L, hL, hLz⟩ := ProjBerk.exists_pos_nat_mul_eq_int D.terms (fun t => t.2) hD
  choose z hz using hLz
  have hne : (Finset.univ : Finset D.terms).Nonempty := by
    obtain ⟨t, ht, -⟩ := D.exists_ne_zero
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  set zf : D.terms → ℤ := fun i => z i.1 i.2 with hzf
  set Z : ℤ := Finset.univ.sup' hne zf with hZdef
  have hZ : ∀ i, zf i ≤ Z := fun i => Finset.le_sup' zf (Finset.mem_univ i)
  set e : D.terms → ℕ := fun i => (Z - zf i).toNat with he_def
  set s : D.terms → MvPolynomial (Fin (M + 1)) k := fun i => i.1.1 ^ L with hs_def
  have he : ∀ i, ((e i : ℕ) : ℝ) = (Z : ℝ) - (zf i : ℝ) := fun i => by
    have : ((e i : ℕ) : ℤ) = Z - zf i := Int.toNat_of_nonneg (by linarith [hZ i])
    exact_mod_cast this
  -- `L (log|sᵢ| + λᵢ) = log|sᵢ^L t^{eᵢ}|_{σ(·)} + Z`
  have hterm : ∀ (i : D.terms) (v : ProjBerk k M), ((L : ℝ) : EReal) * ProjBerk.termVal i.1 v =
      Berk.logAbs (coneGen s e i) (gaussExt v) + ((Z : ℝ) : EReal) := fun i v => by
    rw [coneGen, ProjBerk.logAbs_C_mul_X_pow_gaussExt, ProjBerk.termVal_def,
      ProjBerk.ereal_coe_mul_add (Nat.cast_nonneg L), ← EReal.coe_mul, hz i.1 i.2]
    change _ = logAbs (i.1.1 ^ L) v - ((e i : ℝ) : EReal) + ((Z : ℝ) : EReal)
    rw [ereal_sub_coe_add_coe, ProjBerk.logAbs_pow, he]
    congr 2
    simp [hzf]
  refine ⟨D.terms, inferInstance, s, D.deg * L, e, L * D.m, Z, Nat.mul_pos hL D.m_pos,
    fun i => (D.isHomogeneous i.1 i.2).pow L, fun v => ?_, fun v => ?_⟩
  · obtain ⟨t, ht, hv⟩ := hfin v.1 v.2
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [hs_def, map_pow]
    exact pow_ne_zero _ hv
  · have hsup : coneSup s e v.1 + ((Z : ℝ) : EReal) =
        ((L : ℝ) : EReal) * D.terms.sup fun t => ProjBerk.termVal t v.1 := by
      rw [coneSup, Finset.apply_sup_eq_sup_comp_of_linearOrder (s := Finset.univ)
        (fun x : EReal => x + ((Z : ℝ) : EReal)) (fun _ _ h => add_le_add_left h _)
        (EReal.bot_add _), ProjBerk.ereal_coe_mul_finset_sup (by exact_mod_cast hL)]
      rw [← Finset.sup_attach D.terms, ← Finset.univ_eq_attach]
      exact Finset.sup_congr rfl fun i _ => (hterm i v.1).symm
    rw [hψD v, hsup, ProjBerk.ereal_coe_mul_coe_mul, ProjBerk.FSData.eval_def]
    congr 2
    push_cast
    field_simp [D.m_ne_zero]

/-! ### The Shilov boundary lemma (`lem:sg-shilov`) -/

variable [IsAlgClosed k]

/-- **The Shilov boundary on `X`, comparison form** (`lem:sg-shilov`): for `ψ ∈ 𝓗_fin(X, b)` there
is a finite set `Σ ⊆ X^div` containing `⋆` such that every Fubini–Study function `φ` of any class
`a` with rational weights (given by data `D` on `ℙᴹ` restricted to `X^an`) with `φ ≤ ψ` on `Σ`
satisfies `φ ≤ ψ` on `X^an`. -/
theorem IsFinFS.exists_finset_le_of_le {b : ℚ} {ψ : X.an → EReal} (hψ : X.IsFinFS b ψ) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (a : ℚ) (D : ProjBerk.FSData k M a), D.IsRational → (∀ w ∈ S, D.eval w.1 ≤ ψ w) →
        ∀ v : X.an, D.eval v.1 ≤ ψ v := by
  have hψfin := hψ.ne_bot
  obtain ⟨ι, _, s, d, e, K, Z, hK, hs, hz, hψe⟩ := hψ.exists_coneSup
  obtain ⟨S, hS, hSdiv, hB⟩ := exists_finset_shilov_coneSup s e hs hz
  refine ⟨S, hS, hSdiv, fun a D' hD' h v => ?_⟩
  obtain ⟨Q, hQ, hQz⟩ := ProjBerk.exists_pos_nat_mul_eq_int D'.terms (fun t => t.2) hD'
  choose w hw using hQz
  have hPbot : ∀ v : X.an, coneSup s e v.1 ≠ ⊥ := fun v h0 => hψfin v (by
    rw [hψe v, h0, EReal.bot_add]
    exact EReal.coe_mul_bot_of_pos (inv_pos.2 (by exact_mod_cast hK)))
  have hPtop : ∀ v : X.an, coneSup s e v.1 ≠ ⊤ := fun v =>
    ne_top_of_le_ne_top EReal.zero_ne_top (ProjBerk.coneSup_le_zero s e v.1)
  -- each term `m'⁻¹ (log|σ| + μ)` of `φ` gives a single inequality `log|σ^{KQ}| + z ≤ r φ_𝔦`
  have key : ∀ t (ht : t ∈ D'.terms) (v : X.an),
      (((D'.m : ℝ)⁻¹ : ℝ) : EReal) * ProjBerk.termVal t v.1 ≤ ψ v ↔
        logAbs (t.1 ^ (K * Q)) v.1 + (((K * w t ht - D'.m * Q * Z : ℤ) : ℝ) : EReal) ≤
          (((D'.m * Q : ℕ) : ℝ) : EReal) * coneSup s e v.1 := fun t ht v => by
    rw [hψe v, ProjBerk.termVal_def, ProjBerk.logAbs_pow]
    exact ProjBerk.fsTerm_le_iff (ProjBerk.logAbs_ne_top _ _) (hPbot v) (hPtop v) D'.m_pos hK hQ
      (hw t ht)
  rw [ProjBerk.FSData.eval_def, ProjBerk.ereal_coe_mul_finset_sup D'.inv_m_pos, Finset.sup_le_iff]
  intro t ht
  rw [key t ht v]
  refine hB _ _ ((D'.isHomogeneous t ht).pow _) _ _ (fun w' hw' => ?_) v
  rw [← key t ht w']
  exact (D'.termVal_le_eval_mul w'.1 ht).trans (h w' hw')

/-- **The Shilov boundary on `X`** (**`lem:sg-shilov`**, BJ22 Shilov): for every
`ψ ∈ 𝓗_fin(X, b)` there is a finite set `Σ ⊆ X^div` containing `⋆` such that
`sup_{X^an} (φ - ψ) = max_Σ (φ - ψ)` for every `a ∈ ℚ` and every Fubini–Study function `φ` of
class `a` on `X^an` with rational weights (`φ = D.eval` for rational data `D`). -/
theorem IsFinFS.exists_finset_iSup_sub_eq {b : ℚ} {ψ : X.an → EReal} (hψ : X.IsFinFS b ψ) :
    ∃ S : Finset X.an, X.triv ∈ S ∧ (∀ w ∈ S, X.IsDivisorial w) ∧
      ∀ (a : ℚ) (φ : X.an → EReal),
        (∃ D : ProjBerk.FSData k M a, D.IsRational ∧ ∀ v : X.an, φ v = D.eval v.1) →
        ⨆ v, (φ v - ψ v) = S.sup fun v => φ v - ψ v := by
  obtain ⟨S, hS, hSdiv, hle⟩ := hψ.exists_finset_le_of_le
  refine ⟨S, hS, hSdiv, fun a φ hφ => le_antisymm (iSup_le fun v => ?_)
    (Finset.sup_le fun w _ => le_iSup (fun v => φ v - ψ v) w)⟩
  obtain ⟨D, hD, hφD⟩ := hφ
  have hψr : ∀ v, ψ v = (((ψ v).toReal : ℝ) : EReal) := fun v =>
    (hψ.coe_toReal v).symm
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨q, hMq, hqc⟩ := EReal.lt_iff_exists_rat_btwn.1 hc
  -- apply the comparison form to `φ - q`
  obtain ⟨D', hD', hD'eq⟩ := (ProjBerk.IsRatFS.add_const ⟨D, hD, rfl⟩ (-q) :
    ProjBerk.IsRatFS a fun v => D.eval v + (((-q : ℚ) : ℝ) : EReal))
  have hD'v : ∀ v : ProjBerk k M, D'.eval v = D.eval v + (((-q : ℚ) : ℝ) : EReal) := fun v =>
    (congrFun hD'eq v).symm
  have h := hle a D' hD' (fun w hw => by
    have h1 : φ w - ψ w ≤ ((q : ℝ) : EReal) :=
      (Finset.le_sup (f := fun v => φ v - ψ v) hw).trans hMq.le
    rw [hψr w, hφD w] at h1
    rw [hψr w, hD'v]
    rw [ereal_sub_coe_le_coe_iff] at h1
    simpa only [Rat.cast_neg] using h1) v
  have h2 : φ v - ψ v ≤ ((q : ℝ) : EReal) := by
    rw [hψr v, hφD v]
    rw [hψr v, hD'v] at h
    rw [ereal_sub_coe_le_coe_iff]
    simpa only [Rat.cast_neg] using h
  exact h2.trans hqc.le

end ProjSubvariety

end EnvelopeProperty
