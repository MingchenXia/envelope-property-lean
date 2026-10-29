/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.NonflatIdentification
import EnvelopeProperty.Local.ProjectionChartRegularizable
import EnvelopeProperty.Projective.EnvelopePn

/-!
# Nonflat norms of functions regularizable on blowup charts (FHX Proposition 5.22)

This file formalizes `prop:nf-nonflat-norm` of the blueprint chapter `nonflat-route.tex`:
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (FHX), Proposition 5.22
(`prop:nonflat-norm`; Section 5, `sec:normal-local-regularization`) for the functions regularizable on the charts of a blowup
(`IsChartRegularizable`, `def:nf-chart-regularizable`), the class to which FHX Corollary 5.26
(`cor:normal-weak-global`) applies Theorem 5.25. It discharges the hypothesis class
`ChartNonflatNorms` of `Local/ProjectionChartRegularizable` (in one universe, as used by
`ProjSubvariety.isPSH_of_isPSH_comp_proj`), conditional only on the imported FHX Lemma 5.11(5),(6)
(`WuRegularization k`, an explicit instance argument, not an axiom).

## Setting (`conv:nf-setting`)

`Y = Spec A` is a normal affine variety over the countable algebraically closed trivially valued
field `k`, `S = Spec B ≅ Spec k[x]_{h_S}` a principal open of `𝔸ⁿ` (`n ≥ 1`), `φ: B → A` finite,
injective and generically étale of degree `d = genericDegree φ`, and `Z = V(S) ⊊ Y`. The weights
`m_y(π) = nonflatWeight φ hφ h y` (`def:nf-weights`) are defined from a good locus
element `h` (`IsNonflatGoodLocus`, `lem:nf-good-locus`), `S_0 = S_h`, `Y_0 = Y_{φ(h)}`, and
`N_π u = nonflatNorm φ hφ h u`.

## Main results

* `hasLogGrowth_nonflatNorm`: `N_π u` has logarithmic growth if `u` has (`lem:growth`(2) and
  `∑_{π(y) = s} m_y = d`).
* `IsChartRegularizable.isRegularizable_awayComap_goodLocus`: `u|_{Y_0} ∈ ℛ(Y_0)` (`prop:gluing`(2):
  `Y_0` misses `Z` and is covered by principal opens on which `u` is regularizable).
* **`prop:nf-nonflat-norm`**: `IsChartRegularizable.isRegularizable_nonflatNorm`: `N_π u ∈ ℛ(S)`
  for `u` regularizable on the charts of a blowup, of logarithmic growth, and regularizable on
  principal opens covering `Y^an \ Z^an`. Proof as in the blueprint: `v₀ = N_{π|_{Y_0}} u ∈ ℛ(S_0)`
  (`IsRegularizable.flatNormFun_of_free` for the finite free `B_h → A_{φ(h)}`), `v₀ = N_π u` on
  `S_0^an` (`nonflatNorm_awayComap`), the growth bound, the extension `v ∈ ℛ(S)` of `v₀`
  (`lem:nonflat-extension`, `IsRegularizable.exists_extend_of_isAffineSpacePrincipalOpen` with the
  envelope property of `ℙⁿ`, `ProjBerk.hasEnvelopeProperty_of_countable`), and
  `prop:nf-identification` (`IsChartRegularizable.eq_nonflatNorm`).
* `nonempty_normWeights_isChartRegularizable`: the weights as `NormWeights φ S IsChartRegularizable d`
  (with `m_y ≥ 1` and `∑ m_y = d` from `nonflatNormWeights`).
* The instance `ChartNonflatNorms.of_wuRegularization: ChartNonflatNorms.{u, u, u} k` from
  `WuRegularization.{u, u} k`. It does not loop with `ChartNonflatNorms.of_nonflatNorms` (no
  instance produces `NonflatNorms` or `WuRegularization` from `ChartNonflatNorms`);
  `WuRegularization` is found from `ConvexPLApproximation` (`ConvexPLApproximation.toWuRegularization`)
  and from `LocalPositivity` (`LocalPositivity.toConvexPLApproximation`).

## Comparison with the blueprint

* Over `S_0` the norm is taken in the flat form (`IsRegularizable.flatNormFun_of_free` along the
  finite free `B_h → A_{φ(h)}`) instead of the étale form of `lem:finite-etale-norm`; the two agree
  there (`IsNonflatGoodLocus.nonflatNorm_awayComap_eq_normFun`).
* The growth bound `v₀ ≤ g ∘ ι + C` with `g ∈ FS(S)` is obtained from the logarithmic growth of
  `N_π u` on all of `S^an` (`hasLogGrowth_nonflatNorm`), which uses `∑_{π(y) = s} m_y = d` for every
  `s` (not only over `S_0`).
* Generic étaleness enters only through the existence of a good locus element
  (`exists_isNonflatGoodLocus`).
-/

open scoped NNReal ENNReal Topology TensorProduct

noncomputable section

universe u

namespace EnvelopeProperty

open Berk

/-! ### Logarithmic growth of the norm -/

section Growth

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Type u} [CommRing A] [IsDomain A]
  [Algebra k A] [CommRing B] [Algebra k B]

/-- **The norm of a function of logarithmic growth has logarithmic growth** (`prop:nf-nonflat-norm`,
proof; `lem:growth`(2)). If `u ≤ g + C₀` with `g ∈ FS(Y)`, then `g ≤ C h_std ∘ π + C'` for the
standard FS function `h_std ≥ 0` of `S` (FHX Lemma 5.8(2)), and the weights over every point add
up to `d` (`sum_nonflatWeight`); so `N_π u ≤ d C h_std + d (|C'| + |C₀|)`. -/
theorem hasLogGrowth_nonflatNorm {n : ℕ} (hn : 1 ≤ n) (hB : IsAffineSpacePrincipalOpen k B n)
    (φ : B →ₐ[k] A) (hinj : Function.Injective φ) (hφ : (φ : B →+* A).Finite) {S : Finset A}
    {h : B} (hh : IsNonflatGoodLocus φ S h) {u : Berk k A → EReal} (hu : HasLogGrowth u) :
    HasLogGrowth (nonflatNorm φ hφ h u) := by
  have := hB.finiteType
  obtain ⟨g, C₀, hg⟩ := hu
  obtain ⟨C, C', hC, hCg⟩ :=
    FSData.exists_eval_le_comap_of_isIntegral φ hφ.to_isIntegral g (FSData.std k B)
  set d : ℝ := (genericDegree (φ : B →+* A) : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  refine (((FSData.std k B).hasLogGrowth.smul (c := d * C) (by positivity)).add_const
    (d * (|C'| + |C₀|))).mono fun s => ?_
  set e := (FSData.std k B).evalReal s with he
  have he0 : 0 ≤ e := FSData.evalReal_std_nonneg k B s
  set M : ℝ := C * e + (|C'| + |C₀|) with hM
  have hM0 : 0 ≤ M := add_nonneg (mul_nonneg hC he0) (by positivity)
  have hle : ∀ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset, u y ≤ (M : EReal) := by
    intro y hy
    have hy0 := (Set.Finite.mem_toFinset _).1 hy
    have hy' : comap φ y = s := hy0
    refine (hg y).trans ?_
    have h1 := hCg y
    rw [hy', ← (FSData.std k B).coe_evalReal s, ← he] at h1
    rw [← g.coe_evalReal] at h1 ⊢
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [hM]
    linarith [le_abs_self C', le_abs_self C₀]
  calc nonflatNorm φ hφ h u s
      ≤ ∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
          ((nonflatWeight φ hφ h y : ℝ) : EReal) * (M : EReal) :=
        Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hle y hy) (by positivity)
    _ = ((∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
          (nonflatWeight φ hφ h y : ℝ)) * M : ℝ) := by
        rw [Finset.sum_mul, ereal_coe_finsetSum]
        simp only [EReal.coe_mul]
    _ = ((d * C : ℝ) : EReal) * (FSData.std k B).eval s + ((d * (|C'| + |C₀|) : ℝ) : EReal) := by
        rw [← Nat.cast_sum, sum_nonflatWeight φ hφ hn hB hinj hh s, ← hd,
          ← (FSData.std k B).coe_evalReal s, ← he, ← EReal.coe_mul, ← EReal.coe_add, hM]
        congr 1
        ring

end Growth

/-! ### Regularity of the norm (`prop:nf-nonflat-norm`) -/

section Regularity

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [WuRegularization.{u, u} k]
  {A B : Type u} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A] [CommRing B] [Algebra k B]

/-- **`u|_{Y_0} ∈ ℛ(Y_0)`** (`prop:nf-nonflat-norm`, proof). The variety `Y_0 = Spec A_{φ(h)}` is
normal, affine and contained in `Y \ Z`, so it is covered by principal opens `(Y_0)_g = Y_{φ(h) g}`
on which `u` is regularizable (FHX Lemma 5.11(4), `IsRegularizable.comp_awayComap_algebraMap`);
`u` is upper semicontinuous (`IsChartRegularizable.upperSemicontinuous`) and of logarithmic growth,
so `u|_{Y_0}` is regularizable by FHX Proposition 5.20(2) (`IsRegularizable.of_cover_principal`). -/
theorem IsChartRegularizable.isRegularizable_awayComap_goodLocus (φ : B →ₐ[k] A)
    (hinj : Function.Injective φ) {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h)
    {u : Berk k A → EReal} (hu : IsChartRegularizable u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable fun y : Berk k (Localization.Away ((φ : B →+* A) h)) =>
      u (awayComap ((φ : B →+* A) h) y) := by
  have hφh : (φ : B →+* A) h ≠ 0 := (map_ne_zero_iff _ hinj).2 hh.ne_zero
  have := isDomain_localizationAway hφh
  have := NonflatExtension.finiteType_localizationAway (k := k) ((φ : B →+* A) h)
  have : IsIntegrallyClosed (Localization.Away ((φ : B →+* A) h)) :=
    isIntegrallyClosed_localizationAway hφh
  refine IsRegularizable.of_cover_principal
    (hu.upperSemicontinuous.comp (continuous_awayComap _))
    (hlog.comp_comap (IsScalarTower.toAlgHom k A (Localization.Away ((φ : B →+* A) h))))
    fun x => ?_
  have hx : (comap φ (awayComap ((φ : B →+* A) h) x)).val h ≠ 0 := awayComap_val_ne_zero _ x
  obtain ⟨g, hg0, hxg, hgreg⟩ := hcover _ (hh.exists_mem_ne_zero hx)
  exact ⟨algebraMap A _ g, (map_ne_zero_iff _ (algebraMap_away_injective hφh)).2 hg0, hxg,
    IsRegularizable.comp_awayComap_algebraMap hφh hg0 hgreg⟩

/-- **Nonflat norms for functions regularizable on blowup charts** (FHX Proposition 5.22,
`prop:nonflat-norm`, in the form `prop:nf-nonflat-norm`), conditional on the imported FHX Lemma
5.11(5),(6) (`WuRegularization k`). Let `B ≅ k[x]_{h_S}` be a principal open of `𝔸ⁿ` (`n ≥ 1`),
`φ : B → A` finite and injective onto a normal domain `A` of finite type, and `h` a good locus
element (`B_h ⊗_B A` finite free étale over `B_h`, `φ(h) ∈ (S)`). If `u` is regularizable on the
charts of a blowup, of logarithmic growth, and regularizable on principal opens covering
`Y^an \ Z^an`, `Z = V(S)`, then `N_π u = ∑_{π(y) = ·} m_y(π) u(y)` is regularizable on `S`. -/
theorem IsChartRegularizable.isRegularizable_nonflatNorm {n : ℕ} (hn : 1 ≤ n)
    (hB : IsAffineSpacePrincipalOpen k B n) (φ : B →ₐ[k] A) (hinj : Function.Injective φ)
    (hφ : (φ : B →+* A).Finite) {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h)
    {u : Berk k A → EReal} (hu : IsChartRegularizable u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable (nonflatNorm φ hφ h u) := by
  have := hB.isDomain
  have := hB.isIntegrallyClosed
  have := hB.finiteType
  -- `v₀ = N_{π|_{Y_0}} (u|_{Y_0}) ∈ ℛ(S_0)` along the finite free `B_h → A_{φ(h)}`
  let := (Localization.awayMap (φ : B →+* A) h).toAlgebra
  have := nonflat_awayMap_isScalarTower φ h
  have := nonflat_awayMap_moduleFinite φ hφ h
  have := hh.awayMap_free
  have := isDomain_localizationAway hh.ne_zero
  have := hh.isDomain_away hinj
  have := NonflatExtension.finiteType_localizationAway (k := k) h
  have : IsIntegrallyClosed (Localization.Away h) :=
    isIntegrallyClosed_localizationAway hh.ne_zero
  have hv₀ := (hu.isRegularizable_awayComap_goodLocus φ hinj hh hlog hcover).flatNormFun_of_free
    (B := Localization.Away h)
  -- the growth bound and the extension of `v₀` to `v ∈ ℛ(S)` (`lem:nonflat-extension`)
  obtain ⟨g, C, hgC⟩ := hasLogGrowth_nonflatNorm hn hB φ hinj hφ hh hlog
  obtain ⟨v, hvreg, hvext⟩ := IsRegularizable.exists_extend_of_isAffineSpacePrincipalOpen hn hB
    (fun _ ha => ProjBerk.hasEnvelopeProperty_of_countable n (by exact_mod_cast ha.le))
    hh.ne_zero hv₀ g C fun y => by
      rw [← nonflatNorm_awayComap φ hφ h u y]
      exact hgC _
  -- `v = N_π u` on `S_0^an`, hence on `S^an` (`prop:nf-identification`)
  have hv : ∀ s : Berk k B, s.val h ≠ 0 → v s = nonflatNorm φ hφ h u s := fun s hs => by
    rw [← awayComap_awayLift h s hs, hvext, nonflatNorm_awayComap φ hφ h u]
  rw [← hu.eq_nonflatNorm hn hB φ hinj hφ hh hvreg hv]
  exact hvreg

end Regularity

/-! ### The weights and the hypothesis class `ChartNonflatNorms` -/

section Weights

/-- **FHX Proposition 5.22 for functions regularizable on blowup charts** (`prop:nf-nonflat-norm`),
conditional on `WuRegularization k`, in the form of the hypothesis class `ChartNonflatNorms`:
weights `m_y ≥ 1` with `∑_{π(y) = s} m_y = d = genericDegree φ` for every `s` (`def:nf-weights`,
`lem:nf-weights-basic`, fixed before `u`), such that `N_π u` is regularizable for every `u`
regularizable on the charts of a blowup, of logarithmic growth and regularizable on principal opens
covering `Y^an \ Z^an`. The weights are `nonflatWeight φ hfin h` for a good locus element `h`
(`exists_isNonflatGoodLocus`). -/
theorem nonempty_normWeights_isChartRegularizable {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] [WuRegularization.{u, u} k] {A B : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [IsIntegrallyClosed A] [CommRing B] [Algebra k B]
    {n : ℕ} (hn : 1 ≤ n) (hB : IsAffineSpacePrincipalOpen k B n) (φ : B →ₐ[k] A)
    (hinj : Function.Injective φ) (hfin : (φ : B →+* A).Finite)
    (het : IsGenericallyEtale (φ : B →+* A)) (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0) :
    Nonempty (NormWeights φ S IsChartRegularizable (genericDegree (φ : B →+* A))) := by
  obtain ⟨h, hh⟩ := exists_isNonflatGoodLocus hB φ hinj hfin het S hS
  exact ⟨nonflatNormWeights φ hfin hn hB hinj hh fun _ hu hlog hcover =>
    hu.isRegularizable_nonflatNorm hn hB φ hinj hfin hh hlog hcover⟩

/-- **`ChartNonflatNorms` from `WuRegularization`** (`prop:nf-nonflat-norm`): the hypothesis class
of `Local/ProjectionChartRegularizable` (FHX Proposition 5.22 for functions regularizable on blowup
charts) holds in one universe whenever the imported FHX Lemma 5.11(5),(6) does. In particular it is
found by instance search from `ConvexPLApproximation` and from `LocalPositivity`. -/
instance ChartNonflatNorms.of_wuRegularization {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] [WuRegularization.{u, u} k] : ChartNonflatNorms.{u, u, u} k where
  exists_normWeights _ _ _ _ _ _ _ _ _ _ hn hB φ hinj hfin het S hS :=
    nonempty_normWeights_isChartRegularizable hn hB φ hinj hfin het S hS

end Weights

end EnvelopeProperty
