/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Compactification

/-!
# The compactification lemma for principal opens of affine space

This file restates the compactification lemma on `ℙⁿ`
(`EnvelopeProperty.Projective.Compactification`, Fang–Han–Xia, *The envelope property for
unibranch projective varieties*, Lemma 5.10, `lem:compactification`) for the charts `σ = xⱼ h`,
`h` a nonzero form of degree `d`, where the chart `S = ℙⁿ_σ` is the principal open
`{dehom h ≠ 0}` of the affine chart `𝔸ⁿ = {xⱼ ≠ 0}`: `A_{xⱼ h} ≃ k[y]_{dehom h}`
(`ProjBerk.mulChartEquiv`) and `U_{xⱼ h} ≃ (Spec k[y]_{dehom h})^an` (`ProjBerk.mulChart`).
This is the form used in the extension step of FHX Proposition 5.22 (`prop:nonflat-norm`, with
`j = 0` and `h` the homogenization of the equation of `S ⊆ 𝔸ⁿ`), as explained in
`rmk:bj-compactification-full` of the blueprint chapter `bj22.tex`.

* `ProjBerk.dehom_ne_zero`: `dehom h ≠ 0` for a nonzero form `h`.
* `ProjBerk.isIntegrallyClosed_chartAlg_mul`: `A_{xⱼ h}` is integrally closed (a localization of
  a polynomial ring), so the integral-closedness hypothesis of `ProjBerk.isPSH_chartExt` holds.
* `ProjBerk.IsPSH.isRegularizable_mulChart` (part (1), `lem:bj-compactification-regularize`): for
  countable `k`, `c ∈ ℚ_{>0}` and `Φ ∈ PSH(c (d + 1))`, the function `Φ - c log|xⱼ h|` on `S^an`
  is regularizable on `S = Spec k[y]_{dehom h}`.
* `ProjBerk.isPSH_mulChartExt` (part (2), `lem:bj-compactification-extend`, **conditional on the
  imported `WuRegularization.growthControl`**): for `w ∈ ℛ(S)` with `w ≤ -κ log|xⱼ h| + B₀` and
  rational `a > κ`, the extension `ProjBerk.mulChartExt j hh w a` of `w + a log|xⱼ h|` by `-∞`
  lies in `PSH(a (d + 1))`.
-/

open scoped NNReal ENNReal Topology

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

namespace ProjBerk

universe u

variable {k : Type u} [Field k] {n : ℕ} (j : Fin (n + 1)) {d : ℕ}
  {h : MvPolynomial (Fin (n + 1)) k}

/-- The point of `U_{xⱼ h}` attached to `y ∈ (Spec k[y]_{dehom h})^an` is the inverse chart of
`A_{xⱼ h}` at the pullback of `y` along `A_{xⱼ h} ≃ k[y]_{dehom h}`. -/
theorem coe_mulChart_symm (hh : h.IsHomogeneous d) (y : Berk k (Localization.Away (dehom j h))) :
    (((mulChart j hh).symm y : chartDomain (X j * h)) : ProjBerk k n) =
      chartInv (X j * h) (d + 1) (isHomogeneous_X_mul j hh) (Nat.succ_pos d)
        (Berk.comap (mulChartEquiv j hh : chartAlg (X j * h) (d + 1) →ₐ[k]
          Localization.Away (dehom j h)) y) := by
  rw [mulChart, Homeomorph.symm_trans_apply, coe_chartHomeomorph_symm_apply]
  rfl

theorem _root_.EnvelopeProperty.Berk.comap_comap_symm {A B : Type*} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B]
    (φ : A ≃ₐ[k] B) (x : Berk k A) :
    Berk.comap (φ : A →ₐ[k] B) (Berk.comap (φ.symm : B →ₐ[k] A) x) = x :=
  Berk.ext_val fun a => by simp

theorem _root_.EnvelopeProperty.Berk.comap_symm_comap {A B : Type*} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B]
    (φ : A ≃ₐ[k] B) (y : Berk k B) :
    Berk.comap (φ.symm : B →ₐ[k] A) (Berk.comap (φ : A →ₐ[k] B) y) = y :=
  Berk.ext_val fun b => by simp

/-- For a nonzero form `h`, `A_{xⱼ h}` is a domain. -/
theorem isDomain_chartAlg_mul (hh0 : h ≠ 0) : IsDomain (chartAlg (X j * h) (d + 1)) := by
  have := Berk.isDomain_localizationAway (mul_ne_zero (X_ne_zero j) hh0)
  infer_instance

/-- The dehomogenization of a nonzero form is nonzero. -/
theorem dehom_ne_zero (hh : h.IsHomogeneous d) (hh0 : h ≠ 0) : dehom j h ≠ 0 := by
  intro h0
  have := isDomain_chartAlg_mul j (d := d) hh0
  have hnt : Nontrivial (Localization.Away (dehom j h)) :=
    (mulChartEquiv j hh).symm.toEquiv.nontrivial
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (dehom j h)) (dehom j h)
  have h2 : algebraMap (MvPolynomial (Fin n) k) (Localization.Away (dehom j h)) (dehom j h) =
      0 := by
    have := congrArg (algebraMap (MvPolynomial (Fin n) k) (Localization.Away (dehom j h))) h0
    rwa [map_zero] at this
  rw [h2] at hu
  exact not_isUnit_zero hu

/-- `A_{xⱼ h} ≃ k[y]_{dehom h}` is integrally closed, as a localization of a polynomial ring. -/
theorem isIntegrallyClosed_chartAlg_mul (hh : h.IsHomogeneous d) (hh0 : h ≠ 0) :
    IsIntegrallyClosed (chartAlg (X j * h) (d + 1)) := by
  have : IsIntegrallyClosed (Localization.Away (dehom j h)) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (dehom j h))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (dehom_ne_zero j hh hh0))
  exact IsIntegrallyClosed.of_equiv (mulChartEquiv j hh).symm.toRingEquiv

/-! ### Part (1) -/

/-- **Compactification, part (1)**, for `S = {dehom h ≠ 0} ⊆ 𝔸ⁿ` (FHX Lemma 5.10(1),
`lem:bj-compactification-regularize`): for countable `k`, a nonzero form `h` of degree `d`,
`c ∈ ℚ_{>0}` and `Φ ∈ PSH(c (d + 1))`, the function `Φ - c log|xⱼ h|`, transported to
`S^an = (Spec k[y]_{dehom h})^an` by the chart `mulChart`, is regularizable on `S`. -/
theorem IsPSH.isRegularizable_mulChart [Countable k] (hh : h.IsHomogeneous d) (hh0 : h ≠ 0)
    {c : ℚ} (hc : 0 < c) {Φ : ProjBerk k n → EReal} (hΦ : IsPSH ((c : ℝ) * (d + 1 : ℕ)) Φ) :
    IsRegularizable fun y : Berk k (Localization.Away (dehom j h)) =>
      Φ ((mulChart j hh).symm y) -
        ((c : ℝ) : EReal) * logAbs (X j * h) ((mulChart j hh).symm y) := by
  have hreg := hΦ.isRegularizable_chart (isHomogeneous_X_mul j hh) (Nat.succ_pos d)
    (mul_ne_zero (X_ne_zero j) hh0) hc
  have := finiteType_chartAlg (isHomogeneous_X_mul j hh)
  have : Algebra.FiniteType k (Localization.Away (dehom j h)) :=
    Algebra.FiniteType.equiv this (mulChartEquiv j hh)
  obtain ⟨y₀, hy₀⟩ := hreg.1
  refine hreg.comp_comap (mulChartEquiv j hh : chartAlg (X j * h) (d + 1) →ₐ[k]
    Localization.Away (dehom j h)) ⟨Berk.comap ((mulChartEquiv j hh).symm :
      Localization.Away (dehom j h) →ₐ[k] chartAlg (X j * h) (d + 1)) y₀, ?_⟩
  rw [Berk.comap_comap_symm]
  exact hy₀

/-! ### Part (2) -/

/-- The function on `(ℙⁿ)^an` equal to `w ∘ mulChart + a log|xⱼ h|` on `U_{xⱼ h}` and to `-∞` on
its complement, for `w` on `S^an = (Spec k[y]_{dehom h})^an` (FHX Lemma 5.10(2)). -/
def mulChartExt (hh : h.IsHomogeneous d) (w : Berk k (Localization.Away (dehom j h)) → EReal)
    (a : ℝ) : ProjBerk k n → EReal :=
  chartExt (X j * h) (d + 1) (fun y => w (Berk.comap ((mulChartEquiv j hh).symm :
    Localization.Away (dehom j h) →ₐ[k] chartAlg (X j * h) (d + 1)) y)) a

theorem mulChartExt_of_mem (hh : h.IsHomogeneous d)
    (w : Berk k (Localization.Away (dehom j h)) → EReal) (a : ℝ) {v : ProjBerk k n}
    (hv : v ∈ chartDomain (X j * h)) :
    mulChartExt j hh w a v = w (mulChart j hh ⟨v, hv⟩) + (a : EReal) * logAbs (X j * h) v :=
  chartExt_of_ne_zero _ a hv

theorem mulChartExt_of_not_mem (hh : h.IsHomogeneous d)
    (w : Berk k (Localization.Away (dehom j h)) → EReal) (a : ℝ) {v : ProjBerk k n}
    (hv : v ∉ chartDomain (X j * h)) : mulChartExt j hh w a v = ⊥ :=
  chartExt_of_eq_zero _ a (not_not.1 hv)

theorem mulChartExt_mulChart_symm (hh : h.IsHomogeneous d)
    (w : Berk k (Localization.Away (dehom j h)) → EReal) (a : ℝ)
    (y : Berk k (Localization.Away (dehom j h))) :
    mulChartExt j hh w a ((mulChart j hh).symm y) =
      w y + (a : EReal) * logAbs (X j * h) ((mulChart j hh).symm y) := by
  rw [mulChartExt_of_mem j hh w a ((mulChart j hh).symm y).2, Subtype.coe_eta,
    Homeomorph.apply_symm_apply]

/-- **Compactification, part (2), for regularizable functions on `S = {dehom h ≠ 0} ⊆ 𝔸ⁿ`**
(FHX Lemma 5.10(2), `lem:bj-compactification-extend`), **conditional on the imported
`WuRegularization.growthControl`** (FHX Lemma 5.11(5); an explicit hypothesis, not an axiom).
Let `k` be algebraically closed, `n ≥ 1`, `h` a nonzero form of degree `d`, `w ∈ ℛ(S)` and
`κ ∈ ℚ_{>0}`, `B₀ ∈ ℝ` with `w ≤ -κ log|xⱼ h| + B₀` on `S^an`. For every rational `a > κ`, the
function equal to `w + a log|xⱼ h|` on `S^an = U_{xⱼ h}` and to `-∞` elsewhere lies in
`PSH(a (d + 1))`. -/
theorem isPSH_mulChartExt [IsAlgClosed k] [WuRegularization.{u, u} k] (hn : n ≠ 0)
    (hh : h.IsHomogeneous d) (hh0 : h ≠ 0)
    {w : Berk k (Localization.Away (dehom j h)) → EReal} (hw : IsRegularizable w) {κ : ℚ}
    (hκ : 0 < κ) {B₀ : ℝ}
    (hwB : ∀ y, w y ≤ -((κ : ℝ) : EReal) * logAbs (X j * h) ((mulChart j hh).symm y) + (B₀ : EReal))
    {a : ℚ} (ha : κ < a) : IsPSH ((a : ℝ) * (d + 1 : ℕ)) (mulChartExt j hh w a) := by
  have := isIntegrallyClosed_chartAlg_mul j hh hh0
  have := finiteType_chartAlg (isHomogeneous_X_mul j hh)
  have hw' : IsRegularizable fun y => w (Berk.comap ((mulChartEquiv j hh).symm :
      Localization.Away (dehom j h) →ₐ[k] chartAlg (X j * h) (d + 1)) y) := by
    obtain ⟨y₀, hy₀⟩ := hw.1
    refine hw.comp_comap ((mulChartEquiv j hh).symm :
      Localization.Away (dehom j h) →ₐ[k] chartAlg (X j * h) (d + 1))
      ⟨Berk.comap (mulChartEquiv j hh : chartAlg (X j * h) (d + 1) →ₐ[k]
        Localization.Away (dehom j h)) y₀, ?_⟩
    rw [Berk.comap_symm_comap]
    exact hy₀
  refine isPSH_chartExt hn (isHomogeneous_X_mul j hh) (Nat.succ_pos d)
    (mul_ne_zero (X_ne_zero j) hh0) hw' hκ (B₀ := B₀) (fun y => ?_) ha
  have h1 := hwB (Berk.comap ((mulChartEquiv j hh).symm :
    Localization.Away (dehom j h) →ₐ[k] chartAlg (X j * h) (d + 1)) y)
  rwa [coe_mulChart_symm, Berk.comap_comap_symm] at h1

end ProjBerk

end EnvelopeProperty
