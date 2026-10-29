/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Subvariety
import EnvelopeProperty.Projective.CompactificationDivisibility

/-!
# Projectively normal subvarieties and their normal charts

Let `k` be a field, `R_M = k[x₀, …, x_M]`, and `X = V(I) ⊆ ℙᴹ` a projective subvariety
(`ProjSubvariety`, `Projective/Subvariety.lean`) with homogeneous coordinate ring `S = R_M / I`.
In the model used for Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Corollary 5.26 (`cor:normal-weak-global`), a normal
projective variety is modelled as a **projectively normal** `X ⊆ ℙᴹ`, i.e. one whose homogeneous
coordinate ring `S` is integrally closed (blueprint `projective-general.tex`, `conv:pg-setting`).

This file proves the blueprint lemma `lem:pg-chart-normal` (used for FHX Lemma 5.10(2),
`lem:compactification`, on `X`): for a form `σ ∉ I`, the chart algebra
`A_σ = S_{(σ̄)} = QuotChartAlg I σ e` is an integrally closed domain of finite type over `k`.

## Proof

`A_σ` embeds into `B = S[σ̄⁻¹]` by `τ̄ / σ̄^N ↦ τ̄ σ̄^{-N}` (`ProjBerk.quotChartLift`, injective by
`ProjBerk.quotChartLift_injective`), and `B` is integrally closed, being a localization of the
integrally closed domain `S`. An element `x` of `Frac A_σ` integral over `A_σ` is therefore an
element `w ∈ B` with `w q ∈ A_σ` for some `0 ≠ q ∈ A_σ`. Writing `w = H̄ / σ̄^N`,
`q = τ̄ / σ̄^m` and `w q = F̄ / σ̄^n` with forms `τ ∉ I` of degree `m e` and `F` of degree `n e`,
we get `τ σ^n H - F σ^{m + N} ∈ I`. Since `I` is a homogeneous prime and `τ σ^n ∉ I`, every
homogeneous component `H_c` with `c ≠ N e` lies in `I`
(`EnvelopeProperty.homogeneousComponent_mem_of_mul_sub_mem`), so `w = H̄_{Ne} / σ̄^N ∈ A_σ`.
This is the blueprint's argument, organized as "the degree-zero part of a graded integrally
closed domain is integrally closed"; it is first proved for any `k`-algebra `C` receiving `R_M`
with kernel `I` in which `σ` becomes a unit and every element is a fraction `φ(H) / φ(σ)^N`
(`ProjBerk.isIntegrallyClosed_quotChartAlg_of_lift`).

## Main definitions

* `ProjSubvariety.IsProjNormal X`: `R_M / I` is integrally closed (`conv:pg-setting`).

## Main results

* `EnvelopeProperty.mem_of_forall_homogeneousComponent_mem`,
  `EnvelopeProperty.homogeneousComponent_mem_of_mul_sub_mem`,
  `EnvelopeProperty.sub_homogeneousComponent_mem_of_mul_sub_mem`: congruences modulo a homogeneous
  prime ideal.
* `EnvelopeProperty.isIntegrallyClosed_of_forall_mul_mem_range`: `A ↪ C` with `C` integrally
  closed and `w ∈ j(A)` whenever `w j(q) ∈ j(A)` for some `q ≠ 0` forces `A` integrally closed.
* `ProjBerk.isIntegrallyClosed_quotChartAlg_of_lift`.
* `ProjSubvariety.isIntegrallyClosed_quotChartAlg` (`lem:pg-chart-normal`); together with
  `ProjBerk.isDomain_quotChartAlg` and `ProjBerk.finiteType_quotChartAlg`
  (`ProjSubvariety.isIntegrallyClosed_quotChartAlg_and`).

## Deviations from the blueprint

* The hypothesis `e ≥ 1` on the degree of `σ` is not needed and is dropped.
-/

open scoped NNReal ENNReal Topology

open MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Congruences modulo a homogeneous prime ideal -/

section HomogeneousCongr

variable {k : Type*} [Field k] {ι : Type*} {I : Ideal (MvPolynomial ι k)}

/-- A polynomial all of whose homogeneous components lie in an ideal lies in it. -/
theorem mem_of_forall_homogeneousComponent_mem {f : MvPolynomial ι k}
    (h : ∀ c, homogeneousComponent c f ∈ I) : f ∈ I := by
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun c _ => h c

/-- If `ρ ∉ I` is a form of degree `a`, `G` a form of degree `b`, and `ρ H ≡ G` modulo a
homogeneous prime `I`, then the homogeneous components `H_c` of `H` with `a + c ≠ b` lie in `I`. -/
theorem homogeneousComponent_mem_of_mul_sub_mem (hI : IsHomogeneousIdeal I) [I.IsPrime]
    {a b : ℕ} {ρ G H : MvPolynomial ι k} (hρ : ρ.IsHomogeneous a) (hρI : ρ ∉ I)
    (hG : G.IsHomogeneous b) (h : ρ * H - G ∈ I) {c : ℕ} (hc : a + c ≠ b) :
    homogeneousComponent c H ∈ I := by
  have h₁ := hI _ h (a + c)
  rw [map_sub, homogeneousComponent_mul_of_isHomogeneous hρ, homogeneousComponent_of_mem hG,
    if_neg hc, sub_zero] at h₁
  exact (Ideal.IsPrime.mem_or_mem ‹_› h₁).resolve_left hρI

/-- If `ρ ∉ I` is a form of degree `a`, `G` a form of degree `b = a + c`, and `ρ H ≡ G` modulo a
homogeneous prime `I`, then `H ≡ H_c` modulo `I`. -/
theorem sub_homogeneousComponent_mem_of_mul_sub_mem (hI : IsHomogeneousIdeal I) [I.IsPrime]
    {a b c : ℕ} {ρ G H : MvPolynomial ι k} (hρ : ρ.IsHomogeneous a) (hρI : ρ ∉ I)
    (hG : G.IsHomogeneous b) (h : ρ * H - G ∈ I) (hc : a + c = b) :
    H - homogeneousComponent c H ∈ I := by
  refine mem_of_forall_homogeneousComponent_mem fun c' => ?_
  rw [map_sub, homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous c H)]
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl, sub_self]
    exact I.zero_mem
  · rw [if_neg (Ne.symm hcc), sub_zero]
    exact homogeneousComponent_mem_of_mul_sub_mem hI hρ hρI hG h fun h' => hcc (by omega)

end HomogeneousCongr

/-! ### A criterion for integral closedness -/

section Criterion

/-- Let `j : A → C` be an injective ring map from a domain to an integrally closed domain such
that `w ∈ C` lies in the image of `j` as soon as `w j(q) ∈ j(A)` for some `q ≠ 0`. Then `A` is
integrally closed. (This is how the degree-zero part of a graded integrally closed domain is seen
to be integrally closed.) -/
theorem isIntegrallyClosed_of_forall_mul_mem_range {A C : Type*} [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [IsIntegrallyClosed C] (j : A →+* C) (hj : Function.Injective j)
    (key : ∀ (w : C) (q a : A), q ≠ 0 → w * j q = j a → ∃ y, j y = w) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨a, q, hq, rfl⟩ := IsFractionRing.div_surjective A x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hg : Function.Injective ((algebraMap C (FractionRing C)).comp j) :=
    (IsFractionRing.injective C (FractionRing C)).comp hj
  set ψ : FractionRing A →+* FractionRing C := IsFractionRing.lift hg
  have hψ : ∀ b, ψ (algebraMap A (FractionRing A) b) = algebraMap C (FractionRing C) (j b) :=
    fun b => IsFractionRing.lift_algebraMap hg b
  have hψcomp : ψ.comp (algebraMap A (FractionRing A)) = (algebraMap C (FractionRing C)).comp j :=
    RingHom.ext hψ
  -- the image of `x` in `Frac C` is integral over `C`, hence in `C`
  have hint : IsIntegral C
      (ψ (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) q)) := by
    obtain ⟨p, hpm, hp⟩ := hx
    refine ⟨p.map j, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hψcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hqK : algebraMap A (FractionRing A) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hq0
  have hwqa : w * j q = j a := by
    refine IsFractionRing.injective C (FractionRing C) ?_
    rw [map_mul, hw, ← hψ, ← hψ, ← map_mul, div_mul_cancel₀ _ hqK]
  obtain ⟨y, hy⟩ := key w q a hq0 hwqa
  refine ⟨y, ψ.injective ?_⟩
  rw [hψ, hy, hw]

end Criterion

namespace ProjBerk

variable {k : Type u} [Field k] {M : ℕ}

/-! ### Normality of the quotient chart algebras -/

section ChartNormal

variable {I : Ideal (MvPolynomial (Fin (M + 1)) k)} {σ : MvPolynomial (Fin (M + 1)) k} {d : ℕ}

/-- **Normality of the charts, abstract form.** Let `I` be a homogeneous prime, `σ ∉ I` a form of
degree `d`, and `φ : R_M → C` a `k`-algebra map to an integrally closed domain with kernel `I`,
`φ(σ)` a unit, and every element of `C` of the form `φ(H) / φ(σ)^N`. Then the quotient chart
algebra `A_σ / I_{(σ)}` is integrally closed. (For `C = S[σ̄⁻¹]` this is `lem:pg-chart-normal`.) -/
theorem isIntegrallyClosed_quotChartAlg_of_lift (hI : IsHomogeneousIdeal I) [I.IsPrime]
    (hσ : σ.IsHomogeneous d) (hσI : σ ∉ I) {C : Type*} [CommRing C] [IsDomain C] [Algebra k C]
    [IsIntegrallyClosed C] (φ : MvPolynomial (Fin (M + 1)) k →ₐ[k] C)
    (hφI : ∀ f ∈ I, φ f = 0) (hker : ∀ f, φ f = 0 → f ∈ I) (hσu : IsUnit (φ σ))
    (hsurj : ∀ c : C, ∃ (N : ℕ) (H : MvPolynomial (Fin (M + 1)) k), c * φ σ ^ N = φ H) :
    IsIntegrallyClosed (QuotChartAlg I σ d) := by
  have := isDomain_quotChartAlg (d := d) hσI
  set j := quotChartLift I σ d φ hφI hσu
  have hj : Function.Injective j :=
    quotChartLift_injective φ hφI hσu hσ fun _ f _ hf => hker f hf
  -- every element of `A_σ / I_{(σ)}` is `τ̄ / σ̄^N` with `τ` a form of degree `N d`
  have hmk : ∀ q : QuotChartAlg I σ d, ∃ (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k),
      τ.IsHomogeneous (N * d) ∧ q = quotChartMk I σ d N τ ∧ j q * φ σ ^ N = φ τ := by
    intro q
    obtain ⟨q', rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_chartMk hσ q'
    refine ⟨N, τ, hτ, rfl, ?_⟩
    have h := quotChartLift_quotChartMk_mul_pow (d := d) φ hφI hσu N τ
    rwa [homogeneousComponent_eq_self hτ] at h
  -- the degree-zero argument: `w ∈ C` with `w j(q) ∈ j(A_σ / I_{(σ)})` lies in the image
  have key : ∀ (w : C) (q a : QuotChartAlg I σ d), q ≠ 0 → w * j q = j a →
      ∃ y, j y = w := by
    intro w q a hq hwqa
    obtain ⟨N, H, hw⟩ := hsurj w
    obtain ⟨m, τ, hτ, rfl, hjq⟩ := hmk q
    obtain ⟨n, F, hF, rfl, hja⟩ := hmk a
    have hτI : τ ∉ I := fun h => hq ((quotChartMk_eq_zero_iff hσI hτ).2 h)
    have hρ : (τ * σ ^ n).IsHomogeneous (m * d + d * n) := hτ.mul (hσ.pow n)
    have hρI : τ * σ ^ n ∉ I := fun h =>
      ((Ideal.IsPrime.mem_or_mem ‹_› h).elim hτI fun h' =>
        hσI (Ideal.IsPrime.mem_of_pow_mem ‹_› n h'))
    have hG : (F * σ ^ (m + N)).IsHomogeneous (n * d + d * (m + N)) := hF.mul (hσ.pow _)
    have hmem : τ * σ ^ n * H - F * σ ^ (m + N) ∈ I := by
      refine hker _ ?_
      rw [map_sub, sub_eq_zero, map_mul, map_mul, map_mul, map_pow, map_pow, ← hjq, ← hja, ← hw,
        ← hwqa]
      ring
    have hH := sub_homogeneousComponent_mem_of_mul_sub_mem (c := N * d) hI hρ hρI hG hmem
      (by ring)
    refine ⟨quotChartMk I σ d N H, (hσu.pow N).mul_left_injective ?_⟩
    have h := quotChartLift_quotChartMk_mul_pow (d := d) φ hφI hσu N H
    simp only at h ⊢
    rw [h, hw, ← sub_eq_zero, ← map_sub]
    exact hφI _ (by rw [← neg_sub, neg_mem_iff]; exact hH)
  exact isIntegrallyClosed_of_forall_mul_mem_range j.toRingHom hj key

end ChartNormal

end ProjBerk

open ProjBerk

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- A projective subvariety `X = V(I) ⊆ ℙᴹ` is **projectively normal** if its homogeneous
coordinate ring `S = R_M / I` is integrally closed (`conv:pg-setting`). This is the model of a
normal projective variety with an ample line bundle used for FHX Corollary 5.26
(`rmk:pg-subvariety-psh-comparison`). -/
def IsProjNormal : Prop :=
  IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal)

theorem isProjNormal_iff :
    X.IsProjNormal ↔ IsIntegrallyClosed (MvPolynomial (Fin (M + 1)) k ⧸ X.ideal) :=
  Iff.rfl

variable {X}

/-- **Normal charts** (`lem:pg-chart-normal`). If `X` is projectively normal, then for every form
`σ ∉ I` the chart algebra `A_σ = S_{(σ̄)}` (modelled as `QuotChartAlg I σ e`) is integrally
closed. -/
theorem isIntegrallyClosed_quotChartAlg (hX : X.IsProjNormal) {σ : MvPolynomial (Fin (M + 1)) k}
    {e : ℕ} (hσ : σ.IsHomogeneous e) (hσI : σ ∉ X.ideal) :
    IsIntegrallyClosed (QuotChartAlg X.ideal σ e) := by
  set S := MvPolynomial (Fin (M + 1)) k ⧸ X.ideal
  have : IsIntegrallyClosed S := hX
  set s : S := Ideal.Quotient.mk X.ideal σ
  have hs : s ≠ 0 := fun h => hσI (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hle : Submonoid.powers s ≤ nonZeroDivisors S := powers_le_nonZeroDivisors_of_noZeroDivisors hs
  have : IsDomain (Localization.Away s) := IsLocalization.isDomain_localization hle
  have : IsIntegrallyClosed (Localization.Away s) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away s) (Submonoid.powers s) hle
  have hinj : Function.Injective (algebraMap S (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) hle
  let φ : MvPolynomial (Fin (M + 1)) k →ₐ[k] Localization.Away s :=
    (IsScalarTower.toAlgHom k S (Localization.Away s)).comp (Ideal.Quotient.mkₐ k X.ideal)
  have hφ : ∀ f, φ f = algebraMap S (Localization.Away s) (Ideal.Quotient.mk X.ideal f) :=
    fun _ => rfl
  refine isIntegrallyClosed_quotChartAlg_of_lift X.isHomogeneousIdeal hσ hσI φ
    (fun f hf => by rw [hφ, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero])
    (fun f hf => by
      rw [hφ, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem] at hf
      exact hf)
    (by rw [hφ]; exact IsLocalization.Away.algebraMap_isUnit s) fun c => ?_
  obtain ⟨N, a, h⟩ := IsLocalization.Away.surj s c
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨N, H, by rw [hφ, hφ, h]⟩

/-- **Normal charts** (`lem:pg-chart-normal`), complete statement: if `X` is projectively normal
and `σ ∉ I` is a form, then `A_σ` is an integrally closed domain of finite type over `k`. -/
theorem isIntegrallyClosed_quotChartAlg_and (hX : X.IsProjNormal)
    {σ : MvPolynomial (Fin (M + 1)) k} {e : ℕ} (hσ : σ.IsHomogeneous e) (hσI : σ ∉ X.ideal) :
    IsDomain (QuotChartAlg X.ideal σ e) ∧ Algebra.FiniteType k (QuotChartAlg X.ideal σ e) ∧
      IsIntegrallyClosed (QuotChartAlg X.ideal σ e) :=
  ⟨isDomain_quotChartAlg hσI, finiteType_quotChartAlg hσ,
    isIntegrallyClosed_quotChartAlg hX hσ hσI⟩

end ProjSubvariety

end EnvelopeProperty
