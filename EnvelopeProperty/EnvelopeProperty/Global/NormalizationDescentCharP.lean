/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.Unibranch
import EnvelopeProperty.Global.WeightedNorm

/-!
# Psh functions descend through the normalization of a unibranch model: characteristic `p`

This file implements the characteristic-`p` part of the blueprint node
`thm:gl-normalization-reflection` of `global.tex` (subsection `subsec:gl-main`) for the
formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(revision `832e086`, §8, Theorem 8.3 `thm:normalization-reflection`, positive characteristic), and
some chart lemmas shared with the characteristic-`0` part
(`EnvelopeProperty.Global.AdditiveSandwich`, `EnvelopeProperty.Global.NormalizationDescent`).

Let `𝒳` be a unibranch model (`MultiModel.IsUnibranch`) over an algebraically closed field `k`,
`𝒴 = 𝒳^ν` its normalization, and `ν^an : 𝒴^an ≃ₜ 𝒳^an` the homeomorphism of
`lem:gl-unibranch-universal` (`MultiModel.IsUnibranch.anHomeomorph`).

## Main results

* `MultiModel.exists_mul_chartDenZ_mem_sections`: for `x` in a chart algebra `A_j` of a model
  there is `β ∈ ℕ^r` with `x z̃_j^e ∈ R_e` for every `e ≥ β` (`e ∈ ℤ^r`).
* `MultiModel.IsUnibranch.secAbs_symm`: sections `f ∈ R_a(𝒳) ⊆ R_a(𝒴)` have the same values,
  `|f|_{(ν^an)⁻¹ v} = |f|_v` (`lem:gl-pullback`).
* `MultiModel.IsUnibranch.exists_pow_pow_mem_sections` (`char k = p`): every section
  `f ∈ R_d(𝒴)` has a power `f^{pⁿ} ∈ R_{pⁿ d}(𝒳)`.
* `MultiModel.IsUnibranch.isFS_comp_symm_of_charP`: `φ ∘ (ν^an)⁻¹ ∈ 𝓗(𝒳, a)` for
  `φ ∈ 𝓗(𝒴, a)`.
* `MultiModel.IsUnibranch.isPSH_comp_symm_of_charP` (**`thm:gl-normalization-reflection`,
  characteristic `p`**): `ψ ∘ (ν^an)⁻¹ ∈ PSH(𝒳, θ)` for every `ψ ∈ PSH(𝒴, θ)` and **every**
  `θ ∈ ℝ^r`. This is exactly the hypothesis `hrefl` of
  `MultiModel.IsUnibranch.hasEnvelopeProperty_of_reflection`.

## Deviations from the blueprint proof

The blueprint chooses finitely many homogeneous generators of `S^ν` over `S`, one `p`-power `q`
for all of them, shows `p^q ∈ R(𝒳)` for every `p ∈ S^ν` and then `f^q ∈ R_{qma}(𝒳)` for sections
`f ∈ R_{ma}(𝒴)` by the ideal argument. Here the power is chosen per section and per chart: for a
section `f ∈ R_d(𝒴)` and a chart `j`, `f / z̃_j^d ∈ B_j` has a `p`-power in `A_j`
(`thm:gl-frobenius-descent`, `MultiModel.IsUnibranch.exists_pow_pow_mem_chartAlg`); a common power
over the finitely many charts gives `f^{pⁿ} / z̃_j^{pⁿ d} ∈ A_j` for all `j`, hence
`f^{pⁿ} ∈ R_{pⁿ d}(𝒳)` by the chart criterion `MultiModel.mem_sections_of_forall_div_chartDenZ`
(the ideal argument, lane G7). For Fubini–Study data the power is then made common to the finitely
many terms. No generators of `S^ν` and no additivity of Frobenius are needed.
-/

open scoped NNReal ENNReal Topology

open Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}

/-! ### Chart denominators and sections -/

section ChartDen

variable {Y : MultiModel k K r}

/-- `z̃_j^{e + e'} = z̃_j^e z̃_j^{e'}` for a chart with nonzero coordinates (`e, e' ∈ ℤ^r`). -/
theorem chartDenZ_add {j : Y.ChartIndex} (hj : ∀ c, Y.coord c (j c) ≠ 0) (e e' : Fin r → ℤ) :
    Y.chartDenZ j (e + e') = Y.chartDenZ j e * Y.chartDenZ j e' := by
  rw [chartDenZ, chartDenZ, chartDenZ, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun c _ => by rw [Pi.add_apply, zpow_add₀ (hj c)]

/-- `z̃_j^0 = 1`. -/
theorem chartDenZ_zero (j : Y.ChartIndex) : Y.chartDenZ j 0 = 1 := by
  simp [chartDenZ]

/-- **Chart elements times chart denominators are sections.** For `x` in the chart algebra `A_j`
there is `β ∈ ℕ^r` with `x z̃_j^e ∈ R_e` for every `e ∈ ℤ^r` with `e ≥ β`: writing
`x = h / z̃_j^β` with `h ∈ S_β`, `x z̃_j^e = h z̃_j^{e - β} ∈ S_e` (`lem:gl-sections`(1),(4)). -/
theorem exists_mul_chartDenZ_mem_sections {j : Y.ChartIndex} (hj : ∀ c, Y.coord c (j c) ≠ 0)
    {x : K} (hx : x ∈ Y.chartAlg j) :
    ∃ β : Fin r →₀ ℕ, ∀ e : Fin r → ℤ, (∀ c, (β c : ℤ) ≤ e c) →
      x * Y.chartDenZ j e ∈ Y.sections e := by
  obtain ⟨β, h, hh, rfl⟩ := (mem_chartAlg_iff hj).1 hx
  refine ⟨β, fun e he => ?_⟩
  set δ : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun c => (e c - β c).toNat with hδdef
  have hδ : ∀ c, e c = ((β + δ) c : ℕ) := fun c => by
    have := he c
    simp only [hδdef, Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm, Nat.cast_add]
    omega
  have hP : Y.chartDenZ j e = Y.chartDen j β * Y.chartDen j δ := by
    rw [← chartDen_add, chartDenZ, chartDen]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [hδ c, zpow_natCast]
  have key : h / Y.chartDen j β * Y.chartDenZ j e = h * Y.chartDen j δ := by
    rw [hP]
    field_simp [chartDen_ne_zero hj β]
  rw [key]
  exact mem_sections_of_mem_piece hδ (mul_mem_piece hh (Y.chartDen_mem_piece j δ))

/-- For `e ≥ 0`, `z̃_j^e ∈ R_e`. -/
theorem chartDenZ_mem_sections (j : Y.ChartIndex) {e : Fin r → ℤ} (he : ∀ c, 0 ≤ e c) :
    Y.chartDenZ j e ∈ Y.sections e := by
  set δ : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun c => (e c).toNat with hδdef
  have hδ : ∀ c, e c = (δ c : ℕ) := fun c => by
    have := he c
    simp only [hδdef, Finsupp.coe_equivFunOnFinite_symm]
    omega
  have hP : Y.chartDenZ j e = Y.chartDen j δ := by
    rw [chartDenZ, chartDen]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [hδ c, zpow_natCast]
  rw [hP]
  exact mem_sections_of_mem_piece hδ (Y.chartDen_mem_piece j δ)

end ChartDen

/-! ### Sections of a unibranch model and of its normalization -/

section Unibranch

variable {X : MultiModel k K r} [Infinite k] [PerfectField k]

namespace IsUnibranch

variable (hX : X.IsUnibranch)

include hX

/-- **Values of sections under `(ν^an)⁻¹`** (`lem:gl-pullback`): for `f ∈ R_a(𝒳) ⊆ R_a(𝒴)`,
`|f|_{(ν^an)⁻¹ v} = |f|_v`. -/
theorem secAbs_symm [IsAlgClosed k] (v : X.an) {a : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections a) :
    X.normalization.secAbs (hX.anHomeomorph.symm v).1 a f = X.secAbs v.1 a f := by
  have h := (FiniteHom.ofNormalization X).secAbs_anMap (hX.anHomeomorph.symm v) hf
  rw [← hX.anHomeomorph_apply, Homeomorph.apply_symm_apply] at h
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using h

/-- `log |f|_{(ν^an)⁻¹ v} = log |f|_v` for `f ∈ R_a(𝒳)`. -/
theorem logSecAbs_symm [IsAlgClosed k] (v : X.an) {a : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections a) :
    X.normalization.logSecAbs (hX.anHomeomorph.symm v).1 a f = X.logSecAbs v.1 a f := by
  rw [logSecAbs, logSecAbs, hX.secAbs_symm v hf]

/-- `log |f|_{ν^an(w)} = log |f|_w` for `f ∈ R_a(𝒳)`. -/
theorem logSecAbs_anHomeomorph [IsAlgClosed k] (w : X.normalization.an) {a : Fin r → ℤ} {f : K}
    (hf : f ∈ X.sections a) :
    X.logSecAbs (hX.anHomeomorph w).1 a f = X.normalization.logSecAbs w.1 a f := by
  rw [← hX.logSecAbs_symm (hX.anHomeomorph w) hf, Homeomorph.symm_apply_apply]

/-! ### Characteristic `p` -/

/-- **Frobenius descent of sections** (`thm:gl-normalization-reflection`, characteristic `p`,
first step): if `char k = p > 0`, every section `f ∈ R_d(𝒴)` of the normalization has a power
`f^{pⁿ} ∈ R_{pⁿ d}(𝒳)`. On each chart `j`, `f / z̃_j^d ∈ B_j` has a `p`-power in `A_j`
(`thm:gl-frobenius-descent`); with a common power for the finitely many charts, the chart
criterion `mem_sections_of_forall_div_chartDenZ` applies. -/
theorem exists_pow_pow_mem_sections [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {d : Fin r → ℤ} {f : K} (hf : f ∈ X.normalization.sections d) :
    ∃ n : ℕ, f ^ p ^ n ∈ X.sections (p ^ n • d) := by
  classical
  have h1 : ∀ j : X.ChartIndex, ∃ n : ℕ, (∀ c, X.coord c (j c) ≠ 0) →
      (f / X.chartDenZ j d) ^ p ^ n ∈ X.chartAlg j := by
    intro j
    by_cases hj : ∀ c, X.coord c (j c) ≠ 0
    · obtain ⟨n, hn⟩ := hX.exists_pow_pow_mem_chartAlg p hj
        (X.normalization.div_chartDenZ_mem_chartAlg (j := j) hj hf)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose n hn using h1
  refine ⟨Finset.univ.sup n, mem_sections_of_forall_div_chartDenZ fun j hj => ?_⟩
  have hle : n j ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ j)
  have e : (f / X.chartDenZ j d) ^ p ^ Finset.univ.sup n =
      ((f / X.chartDenZ j d) ^ p ^ n j) ^ p ^ (Finset.univ.sup n - n j) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hle]
  rw [chartDenZ_nsmul, ← div_pow, e]
  exact Subalgebra.pow_mem _ (hn j hj) _

/-- A common Frobenius power for finitely many sections of the normalization. -/
theorem exists_pow_pow_mem_sections_finset [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {d : Fin r → ℤ} (s : Finset (K × ℝ)) (hs : ∀ t ∈ s, t.1 ∈ X.normalization.sections d) :
    ∃ n : ℕ, ∀ t ∈ s, t.1 ^ p ^ n ∈ X.sections (p ^ n • d) := by
  classical
  have h1 : ∀ t ∈ s, ∃ n : ℕ, ∀ n', n ≤ n' → t.1 ^ p ^ n' ∈ X.sections (p ^ n' • d) := by
    intro t ht
    obtain ⟨n, hn⟩ := hX.exists_pow_pow_mem_sections p (hs t ht)
    refine ⟨n, fun n' hn' => ?_⟩
    have h := pow_mem_sections hn (p ^ (n' - n))
    have e1 : (t.1 ^ p ^ n) ^ p ^ (n' - n) = t.1 ^ p ^ n' := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn']
    have e2 : p ^ (n' - n) • p ^ n • d = p ^ n' • d := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn']
    rwa [e1, e2] at h
  choose n hn using h1
  refine ⟨s.attach.sup fun t => n t.1 t.2, fun t ht => hn t ht _ ?_⟩
  exact Finset.le_sup (f := fun t : s => n t.1 t.2) (Finset.mem_attach _ ⟨t, ht⟩)

/-- **Fubini–Study functions descend in characteristic `p`** (`thm:gl-normalization-reflection`,
characteristic `p`): `φ ∘ (ν^an)⁻¹ ∈ 𝓗(𝒳, a)` for `φ = m⁻¹ max_t (log |f_t| + λ_t) ∈ 𝓗(𝒴, a)`.
With `q = pⁿ` such that all `f_t^q ∈ R_{qma}(𝒳)`,
`φ = (qm)⁻¹ max_t (log |f_t^q| + q λ_t)` and the values of `f_t^q` agree on `𝒳` and `𝒴`. -/
theorem isFS_comp_symm_of_charP [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {a : Fin r → ℚ} {φ : X.normalization.an → EReal} (hφ : X.normalization.IsFS a φ) :
    X.IsFS a (φ ∘ hX.anHomeomorph.symm) := by
  classical
  obtain ⟨D, ⟨t₀, ht₀, ht₀0⟩, hD⟩ := hφ
  obtain ⟨n, hn⟩ := hX.exists_pow_pow_mem_sections_finset p D.terms D.mem_sections
  set q : ℕ := p ^ n with hqdef
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos n
  let D' : X.FSData a :=
    { m := q * D.m
      m_pos := Nat.mul_pos hq D.m_pos
      deg := q • D.deg
      deg_eq := fun c => by
        rw [intCast_nsmul_apply, D.deg_eq c, Nat.cast_mul]
        ring
      terms := scaleTerms q D.terms
      mem_sections := fun t ht => by
        obtain ⟨t', ht', rfl⟩ := mem_scaleTerms.1 ht
        exact hn t' ht' }
  refine ⟨D', ⟨(t₀.1 ^ q, (q : ℝ) * t₀.2), mem_scaleTerms.2 ⟨t₀, ht₀, rfl⟩,
    pow_ne_zero _ ht₀0⟩, fun v => ?_⟩
  rw [Function.comp_apply, hD, FSData.eval_def, FSData.eval_def]
  change _ = ((((q * D.m : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
    (scaleTerms q D.terms).sup fun t => X.termVal (q • D.deg) t v
  have hterm : ∀ t ∈ scaleTerms q D.terms, X.termVal (q • D.deg) t v =
      X.normalization.termVal (q • D.deg) t (hX.anHomeomorph.symm v) := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := mem_scaleTerms.1 ht
    rw [termVal_def, termVal_def, hX.logSecAbs_symm v (hn t' ht')]
  rw [Finset.sup_congr rfl hterm, sup_scaleTerms hq D.mem_sections,
    ProjBerk.ereal_coe_mul_coe_mul]
  congr 2
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Nat.cast_mul]
  field_simp [D.m_ne_zero]

/-- **Psh functions descend through the normalization in characteristic `p`**
(`thm:gl-normalization-reflection`, characteristic `p`; FHX Theorem 8.3): if `char k = p > 0`,
then `ψ ∘ (ν^an)⁻¹ ∈ PSH(𝒳, θ)` for every `ψ ∈ PSH(𝒴, θ)` and **every** `θ ∈ ℝ^r`. The
approximating Fubini–Study nets descend termwise (`isFS_comp_symm_of_charP`); no PSH2 is used. -/
theorem isPSH_comp_symm_of_charP [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {θ : Fin r → ℝ} {ψ : X.normalization.an → EReal} (hψ : X.normalization.IsPSH θ ψ) :
    X.IsPSH θ (ψ ∘ hX.anHomeomorph.symm) :=
  FSSystemC.IsPSH.comp_of_isFS (F := X.normalization.fsSystem) (G := X.fsSystem)
    hX.anHomeomorph.symm.continuous hX.anHomeomorph_symm_triv
    (fun _ _ hφ => hX.isFS_comp_symm_of_charP p hφ) hψ

end IsUnibranch

end Unibranch

end MultiModel

end EnvelopeProperty
