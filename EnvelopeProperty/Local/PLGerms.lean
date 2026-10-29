/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLSheaf
import EnvelopeProperty.Projective.SubvarietyCompactification
import EnvelopeProperty.Projective.SubvarietyComparison

/-!
# Global PL representatives of logarithmic germs

Homogeneous logarithms, and hence logarithms of regular functions on projective affine
charts, have global PL representatives near every point where they are finite. This is a
local algebraic step in FHX Lemma 5.5; no positivity criterion is assumed here.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty.ProjSubvariety

open ProjBerk

universe u

variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}

/-- A homogeneous logarithm finite at a point has a global PL representative near that point. -/
theorem exists_isPL_log_germ {d : ℕ} {s : MvPolynomial (Fin (M + 1)) k}
    (hs : s.IsHomogeneous d) {x : X.an} (hx : (x : ProjBerk k M).1.val s ≠ 0) :
    ∃ (U : Set X.an) (g : X.an → ℝ), IsOpen U ∧ x ∈ U ∧ X.IsPL g ∧
      ∀ y ∈ U, (y : ProjBerk k M).1.val s ≠ 0 ∧
        g y = Real.log ((y : ProjBerk k M).1.val s : ℝ) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨c, hc⟩ := exists_rat_lt (Real.log ((x : ProjBerk k M).1.val s : ℝ))
  let U : Set X.an := {y | ((c : ℝ) : EReal) < ProjBerk.logAbs s y.1}
  let g : X.an → ℝ := fun y => (max (ProjBerk.logAbs s y.1) ((c : ℝ) : EReal)).toReal
  have hfin := (ProjBerk.isRatFS_logAbs hs hs0).max_const c
  have hg : X.IsPL g := by
    apply IsFinFS.isPL (a := (d : ℚ))
    exact isFinFS_iff_exists_restrict.mpr
      ⟨_, hfin.1, fun v => hfin.2 v.1, fun _ => rfl⟩
  refine ⟨U, g, isOpen_lt continuous_const
    ((ProjBerk.continuous_logAbs s).comp continuous_subtype_val), ?_, hg, ?_⟩
  · change ((c : ℝ) : EReal) < ProjBerk.logAbs s x.1
    rw [ProjBerk.logAbs_def, ENNReal.log_of_nnreal hx]
    exact_mod_cast hc
  · intro y hy
    have hsy : (y : ProjBerk k M).1.val s ≠ 0 := by
      intro hzero
      have hbot := (ProjBerk.logAbs_eq_bot_iff s y.1).mpr hzero
      change ((c : ℝ) : EReal) < ProjBerk.logAbs s y.1 at hy
      rw [hbot] at hy
      exact not_lt_bot hy
    refine ⟨hsy, ?_⟩
    change (max (ProjBerk.logAbs s y.1) ((c : ℝ) : EReal)).toReal = _
    rw [max_eq_left hy.le, ProjBerk.logAbs_def, ENNReal.log_of_nnreal hsy,
      EReal.toReal_coe]

/-- A regular chart function nonzero at a point has a logarithmic germ represented by global PL. -/
theorem exists_isPL_chart_log_germ {σ : MvPolynomial (Fin (M + 1)) k} {d : ℕ}
    (hσ : σ.IsHomogeneous d) (f : QuotChartAlg X.ideal σ d)
    {x : X.an} (hxσ : (x : ProjBerk k M).1.val σ ≠ 0)
    (hxf : (X.chartMap σ d x hxσ).val f ≠ 0) :
    ∃ (U : Set X.an) (g : X.an → ℝ), IsOpen U ∧ x ∈ U ∧ X.IsPL g ∧
      ∀ y ∈ U, ∃ hyσ : (y : ProjBerk k M).1.val σ ≠ 0,
        g y = Real.log ((X.chartMap σ d y hyσ).val f : ℝ) := by
  obtain ⟨N, τ, hτ, rfl⟩ := X.exists_eq_quotChartMk hσ f
  have hxτ : (x : ProjBerk k M).1.val τ ≠ 0 := by
    intro hzero
    apply hxf
    rw [chartMap_val_quotChartMk x hxσ hτ, hzero, zero_div]
  obtain ⟨Uσ, gσ, hUσ, hxUσ, hgσ, heqσ⟩ := exists_isPL_log_germ hσ hxσ
  obtain ⟨Uτ, gτ, hUτ, hxUτ, hgτ, heqτ⟩ := exists_isPL_log_germ hτ hxτ
  refine ⟨Uσ ∩ Uτ, fun y => gτ y - (N : ℝ) * gσ y,
    hUσ.inter hUτ, ⟨hxUσ, hxUτ⟩, hgτ.sub ?_, ?_⟩
  · simpa only [Rat.cast_natCast] using hgσ.smul (N : ℚ)
  · intro y hy
    obtain ⟨hyσ, hyσeq⟩ := heqσ y hy.1
    obtain ⟨hyτ, hyτeq⟩ := heqτ y hy.2
    refine ⟨hyσ, ?_⟩
    change gτ y - (N : ℝ) * gσ y = _
    rw [hyσeq, hyτeq, chartMap_val_quotChartMk y hyσ hτ, NNReal.coe_div,
      NNReal.coe_pow, Real.log_div (NNReal.coe_ne_zero.mpr hyτ)
        (pow_ne_zero N (NNReal.coe_ne_zero.mpr hyσ)), Real.log_pow]

/-- Local convexity already forces global PL membership, before using a positivity criterion. -/
theorem IsLocallyConvex.isPL {a : ℚ} {φ : X.an → ℝ}
    (hφ : X.IsLocallyConvex a φ) : X.IsPL φ := by
  classical
  apply FSSystem.isPL_of_locally_isPL X.fsSystem X.separatesPoints_isPL
  intro x
  obtain ⟨W, hW, hxW, σ, d, hσ, hd, _hσI, hWσ, hconv⟩ := hφ x
  have hxσ := hWσ x hxW
  let z := X.chartMap σ d x hxσ
  have hz : z ∈ X.chartInv σ d hσ hd ⁻¹' W := by
    simpa only [Set.mem_preimage, z, chartInv_chartMap] using hxW
  obtain ⟨V, hV, hzV, _hVW, n, f, s, hs, hf, heq⟩ := hconv z hz
  have hfz : ∀ i, z.val (f i) ≠ 0 := hf z hzV
  choose U g hU hxU hg heqg using fun i =>
    exists_isPL_chart_log_germ hσ (f i) hxσ (hfz i)
  obtain ⟨Uσ, gσ, hUσ, hxUσ, hgσ, heqσ⟩ := exists_isPL_log_germ hσ hxσ
  let A : ((Fin n → ℚ) × ℚ) → X.an → ℝ := fun p y =>
    ∑ i, (p.1 i : ℝ) * g i y + p.2
  have hA : ∀ p, X.IsPL (A p) := by
    intro p
    have hsum : X.IsPL (fun y => ∑ i, (p.1 i : ℝ) * g i y) := by
      change (fun y => ∑ i, (p.1 i : ℝ) * g i y) ∈ X.fsSystem.plSubmodule
      have hh : ∀ i, (fun y => (p.1 i : ℝ) * g i y) ∈ X.fsSystem.plSubmodule :=
        fun i => (hg i).smul (p.1 i)
      convert X.fsSystem.plSubmodule.sum_mem (t := Finset.univ) (fun i _ => hh i) using 1
      ext y
      simp only [Finset.sum_apply]
    exact hsum.add_const p.2
  have hmax : X.IsPL (s.sup' hs A) :=
    Finset.sup'_induction hs A (fun b hb c hc => hb.max hc) (fun p _ => hA p)
  let B : Set X.an := (X.chartInv σ d hσ hd '' V) ∩ Uσ ∩ ⋂ i, U i
  refine ⟨B, fun y => (s.sup' hs A) y + ((a / (d : ℚ) : ℚ) : ℝ) * gσ y, ?_, ?_,
    hmax.add (hgσ.smul (a / (d : ℚ))), ?_⟩
  · exact ((isOpenEmbedding_chartInv hσ hd).isOpenMap V hV).inter hUσ |>.inter
      (isOpen_iInter_of_finite hU)
  · exact ⟨⟨⟨z, hzV, chartInv_chartMap hσ hd x hxσ⟩, hxUσ⟩,
      Set.mem_iInter.mpr hxU⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := hy.1.1
    have hgval : ∀ i, g i (X.chartInv σ d hσ hd t) = Real.log (t.val (f i) : ℝ) := by
      intro i
      obtain ⟨hti, heqi⟩ := heqg i _ (Set.mem_iInter.mp hy.2 i)
      simpa only [chartMap_chartInv] using heqi
    have hσval := (heqσ _ hy.1.2).2
    have hpres := heq t ht
    rw [chartFun] at hpres
    have hreal := EReal.coe_injective hpres
    change φ (X.chartInv σ d hσ hd t) =
      (s.sup' hs A) (X.chartInv σ d hσ hd t) +
        ((a / (d : ℚ) : ℚ) : ℝ) * gσ (X.chartInv σ d hσ hd t)
    rw [Finset.sup'_apply]
    have hAeq : ∀ p, A p (X.chartInv σ d hσ hd t) = tropAffine f p t := by
      intro p
      simp only [A, tropAffine, hgval]
    simp only [hAeq]
    rw [hσval, Rat.cast_div, Rat.cast_natCast]
    linarith

end EnvelopeProperty.ProjSubvariety
