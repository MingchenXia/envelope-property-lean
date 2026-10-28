/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupChartHomSurjective

/-!
# Faithfulness of the actual paper blowup chart point map

The two selected coordinate values recover the normalization scales.
Every original chart-ring element has a bihomogeneous representative, so
its entire seminorm value is recovered from the bigraded point. No chart
inverse or covering statement is assumed.
-/

open scoped NNReal Topology
open Topology MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))
    [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

/-- Every bihomogeneous representative recovers its whole chart element
value from the actual normalized bigraded point and its two coordinates. -/
theorem fc_chartPoint_recover_val
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g)
    (w : Berk k (blowupChart (B.centerSet i) g)) {a b : ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    w.val (B.chartHom i g F) =
      (B.chartPoint i hg hg0 w : BiProjBerk k M M').1.val F /
        ((B.chartPoint i hg hg0 w : BiProjBerk k M M').1.val (X (Sum.inl i)) ^ a *
          (B.chartPoint i hg hg0 w : BiProjBerk k M M').1.val (X (Sum.inr l)) ^ b) := by
  rw [B.chartPoint_val_of_isWeightedHomogeneous hg hg0 w hF,
    B.chartPoint_val_X_inl_self hg hg0 w,
    B.chartPoint_val_X_inr_of_centerGen_eq hg hg0 w hl]
  have hden : BiProjBerk.scaleX (B.chartHom i g) w ^ a *
      BiProjBerk.scaleY (B.chartHom i g) w ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (B.scaleX_chartHom_ne_zero g w))
      (pow_ne_zero _ (B.scaleY_chartHom_ne_zero hg hg0 w))
  rw [show (BiProjBerk.scaleX (B.chartHom i g) w)⁻¹ ^ a *
      (BiProjBerk.scaleY (B.chartHom i g) w)⁻¹ ^ b =
      (BiProjBerk.scaleX (B.chartHom i g) w ^ a *
        BiProjBerk.scaleY (B.chartHom i g) w ^ b)⁻¹ from by simp only [inv_pow, mul_inv],
    div_inv_eq_mul, div_mul_cancel₀ _ hden]

/-- The original chart map is faithful on the entire seminorm, including
sums of chart fractions, for every genuine nonzero Rees generator. -/
theorem fc_chartPoint_injective
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    Function.Injective (B.chartPoint i hg hg0) := by
  obtain ⟨l, hl⟩ := (B.mem_centerSet_iff i).1 hg
  intro w w' hw
  apply Berk.ext_val
  intro z
  obtain ⟨⟨a, b⟩, F, hF, hFz⟩ := B.fc_chartHom_homogeneous_preimage i hg0 l hl z
  rw [← hFz, B.fc_chartPoint_recover_val i hg hg0 l hl w hF,
    B.fc_chartPoint_recover_val i hg hg0 l hl w' hF, hw]

/-- The entire old affine chart is homeomorphic to its actual image in the
bigraded blowup point space. The inverse is continuous on every original
ring element, by the proved bihomogeneous value-recovery formula. -/
def fc_chartPointRangeHomeomorph
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    Berk k (blowupChart (B.centerSet i) g) ≃ₜ Set.range (B.chartPoint i hg hg0) := by
  let e := Equiv.ofInjective (B.chartPoint i hg hg0) (B.fc_chartPoint_injective i hg hg0)
  refine { toEquiv := e
           continuous_toFun := (B.continuous_chartPoint hg hg0).subtype_mk _
           continuous_invFun := ?_ }
  apply Berk.continuous_iff.mpr
  intro z
  obtain ⟨l, hl⟩ := (B.mem_centerSet_iff i).1 hg
  obtain ⟨⟨a, b⟩, F, hF, hFz⟩ := B.fc_chartHom_homogeneous_preimage i hg0 l hl z
  have he (y : Set.range (B.chartPoint i hg hg0)) :
      B.chartPoint i hg hg0 (e.symm y) = y.1 :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hc (P : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
      Continuous (fun y : Set.range (B.chartPoint i hg hg0) =>
        (y.1 : BiProjBerk k M M').1.val P) :=
    (Berk.continuous_val_apply P).comp (BiProjBerk.continuous_val.comp
      ((continuous_subtype_val : Continuous (Subtype.val : B.an → BiProjBerk k M M')).comp
        (continuous_subtype_val : Continuous
          (Subtype.val : Set.range (B.chartPoint i hg hg0) → B.an))))
  have hx (y : Set.range (B.chartPoint i hg hg0)) :
      (y.1 : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0 := by
    obtain ⟨w, hw⟩ := y.2
    rw [← hw, B.chartPoint_val_X_inl_self hg hg0 w]
    exact inv_ne_zero (B.scaleX_chartHom_ne_zero g w)
  have hy (y : Set.range (B.chartPoint i hg hg0)) :
      (y.1 : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0 := by
    obtain ⟨w, hw⟩ := y.2
    rw [← hw, B.chartPoint_val_X_inr_of_centerGen_eq hg hg0 w hl]
    exact inv_ne_zero (B.scaleY_chartHom_ne_zero hg hg0 w)
  have hcont := (hc F).div ((hc (X (Sum.inl i))).pow a |>.mul
    ((hc (X (Sum.inr l))).pow b))
      (fun y => mul_ne_zero (pow_ne_zero _ (hx y)) (pow_ne_zero _ (hy y)))
  convert hcont using 1
  funext y
  change (e.symm y).val z =
    (y.1 : BiProjBerk k M M').1.val F /
      ((y.1 : BiProjBerk k M M').1.val (X (Sum.inl i)) ^ a *
        (y.1 : BiProjBerk k M M').1.val (X (Sum.inr l)) ^ b)
  rw [← hFz]
  exact (B.fc_chartPoint_recover_val i hg hg0 l hl (e.symm y) hF).trans (by rw [he y])

/-- The actual chart-point map is an embedding; no description of its image
or surjectivity onto an asserted chart is used. -/
theorem fc_isEmbedding_chartPoint
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    IsEmbedding (B.chartPoint i hg hg0) := by
  convert IsEmbedding.subtypeVal.comp
    (B.fc_chartPointRangeHomeomorph i hg hg0).isEmbedding using 1
  funext w
  rfl

end EnvelopeProperty.ProjSubvariety.BlowupCenter
