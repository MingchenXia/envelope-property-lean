/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupChartInverse
import EnvelopeProperty.Global.FibreChartCover

/-!
# Actual Rees-chart atlas of the existing bigraded blowup point model

The constructed inverse chart point proves that the original chart map
has exactly the two-coordinate nonvanishing locus as image. It is an open
embedding and gives a genuine chart homeomorphism. Over a fixed value-one
base coordinate every point has a chart representative retaining the whole
original affine base seminorm. No native whole-fibre comparison is assumed.
-/

open scoped NNReal Topology
open Topology MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))

section DomainChart
variable [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

/-- The actual original chart map has exactly the asserted coordinate-open
image, by the constructed inverse evaluation and its whole-point identity. -/
theorem fc_range_chartPoint
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) :
    Set.range (B.chartPoint i hg hg0) =
      {y : B.an | (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0 ∧
        (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0} := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · rw [B.chartPoint_val_X_inl_self hg hg0 w]
      exact inv_ne_zero (B.scaleX_chartHom_ne_zero g w)
    · rw [B.chartPoint_val_X_inr_of_centerGen_eq hg hg0 w hl]
      exact inv_ne_zero (B.scaleY_chartHom_ne_zero hg hg0 w)
  · rintro ⟨hyi, hyl⟩
    exact ⟨B.fc_chartInversePoint i hg0 l hl y hyi hyl,
      B.fc_chartPoint_chartInversePoint i hg hg0 l hl y hyi hyl⟩

/-- The original paper Rees chart is a genuine open chart of the entire
bigraded blowup model, with no assumed chart-cover certificate. -/
theorem fc_isOpenEmbedding_chartPoint
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    IsOpenEmbedding (B.chartPoint i hg hg0) := by
  obtain ⟨l, hl⟩ := (B.mem_centerSet_iff i).1 hg
  refine ⟨B.fc_isEmbedding_chartPoint i hg hg0, ?_⟩
  rw [B.fc_range_chartPoint i hg hg0 l hl]
  have hc (P : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
      Continuous (fun y : B.an => (y : BiProjBerk k M M').1.val P) :=
    (Berk.continuous_val_apply P).comp (BiProjBerk.continuous_val.comp
      (continuous_subtype_val : Continuous (Subtype.val : B.an → BiProjBerk k M M')))
  exact (isOpen_ne.preimage (hc (X (Sum.inl i)))).inter
    (isOpen_ne.preimage (hc (X (Sum.inr l))))

/-- The original actual fraction-adjoin chart ring gives the whole old
bigraded analytic coordinate-open locus, including its topology. -/
def fc_chartHomeomorph
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) :
    Berk k (blowupChart (B.centerSet i) g) ≃ₜ
      {y : B.an // (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0 ∧
        (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0} :=
  (B.fc_chartPointRangeHomeomorph i hg hg0).trans
    (Homeomorph.setCongr (B.fc_range_chartPoint i hg hg0 l hl))

@[simp]
theorem fc_chartHomeomorph_apply
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g)
    (w : Berk k (blowupChart (B.centerSet i) g)) :
    (B.fc_chartHomeomorph i hg hg0 l hl w).1 = B.chartPoint i hg hg0 w := rfl

end DomainChart

/-- Every point in the entire old fibre is represented by an actual
nonzero original Rees chart, retaining its whole affine base seminorm.
The required chart domain structure is derived from the given base point. -/
theorem fc_exists_chartPoint_eq (t : V.an)
    (hi : (t : ProjBerk k M).1.val (X i) = 1) (y : B.an) (hy : B.proj y = t) :
    letI := fc_isDomain_baseChart t i hi
    ∃ (l : Fin (M' + 1)) (hl0 : B.centerGen i l ≠ 0)
      (w : Berk k (blowupChart (B.centerSet i) (B.centerGen i l))),
      Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) (B.centerGen i l)) w =
        V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero) ∧
      B.chartPoint i (B.centerGen_mem_centerSet i l) hl0 w = y := by
  let := fc_isDomain_baseChart t i hi
  obtain ⟨l, hl0, hyl⟩ := B.fc_exists_nonzero_generator_val_one t i hi y
  have hyi := (B.fc_fibre_val_X_inl hy i).trans hi
  let w := B.fc_chartInversePoint i hl0 l rfl y
    (hyi.trans_ne one_ne_zero) (hyl.trans_ne one_ne_zero)
  have he := B.fc_chartPoint_chartInversePoint i (B.centerGen_mem_centerSet i l) hl0 l rfl y
    (hyi.trans_ne one_ne_zero) (hyl.trans_ne one_ne_zero)
  refine ⟨l, hl0, w, ?_, he⟩
  apply (ProjSubvariety.isOpenEmbedding_chartInv (X := V)
    (isHomogeneous_X k i) one_pos).injective
  calc
    V.chartInv (X i) 1 (isHomogeneous_X k i) one_pos
        (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) (B.centerGen i l)) w) =
        B.proj (B.chartPoint i (B.centerGen_mem_centerSet i l) hl0 w) :=
      (B.proj_chartPoint (B.centerGen_mem_centerSet i l) hl0 w).symm
    _ = t := by rw [he, hy]
    _ = V.chartInv (X i) 1 (isHomogeneous_X k i) one_pos
        (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)) :=
      (ProjSubvariety.chartInv_chartMap (isHomogeneous_X k i) one_pos t
        (hi.trans_ne one_ne_zero)).symm

end EnvelopeProperty.ProjSubvariety.BlowupCenter
