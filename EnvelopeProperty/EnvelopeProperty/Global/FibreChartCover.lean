/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.FibreModel

/-!
# A fixed base chart and genuine nonzero Rees generators cover each fibre

A value-one base coordinate works on the whole analytic blowup fibre.
Every point then has a value-one second coordinate whose original centre
generator is nonzero as a ring element. This constructs the chart index
cover required for comparison with the actual affine-base Rees scheme;
it does not assume or assert the missing inverse chart comparison.
-/

open scoped NNReal Topology
open Topology MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M')

/-- Every point in the whole fibre retains every first-coordinate value. -/
theorem fc_fibre_val_X_inl {t : V.an} {y : B.an} (hy : B.proj y = t)
    (i : Fin (M + 1)) :
    (y : BiProjBerk k M M').1.val (X (Sum.inl i)) =
      (t : ProjBerk k M).1.val (X i) := by
  have he := congrArg (fun z : V.an => (z : ProjBerk k M).1.val (X i)) hy
  simpa only [B.proj_val_apply, rename_X] using he

/-- A value-one base coordinate derives the actual domain structure of its
affine quotient chart; it is not an additional domain hypothesis. -/
theorem fc_isDomain_baseChart (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (X i) = 1) :
    IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1) :=
  ProjBerk.isDomain_quotChartAlg
    (ProjSubvariety.notMem_ideal_of_val_ne_zero (hi.trans_ne one_ne_zero))

/-- The second value-one coordinate of a fibre point always corresponds to
a genuinely nonzero original Rees generator. -/
theorem fc_exists_nonzero_generator_val_one (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (X i) = 1)
    (y : B.an) :
    ∃ l : Fin (M' + 1), B.centerGen i l ≠ 0 ∧
      (y : BiProjBerk k M M').1.val (X (Sum.inr l)) = 1 := by
  obtain ⟨l, hl⟩ := (y : BiProjBerk k M M').exists_val_X_inr_eq_one
  refine ⟨l, ?_, hl⟩
  intro hzero
  have hG := (B.centerGen_eq_zero_iff i
    (ProjSubvariety.notMem_ideal_of_val_ne_zero (hi.trans_ne one_ne_zero)) l).1 hzero
  have hY : (X (Sum.inr l) : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) ∈ B.ideal := by
    apply (B.mem_ideal_iff_of_isWeightedHomogeneous
      (isWeightedHomogeneous_X k (biWeight M M') (Sum.inr l))).2
    simpa only [B.subst_X_inr] using hG
  exact one_ne_zero (hl.symm.trans (y.2 _ hY))

/-- The actual open second-coordinate locus on the entire original fibre. -/
def fcFibreYChart (t : V.an) (l : Fin (M' + 1)) :
    Set {y : B.an // B.proj y = t} :=
  {y | (y.1 : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0}

theorem isOpen_fcFibreYChart (t : V.an) (l : Fin (M' + 1)) :
    IsOpen (B.fcFibreYChart t l) := by
  exact isOpen_ne.preimage
    (((Berk.continuous_val_apply (X (Sum.inr l))).comp continuous_subtype_val).comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- Nonzero original Rees-generator indices give a genuine finite open
cover of the whole original analytic fibre over the chosen base chart. -/
theorem fc_fibre_iUnion_yChart (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (X i) = 1) :
    (⋃ l : {l : Fin (M' + 1) // B.centerGen i l ≠ 0}, B.fcFibreYChart t l.1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨l, hl, hv⟩ := B.fc_exists_nonzero_generator_val_one t i hi y.1
  exact Set.mem_iUnion.mpr ⟨⟨l, hl⟩, hv.trans_ne one_ne_zero⟩

/-- Normalizing the base coordinate to value one normalizes the entire
affine coordinate family without a bound hypothesis. -/
theorem fc_baseChart_sup_X (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (X i) = 1) :
    Finset.univ.sup (fun j =>
      (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val
        (ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j))) = 1 := by
  have hform (j : Fin (M + 1)) : (X j : MvPolynomial (Fin (M + 1)) k).IsHomogeneous (1 * 1) := by
    simpa using isHomogeneous_X k j
  simp_rw [ProjSubvariety.chartMap_val_quotChartMk t (hi.trans_ne one_ne_zero) (hform _),
    hi, one_pow, div_one]
  exact (t : ProjBerk k M).sup_val_X

end EnvelopeProperty.ProjSubvariety.BlowupCenter
