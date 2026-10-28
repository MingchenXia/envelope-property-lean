/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupChartKernel
import EnvelopeProperty.Global.BlowupChartEmbedding
import EnvelopeProperty.Projective.Bihomogenize

/-!
# Constructed inverse evaluations for the original blowup charts

Divide the actual completed-residue-field coordinate evaluations by the
two selected nonzero coordinates. Bihomogenization and the proved exact
homogeneous chart kernel make this evaluation descend through the actual
surjective chart homomorphism. No inverse point or comparison is assumed.
-/

open scoped NNReal Topology
open Topology MvPolynomial
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))

/-- Evaluate the original homogeneous coordinates as genuine fractions in
the actual completed residue field of the whole original point. -/
def fc_chartDehomEval (y : B.an) (l : Fin (M' + 1)) :
    MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k]
      Berk.H (y : BiProjBerk k M M').1 :=
  aeval (Sum.elim
    (fun j => (y : BiProjBerk k M M').1.toH (X (Sum.inl j)) /
      (y : BiProjBerk k M M').1.toH (X (Sum.inl i)))
    (fun m => (y : BiProjBerk k M M').1.toH (X (Sum.inr m)) /
      (y : BiProjBerk k M M').1.toH (X (Sum.inr l))))

/-- This is the actual weighted homogeneous evaluation identity, on every
form and not just on coordinate generators. -/
theorem fc_chartDehomEval_of_isWeightedHomogeneous (y : B.an) (l : Fin (M' + 1))
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    B.fc_chartDehomEval i y l F =
      ((y : BiProjBerk k M M').1.toH (X (Sum.inl i)))⁻¹ ^ a *
        ((y : BiProjBerk k M M').1.toH (X (Sum.inr l)))⁻¹ ^ b *
          (y : BiProjBerk k M M').1.toH F := by
  let q := (y : BiProjBerk k M M').1
  let ρ : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] Berk.H q :=
    IsScalarTower.toAlgHom k _ _
  have hρ : (aeval fun v => ρ (X v)) = ρ := by
    ext v
    simp only [aeval_X]
  have hfun : (Sum.elim
      (fun j => q.toH (X (Sum.inl j)) / q.toH (X (Sum.inl i)))
      (fun m => q.toH (X (Sum.inr m)) / q.toH (X (Sum.inr l)))) =
      (fun v => (q.toH (X (Sum.inl i)))⁻¹ ^ (biWeight M M' v).1 *
        (q.toH (X (Sum.inr l)))⁻¹ ^ (biWeight M M' v).2 * ρ (X v)) := by
    funext v
    cases v <;> simp [biWeight, ρ, Berk.algebraMap_H, div_eq_mul_inv, mul_comm]
  change (aeval (Sum.elim
      (fun j => q.toH (X (Sum.inl j)) / q.toH (X (Sum.inl i)))
      (fun m => q.toH (X (Sum.inr m)) / q.toH (X (Sum.inr l))))) F = _
  rw [hfun, hF.aeval_pow_mul_pow_mul, hρ]
  rfl

theorem fc_chartDehomEval_X_inl_self (y : B.an) (l : Fin (M' + 1))
    (hi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0) :
    B.fc_chartDehomEval i y l (X (Sum.inl i)) = 1 := by
  change (aeval _) (X (Sum.inl i)) = 1
  rw [aeval_X]
  exact div_self (fun h => hi (((y : BiProjBerk k M M').1.toH_eq_zero_iff).1 h))

theorem fc_chartDehomEval_X_inr_self (y : B.an) (l : Fin (M' + 1))
    (hl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0) :
    B.fc_chartDehomEval i y l (X (Sum.inr l)) = 1 := by
  change (aeval _) (X (Sum.inr l)) = 1
  rw [aeval_X]
  exact div_self (fun h => hl (((y : BiProjBerk k M M').1.toH_eq_zero_iff).1 h))

variable [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

/-- The genuine chart kernel is contained in the kernel of the constructed
fraction evaluation, including all nonhomogeneous polynomials. -/
theorem fc_chartHom_ker_le_chartDehomEval
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0) :
    RingHom.ker (B.chartHom i g).toRingHom ≤
      RingHom.ker (B.fc_chartDehomEval i y l).toRingHom := by
  intro P hP
  change B.chartHom i g P = 0 at hP
  change B.fc_chartDehomEval i y l P = 0
  obtain ⟨⟨a, b⟩, F, hF, eφ, eψ⟩ := exists_bihomogeneous_pair_of_map_coordinates_eq_one
    (B.chartHom i g) (B.fc_chartDehomEval i y l) i l
    (B.chartHom_X_inl_self g) (B.chartHom_X_inr_of_centerGen_eq hg0 hl)
    (B.fc_chartDehomEval_X_inl_self i y l hyi) (B.fc_chartDehomEval_X_inr_self i y l hyl) P
  have hFI := (B.fc_chartHom_eq_zero_iff_mem_ideal i hg0 hF).1 (eφ.trans hP)
  have hz : (y : BiProjBerk k M M').1.toH F = 0 :=
    ((y : BiProjBerk k M M').1.toH_eq_zero_iff).2 (y.2 F hFI)
  rw [← eψ, B.fc_chartDehomEval_of_isWeightedHomogeneous i y l hF, hz, mul_zero]

/-- The actual dehomogeneous evaluation descends to the whole original
fraction-adjoin chart algebra by its proved kernel and surjectivity. -/
def fc_chartInverseEval
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0) :
    blowupChart (B.centerSet i) g →ₐ[k] Berk.H (y : BiProjBerk k M M').1 :=
  AlgHom.liftOfSurjective (B.chartHom i g) (B.fc_chartHom_surjective i g)
    (B.fc_chartDehomEval i y l) (B.fc_chartHom_ker_le_chartDehomEval i hg0 l hl y hyi hyl)

@[simp]
theorem fc_chartInverseEval_chartHom
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0)
    (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    B.fc_chartInverseEval i hg0 l hl y hyi hyl (B.chartHom i g F) =
      B.fc_chartDehomEval i y l F :=
  AlgHom.liftOfSurjective_apply _ _ _ _ F

/-- Pulling the actual completed-field norm back through the constructed
evaluation gives an original paper affine-chart point. -/
def fc_chartInversePoint
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0) :
    Berk k (blowupChart (B.centerSet i) g) where
  val := (NormedField.valuation (K := Berk.H (y : BiProjBerk k M M').1)).comap
    (B.fc_chartInverseEval i hg0 l hl y hyi hyl).toRingHom
  val_algebraMap c hc := by
    change ‖B.fc_chartInverseEval i hg0 l hl y hyi hyl
      (algebraMap k (blowupChart (B.centerSet i) g) c)‖₊ = 1
    rw [AlgHom.commutes]
    apply NNReal.eq
    exact Berk.norm_algebraMap_k_H (y : BiProjBerk k M M').1 hc

/-- Every homogeneous polynomial has its exact original divided value at
the constructed inverse chart point. -/
theorem fc_chartInversePoint_val_of_isWeightedHomogeneous
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0)
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    (B.fc_chartInversePoint i hg0 l hl y hyi hyl).val (B.chartHom i g F) =
      (y : BiProjBerk k M M').1.val F /
        ((y : BiProjBerk k M M').1.val (X (Sum.inl i)) ^ a *
          (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ^ b) := by
  change ‖B.fc_chartInverseEval i hg0 l hl y hyi hyl (B.chartHom i g F)‖₊ = _
  rw [B.fc_chartInverseEval_chartHom, B.fc_chartDehomEval_of_isWeightedHomogeneous i y l hF]
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_inv, Berk.nnnorm_toH,
    div_eq_mul_inv, mul_inv, inv_pow]
  ac_rfl

/-- The first normalization scale of the constructed inverse point is
exactly the inverse of the selected original coordinate value. -/
theorem fc_scaleX_chartInversePoint
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0) :
    BiProjBerk.scaleX (B.chartHom i g) (B.fc_chartInversePoint i hg0 l hl y hyi hyl) =
      ((y : BiProjBerk k M M').1.val (X (Sum.inl i)))⁻¹ := by
  let w := B.fc_chartInversePoint i hg0 l hl y hyi hyl
  have hcoord (j : Fin (M + 1)) : w.val (B.chartHom i g (X (Sum.inl j))) =
      (y : BiProjBerk k M M').1.val (X (Sum.inl j)) /
        (y : BiProjBerk k M M').1.val (X (Sum.inl i)) := by
    simpa only [pow_one, pow_zero, mul_one] using
      B.fc_chartInversePoint_val_of_isWeightedHomogeneous i hg0 l hl y hyi hyl
        (isWeightedHomogeneous_X k (biWeight M M') (Sum.inl j))
  change Finset.univ.sup (fun j => w.val (B.chartHom i g (X (Sum.inl j)))) = _
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    rw [hcoord j, div_eq_mul_inv]
    exact (mul_le_mul' ((y : BiProjBerk k M M').val_X_inl_le_one j) le_rfl).trans_eq
      (one_mul _)
  · obtain ⟨j, hj⟩ := (y : BiProjBerk k M M').exists_val_X_inl_eq_one
    have he := hcoord j
    rw [hj, one_div] at he
    exact he.symm.trans_le (Finset.le_sup (f := fun j =>
      w.val (B.chartHom i g (X (Sum.inl j)))) (Finset.mem_univ j))

/-- The second normalization scale is likewise the inverse of the original
selected coordinate value, with no bounded-coefficient assumption. -/
theorem fc_scaleY_chartInversePoint
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0) :
    BiProjBerk.scaleY (B.chartHom i g) (B.fc_chartInversePoint i hg0 l hl y hyi hyl) =
      ((y : BiProjBerk k M M').1.val (X (Sum.inr l)))⁻¹ := by
  let w := B.fc_chartInversePoint i hg0 l hl y hyi hyl
  have hcoord (m : Fin (M' + 1)) : w.val (B.chartHom i g (X (Sum.inr m))) =
      (y : BiProjBerk k M M').1.val (X (Sum.inr m)) /
        (y : BiProjBerk k M M').1.val (X (Sum.inr l)) := by
    simpa only [pow_one, pow_zero, one_mul] using
      B.fc_chartInversePoint_val_of_isWeightedHomogeneous i hg0 l hl y hyi hyl
        (isWeightedHomogeneous_X k (biWeight M M') (Sum.inr m))
  change Finset.univ.sup (fun m => w.val (B.chartHom i g (X (Sum.inr m)))) = _
  apply le_antisymm
  · apply Finset.sup_le
    intro m _
    rw [hcoord m, div_eq_mul_inv]
    exact (mul_le_mul' ((y : BiProjBerk k M M').val_X_inr_le_one m) le_rfl).trans_eq
      (one_mul _)
  · obtain ⟨m, hm⟩ := (y : BiProjBerk k M M').exists_val_X_inr_eq_one
    have he := hcoord m
    rw [hm, one_div] at he
    exact he.symm.trans_le (Finset.le_sup (f := fun m =>
      w.val (B.chartHom i g (X (Sum.inr m)))) (Finset.mem_univ m))

/-- The genuinely constructed inverse point recovers the entire original
bigraded blowup point on the actual two-coordinate nonvanishing locus. -/
theorem fc_chartPoint_chartInversePoint
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0)
    (l : Fin (M' + 1)) (hl : B.centerGen i l = g) (y : B.an)
    (hyi : (y : BiProjBerk k M M').1.val (X (Sum.inl i)) ≠ 0)
    (hyl : (y : BiProjBerk k M M').1.val (X (Sum.inr l)) ≠ 0) :
    B.chartPoint i hg hg0 (B.fc_chartInversePoint i hg0 l hl y hyi hyl) = y := by
  apply Subtype.ext
  apply BiProjBerk.ext_of_isWeightedHomogeneous
  intro ⟨a, b⟩ F hF
  rw [B.chartPoint_val_of_isWeightedHomogeneous hg hg0 _ hF,
    B.fc_chartInversePoint_val_of_isWeightedHomogeneous i hg0 l hl y hyi hyl hF,
    B.fc_scaleX_chartInversePoint, B.fc_scaleY_chartInversePoint, inv_pow, inv_pow,
    ← mul_inv, div_inv_eq_mul,
    div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hyi) (pow_ne_zero _ hyl))]

end EnvelopeProperty.ProjSubvariety.BlowupCenter
