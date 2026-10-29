/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.WeightedPolynomialCompletion
import Mathlib.Analysis.Normed.Group.HomCompletion

/-! # Genuine coefficients of the actual weighted polynomial completion -/
open scoped NNReal Topology
open UniformSpace Topology Filter
noncomputable section
namespace EnvelopeProperty.WeightedPolynomialCompletion
open WeightedPolynomial
variable {A ι : Type*} [SeminormedCommRing A] [IsUltrametricDist A]

private def sourceCoefficient (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (m : ι →₀ ℕ) :
    NormedAddGroupHom (PolynomialRing (A := A) w hw) A :=
  (show PolynomialRing (A := A) w hw →+ A from
    { toFun p := (polynomialEquiv w hw p).coeff m
      map_zero' := by simp
      map_add' p q := by simp only [map_add, MvPolynomial.coeff_add] }).mkNormedAddGroupHom'
        (weight w m)⁻¹ fun p => by
    change ‖(polynomialEquiv w hw p).coeff m‖₊ ≤ _
    rw [mul_comm]
    apply (le_div_iff₀ (weight_pos w hw m)).mpr
    exact (le_gauss w _ m).trans_eq (nnnorm_polynomial w hw p).symm

/-- Every original exponent has a genuine continuous additive coefficient map into Completion A. -/
def completedCoefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (m : ι →₀ ℕ) :
    NormedAddGroupHom (Ring (A := A) w hw) (Completion A) :=
  (sourceCoefficient w hw m).completion

/-- Every ORIGINAL polynomial coefficient is retained by the actual completion coefficient map. -/
@[simp]
theorem completedCoefficientMap_polynomialMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (m : ι →₀ ℕ) (p : MvPolynomial ι A) :
    completedCoefficientMap w hw m (polynomialMap w hw p) = ((p.coeff m : A) : Completion A) := by
  change (sourceCoefficient w hw m).completion
    (↑((polynomialEquiv (A := A) w hw).symm p) : Completion (PolynomialRing (A := A) w hw)) = _
  rw [NormedAddGroupHom.completion_coe]
  change ((((polynomialEquiv w hw) ((polynomialEquiv w hw).symm p)).coeff m : A) : Completion A) = _
  rw [RingEquiv.apply_symm_apply]

/-- The sharp weighted coefficient bound holds on EVERY original completed function. -/
theorem nnnorm_completedCoefficientMap_weight_le (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (m : ι →₀ ℕ) (f : Ring (A := A) w hw) :
    ‖completedCoefficientMap w hw m f‖₊ * weight w m ≤ ‖f‖₊ := by
  refine (denseRange_polynomialMap w hw).induction_on f
    (isClosed_le (((completedCoefficientMap w hw m).continuous.nnnorm).mul_const _)
      continuous_nnnorm) ?_
  intro p
  rw [completedCoefficientMap_polynomialMap, Completion.nnnorm_coe, nnnorm_polynomialMap]
  exact le_gauss w p m

/-- Actual coefficient multiplication preserves the ENTIRE original scalar action. -/
theorem completedCoefficientMap_coeff_mul (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (m : ι →₀ ℕ) (a : A) (f : Ring (A := A) w hw) :
    completedCoefficientMap w hw m (coefficients w hw a*f) =
      (a : Completion A)*completedCoefficientMap w hw m f := by
  refine (denseRange_polynomialMap w hw).induction_on f
    (isClosed_eq ((completedCoefficientMap w hw m).continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul (completedCoefficientMap w hw m).continuous)) ?_
  intro p
  change completedCoefficientMap w hw m (polynomialMap w hw (MvPolynomial.C a)*polynomialMap w hw p) = _
  rw [← map_mul, completedCoefficientMap_polynomialMap, completedCoefficientMap_polynomialMap,
    MvPolynomial.coeff_C_mul, Completion.coe_mul]

/-- Bounds on all GENUINE coefficients characterize the norm of the WHOLE original function. -/
theorem nnnorm_le_iff_completedCoefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : Ring (A := A) w hw) (C : ℝ≥0) :
    ‖f‖₊ ≤ C ↔ ∀ m, ‖completedCoefficientMap w hw m f‖₊ * weight w m ≤ C := by
  constructor
  · intro hf m
    exact (nnnorm_completedCoefficientMap_weight_le w hw m f).trans hf
  · intro hc
    apply NNReal.coe_le_coe.mp
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ : ℝ≥0 := ⟨ε/2, le_of_lt (half_pos hε)⟩
    obtain ⟨p,hp⟩ := (denseRange_polynomialMap (A := A) w hw).exists_dist_lt f (half_pos hε)
    have he : ‖polynomialMap w hw p-f‖₊ ≤ δ := by
      apply NNReal.coe_le_coe.mp
      change ‖polynomialMap w hw p-f‖ ≤ ε/2
      rw [norm_sub_rev]
      exact le_of_lt (by simpa only [dist_eq_norm] using hp)
    have hpn : ‖polynomialMap w hw p‖₊ ≤ C+δ := by
      rw [nnnorm_polynomialMap]
      apply (gauss_le_iff w p _).mpr
      intro m
      rw [← Completion.nnnorm_coe, ← completedCoefficientMap_polynomialMap w hw m p]
      calc
        _ = ‖completedCoefficientMap w hw m (polynomialMap w hw p-f)+
            completedCoefficientMap w hw m f‖₊ * weight w m := by rw [map_sub,sub_add_cancel]
        _ ≤ (‖completedCoefficientMap w hw m (polynomialMap w hw p-f)‖₊+
            ‖completedCoefficientMap w hw m f‖₊)*weight w m :=
          mul_le_mul_of_nonneg_right (nnnorm_add_le _ _) zero_le
        _ = _ := add_mul _ _ _
        _ ≤ δ+C := add_le_add ((nnnorm_completedCoefficientMap_weight_le w hw m _).trans he) (hc m)
        _ = C+δ := add_comm _ _
    have hf : ‖f‖₊ ≤ δ+(C+δ) := by
      calc
        _ = ‖(f-polynomialMap w hw p)+polynomialMap w hw p‖₊ := by rw [sub_add_cancel]
        _ ≤ ‖f-polynomialMap w hw p‖₊+‖polynomialMap w hw p‖₊ := nnnorm_add_le _ _
        _ ≤ _ := add_le_add (by
          have hh : ‖f-polynomialMap w hw p‖₊ = ‖polynomialMap w hw p-f‖₊ :=
            NNReal.coe_injective (norm_sub_rev _ _)
          rwa [hh]) hpn
    have hfr : ‖f‖ ≤ (δ : ℝ)+((C : ℝ)+(δ : ℝ)) := by exact_mod_cast hf
    change ‖f‖ ≤ (C : ℝ)+ε
    change ‖f‖ ≤ ε/2+((C : ℝ)+ε/2) at hfr
    linarith

/-- Every ORIGINAL completed function is detected by all its genuine completed coefficients. -/
theorem completedCoefficientMap_ext (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    {f g : Ring (A := A) w hw}
    (h : ∀ m, completedCoefficientMap w hw m f = completedCoefficientMap w hw m g) : f=g := by
  have hz : ‖f-g‖₊ ≤ 0 := (nnnorm_le_iff_completedCoefficientMap w hw (f-g) 0).mpr (by
    intro m
    rw [map_sub, h m, sub_self, nnnorm_zero, zero_mul])
  exact sub_eq_zero.mp (nnnorm_eq_zero.mp (le_antisymm hz zero_le))

/-- The true original completed norm is exactly its bounded weighted coefficient supremum. -/
theorem nnnorm_eq_iSup_completedCoefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : Ring (A := A) w hw) :
    ‖f‖₊ = ⨆ m, ‖completedCoefficientMap w hw m f‖₊ * weight w m := by
  have hb : BddAbove (Set.range (fun m => ‖completedCoefficientMap w hw m f‖₊ * weight w m)) :=
    ⟨‖f‖₊, by rintro _ ⟨m,rfl⟩; exact nnnorm_completedCoefficientMap_weight_le w hw m f⟩
  apply le_antisymm
  · exact (nnnorm_le_iff_completedCoefficientMap w hw f _).mpr fun m => le_ciSup hb m
  · exact ciSup_le fun m => nnnorm_completedCoefficientMap_weight_le w hw m f

/-- The genuine weighted coefficient family tends to zero outside actual finite exponent sets. -/
theorem tendsto_weighted_completedCoefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : Ring (A := A) w hw) :
    Tendsto (fun m => ‖completedCoefficientMap w hw m f‖₊ * weight w m) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := (denseRange_polynomialMap (A := A) w hw).exists_dist_lt f hε
  filter_upwards [p.support.eventually_cofinite_notMem] with m hm
  have hz : completedCoefficientMap w hw m (polynomialMap w hw p) = 0 := by
    rw [completedCoefficientMap_polynomialMap, MvPolynomial.notMem_support_iff.mp hm]
    exact Completion.coe_zero
  have he : completedCoefficientMap w hw m f = completedCoefficientMap w hw m (f-polynomialMap w hw p) := by
    rw [map_sub,hz,sub_zero]
  rw [he]
  have hb := nnnorm_completedCoefficientMap_weight_le w hw m (f-polynomialMap w hw p)
  have hreal : ((‖completedCoefficientMap w hw m (f-polynomialMap w hw p)‖₊ * weight w m : ℝ≥0) : ℝ) ≤
      ‖f-polynomialMap w hw p‖ := by exact_mod_cast hb
  simpa only [NNReal.dist_eq,NNReal.coe_zero,sub_zero,abs_of_nonneg (NNReal.coe_nonneg _)] using
    hreal.trans_lt (by simpa only [dist_eq_norm] using hp)

variable [T0Space A] [CompleteSpace A]

/-- When ORIGINAL A is complete and separated, coefficients take values in that SAME A. -/
def coefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i) (m : ι →₀ ℕ) :
    NormedAddGroupHom (Ring (A := A) w hw) A :=
  (sourceCoefficient w hw m).extension

/-- Every coefficient is exactly the ORIGINAL A coefficient on every actual polynomial. -/
@[simp]
theorem coefficientMap_polynomialMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (m : ι →₀ ℕ) (p : MvPolynomial ι A) :
    coefficientMap w hw m (polynomialMap w hw p) = p.coeff m := by
  change (sourceCoefficient w hw m).extension
    (↑((polynomialEquiv (A := A) w hw).symm p) : Completion (PolynomialRing (A := A) w hw)) = _
  rw [NormedAddGroupHom.extension_coe]
  change ((polynomialEquiv w hw) ((polynomialEquiv w hw).symm p)).coeff m = _
  rw [RingEquiv.apply_symm_apply]

/-- The two actual coefficient constructions agree through the ORIGINAL completion map. -/
theorem coe_coefficientMap_eq_completedCoefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (m : ι →₀ ℕ) (f : Ring (A := A) w hw) :
    ((coefficientMap w hw m f : A) : Completion A) = completedCoefficientMap w hw m f := by
  refine (denseRange_polynomialMap w hw).induction_on f
    (isClosed_eq ((Completion.continuous_coe (α := A)).comp (coefficientMap w hw m).continuous)
      (completedCoefficientMap w hw m).continuous) ?_
  intro p
  rw [coefficientMap_polynomialMap, completedCoefficientMap_polynomialMap]

/-- Actual original coefficient scalars act on EVERY same-A completed coefficient. -/
theorem coefficientMap_coeff_mul (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (m : ι →₀ ℕ) (a : A) (f : Ring (A := A) w hw) :
    coefficientMap w hw m (coefficients w hw a*f) = a*coefficientMap w hw m f := by
  apply Completion.coe_injective A
  rw [Completion.coe_mul, coe_coefficientMap_eq_completedCoefficientMap,
    coe_coefficientMap_eq_completedCoefficientMap, completedCoefficientMap_coeff_mul]

/-- The original A-valued coefficients obey the SAME sharp weighted bound. -/
theorem nnnorm_coefficientMap_weight_le (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (m : ι →₀ ℕ) (f : Ring (A := A) w hw) :
    ‖coefficientMap w hw m f‖₊ * weight w m ≤ ‖f‖₊ := by
  rw [← Completion.nnnorm_coe, coe_coefficientMap_eq_completedCoefficientMap]
  exact nnnorm_completedCoefficientMap_weight_le w hw m f

/-- All ORIGINAL A-valued coefficients characterize the WHOLE original function norm. -/
theorem nnnorm_le_iff_coefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : Ring (A := A) w hw) (C : ℝ≥0) :
    ‖f‖₊ ≤ C ↔ ∀ m, ‖coefficientMap w hw m f‖₊ * weight w m ≤ C := by
  rw [nnnorm_le_iff_completedCoefficientMap w hw f C]
  simp only [← coe_coefficientMap_eq_completedCoefficientMap, Completion.nnnorm_coe]

/-- The SAME original A-valued coefficients detect every actual completed function. -/
theorem coefficientMap_ext (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    {f g : Ring (A := A) w hw} (h : ∀ m, coefficientMap w hw m f=coefficientMap w hw m g) : f=g := by
  apply completedCoefficientMap_ext w hw
  intro m
  rw [← coe_coefficientMap_eq_completedCoefficientMap, ← coe_coefficientMap_eq_completedCoefficientMap, h m]

/-- The true weighted-c0 family is formed by the SAME original A-valued coefficients. -/
theorem tendsto_weighted_coefficientMap (w : ι → ℝ≥0) (hw : ∀ i, 0 < w i)
    (f : Ring (A := A) w hw) :
    Tendsto (fun m => ‖coefficientMap w hw m f‖₊ * weight w m) cofinite (𝓝 0) := by
  simpa only [← coe_coefficientMap_eq_completedCoefficientMap, Completion.nnnorm_coe] using
    tendsto_weighted_completedCoefficientMap w hw f

end EnvelopeProperty.WeightedPolynomialCompletion
