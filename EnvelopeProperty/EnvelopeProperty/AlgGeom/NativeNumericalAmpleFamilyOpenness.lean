import EnvelopeProperty.AlgGeom.NativeNumericalAmpleCone

/-! # Full intrinsic ample-cone openness under every finite original line-family map -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.NativeRealNumericalClasses

private def directionalInteriorCone {M : Type*} [AddCommGroup M] [Module ℝ M]
    {ι : Type*} [Fintype ι] (C : ConvexCone ℝ M) (F : (ι → ℝ) →ₗ[ℝ] M) :
    ConvexCone ℝ M where
  carrier := {x | ∃ ε : ℝ, 0 < ε ∧ ∀ a : ι → ℝ, (∀ i, |a i| < ε) → x + F a ∈ C}
  smul_mem' := by
    intro r hr x hx
    obtain ⟨ε, hε, hx⟩ := hx
    refine ⟨r * ε, mul_pos hr hε, fun a ha => ?_⟩
    have hsmall (i : ι) : |(r⁻¹ • a) i| < ε := by
      have h := (div_lt_iff₀ hr).2 (show |a i| < ε * r by simpa only [mul_comm] using ha i)
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hr,
        div_eq_inv_mul] using h
    have h := C.smul_mem hr (hx (r⁻¹ • a) hsmall)
    simpa only [smul_add, F.map_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h
  add_mem' := by
    intro x hx y hy
    obtain ⟨ε, hε, hx⟩ := hx
    obtain ⟨δ, hδ, hy⟩ := hy
    have hyC : y ∈ C := by simpa using hy 0 (fun _ => by simpa using hδ)
    refine ⟨ε, hε, fun a ha => ?_⟩
    simpa only [add_assoc, add_left_comm, add_comm] using C.add_mem (hx a ha) hyC

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (p : X ⟶ Spec (.of k)) [IsProjective p] {ι : Type v} [Fintype ι]
  (B : ι → X.Modules) (hB : ∀ i, IsInvertible (B i))

/-- Every class of the SAME true ample cone has a derived positive perturbation radius
along EVERY finite family of original numerical lines, without a topology premise on N1. -/
theorem exists_ampleCone_lineFamily_radius (θ : Space p) (hθ : θ ∈ ampleCone p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ι → ℝ, (∀ i, |a i| < ε) →
      θ + lineFamilyMap p B hB a ∈ ampleCone p := by
  have h : ampleCone p ≤ directionalInteriorCone (ampleCone p) (lineFamilyMap p B hB) := by
    apply ConvexCone.hull_min
    rintro _ ⟨A, hA, rfl⟩
    exact exists_ample_lineFamily_radius p A hA B hB
  exact h hθ

/-- The inverse image of the ENTIRE genuine intrinsic ample cone under EVERY original
finite line-family map is ordinary open in its real coefficient space. -/
theorem isOpen_lineFamilyMap_preimage_ampleCone :
    IsOpen {a : ι → ℝ | lineFamilyMap p B hB a ∈ ampleCone p} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro a ha
  obtain ⟨ε, hε, h⟩ := exists_ampleCone_lineFamily_radius p B hB _ ha
  refine ⟨{b : ι → ℝ | ∀ i, |b i - a i| < ε}, ?_, ?_, ?_⟩
  · intro b hb
    have hsmall : ∀ i, |(b - a) i| < ε := hb
    have hh := h (b - a) hsmall
    rwa [map_sub, add_sub_cancel] at hh
  · simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt ((continuous_apply i).sub continuous_const |>.abs) continuous_const
  · simpa using fun _ : ι => hε

end EnvelopeProperty.NativeRealNumericalClasses
