/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Actual same-bound lifts through normed ideal quotients

The quotient norm is Mathlib's genuine infimum norm. Original ideals are
preserved; closed relation ideals use topological closure, not radicals.
-/
open Topology
noncomputable section
namespace EnvelopeProperty.NormedIdealQuotient
variable {A B : Type*} [SeminormedCommRing A] [SeminormedCommRing B]
  (I : Ideal A) (φ : A →+* B) (hI : ∀ a ∈ I, φ a = 0)

/-- The true quotient lift retains the SAME original positive norm bound. -/
theorem norm_lift_le (C : ℝ) (hC : 0 < C) (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)
    (q : A ⧸ I) : ‖Ideal.Quotient.lift I φ hI q‖ ≤ C * ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, rfl, ha⟩ := Ideal.Quotient.norm_mk_lt q (div_pos hε hC)
  rw [Ideal.Quotient.lift_mk]
  calc
    ‖φ a‖ ≤ C * ‖a‖ := hφ a
    _ ≤ C * ‖(Ideal.Quotient.mk I) a‖ + ε := by
      have hc := mul_lt_mul_of_pos_left ha hC
      rw [mul_add, mul_div_cancel₀ ε hC.ne'] at hc
      exact hc.le

/-- Actual bounded ring maps descend through the genuine quotient with their bound. -/
theorem isBounded_lift (hφ : φ.IsBounded) : (Ideal.Quotient.lift I φ hI).IsBounded := by
  obtain ⟨C, hC, hφ⟩ := hφ
  exact ⟨C, hC, norm_lift_le I φ hI C hC hφ⟩

/-- The actual bounded quotient ring map is continuous, including seminormed targets. -/
theorem continuous_lift_of_bound (C : ℝ) (hC : 0 < C) (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖) :
    Continuous (Ideal.Quotient.lift I φ hI) :=
  AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.lift I φ hI) C
    (norm_lift_le I φ hI C hC hφ)

/-- A true continuous ring map into a separated normed target kills actual relation closure. -/
theorem closure_le_ker_of_continuous {E : Type*} [NormedCommRing E]
    (f : A →+* E) (hf : Continuous f) (h : I ≤ RingHom.ker f) :
    I.closure ≤ RingHom.ker f := by
  change closure (I : Set A) ⊆ (RingHom.ker f : Set A)
  apply closure_minimal h
  exact isClosed_eq hf continuous_const

end EnvelopeProperty.NormedIdealQuotient
