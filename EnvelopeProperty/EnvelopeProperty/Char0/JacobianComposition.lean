/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.RelativeJacobianIdeal

/-!
# Exact composition of the genuine all-original-functions Jacobian ideal

The original source need not have coordinates or free differentials. The
actual source-function determinants factor through any actual intermediate
differential basis, and their generated ideal satisfies the exact chain rule.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module Ideal
open scoped Classical

variable {k R S A : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing A]
  [Algebra k S] [Algebra k A] [Algebra R S] [Algebra R A] [Algebra S A]
  [IsScalarTower k S A] [IsScalarTower R S A] {n : ℕ}

/-- Every original source-function differential matrix satisfies the actual chain rule. -/
theorem sourceFunctionDifferentialMatrix_comp
    (bS : Basis (Fin n) S (KaehlerDifferential k S))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) (w : Fin n → R) :
    sourceFunctionDifferentialMatrix (R := R) bA w = relativeDifferentialMatrix bS bA *
      (algebraMap S A).mapMatrix (sourceFunctionDifferentialMatrix (R := R) bS w) := by
  have h := sourceFunctionDifferentialMatrix_factor bS bA (fun i => algebraMap R S (w i))
  have hleft : sourceFunctionDifferentialMatrix (R := S) bA
      (fun i => algebraMap R S (w i)) = sourceFunctionDifferentialMatrix (R := R) bA w := by
    ext i j
    simp only [sourceFunctionDifferentialMatrix, ← IsScalarTower.algebraMap_apply R S A]
  rw [hleft] at h
  exact h

/-- Determinants of all original source-function tuples satisfy the exact chain rule. -/
theorem sourceFunctionDifferentialMatrix_det_comp
    (bS : Basis (Fin n) S (KaehlerDifferential k S))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) (w : Fin n → R) :
    (sourceFunctionDifferentialMatrix (R := R) bA w).det = relativeDifferentialDet bS bA *
      algebraMap S A (sourceFunctionDifferentialMatrix (R := R) bS w).det := by
  rw [sourceFunctionDifferentialMatrix_comp bS bA w, Matrix.det_mul,
    ← (algebraMap S A).map_det]
  rfl

/-- The genuine original-source Jacobian ideal composes exactly with the actual relative
differential determinant. No coordinates on the original source are assumed. -/
theorem affineRelativeJacobianIdeal_comp
    (bS : Basis (Fin n) S (KaehlerDifferential k S))
    (bA : Basis (Fin n) A (KaehlerDifferential k A)) :
    affineRelativeJacobianIdeal (R := R) bA = span {relativeDifferentialDet bS bA} *
      (affineRelativeJacobianIdeal (R := R) bS).map (algebraMap S A) := by
  rw [affineRelativeJacobianIdeal, affineRelativeJacobianIdeal, Ideal.map_span,
    Ideal.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, Set.mem_singleton _, _, ⟨_, ⟨w, rfl⟩, rfl⟩,
      (sourceFunctionDifferentialMatrix_det_comp bS bA w).symm⟩
  · rintro ⟨r, (rfl : r = _), s, ⟨_, ⟨w, rfl⟩, rfl⟩, rfl⟩
    exact ⟨w, sourceFunctionDifferentialMatrix_det_comp bS bA w⟩

/-- The genuine all-original-functions Jacobian ideal does not depend on the actual target
differential basis. -/
theorem affineRelativeJacobianIdeal_basis_independent
    (bA bA' : Basis (Fin n) A (KaehlerDifferential k A)) :
    affineRelativeJacobianIdeal (R := R) bA = affineRelativeJacobianIdeal (R := R) bA' := by
  have h := affineRelativeJacobianIdeal_comp (R := R) (S := A) bA bA'
  have hu : span {relativeDifferentialDet bA bA'} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr (isUnit_relativeDifferentialDet bA bA')
  rw [hu, Ideal.top_mul, Algebra.algebraMap_self, Ideal.map_id] at h
  exact h.symm

end EnvelopeProperty.Char0
