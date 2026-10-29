/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.RelativeJacobianIdeal

/-!
# Actual derivation Jacobian ideals through an etale leaf

Actual derivations with values in a further algebra expand in the actual
etale differential basis. Their original-source Jacobian ideal therefore
factors by the actual leaf-coordinate derivative determinant.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open Module Ideal
open scoped Classical

variable {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
  [Algebra k A] [Algebra k S] [Algebra A S] [IsScalarTower k A S] {n : ℕ}

/-- An actual derivation into a compatible algebra expands in actual etale coordinates. -/
theorem derivation_apply_eq_sum_etale (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (D : Derivation k A S) (f : A) :
    D f = ∑ j, algebraMap A S (etalePartialDeriv v hv j f) * D (v j) := by
  let b := etaleDifferentialBasis v hv
  calc
    D f = D.liftKaehlerDifferential (KaehlerDifferential.D k A f) :=
      (Derivation.liftKaehlerDifferential_comp_D D f).symm
    _ = ∑ j, b.repr (KaehlerDifferential.D k A f) j • D (v j) := by
      conv_lhs => rw [← b.sum_repr (KaehlerDifferential.D k A f)]
      simp only [map_sum, map_smul, b, etaleDifferentialBasis_apply,
        Derivation.liftKaehlerDifferential_comp_D]
    _ = ∑ j, algebraMap A S (etalePartialDeriv v hv j f) * D (v j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Algebra.smul_def]
      rfl

variable {R : Type*} [CommRing R] [Algebra R A]

/-- The actual ideal of all original-source tuple determinants in a given family of
actual derivations; no determinant ideal is supplied as a premise. -/
def derivationSourceJacobianIdeal (D : Fin n → Derivation k A S) : Ideal S :=
  span (Set.range fun w : Fin n → R => (Matrix.of fun i j => D j (algebraMap R A (w i))).det)

/-- The actual original-source derivative matrix factors through the leaf coordinates. -/
theorem derivation_source_matrix_comp (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (D : Fin n → Derivation k A S) (w : Fin n → R) :
    (Matrix.of fun i j => D j (algebraMap R A (w i))) =
      ((algebraMap A S).mapMatrix
        (sourceFunctionDifferentialMatrix (R := R) (etaleDifferentialBasis v hv) w)).transpose *
      (Matrix.of fun i j => D j (v i)) := by
  ext i j
  exact derivation_apply_eq_sum_etale v hv (D j) (algebraMap R A (w i))

/-- Every actual original-source derivative determinant has its exact coordinate factor. -/
theorem derivation_source_det_comp (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (D : Fin n → Derivation k A S) (w : Fin n → R) :
    (Matrix.of fun i j => D j (algebraMap R A (w i))).det =
      (Matrix.of fun i j => D j (v i)).det *
        algebraMap A S (sourceFunctionDifferentialMatrix (R := R)
          (etaleDifferentialBasis v hv) w).det := by
  rw [derivation_source_matrix_comp v hv D w, Matrix.det_mul, Matrix.det_transpose,
    ← (algebraMap A S).map_det]
  exact mul_comm _ _

/-- The genuine original-source derivation Jacobian ideal equals the coordinate derivative
determinant times the actual mapped all-original-functions leaf Jacobian ideal. -/
theorem derivationSourceJacobianIdeal_eq (v : Fin n → A)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (D : Fin n → Derivation k A S) :
    derivationSourceJacobianIdeal (R := R) D =
      span {(Matrix.of fun i j => D j (v i)).det} *
        (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map
          (algebraMap A S) := by
  rw [derivationSourceJacobianIdeal, affineRelativeJacobianIdeal, Ideal.map_span,
    Ideal.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, Set.mem_singleton _, _, ⟨_, ⟨w, rfl⟩, rfl⟩,
      (derivation_source_det_comp v hv D w).symm⟩
  · rintro ⟨r, (rfl : r = _), s, ⟨_, ⟨w, rfl⟩, rfl⟩, rfl⟩
    exact ⟨w, derivation_source_det_comp v hv D w⟩

end EnvelopeProperty.Char0
