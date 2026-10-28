import EnvelopeProperty.Cartier.EtaleDifferentialLeibniz

/-! # Actual entire etale differential and coordinate exterior multiplication -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleDifferentialCoordinateWedge
open scoped TensorProduct Classical
open PolynomialDeRham
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)

/-- The actual original tensor coordinate left product, with the SAME coefficient ring. -/
def tensorLeftWedge (i : Fin n) (q : ℕ) :
    (B ⊗[R] (⋀[R]^q (Fin n →₀ R))) →ₗ[B]
      (B ⊗[R] (⋀[R]^(q+1) (Fin n →₀ R))) :=
  TensorProduct.AlgebraTensorModule.lTensor B B (leftWedge (Finsupp.single i 1) q)

/-- EVERY actual original coefficient tensor is retained by original left multiplication. -/
theorem tensorLeftWedge_tmul (i : Fin n) (q : ℕ) (b : B) (w : ⋀[R]^q (Fin n →₀ R)) :
    tensorLeftWedge (R := R) (B := B) i q (b ⊗ₜ[R] w) =
      b ⊗ₜ[R] leftWedge (Finsupp.single i 1) q w := rfl

/-- The SAME whole original coordinate differential genuinely anticommutes with actual
coordinate left multiplication, including characteristic two. -/
theorem tensorDifferential_leftWedge (i : Fin n) (q : ℕ)
    (z : B ⊗[R] (⋀[R]^q (Fin n →₀ R))) :
    EtaleDeRham.tensorDifferential v hv (q+1)
        (tensorLeftWedge (R := R) (B := B) i q z) +
      tensorLeftWedge (R := R) (B := B) i (q+1) (EtaleDeRham.tensorDifferential v hv q z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | add z w hz hw =>
    simp only [map_add]
    rw [add_add_add_comm, hz, hw, add_zero]
  | tmul b w =>
    simp only [tensorLeftWedge_tmul, EtaleDeRham.tensorDifferential_tmul, map_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [← TensorProduct.tmul_add, leftWedge_anticomm, TensorProduct.tmul_zero]

/-- Actual exterior comparison intertwines the ENTIRE tensor coordinate left map and the
SAME original cotangent-coordinate left multiplication. -/
theorem formEquiv_tensorLeftWedge (i : Fin n) (q : ℕ)
    (z : B ⊗[R] (⋀[R]^q (Fin n →₀ R))) :
    EtaleDeRham.formEquiv v hv (q+1) (tensorLeftWedge (R := R) (B := B) i q z) =
      leftWedge (Char0.etaleDifferentialBasis v hv i) q (EtaleDeRham.formEquiv v hv q z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b w => exact EtaleDifferentialLeibniz.formEquiv_leftWedge v hv q i b w

/-- The SAME original actual etale differential anticommutes with original coordinate
left multiplication on EVERY original homogeneous form. -/
theorem differential_leftWedge_coordinate (i : Fin n) (q : ℕ)
    (w : ⋀[B]^q (KaehlerDifferential R B)) :
    EtaleDeRham.differential v hv (q+1) (leftWedge (Char0.etaleDifferentialBasis v hv i) q w) +
      leftWedge (Char0.etaleDifferentialBasis v hv i) (q+1) (EtaleDeRham.differential v hv q w) = 0 := by
  obtain ⟨z, rfl⟩ := (EtaleDeRham.formEquiv v hv q).surjective w
  rw [← formEquiv_tensorLeftWedge, EtaleDeRham.differential_formEquiv,
    EtaleDeRham.differential_formEquiv, ← formEquiv_tensorLeftWedge,
    ← map_add, tensorDifferential_leftWedge, map_zero]

end EnvelopeProperty.Cartier.EtaleDifferentialCoordinateWedge
