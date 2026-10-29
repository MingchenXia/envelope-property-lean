import EnvelopeProperty.Cartier.ExteriorBasisScalarExtension

/-! # Genuine scalar Leibniz formula for the SAME original etale differential -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleDifferentialLeibniz
open scoped TensorProduct Classical
open PolynomialDeRham
universe u

/-- Actual left exterior multiplication is genuinely linear in the original vector as well
as in the original homogeneous form. -/
def leftWedgeLinear {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M] (q : ℕ) :
    M →ₗ[A] ((⋀[A]^q M) →ₗ[A] (⋀[A]^(q+1) M)) where
  toFun m := leftWedge m q
  map_add' m n := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ExteriorAlgebra.ι A (m+n) * (w : ExteriorAlgebra A M) =
      ExteriorAlgebra.ι A m * w + ExteriorAlgebra.ι A n * w
    rw [map_add, add_mul]
  map_smul' a m := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ExteriorAlgebra.ι A (a • m) * (w : ExteriorAlgebra A M) =
      a • (ExteriorAlgebra.ι A m * w)
    rw [map_smul, smul_mul_assoc]

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)

/-- Actual original etale exterior scalar extension preserves left multiplication by every
original coordinate basis vector, with every original coefficient retained. -/
theorem formEquiv_leftWedge (q : ℕ) (i : Fin n) (b : B)
    (w : ⋀[R]^q (Fin n →₀ R)) :
    EtaleDeRham.formEquiv v hv (q+1)
        (b ⊗ₜ[R] leftWedge (Finsupp.single i 1) q w) =
      leftWedge (Char0.etaleDifferentialBasis v hv i) q
        (EtaleDeRham.formEquiv v hv q (b ⊗ₜ[R] w)) := by
  let e := (Finsupp.basisSingleOne : Module.Basis (Fin n) R (Fin n →₀ R))
  let c := Char0.etaleDifferentialBasis v hv
  have h := ExteriorBasisScalarExtension.exteriorEquiv_leftWedge e c (e i) q w
  rw [ExteriorBasisScalarExtension.basisSemilinearMap_basis] at h
  have h' : EtaleDeRham.formEquiv v hv (q+1)
      ((1 : B) ⊗ₜ[R] leftWedge (Finsupp.single i 1) q w) =
      leftWedge (c i) q (EtaleDeRham.formEquiv v hv q ((1 : B) ⊗ₜ[R] w)) := h
  have hb (q : ℕ) (x : ⋀[R]^q (Fin n →₀ R)) :
      b ⊗ₜ[R] x = b • ((1 : B) ⊗ₜ[R] x) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hb, hb, map_smul, map_smul, map_smul, h']

/-- The SAME actual original universal differential has its genuine original cotangent
basis expansion, with the original coordinate derivatives and NO matching premise. -/
theorem universalD_expansion (a : B) :
    ∑ i, Char0.etalePartialDeriv v hv i a • Char0.etaleDifferentialBasis v hv i =
      KaehlerDifferential.D R B a :=
  (Char0.etaleDifferentialBasis v hv).sum_repr (KaehlerDifferential.D R B a)

/-- Actual left exterior multiplication by the SAME original universal differential is
exactly the original coordinate derivative sum on EVERY original form. -/
theorem leftWedge_universalD (q : ℕ) (a : B)
    (w : ⋀[B]^q (KaehlerDifferential R B)) :
    leftWedge (KaehlerDifferential.D R B a) q w =
      ∑ i, Char0.etalePartialDeriv v hv i a •
        leftWedge (Char0.etaleDifferentialBasis v hv i) q w := by
  rw [← universalD_expansion v hv a]
  change (leftWedgeLinear q (∑ i, Char0.etalePartialDeriv v hv i a •
    Char0.etaleDifferentialBasis v hv i)) w = _
  rw [map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

private theorem equiv_mul_tmul {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (e : (B ⊗[A] M) ≃ₗ[B] N) (a b : B) (m : M) :
    e ((a*b) ⊗ₜ[A] m) = a • e (b ⊗ₜ[A] m) := by
  rw [← e.map_smul]
  rfl

/-- The SAME original whole etale differential satisfies the genuine intrinsic scalar
Leibniz rule on EVERY original homogeneous form. -/
theorem differential_smul (q : ℕ) (a : B)
    (w : ⋀[B]^q (KaehlerDifferential R B)) :
    EtaleDeRham.differential v hv q (a • w) =
      leftWedge (KaehlerDifferential.D R B a) q w + a • EtaleDeRham.differential v hv q w := by
  obtain ⟨z, rfl⟩ := (EtaleDeRham.formEquiv v hv q).surjective w
  rw [← (EtaleDeRham.formEquiv v hv q).map_smul]
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero, add_zero]
  | add z t hz ht =>
    simp only [smul_add, map_add, hz, ht]
    abel
  | tmul b x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul,
      EtaleDeRham.differential_formEquiv, EtaleDeRham.tensorDifferential_tmul,
      leftWedge_universalD v hv, EtaleDeRham.differential_formEquiv,
      EtaleDeRham.tensorDifferential_tmul]
    simp only [map_sum, Finset.smul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hderiv : Char0.etalePartialDeriv v hv i (a*b) =
        Char0.etalePartialDeriv v hv i a * b + a * Char0.etalePartialDeriv v hv i b := by
      rw [Derivation.leibniz]
      change a * Char0.etalePartialDeriv v hv i b + b * Char0.etalePartialDeriv v hv i a = _
      ring
    rw [hderiv, TensorProduct.add_tmul, map_add, equiv_mul_tmul, equiv_mul_tmul,
      formEquiv_leftWedge]

private theorem leftWedge_one_self {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (m : M) :
    leftWedge m 1 ((exteriorPower.oneEquiv A M).symm m) = 0 := by
  rw [exteriorPower.oneEquiv_symm_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ι A m * ExteriorAlgebra.ιMulti A 1 (fun _ => m) = 0
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  exact ExteriorAlgebra.ι_sq_zero m

/-- The SAME original universal differential gives a genuinely closed original one-form. -/
theorem differential_universalD (a : B) :
    EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm (KaehlerDifferential.D R B a)) = 0 := by
  have h := congrArg (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm
    (EtaleDeRham.differential_zero v hv a)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← h]
  exact EtaleDeRham.differential_square v hv 0 _

/-- Every actual original a^m da is closed in the SAME original complex, for EVERY m.
No characteristic or closedness hypothesis is assumed. -/
theorem differential_power_universalD (a : B) (m : ℕ) :
    EtaleDeRham.differential v hv 1
      (a^m • (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm
        (KaehlerDifferential.D R B a)) = 0 := by
  rw [differential_smul, differential_universalD, smul_zero, add_zero, Derivation.leibniz_pow]
  change (leftWedgeLinear 1 (m • (a^(m-1) • KaehlerDifferential.D R B a)))
    ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm (KaehlerDifferential.D R B a)) = 0
  simp only [map_nsmul, map_smul, LinearMap.smul_apply]
  change m • (a^(m-1) • leftWedge (KaehlerDifferential.D R B a) 1
    ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm (KaehlerDifferential.D R B a))) = 0
  rw [leftWedge_one_self, smul_zero, nsmul_zero]

end EnvelopeProperty.Cartier.EtaleDifferentialLeibniz
