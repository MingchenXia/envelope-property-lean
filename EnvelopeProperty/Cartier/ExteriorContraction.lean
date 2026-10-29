import EnvelopeProperty.Cartier.PolynomialDeRham
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Actual homogeneous exterior contraction and Cartan identities

These are restrictions of the ORIGINAL Clifford operators for the zero quadratic form.
Homogeneous degree preservation is proved, not supplied.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.ExteriorContraction
open PolynomialDeRham
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem homogeneous_contraction (ℓ : Module.Dual R M) (n : ℕ)
    (x : ExteriorAlgebra R M) (hx : x ∈ (⋀[R]^n M)) :
    match n with
    | 0 => CliffordAlgebra.contractLeft (Q := 0) ℓ x = 0
    | q+1 => CliffordAlgebra.contractLeft (Q := 0) ℓ x ∈ (⋀[R]^q M) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => exact CliffordAlgebra.contractLeft_algebraMap 0 ℓ r
  | add x y n hx hy ihx ihy =>
    cases n with
    | zero => simp only [map_add, ihx, ihy, add_zero]
    | succ q =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm n x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [CliffordAlgebra.contractLeft_ι_mul]
    cases n with
    | zero =>
      rw [ih, mul_zero, sub_zero]
      exact Submodule.smul_mem _ _ hx
    | succ q =>
      apply Submodule.sub_mem _ (Submodule.smul_mem _ _ hx)
      change ExteriorAlgebra.ι R v * CliffordAlgebra.contractLeft (Q := 0) ℓ x ∈
        (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)) ^ (q+1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) ih

/-- The ORIGINAL contraction lowers the actual exterior degree; no preservation premise. -/
theorem contract_mem (ℓ : Module.Dual R M) (q : ℕ) (x : ⋀[R]^(q+1) M) :
    CliffordAlgebra.contractLeft (Q := 0) ℓ (x : ExteriorAlgebra R M) ∈ (⋀[R]^q M) :=
  homogeneous_contraction ℓ (q+1) x x.property

/-- The actual original homogeneous contraction, derived on every original exterior power. -/
def interior (ℓ : Module.Dual R M) (q : ℕ) : (⋀[R]^(q+1) M) →ₗ[R] (⋀[R]^q M) where
  toFun x := ⟨CliffordAlgebra.contractLeft (Q := 0) ℓ x, contract_mem ℓ q x⟩
  map_add' x y := Subtype.ext (map_add (CliffordAlgebra.contractLeft (Q := 0) ℓ)
    (x : ExteriorAlgebra R M) (y : ExteriorAlgebra R M))
  map_smul' a x := Subtype.ext (map_smul (CliffordAlgebra.contractLeft (Q := 0) ℓ)
    a (x : ExteriorAlgebra R M))

/-- The whole SAME original exterior algebra operator is retained. -/
theorem interior_apply (ℓ : Module.Dual R M) (q : ℕ) (x : ⋀[R]^(q+1) M) :
    (interior ℓ q x : ExteriorAlgebra R M) =
      CliffordAlgebra.contractLeft (Q := 0) ℓ (x : ExteriorAlgebra R M) := rfl

/-- The genuine exterior Cartan anticommutator on the WHOLE original homogeneous module. -/
theorem interior_leftWedge (ℓ : Module.Dual R M) (v : M) (q : ℕ) (x : ⋀[R]^(q+1) M) :
    interior ℓ (q+1) (leftWedge v (q+1) x) + leftWedge v q (interior ℓ q x) = ℓ v • x := by
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (Q := 0) ℓ (ExteriorAlgebra.ι R v * x) +
    ExteriorAlgebra.ι R v * CliffordAlgebra.contractLeft (Q := 0) ℓ x = ℓ v • (x : ExteriorAlgebra R M)
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]

/-- Actual homogeneous contraction squares to zero in every degree and every characteristic. -/
theorem interior_self (ℓ : Module.Dual R M) (q : ℕ) (x : ⋀[R]^(q+1+1) M) :
    interior ℓ q (interior ℓ (q+1) x) = 0 := by
  apply Subtype.ext
  exact CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm R M)) ℓ
    (x : ExteriorAlgebra R M)

/-- Actual contractions anticommute without inverting two. -/
theorem interior_anticomm (ℓ ℓ' : Module.Dual R M) (q : ℕ) (x : ⋀[R]^(q+1+1) M) :
    interior ℓ q (interior ℓ' (q+1) x) + interior ℓ' q (interior ℓ (q+1) x) = 0 := by
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (Q := 0) ℓ
      (CliffordAlgebra.contractLeft (Q := 0) ℓ' x) +
    CliffordAlgebra.contractLeft (Q := 0) ℓ'
      (CliffordAlgebra.contractLeft (Q := 0) ℓ x) = 0
  rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]

end EnvelopeProperty.Cartier.ExteriorContraction
