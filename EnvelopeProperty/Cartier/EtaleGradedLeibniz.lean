import EnvelopeProperty.Cartier.EtaleDifferentialCoordinateWedge

/-! # Whole original graded Leibniz for the actual etale differential -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleGradedLeibniz
open scoped TensorProduct Classical
open PolynomialDeRham
universe u

section Product
variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]

/-- The actual original homogeneous exterior product. The result has degree r+q so
successively prepending original vectors is definitionally compatible with degree increments. -/
def wedgeProduct (q r : ℕ) :
    (⋀[A]^q M) →ₗ[A] (⋀[A]^r M) →ₗ[A] (⋀[A]^(r+q) M) where
  toFun a :=
    { toFun := fun b => ⟨(a : ExteriorAlgebra A M) * b, by
        change (a : ExteriorAlgebra A M) * b ∈
          (LinearMap.range (ExteriorAlgebra.ι A : M →ₗ[A] ExteriorAlgebra A M))^(r+q)
        rw [Nat.add_comm r q, pow_add]
        exact Submodule.mul_mem_mul a.property b.property⟩
      map_add' := fun b c => Subtype.ext (mul_add _ _ _)
      map_smul' := fun b c => Subtype.ext (mul_smul_comm _ _ _) }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    exact Subtype.ext (add_mul _ _ _)
  map_smul' a b := by
    apply LinearMap.ext
    intro c
    exact Subtype.ext (smul_mul_assoc _ _ _)

/-- The SAME actual ambient exterior-algebra product is retained on EVERY pair of forms. -/
theorem coe_wedgeProduct (q r : ℕ) (a : ⋀[A]^q M) (b : ⋀[A]^r M) :
    (wedgeProduct q r a b : ExteriorAlgebra A M) =
      (a : ExteriorAlgebra A M) * b := rfl

/-- Original left multiplication is compatible with the actual whole original product. -/
theorem wedgeProduct_leftWedge (q r : ℕ) (m : M) (a : ⋀[A]^q M) (b : ⋀[A]^r M) :
    wedgeProduct (q+1) r (leftWedge m q a) b =
      leftWedge m (r+q) (wedgeProduct q r a b) := by
  apply Subtype.ext
  exact mul_assoc (ExteriorAlgebra.ι A m) a b

/-- The SAME original degree-zero exterior identification gives true coefficient action. -/
theorem wedgeProduct_zero_left (r : ℕ) (a : A) (b : ⋀[A]^r M) :
    wedgeProduct 0 r ((exteriorPower.zeroEquiv A M).symm a) b = a • b := by
  rw [exteriorPower.zeroEquiv_symm_apply]
  apply Subtype.ext
  change (a • ExteriorAlgebra.ιMulti (M := M) A 0 _) * (b : ExteriorAlgebra A M) = a • b
  rw [ExteriorAlgebra.ιMulti_zero_apply, smul_mul_assoc, one_mul]

end Product

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)

/-- EVERY original coordinate wedge, including repetitions, as an actual original form. -/
def coordinateWedge (q : ℕ) (i : Fin q → Fin n) : ⋀[B]^q (KaehlerDifferential R B) :=
  exteriorPower.ιMulti B q (fun j => Char0.etaleDifferentialBasis v hv (i j))

private theorem coordinateWedge_zero (i : Fin 0 → Fin n) :
    coordinateWedge v hv 0 i = (exteriorPower.zeroEquiv B (KaehlerDifferential R B)).symm 1 := by
  apply (exteriorPower.zeroEquiv B (KaehlerDifferential R B)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact exteriorPower.zeroEquiv_ιMulti _

private theorem coordinateWedge_succ (q : ℕ) (i : Fin (q+1) → Fin n) :
    coordinateWedge v hv (q+1) i = leftWedge (Char0.etaleDifferentialBasis v hv (i 0)) q
      (coordinateWedge v hv q (fun j => i j.succ)) := by
  rw [coordinateWedge, coordinateWedge, ExteriorBasisScalarExtension.leftWedge_ιMulti]
  congr 1
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

/-- Actual whole coordinate-wedge products have the DERIVED original graded sign rule.
No coordinate-wedge Leibniz or closedness premise is supplied. -/
theorem differential_coordinateWedge_product (q : ℕ) (i : Fin q → Fin n)
    (r : ℕ) (w : ⋀[B]^r (KaehlerDifferential R B)) :
    (EtaleDeRham.differential v hv (r+q) (wedgeProduct q r (coordinateWedge v hv q i) w) :
      ExteriorAlgebra B (KaehlerDifferential R B)) =
      (-1 : B)^q • ((coordinateWedge v hv q i : ExteriorAlgebra B (KaehlerDifferential R B)) *
        (EtaleDeRham.differential v hv r w : ExteriorAlgebra B (KaehlerDifferential R B))) := by
  induction q with
  | zero =>
    rw [coordinateWedge_zero, wedgeProduct_zero_left, one_smul]
    simp only [Nat.add_zero, pow_zero, one_smul, exteriorPower.zeroEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_zero_apply, one_mul]
  | succ q ih =>
    rw [coordinateWedge_succ, wedgeProduct_leftWedge]
    have h := congrArg
      (fun z : ⋀[B]^((r+q)+1+1) (KaehlerDifferential R B) =>
        (z : ExteriorAlgebra B (KaehlerDifferential R B)))
      (EtaleDifferentialCoordinateWedge.differential_leftWedge_coordinate v hv (i 0) (r+q)
        (wedgeProduct q r (coordinateWedge v hv q (fun j => i j.succ)) w))
    have hanti :
        (EtaleDeRham.differential v hv ((r+q)+1)
          (leftWedge (Char0.etaleDifferentialBasis v hv (i 0)) (r+q)
            (wedgeProduct q r (coordinateWedge v hv q (fun j => i j.succ)) w)) :
          ExteriorAlgebra B (KaehlerDifferential R B)) =
        -(ExteriorAlgebra.ι B (Char0.etaleDifferentialBasis v hv (i 0)) *
          (EtaleDeRham.differential v hv (r+q)
            (wedgeProduct q r (coordinateWedge v hv q (fun j => i j.succ)) w) :
            ExteriorAlgebra B (KaehlerDifferential R B))) :=
      eq_neg_iff_add_eq_zero.mpr h
    change (EtaleDeRham.differential v hv ((r+q)+1)
      (leftWedge (Char0.etaleDifferentialBasis v hv (i 0)) (r+q)
        (wedgeProduct q r (coordinateWedge v hv q (fun j => i j.succ)) w)) :
      ExteriorAlgebra B (KaehlerDifferential R B)) = _
    rw [hanti, ih]
    change -(ExteriorAlgebra.ι B (Char0.etaleDifferentialBasis v hv (i 0)) *
        ((-1 : B)^q • ((coordinateWedge v hv q (fun j => i j.succ) :
          ExteriorAlgebra B (KaehlerDifferential R B)) *
          (EtaleDeRham.differential v hv r w : ExteriorAlgebra B (KaehlerDifferential R B))))) =
      (-1 : B)^(q+1) • ((ExteriorAlgebra.ι B (Char0.etaleDifferentialBasis v hv (i 0)) *
        (coordinateWedge v hv q (fun j => i j.succ) : ExteriorAlgebra B (KaehlerDifferential R B))) *
        (EtaleDeRham.differential v hv r w : ExteriorAlgebra B (KaehlerDifferential R B)))
    rw [mul_smul_comm, mul_assoc]
    simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]

private theorem differential_basis_product (q : ℕ) (s : Set.powersetCard (Fin n) q)
    (r : ℕ) (w : ⋀[B]^r (KaehlerDifferential R B)) :
    (EtaleDeRham.differential v hv (r+q)
      (wedgeProduct q r ((Char0.etaleDifferentialBasis v hv).exteriorPower q s) w) :
      ExteriorAlgebra B (KaehlerDifferential R B)) =
      (-1 : B)^q • (((Char0.etaleDifferentialBasis v hv).exteriorPower q s :
        ExteriorAlgebra B (KaehlerDifferential R B)) *
        (EtaleDeRham.differential v hv r w : ExteriorAlgebra B (KaehlerDifferential R B))) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  exact differential_coordinateWedge_product v hv q _ r w

private theorem differential_coefficient_basis_product (q : ℕ) (s : Set.powersetCard (Fin n) q)
    (a : B) (r : ℕ) (w : ⋀[B]^r (KaehlerDifferential R B)) :
    (EtaleDeRham.differential v hv (r+q)
      (wedgeProduct q r (a • (Char0.etaleDifferentialBasis v hv).exteriorPower q s) w) :
      ExteriorAlgebra B (KaehlerDifferential R B)) =
    (EtaleDeRham.differential v hv q (a • (Char0.etaleDifferentialBasis v hv).exteriorPower q s) :
      ExteriorAlgebra B (KaehlerDifferential R B)) * w +
    (-1 : B)^q • ((a • (Char0.etaleDifferentialBasis v hv).exteriorPower q s :
      ExteriorAlgebra B (KaehlerDifferential R B)) *
      (EtaleDeRham.differential v hv r w : ExteriorAlgebra B (KaehlerDifferential R B))) := by
  simp only [map_smul, LinearMap.smul_apply,
    EtaleDifferentialLeibniz.differential_smul, EtaleDeRham.differential_coordinate_wedge,
    smul_zero, add_zero]
  change ExteriorAlgebra.ι B (KaehlerDifferential.D R B a) *
      (((Char0.etaleDifferentialBasis v hv).exteriorPower q s :
        ExteriorAlgebra B (KaehlerDifferential R B)) * w) +
      a • (EtaleDeRham.differential v hv (r+q)
        (wedgeProduct q r ((Char0.etaleDifferentialBasis v hv).exteriorPower q s) w) :
        ExteriorAlgebra B (KaehlerDifferential R B)) =
    (ExteriorAlgebra.ι B (KaehlerDifferential.D R B a) *
      ((Char0.etaleDifferentialBasis v hv).exteriorPower q s :
        ExteriorAlgebra B (KaehlerDifferential R B))) * w +
      (-1 : B)^q • ((a • ((Char0.etaleDifferentialBasis v hv).exteriorPower q s :
        ExteriorAlgebra B (KaehlerDifferential R B))) *
        (EtaleDeRham.differential v hv r w : ExteriorAlgebra B (KaehlerDifferential R B)))
  rw [differential_basis_product, mul_assoc, smul_mul_assoc, smul_comm a ((-1 : B)^q)]

/-- The SAME original differential satisfies WHOLE genuine graded Leibniz on EVERY pair of
original homogeneous forms, with actual products and all original coefficient actions. -/
theorem differential_wedgeProduct (q r : ℕ)
    (a : ⋀[B]^q (KaehlerDifferential R B)) (b : ⋀[B]^r (KaehlerDifferential R B)) :
    (EtaleDeRham.differential v hv (r+q) (wedgeProduct q r a b) :
      ExteriorAlgebra B (KaehlerDifferential R B)) =
    (EtaleDeRham.differential v hv q a : ExteriorAlgebra B (KaehlerDifferential R B)) * b +
      (-1 : B)^q • ((a : ExteriorAlgebra B (KaehlerDifferential R B)) *
        (EtaleDeRham.differential v hv r b : ExteriorAlgebra B (KaehlerDifferential R B))) := by
  let e := (Char0.etaleDifferentialBasis v hv).exteriorPower q
  have ha : ∑ s, e.repr a s • e s = a := e.sum_repr a
  rw [← ha]
  simp only [map_sum, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_mul, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact differential_coefficient_basis_product v hv q s (e.repr a s) r b

end EnvelopeProperty.Cartier.EtaleGradedLeibniz
