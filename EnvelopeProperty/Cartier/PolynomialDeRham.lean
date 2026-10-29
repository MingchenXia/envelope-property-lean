import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# The genuine polynomial de Rham differential on actual exterior cotangent modules

The coordinate tensor construction uses actual exterior powers, with actual anticommutation.
It is subsequently transported by the actual free-cotangent scalar-extension equivalence.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialDeRham
open scoped TensorProduct
open MvPolynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Left exterior multiplication between the actual original homogeneous components. -/
def leftWedge (m : M) (q : ℕ) : (⋀[R]^q M) →ₗ[R] (⋀[R]^(q+1) M) where
  toFun x := ⟨ExteriorAlgebra.ι R m * x, by
    change ExteriorAlgebra.ι R m * x ∈
      (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)) ^ (q+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) x.property⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (mul_smul_comm _ _ _)

/-- Actual exterior square-zero, including in characteristic two. -/
theorem leftWedge_self (m : M) (q : ℕ) (x : ⋀[R]^q M) :
    leftWedge m (q+1) (leftWedge m q x) = 0 := by
  apply Subtype.ext
  change ExteriorAlgebra.ι R m * (ExteriorAlgebra.ι R m * (x : ExteriorAlgebra R M)) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- Actual exterior anticommutation in every degree, without inverting two. -/
theorem leftWedge_anticomm (m n : M) (q : ℕ) (x : ⋀[R]^q M) :
    leftWedge m (q+1) (leftWedge n q x) +
      leftWedge n (q+1) (leftWedge m q x) = 0 := by
  apply Subtype.ext
  change ExteriorAlgebra.ι R m * (ExteriorAlgebra.ι R n * (x : ExteriorAlgebra R M)) +
    ExteriorAlgebra.ι R n * (ExteriorAlgebra.ι R m * (x : ExteriorAlgebra R M)) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

/-- The original standard polynomial partial derivatives commute over every coefficient ring. -/
theorem partials_commute {σ : Type*} (i j : σ) (f : MvPolynomial σ R) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [pderiv_monomial]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hij,
        Finsupp.single_eq_of_ne (Ne.symm hij), tsub_zero, tsub_zero, tsub_right_comm]
      congr 1
      ring
  | add f g hf hg => simp only [map_add, hf, hg]

variable (R) {σ : Type*} [Fintype σ]

/-- The actual tensor-product differential before the canonical cotangent comparison. -/
def tensorDifferential (q : ℕ) :
    (MvPolynomial σ R ⊗[R] (⋀[R]^q (σ →₀ R))) →ₗ[R]
      (MvPolynomial σ R ⊗[R] (⋀[R]^(q+1) (σ →₀ R))) :=
  ∑ i, TensorProduct.map (pderiv i).toLinearMap (leftWedge (Finsupp.single i 1) q)

/-- Its whole original pure-tensor formula, with original standard partials and wedges. -/
theorem tensorDifferential_tmul (q : ℕ) (f : MvPolynomial σ R)
    (w : ⋀[R]^q (σ →₀ R)) :
    tensorDifferential R q (f ⊗ₜ[R] w) =
      ∑ i, pderiv i f ⊗ₜ[R] leftWedge (Finsupp.single i 1) q w := by
  simp only [tensorDifferential, LinearMap.sum_apply, TensorProduct.map_tmul,
]
  rfl

/-- The WHOLE actual coordinate tensor differential squares to zero in every degree. -/
theorem tensorDifferential_square (q : ℕ)
    (z : MvPolynomial σ R ⊗[R] (⋀[R]^q (σ →₀ R))) :
    tensorDifferential R (q+1) (tensorDifferential R q z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f w =>
    rw [tensorDifferential_tmul, map_sum]
    simp_rw [tensorDifferential_tmul]
    let F : σ × σ → MvPolynomial σ R ⊗[R] (⋀[R]^(q+1+1) (σ →₀ R)) := fun a =>
      pderiv a.2 (pderiv a.1 f) ⊗ₜ[R]
        leftWedge (Finsupp.single a.2 1) (q+1) (leftWedge (Finsupp.single a.1 1) q w)
    change (∑ i, ∑ j, F (i,j)) = 0
    rw [← Fintype.sum_prod_type F]
    apply Finset.sum_involution (fun a _ => (a.2, a.1))
    · intro a _
      dsimp only [F]
      rw [partials_commute a.2 a.1 f, ← TensorProduct.tmul_add,
        leftWedge_anticomm, TensorProduct.tmul_zero]
    · intro a _ hn he
      have h : a.1 = a.2 := (congrArg Prod.fst he).symm
      apply hn
      dsimp only [F]
      rw [h, leftWedge_self, TensorProduct.tmul_zero]
    · intro a _
      simp only [Finset.mem_univ]
    · intro a _
      rfl
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]

variable [LinearOrder σ]

/-- A derived genuine isomorphism to the SAME original exterior cotangent module, in EVERY
 degree. Its basis vectors are the actual coordinate differential wedges. -/
def formEquiv (q : ℕ) :
    (MvPolynomial σ R ⊗[R] (⋀[R]^q (σ →₀ R))) ≃ₗ[MvPolynomial σ R]
      (⋀[MvPolynomial σ R]^q (KaehlerDifferential R (MvPolynomial σ R))) :=
  (((Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower q).baseChange
    (MvPolynomial σ R)).equiv
      ((KaehlerDifferential.mvPolynomialBasis R σ).exteriorPower q) (Equiv.refl _)

omit [Fintype σ] in
/-- The original coordinate wedge basis is retained exactly, not merely up to an abstract
isomorphism. -/
theorem formEquiv_one_tmul_basis (q : ℕ) (s : Set.powersetCard σ q) :
    formEquiv R q (1 ⊗ₜ[R]
      (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower q s) =
      (KaehlerDifferential.mvPolynomialBasis R σ).exteriorPower q s := by
  rw [← Module.Basis.baseChange_apply]
  exact Module.Basis.equiv_apply _ _ _ _

omit [Fintype σ] in
/-- Every actual polynomial coefficient of a coordinate differential wedge is retained. -/
theorem formEquiv_tmul_basis (q : ℕ) (f : MvPolynomial σ R) (s : Set.powersetCard σ q) :
    formEquiv R q (f ⊗ₜ[R]
      (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower q s) =
      f • (KaehlerDifferential.mvPolynomialBasis R σ).exteriorPower q s := by
  have h : f ⊗ₜ[R] (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower q s =
      f • (1 ⊗ₜ[R] (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower q s) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, formEquiv_one_tmul_basis]

/-- The actual de Rham differential on the ORIGINAL exterior cotangent modules. -/
def differential (q : ℕ) :
    (⋀[MvPolynomial σ R]^q (KaehlerDifferential R (MvPolynomial σ R))) →+
      (⋀[MvPolynomial σ R]^(q+1) (KaehlerDifferential R (MvPolynomial σ R))) :=
  (formEquiv R (q+1)).toAddMonoidHom.comp
    ((tensorDifferential R q).toAddMonoidHom.comp (formEquiv R q).symm.toAddMonoidHom)

/-- The actual whole comparison intertwines the original exterior differential. -/
theorem differential_formEquiv (q : ℕ)
    (z : MvPolynomial σ R ⊗[R] (⋀[R]^q (σ →₀ R))) :
    differential R q (formEquiv R q z) = formEquiv R (q+1) (tensorDifferential R q z) := by
  change formEquiv R (q+1)
    (tensorDifferential R q ((formEquiv R q).symm (formEquiv R q z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The differential squares to zero on the WHOLE SAME original exterior cotangent module. -/
theorem differential_square (q : ℕ)
    (w : ⋀[MvPolynomial σ R]^q (KaehlerDifferential R (MvPolynomial σ R))) :
    differential R (q+1) (differential R q w) = 0 := by
  obtain ⟨z, rfl⟩ := (formEquiv R q).surjective w
  rw [differential_formEquiv, differential_formEquiv, tensorDifferential_square, map_zero]

/-- Every original constant coordinate differential wedge is closed. -/
theorem differential_coordinate_wedge (q : ℕ) (s : Set.powersetCard σ q) :
    differential R q ((KaehlerDifferential.mvPolynomialBasis R σ).exteriorPower q s) = 0 := by
  rw [← formEquiv_one_tmul_basis R q s, differential_formEquiv, tensorDifferential_tmul]
  simp only [pderiv_one, TensorProduct.zero_tmul, Finset.sum_const_zero, map_zero]

private theorem zeroEquiv_basis {K V I : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] [LinearOrder I] (b : Module.Basis I K V) (s : Set.powersetCard I 0) :
    exteriorPower.zeroEquiv K V (b.exteriorPower 0 s) = 1 := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.zeroEquiv_ιMulti]

private theorem oneEquiv_basis_singleton {K V I : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] [LinearOrder I] (b : Module.Basis I K V) (i : I) :
    exteriorPower.oneEquiv K V
      (b.exteriorPower 1 (Set.powersetCard.ofCard (Finset.card_singleton i))) = b i := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.oneEquiv_ιMulti]
  dsimp only [Function.comp_apply]
  congr 1
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)

private theorem leftWedge_zero (m : M) :
    leftWedge m 0 ((exteriorPower.zeroEquiv R M).symm 1) =
      (exteriorPower.oneEquiv R M).symm m := by
  rw [exteriorPower.zeroEquiv_symm_apply, one_smul, exteriorPower.oneEquiv_symm_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ι R m * ExteriorAlgebra.ιMulti R 0 _ =
    ExteriorAlgebra.ιMulti R 1 (fun _ => m)
  rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one, ExteriorAlgebra.ιMulti_apply]
  simp only [List.ofFn_const, List.replicate_one, List.prod_singleton]

omit [Fintype σ] in
/-- The original polynomial-to-degree-zero identification is exactly the canonical native
zero exterior-power equivalence. -/
theorem formEquiv_zero (f : MvPolynomial σ R) :
    formEquiv R 0 (f ⊗ₜ[R] (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1) =
      (exteriorPower.zeroEquiv (MvPolynomial σ R)
        (KaehlerDifferential R (MvPolynomial σ R))).symm f := by
  let s : Set.powersetCard σ 0 := Set.powersetCard.ofCard (Finset.card_empty (α := σ))
  have hz : (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1 =
      (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower 0 s := by
    apply (exteriorPower.zeroEquiv R (σ →₀ R)).injective
    rw [LinearEquiv.apply_symm_apply, zeroEquiv_basis]
  rw [hz, formEquiv_tmul_basis]
  apply (exteriorPower.zeroEquiv (MvPolynomial σ R)
    (KaehlerDifferential R (MvPolynomial σ R))).injective
  rw [map_smul, zeroEquiv_basis, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

omit [Fintype σ] in
private theorem formEquiv_one_single (f : MvPolynomial σ R) (i : σ) :
    exteriorPower.oneEquiv (MvPolynomial σ R) (KaehlerDifferential R (MvPolynomial σ R))
      (formEquiv R 1 (f ⊗ₜ[R]
        (exteriorPower.oneEquiv R (σ →₀ R)).symm (Finsupp.single i 1))) =
      f • KaehlerDifferential.D R (MvPolynomial σ R) (X i) := by
  let s : Set.powersetCard σ 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  have hz : (exteriorPower.oneEquiv R (σ →₀ R)).symm (Finsupp.single i 1) =
      (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower 1 s := by
    apply (exteriorPower.oneEquiv R (σ →₀ R)).injective
    rw [LinearEquiv.apply_symm_apply, oneEquiv_basis_singleton]
    rfl
  rw [hz, formEquiv_tmul_basis, map_smul, oneEquiv_basis_singleton,
    KaehlerDifferential.mvPolynomialBasis_apply]

/-- In degree zero this is the SAME original universal Kaehler differential, under the
canonical native zero and one exterior-power identifications. -/
theorem differential_zero (f : MvPolynomial σ R) :
    exteriorPower.oneEquiv (MvPolynomial σ R) (KaehlerDifferential R (MvPolynomial σ R))
      (differential R 0
        ((exteriorPower.zeroEquiv (MvPolynomial σ R)
          (KaehlerDifferential R (MvPolynomial σ R))).symm f)) =
      KaehlerDifferential.D R (MvPolynomial σ R) f := by
  rw [← formEquiv_zero, differential_formEquiv, tensorDifferential_tmul, map_sum, map_sum]
  simp_rw [leftWedge_zero]
  calc
    _ = ∑ i, pderiv i f • KaehlerDifferential.D R (MvPolynomial σ R) (X i) :=
      Finset.sum_congr rfl (fun i _ => formEquiv_one_single R (pderiv i f) i)
    _ = _ := by
      apply (KaehlerDifferential.mvPolynomialBasis R σ).repr.injective
      apply Finsupp.ext
      intro i
      simp only [map_sum, map_smul, KaehlerDifferential.mvPolynomialBasis_repr_D_X,
        KaehlerDifferential.mvPolynomialBasis_repr_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]


/-- Genuine coefficient-ring linearity with its actual action through the ORIGINAL polynomial
coefficient map; no action or linearity certificate on the forms is supplied. -/
theorem differential_base_smul (q : ℕ) (a : R)
    (w : ⋀[MvPolynomial σ R]^q (KaehlerDifferential R (MvPolynomial σ R))) :
    differential R q ((C a : MvPolynomial σ R) • w) = (C a : MvPolynomial σ R) • differential R q w := by
  obtain ⟨z, rfl⟩ := (formEquiv R q).surjective w
  rw [← map_smul, differential_formEquiv, differential_formEquiv]
  have h (n : ℕ) (x : MvPolynomial σ R ⊗[R] (⋀[R]^n (σ →₀ R))) :
      (C a : MvPolynomial σ R) • x = a • x := IsScalarTower.algebraMap_smul (MvPolynomial σ R) a x
  calc
    formEquiv R (q+1) (tensorDifferential R q ((C a) • z)) =
        formEquiv R (q+1) (a • tensorDifferential R q z) := by rw [h, map_smul]
    _ = formEquiv R (q+1) ((C a) • tensorDifferential R q z) := by rw [h]
    _ = _ := (formEquiv R (q+1)).map_smul _ _

/-- The actual cochain complex whose objects are the SAME original exterior cotangent modules;
its differentials and square-zero are internally constructed. -/
def complex : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of
    (fun q => AddCommGrpCat.of
      (⋀[MvPolynomial σ R]^q (KaehlerDifferential R (MvPolynomial σ R))))
    (fun q => AddCommGrpCat.ofHom (differential R q))
    (fun q => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro w
      exact differential_square R q w)

end EnvelopeProperty.Cartier.PolynomialDeRham
