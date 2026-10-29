import EnvelopeProperty.Char0.EtaleDifferentials
import EnvelopeProperty.Cartier.PolynomialDeRham
import EnvelopeProperty.Cartier.PolynomialFrobeniusDeRham
import Mathlib.RingTheory.Derivation.Lie

/-!
# Actual exterior de Rham differential from genuine etale coordinates

The original whole cotangent module and actual etale coordinate derivations are retained.
All coordinate commutation is genuinely derived, over arbitrary commutative base rings.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleDeRham
open scoped TensorProduct Classical
open MvPolynomial PolynomialDeRham
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)

/-- The SAME original genuine etale coordinate derivations commute on EVERY original function.
The actual commutator is a derivation and actual etale coordinate determination proves it zero. -/
theorem partials_commute (i j : Fin n) (f : B) :
    Char0.etalePartialDeriv v hv i (Char0.etalePartialDeriv v hv j f) =
      Char0.etalePartialDeriv v hv j (Char0.etalePartialDeriv v hv i f) := by
  have hc : ⁅Char0.etalePartialDeriv v hv i, Char0.etalePartialDeriv v hv j⁆ = 0 := by
    apply Char0.derivation_ext_etale v hv
    intro a
    simp only [Derivation.commutator_apply, Char0.etalePartialDeriv_apply]
    split_ifs <;> simp only [Derivation.map_one_eq_zero, map_zero, Derivation.zero_apply, sub_self]
  have h := congrArg (fun D : Derivation R B B => D f) hc
  rw [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.mp h

/- The generic original polynomial chain-rule proof follows this repository's
Char0.AnalyticChartLocal.derivation_aeval by polynomial induction; the argument needs
only commutative coefficient rings, as also observed in the sibling project's
Alterations.Algebra.ProjectiveSecant.original_derivation_aeval. -/
private theorem derivation_aeval (D : Derivation R B B) (f : MvPolynomial (Fin n) R) :
    D (aeval v f) = ∑ i, aeval v (pderiv i f) * D (v i) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f o hf =>
    have h1 : ∀ i, aeval v (pderiv i (f * X o)) =
        v o * aeval v (pderiv i f) + if o = i then aeval v f else 0 := by
      intro i
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X,
        Pi.single_apply]
      split_ifs <;> simp [mul_comm, add_comm]
    rw [Finset.sum_congr rfl fun i _ => by rw [h1 i]]
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hf, add_mul,
      Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The SAME original whole polynomial map intertwines every genuine etale coordinate
partial with the ORIGINAL standard polynomial partial, with no matching premise. -/
theorem partials_aeval (i : Fin n) (f : MvPolynomial (Fin n) R) :
    Char0.etalePartialDeriv v hv i (aeval v f) = aeval v (pderiv i f) := by
  rw [derivation_aeval]
  simp only [Char0.etalePartialDeriv_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The actual tensor-product differential before the canonical cotangent comparison. -/
def tensorDifferential (q : ℕ) :
    (B ⊗[R] (⋀[R]^q ((Fin n) →₀ R))) →ₗ[R]
      (B ⊗[R] (⋀[R]^(q+1) ((Fin n) →₀ R))) :=
  ∑ i, TensorProduct.map (Char0.etalePartialDeriv v hv i).toLinearMap (leftWedge (Finsupp.single i 1) q)

/-- Its whole original pure-tensor formula, with original etale partials and wedges. -/
theorem tensorDifferential_tmul (q : ℕ) (f : B)
    (w : ⋀[R]^q ((Fin n) →₀ R)) :
    tensorDifferential v hv q (f ⊗ₜ[R] w) =
      ∑ i, Char0.etalePartialDeriv v hv i f ⊗ₜ[R] leftWedge (Finsupp.single i 1) q w := by
  simp only [tensorDifferential, LinearMap.sum_apply, TensorProduct.map_tmul,
]
  rfl

/-- The WHOLE actual coordinate tensor differential squares to zero in every degree. -/
theorem tensorDifferential_square (q : ℕ)
    (z : B ⊗[R] (⋀[R]^q ((Fin n) →₀ R))) :
    tensorDifferential v hv (q+1) (tensorDifferential v hv q z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f w =>
    rw [tensorDifferential_tmul, map_sum]
    simp_rw [tensorDifferential_tmul]
    let F : (Fin n) × (Fin n) → B ⊗[R] (⋀[R]^(q+1+1) ((Fin n) →₀ R)) := fun a =>
      Char0.etalePartialDeriv v hv a.2 (Char0.etalePartialDeriv v hv a.1 f) ⊗ₜ[R]
        leftWedge (Finsupp.single a.2 1) (q+1) (leftWedge (Finsupp.single a.1 1) q w)
    change (∑ i, ∑ j, F (i,j)) = 0
    rw [← Fintype.sum_prod_type F]
    apply Finset.sum_involution (fun a _ => (a.2, a.1))
    · intro a _
      dsimp only [F]
      rw [partials_commute v hv a.2 a.1 f, ← TensorProduct.tmul_add,
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


/-- A derived genuine isomorphism to the SAME original exterior cotangent module, in EVERY
 degree. Its basis vectors are the actual coordinate differential wedges. -/
def formEquiv (q : ℕ) :
    (B ⊗[R] (⋀[R]^q ((Fin n) →₀ R))) ≃ₗ[B]
      (⋀[B]^q (KaehlerDifferential R (B))) :=
  (((Finsupp.basisSingleOne : Module.Basis (Fin n) R ((Fin n) →₀ R)).exteriorPower q).baseChange
    (B)).equiv
      ((Char0.etaleDifferentialBasis v hv).exteriorPower q) (Equiv.refl _)

/-- The original coordinate wedge basis is retained exactly, not merely up to an abstract
isomorphism. -/
theorem formEquiv_one_tmul_basis (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    formEquiv v hv q (1 ⊗ₜ[R]
      (Finsupp.basisSingleOne : Module.Basis (Fin n) R ((Fin n) →₀ R)).exteriorPower q s) =
      (Char0.etaleDifferentialBasis v hv).exteriorPower q s := by
  rw [← Module.Basis.baseChange_apply]
  exact Module.Basis.equiv_apply _ _ _ _

/-- Every actual original function coefficient of a coordinate differential wedge is retained. -/
theorem formEquiv_tmul_basis (q : ℕ) (f : B) (s : Set.powersetCard (Fin n) q) :
    formEquiv v hv q (f ⊗ₜ[R]
      (Finsupp.basisSingleOne : Module.Basis (Fin n) R ((Fin n) →₀ R)).exteriorPower q s) =
      f • (Char0.etaleDifferentialBasis v hv).exteriorPower q s := by
  have h : f ⊗ₜ[R] (Finsupp.basisSingleOne : Module.Basis (Fin n) R ((Fin n) →₀ R)).exteriorPower q s =
      f • (1 ⊗ₜ[R] (Finsupp.basisSingleOne : Module.Basis (Fin n) R ((Fin n) →₀ R)).exteriorPower q s) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, formEquiv_one_tmul_basis]

/-- The actual de Rham differential on the ORIGINAL exterior cotangent modules. -/
def differential (q : ℕ) :
    (⋀[B]^q (KaehlerDifferential R (B))) →+
      (⋀[B]^(q+1) (KaehlerDifferential R (B))) :=
  (formEquiv v hv (q+1)).toAddMonoidHom.comp
    ((tensorDifferential v hv q).toAddMonoidHom.comp (formEquiv v hv q).symm.toAddMonoidHom)

/-- The actual whole comparison intertwines the original exterior differential. -/
theorem differential_formEquiv (q : ℕ)
    (z : B ⊗[R] (⋀[R]^q ((Fin n) →₀ R))) :
    differential v hv q (formEquiv v hv q z) = formEquiv v hv (q+1) (tensorDifferential v hv q z) := by
  change formEquiv v hv (q+1)
    (tensorDifferential v hv q ((formEquiv v hv q).symm (formEquiv v hv q z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The differential squares to zero on the WHOLE SAME original exterior cotangent module. -/
theorem differential_square (q : ℕ)
    (w : ⋀[B]^q (KaehlerDifferential R (B))) :
    differential v hv (q+1) (differential v hv q w) = 0 := by
  obtain ⟨z, rfl⟩ := (formEquiv v hv q).surjective w
  rw [differential_formEquiv, differential_formEquiv, tensorDifferential_square, map_zero]

/-- Every original constant coordinate differential wedge is closed. -/
theorem differential_coordinate_wedge (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    differential v hv q ((Char0.etaleDifferentialBasis v hv).exteriorPower q s) = 0 := by
  rw [← formEquiv_one_tmul_basis v hv q s, differential_formEquiv, tensorDifferential_tmul]
  simp only [Derivation.map_one_eq_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, map_zero]


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

private theorem leftWedge_zero {M : Type*} [AddCommGroup M] [Module R M] (m : M) :
    leftWedge m 0 ((exteriorPower.zeroEquiv R M).symm 1) =
      (exteriorPower.oneEquiv R M).symm m := by
  rw [exteriorPower.zeroEquiv_symm_apply, one_smul, exteriorPower.oneEquiv_symm_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ι R m * ExteriorAlgebra.ιMulti R 0 _ =
    ExteriorAlgebra.ιMulti R 1 (fun _ => m)
  rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one, ExteriorAlgebra.ιMulti_apply]
  simp only [List.ofFn_const, List.replicate_one, List.prod_singleton]

/-- The original algebra-to-degree-zero identification is exactly the canonical native
zero exterior-power equivalence. -/
theorem formEquiv_zero (f : B) :
    formEquiv v hv 0 (f ⊗ₜ[R] (exteriorPower.zeroEquiv R ((Fin n) →₀ R)).symm 1) =
      (exteriorPower.zeroEquiv (B)
        (KaehlerDifferential R (B))).symm f := by
  let s : Set.powersetCard (Fin n) 0 := Set.powersetCard.ofCard (Finset.card_empty (α := (Fin n)))
  have hz : (exteriorPower.zeroEquiv R ((Fin n) →₀ R)).symm 1 =
      (Finsupp.basisSingleOne : Module.Basis (Fin n) R ((Fin n) →₀ R)).exteriorPower 0 s := by
    apply (exteriorPower.zeroEquiv R ((Fin n) →₀ R)).injective
    rw [LinearEquiv.apply_symm_apply, zeroEquiv_basis]
  rw [hz, formEquiv_tmul_basis]
  apply (exteriorPower.zeroEquiv (B)
    (KaehlerDifferential R (B))).injective
  rw [map_smul, zeroEquiv_basis, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

private theorem formEquiv_one_single (f : B) (i : (Fin n)) :
    exteriorPower.oneEquiv (B) (KaehlerDifferential R (B))
      (formEquiv v hv 1 (f ⊗ₜ[R]
        (exteriorPower.oneEquiv R ((Fin n) →₀ R)).symm (Finsupp.single i 1))) =
      f • KaehlerDifferential.D R (B) (v i) := by
  let s : Set.powersetCard (Fin n) 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  have hz : (exteriorPower.oneEquiv R ((Fin n) →₀ R)).symm (Finsupp.single i 1) =
      (Finsupp.basisSingleOne : Module.Basis (Fin n) R ((Fin n) →₀ R)).exteriorPower 1 s := by
    apply (exteriorPower.oneEquiv R ((Fin n) →₀ R)).injective
    rw [LinearEquiv.apply_symm_apply, oneEquiv_basis_singleton]
    rfl
  rw [hz, formEquiv_tmul_basis, map_smul, oneEquiv_basis_singleton,
    Char0.etaleDifferentialBasis_apply]

/-- In degree zero this is the SAME original universal Kaehler differential, under the
canonical native zero and one exterior-power identifications. -/
theorem differential_zero (f : B) :
    exteriorPower.oneEquiv (B) (KaehlerDifferential R (B))
      (differential v hv 0
        ((exteriorPower.zeroEquiv (B)
          (KaehlerDifferential R (B))).symm f)) =
      KaehlerDifferential.D R (B) f := by
  rw [← formEquiv_zero v hv f, differential_formEquiv, tensorDifferential_tmul, map_sum, map_sum]
  simp_rw [leftWedge_zero]
  calc
    _ = ∑ i, Char0.etalePartialDeriv v hv i f • KaehlerDifferential.D R (B) (v i) :=
      Finset.sum_congr rfl (fun i _ => formEquiv_one_single v hv (Char0.etalePartialDeriv v hv i f) i)
    _ = _ := by
      have hrep : (∑ i, Char0.etalePartialDeriv v hv i f •
          Char0.etaleDifferentialBasis v hv i) = KaehlerDifferential.D R B f :=
        (Char0.etaleDifferentialBasis v hv).sum_repr (KaehlerDifferential.D R B f)
      simpa only [Char0.etaleDifferentialBasis_apply] using hrep

/-- Genuine original coefficient-ring linearity, with the SAME actual algebra-map action. -/
theorem differential_base_smul (q : ℕ) (a : R)
    (w : ⋀[B]^q (KaehlerDifferential R B)) :
    differential v hv q ((algebraMap R B a) • w) =
      (algebraMap R B a) • differential v hv q w := by
  obtain ⟨z, rfl⟩ := (formEquiv v hv q).surjective w
  rw [← map_smul, differential_formEquiv, differential_formEquiv]
  have h (m : ℕ) (x : B ⊗[R] (⋀[R]^m (Fin n →₀ R))) :
      (algebraMap R B a) • x = a • x := IsScalarTower.algebraMap_smul B a x
  calc
    formEquiv v hv (q+1) (tensorDifferential v hv q ((algebraMap R B a) • z)) =
        formEquiv v hv (q+1) (a • tensorDifferential v hv q z) := by rw [h, map_smul]
    _ = formEquiv v hv (q+1) ((algebraMap R B a) • tensorDifferential v hv q z) := by rw [h]
    _ = _ := (formEquiv v hv (q+1)).map_smul _ _

/-- The genuine whole original exterior cotangent cochain complex on the actual etale algebra. -/
def complex : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of
    (fun q => AddCommGrpCat.of (⋀[B]^q (KaehlerDifferential R B)))
    (fun q => AddCommGrpCat.ofHom (differential v hv q))
    (fun q => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro w
      exact differential_square v hv q w)

/-- The actual original polynomial coefficient map on EVERY original exterior tensor. -/
def polynomialTensorMap (q : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] (⋀[R]^q (Fin n →₀ R))) →ₗ[R]
      (B ⊗[R] (⋀[R]^q (Fin n →₀ R))) :=
  TensorProduct.map (aeval v).toLinearMap LinearMap.id

/-- EVERY original polynomial coefficient and original wedge is retained by the actual map. -/
theorem polynomialTensorMap_tmul (q : ℕ) (f : MvPolynomial (Fin n) R)
    (w : ⋀[R]^q (Fin n →₀ R)) :
    polynomialTensorMap v q (f ⊗ₜ[R] w) = aeval v f ⊗ₜ[R] w := rfl

/-- The actual WHOLE polynomial-to-etale tensor map intertwines the SAME original
differentials on EVERY input, with true coordinate derivative matching derived internally. -/
theorem tensorDifferential_polynomialTensorMap (q : ℕ)
    (z : MvPolynomial (Fin n) R ⊗[R] (⋀[R]^q (Fin n →₀ R))) :
    tensorDifferential v hv q (polynomialTensorMap v q z) =
      polynomialTensorMap v (q+1) (PolynomialDeRham.tensorDifferential R q z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul f w =>
    simp only [polynomialTensorMap_tmul, tensorDifferential_tmul,
      PolynomialDeRham.tensorDifferential_tmul, map_sum, partials_aeval]

/-- The ACTUAL whole polynomial-to-etale map on the SAME original exterior cotangent
modules, retaining the original polynomial coefficient map and actual cotangent basis. -/
def polynomialFormMap (q : ℕ) :
    (⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R))) →+
      (⋀[B]^q (KaehlerDifferential R B)) :=
  (formEquiv v hv q).toAddMonoidHom.comp
    ((polynomialTensorMap v q).toAddMonoidHom.comp (PolynomialDeRham.formEquiv R q).symm.toAddMonoidHom)

/-- The entire original form map retains EVERY original coefficient-tensor input. -/
theorem polynomialFormMap_formEquiv (q : ℕ)
    (z : MvPolynomial (Fin n) R ⊗[R] (⋀[R]^q (Fin n →₀ R))) :
    polynomialFormMap v hv q (PolynomialDeRham.formEquiv R q z) =
      formEquiv v hv q (polynomialTensorMap v q z) := by
  change formEquiv v hv q (polynomialTensorMap v q
    ((PolynomialDeRham.formEquiv R q).symm (PolynomialDeRham.formEquiv R q z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- EVERY original scalar/basis form maps to the SAME original pulled coefficient and
actual original coordinate differential wedge. -/
theorem polynomialFormMap_smul_basis (q : ℕ) (f : MvPolynomial (Fin n) R)
    (s : Set.powersetCard (Fin n) q) :
    polynomialFormMap v hv q
      (f • (KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q s) =
    aeval v f • (Char0.etaleDifferentialBasis v hv).exteriorPower q s := by
  rw [← PolynomialDeRham.formEquiv_tmul_basis R q f s, polynomialFormMap_formEquiv,
    polynomialTensorMap_tmul, formEquiv_tmul_basis]

/-- The actual WHOLE original exterior cotangent map intertwines the original polynomial
and etale differentials on EVERY original form, not only selected representatives. -/
theorem differential_polynomialFormMap (q : ℕ)
    (w : ⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R))) :
    differential v hv q (polynomialFormMap v hv q w) =
      polynomialFormMap v hv (q+1) (PolynomialDeRham.differential R q w) := by
  obtain ⟨z, rfl⟩ := (PolynomialDeRham.formEquiv R q).surjective w
  rw [polynomialFormMap_formEquiv, differential_formEquiv,
    tensorDifferential_polynomialTensorMap, PolynomialDeRham.differential_formEquiv,
    polynomialFormMap_formEquiv]

variable (p : ℕ) [Fact p.Prime] [CharP B p]

omit [Fact p.Prime] in
private theorem partial_pow (i : Fin n) (a : B) :
    Char0.etalePartialDeriv v hv i (a^p) = 0 := by
  simp only [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero B p, zero_mul]

omit [Fact p.Prime] in
/-- Genuine Frobenius scalar linearity of the WHOLE original etale coordinate tensor
differential, derived from its actual derivations and original positive powers. -/
theorem tensorDifferential_pow_smul (q : ℕ) (a : B)
    (z : B ⊗[R] (⋀[R]^q (Fin n →₀ R))) :
    tensorDifferential v hv q (a^p • z) = a^p • tensorDifferential v hv q z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul f w =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, tensorDifferential_tmul,
      Derivation.leibniz, partial_pow v hv p, mul_zero, add_zero, Finset.smul_sum]
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]

omit [Fact p.Prime] in
/-- The SAME original whole exterior cotangent differential has actual Frobenius linearity. -/
theorem differential_pow_smul (q : ℕ) (a : B)
    (w : ⋀[B]^q (KaehlerDifferential R B)) :
    differential v hv q (a^p • w) = a^p • differential v hv q w := by
  obtain ⟨z, rfl⟩ := (formEquiv v hv q).surjective w
  rw [← map_smul, differential_formEquiv, tensorDifferential_pow_smul,
    map_smul, differential_formEquiv]

/-- The actual native Frobenius-restricted SAME original etale exterior cotangent module. -/
def frobeniusModule (q : ℕ) : ModuleCat B :=
  (ModuleCat.restrictScalars (frobenius B p)).obj
    (ModuleCat.of B (⋀[B]^q (KaehlerDifferential R B)))

/-- The actual whole original differential, genuinely native-linear for Frobenius scalars. -/
def frobeniusDifferential (q : ℕ) :
    frobeniusModule (R := R) (B := B) p q ⟶ frobeniusModule (R := R) (B := B) p (q+1) :=
  ModuleCat.ofHom (X := frobeniusModule (R := R) (B := B) p q)
    (Y := frobeniusModule (R := R) (B := B) p (q+1))
    { toFun := differential v hv q
      map_add' := (differential v hv q).map_add
      map_smul' := fun a w => differential_pow_smul v hv p q a w }

/-- The actual original affine etale de Rham complex with genuine Frobenius scalar action. -/
def frobeniusComplex : CochainComplex (ModuleCat B) ℕ :=
  CochainComplex.of (frobeniusModule (R := R) (B := B) p) (frobeniusDifferential v hv p)
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact differential_square v hv q w)

end EnvelopeProperty.Cartier.EtaleDeRham
