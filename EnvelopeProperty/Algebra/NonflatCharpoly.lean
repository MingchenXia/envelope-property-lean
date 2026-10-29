/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import EnvelopeProperty.Berkovich.ArtinianLocalFactors
import EnvelopeProperty.Berkovich.LocalNormForm

/-!
# Characteristic polynomials over a normal domain

This file formalizes the two algebraic lemmas of the nonflat route to FHX Proposition 5.22
(Fang–Han–Xia, *The envelope property for unibranch projective varieties*, Section 5,
`prop:nonflat-norm`; blueprint chapter `nonflat-route.tex`, subsection `subsec:nf-charpoly`).
They replace the line multiplicities of the FHX proof by intrinsic characteristic polynomials.

## `lem:nf-charpoly`

Let `R` be an integrally closed domain with fraction field `K` and `T` a domain containing `R`
(`FaithfulSMul R T`) and finite over `R`. For `b ∈ T` the characteristic polynomial `χ_b` of
multiplication by `b` on the `K`-vector space `K ⊗_R T` has coefficients in `R`. In Lean,
`nonflatCharpoly R T b : R[X]` is defined as `μ_b ^ (d / deg μ_b)` with `μ_b = minpoly R b` and
`d = Module.finrank R T` (the formula `χ_b = μ_b^{[L : K(b)]}` of the blueprint proof), and
`charpoly_lmul_tensor_eq_map_nonflatCharpoly` proves that its image in `K[X]` is the
characteristic polynomial of `1 ⊗ b` on `K ⊗_R T` (a field by
`nonflat_isField_fractionRing_tensor`, of dimension `d` by `nonflat_finrank_fractionRing_tensor`).
Then:

1. `nonflatCharpoly_monic`, `natDegree_nonflatCharpoly`: `χ_b ∈ R[X]` is monic of degree `d`;
2. `aeval_nonflatCharpoly` (Cayley–Hamilton): `χ_b(b) = 0` in `T`;
3. `dvd_algebraMap_coeff_zero_nonflatCharpoly`, `coeff_zero_nonflatCharpoly_ne_zero`:
   `χ_b(0) ∈ bT`, and `χ_b(0) ≠ 0` if `b ≠ 0`;
4. comparison with free covers: `nonflatCharpoly_map_eq_charpoly_of_injective` (base change to
   a domain `S ⊇ R` over which `S ⊗_R T` is free), `nonflatCharpoly_map_eq_charpoly_of_isUnit`
   (base change to any `R`-algebra in which some `f` with `T_f` free over `R_f` becomes a unit),
   and `nonflatCharpoly_comparison`, `nonflatCharpoly_comparison_of_bijective` (blueprint item
   (4): if `T'` is finite free over `Q`, `R → Q`, and `Ω ⊗_R T ≅ Ω ⊗_Q T'` for some `Q`-algebra
   `Ω ⊇ Q` in which `f` is a unit, then the characteristic polynomial over `Q` of the image `b'`
   of `b` on `T'` is the image of `χ_b`).

`nonflat_exists_free_localizationAway` provides the element `f` (generic freeness of a finite
module over a noetherian domain), and `nonflat_free_away_of_dvd` lets one shrink it.

## `lem:nf-local-charpoly`

For a finite algebra `E` over a field `F` and `b ∈ E` congruent to scalars `c_m` modulo every
maximal ideal `m`, the characteristic polynomial of `b` is `∏_m (X - c_m)^{e_m}` with
`e_m = dim_F E_m` (`nonflat_charpoly_lmul_eq_prod_of_sub_mem`). If `F` is algebraically closed,
the residues `nonflatResidue F m b ∈ F` exist, and `charpoly_lmul_eq_prod_nonflatResidue` is the
blueprint statement; `nonflat_rootMultiplicity_charpoly_lmul` computes the root multiplicities
as sums of the local dimensions `e_m`, which are the lengths of the local factors
(`nonflat_finrank_localization_eq_length`).

The local factors are the project's `finiteAlgebraLocalizationEquiv`
(`Berkovich/ArtinianLocalFactors`); the local length identity is `finrank_eq_localLength`
(`Berkovich/LocalNormForm`, `spectrum:algclosed-local-norm-form`).
-/

open scoped NNReal ENNReal Topology TensorProduct
open Polynomial Matrix

noncomputable section

namespace EnvelopeProperty

/-! ### Auxiliary facts on characteristic polynomials -/

section CharpolyAux

/-- The characteristic matrix of a block diagonal matrix is block diagonal. -/
theorem nonflat_charmatrix_blockDiagonal {R n o : Type*} [CommRing R] [DecidableEq n] [Fintype n]
    [DecidableEq o] [Fintype o] (M : o → Matrix n n R) :
    charmatrix (blockDiagonal M) = blockDiagonal fun k => charmatrix (M k) := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  by_cases hk : k = k'
  · subst hk
    by_cases hij : i = j
    · subst hij; simp
    · rw [charmatrix_apply_ne _ _ _ (by simp [hij]), blockDiagonal_apply_eq,
        blockDiagonal_apply_eq, charmatrix_apply_ne _ _ _ hij]
  · rw [charmatrix_apply_ne _ _ _ (by simp [hk]), blockDiagonal_apply_ne _ _ _ hk,
      blockDiagonal_apply_ne _ _ _ hk]
    simp

/-- The characteristic polynomial of a block diagonal matrix is the product of those of the
blocks. -/
theorem nonflat_charpoly_blockDiagonal {R n o : Type*} [CommRing R] [DecidableEq n] [Fintype n]
    [DecidableEq o] [Fintype o] (M : o → Matrix n n R) :
    (blockDiagonal M).charpoly = ∏ k, (M k).charpoly := by
  rw [Matrix.charpoly, nonflat_charmatrix_blockDiagonal, det_blockDiagonal]
  rfl

/-- The characteristic matrix of a block diagonal matrix with blocks of varying sizes. -/
theorem nonflat_charmatrix_blockDiagonal' {R o : Type*} [CommRing R] [DecidableEq o] [Fintype o]
    {n : o → Type*} [∀ i, DecidableEq (n i)] [∀ i, Fintype (n i)]
    (M : ∀ i, Matrix (n i) (n i) R) :
    charmatrix (blockDiagonal' M) = blockDiagonal' fun k => charmatrix (M k) := by
  ext ⟨k, i⟩ ⟨k', j⟩
  by_cases hk : k = k'
  · subst hk
    by_cases hij : i = j
    · subst hij; simp
    · rw [charmatrix_apply_ne _ _ _ (by simp [hij]), blockDiagonal'_apply_eq,
        blockDiagonal'_apply_eq, charmatrix_apply_ne _ _ _ hij]
  · rw [charmatrix_apply_ne _ _ _ (by simp [hk]), blockDiagonal'_apply_ne _ _ _ hk,
      blockDiagonal'_apply_ne _ _ _ hk]
    simp

/-- The characteristic polynomial of a block diagonal matrix with blocks of varying sizes. -/
theorem nonflat_charpoly_blockDiagonal' {R o : Type*} [CommRing R] [DecidableEq o] [Fintype o]
    {n : o → Type*} [∀ i, DecidableEq (n i)] [∀ i, Fintype (n i)]
    (M : ∀ i, Matrix (n i) (n i) R) :
    (blockDiagonal' M).charpoly = ∏ k, (M k).charpoly := by
  rw [Matrix.charpoly, nonflat_charmatrix_blockDiagonal', det_blockDiagonal']
  rfl

/-- For a finite field extension `L/K` and `x ∈ L`, the characteristic polynomial of
multiplication by `x` is `minpoly K x ^ [L : K(x)]`. -/
theorem nonflat_charpoly_lmul_eq_minpoly_pow {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    LinearMap.charpoly (Algebra.lmul K L x) =
      minpoly K x ^ (Module.finrank K L / (minpoly K x).natDegree) := by
  classical
  let E := IntermediateField.adjoin K {x}
  let pb := IntermediateField.adjoin.powerBasis (K := K) (x := x)
    (Algebra.IsIntegral.isIntegral x)
  let c := Module.Free.chooseBasis E L
  let bb := pb.basis.smulTower c
  rw [← LinearMap.charpoly_toMatrix _ bb]
  change (Algebra.leftMulMatrix bb x).charpoly = _
  have hm : Algebra.leftMulMatrix bb x =
      Algebra.leftMulMatrix bb (algebraMap E L (IntermediateField.AdjoinSimple.gen K x)) := rfl
  rw [hm, Algebra.smulTower_leftMulMatrix_algebraMap, nonflat_charpoly_blockDiagonal,
    Finset.prod_const, Finset.card_univ]
  have h1 : (Algebra.leftMulMatrix pb.basis
      (IntermediateField.AdjoinSimple.gen K x)).charpoly = minpoly K x := by
    have : pb.gen = IntermediateField.AdjoinSimple.gen K x :=
      IntermediateField.adjoin.powerBasis_gen _
    rw [← this, charpoly_leftMulMatrix, this, IntermediateField.minpoly_gen]
  rw [h1]
  congr 1
  rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_mul_finrank K E L,
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x)]
  have : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  rw [Nat.mul_div_cancel_left _ this]

/-- Characteristic polynomials of multiplication maps commute with base change. -/
theorem nonflat_charpoly_lmul_baseChange {R M : Type*} [CommRing R] [CommRing M] [Algebra R M]
    [Module.Free R M] [Module.Finite R M] (S : Type*) [CommRing S] [Algebra R S] (x : M) :
    LinearMap.charpoly (Algebra.lmul S (S ⊗[R] M) (1 ⊗ₜ x)) =
      (LinearMap.charpoly (Algebra.lmul R M x)).map (algebraMap R S) := by
  rw [← Algebra.baseChange_lmul, LinearMap.charpoly_baseChange]

/-- Characteristic polynomials of multiplication maps are invariant under algebra isomorphisms. -/
theorem nonflat_charpoly_lmul_algEquiv {R M N : Type*} [CommRing R] [CommRing M] [CommRing N]
    [Algebra R M] [Algebra R N] [Module.Free R M] [Module.Finite R M] [Module.Free R N]
    [Module.Finite R N] (e : M ≃ₐ[R] N) (x : M) :
    LinearMap.charpoly (Algebra.lmul R N (e x)) = LinearMap.charpoly (Algebra.lmul R M x) := by
  rw [← e.toLinearEquiv.charpoly_conj (Algebra.lmul R M x)]
  congr 1
  ext y
  simp [LinearEquiv.conj_apply]

/-- The characteristic polynomial of multiplication on a finite product of algebras is the
product of the characteristic polynomials on the factors. -/
theorem nonflat_charpoly_lmul_pi {K ι : Type*} [CommRing K] [Fintype ι] {E : ι → Type*}
    [∀ i, CommRing (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Free K (E i)]
    [∀ i, Module.Finite K (E i)] (x : ∀ i, E i) :
    LinearMap.charpoly (Algebra.lmul K (∀ i, E i) x) =
      ∏ i, LinearMap.charpoly (Algebra.lmul K (E i) (x i)) := by
  classical
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex K (E i)) K (E i) :=
    fun i => Module.Free.chooseBasis K (E i)
  rw [← LinearMap.charpoly_toMatrix _ (Pi.basis b)]
  simp_rw [← LinearMap.charpoly_toMatrix _ (b _)]
  change (Algebra.leftMulMatrix (Pi.basis b) x).charpoly =
    ∏ i, (Algebra.leftMulMatrix (b i) (x i)).charpoly
  rw [← nonflat_charpoly_blockDiagonal']
  congr 1
  ext ⟨i, p⟩ ⟨j, q⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr,
    Matrix.blockDiagonal'_apply]
  dsimp only
  by_cases hij : i = j
  · subst hij
    rw [dif_pos rfl, Pi.mul_apply, Pi.single_eq_same, Algebra.leftMulMatrix_eq_repr_mul]
    rfl
  · rw [dif_neg hij, Pi.mul_apply, Pi.single_eq_of_ne hij, mul_zero, map_zero,
      Finsupp.zero_apply]

/-- If `b - c` is nilpotent for a scalar `c`, the characteristic polynomial of `b` is
`(X - c)^{rank}`. -/
theorem nonflat_charpoly_lmul_of_isNilpotent_sub {R E : Type*} [CommRing R] [IsDomain R]
    [CommRing E] [Algebra R E] [Module.Free R E] [Module.Finite R E] (b : E) (c : R)
    (h : IsNilpotent (b - algebraMap R E c)) :
    LinearMap.charpoly (Algebra.lmul R E b) = (X - C c) ^ Module.finrank R E := by
  let f : Module.End R E := Algebra.lmul R E (b - algebraMap R E c)
  have hf : IsNilpotent f := h.map (Algebra.lmul R E)
  have hb : Algebra.lmul R E b = f - (-c) • 1 := by
    ext x
    simp [f, Algebra.coe_lmul_eq_mul, Algebra.smul_def]
  rw [hb, LinearMap.charpoly_sub_smul, hf.charpoly_eq_X_pow_finrank]
  simp [sub_eq_add_neg]

end CharpolyAux

/-! ### Generic freeness -/

/-- **Generic freeness.** A finite module over a noetherian domain becomes free after inverting a
single nonzero element. -/
theorem nonflat_exists_free_localizationAway {R M : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (Localization.Away f ⊗[R] M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (TensorProduct.mk R (FractionRing R) M 1) (FractionRing R)
  refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
  exact Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r)
    (Localization.Away r) (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv.symm

/-! ### The characteristic polynomial over a normal base -/

section Definition

variable (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]

/-- The **characteristic polynomial** `χ_b ∈ R[X]` of `b ∈ T` over `R` (blueprint
`lem:nf-charpoly`), for a domain `T` finite over an integrally closed domain `R ⊆ T`. It is defined
by the formula `χ_b = μ_b ^ (d / deg μ_b)` of the blueprint proof, with `μ_b = minpoly R b` and
`d = Module.finrank R T`; `charpoly_lmul_tensor_eq_map_nonflatCharpoly` shows that its image in
`K[X]`, `K = Frac R`, is the characteristic polynomial of multiplication by `b` on `K ⊗_R T`. -/
def nonflatCharpoly (b : T) : R[X] :=
  minpoly R b ^ (Module.finrank R T / (minpoly R b).natDegree)

/-- Unfolding lemma for `nonflatCharpoly`. -/
theorem nonflatCharpoly_def (b : T) :
    nonflatCharpoly R T b = minpoly R b ^ (Module.finrank R T / (minpoly R b).natDegree) :=
  rfl

variable {R T}

/-- `χ_b` is monic. -/
theorem nonflatCharpoly_monic [Algebra.IsIntegral R T] (b : T) : (nonflatCharpoly R T b).Monic :=
  (minpoly.monic (Algebra.IsIntegral.isIntegral b)).pow _

end Definition

section Normal

variable {R T : Type*} [CommRing R] [IsDomain R] [CommRing T] [IsDomain T] [Algebra R T]
  [FaithfulSMul R T] [Module.Finite R T]

omit [Module.Finite R T] in
variable (R T) in
/-- The images of the nonzero elements of `R` are nonzero divisors of `T`. -/
theorem nonflat_algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid T (nonZeroDivisors R) ≤ nonZeroDivisors T := by
  rintro _ ⟨r, hr, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R T)).2 (nonZeroDivisors.ne_zero hr))

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

variable (T) in
/-- `K ⊗_R T` is a localization of the domain `T`, finite over `K`, hence a field. -/
theorem nonflat_isField_fractionRing_tensor : IsField (K ⊗[R] T) := by
  let _ : Algebra T (K ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors R)) (K ⊗[R] T) :=
    IsLocalization.tensorRight (S := T) K (nonZeroDivisors R)
  have : IsDomain (K ⊗[R] T) := IsLocalization.isDomain_of_le_nonZeroDivisors (R := T)
    (K ⊗[R] T) (nonflat_algebraMapSubmonoid_le R T)
  exact isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)

omit [Module.Finite R T] in
variable (T) in
/-- `T → K ⊗_R T`, `t ↦ 1 ⊗ t`, is injective. -/
theorem nonflat_fractionRing_tmul_injective : Function.Injective fun t : T => (1 : K) ⊗ₜ[R] t := by
  let _ : Algebra T (K ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors R)) (K ⊗[R] T) :=
    IsLocalization.tensorRight (S := T) K (nonZeroDivisors R)
  exact IsLocalization.injective (K ⊗[R] T) (nonflat_algebraMapSubmonoid_le R T)

omit [IsDomain T] [FaithfulSMul R T] [Module.Finite R T] in
variable (R T) in
/-- `dim_K (K ⊗_R T) = rank_R T`. -/
theorem nonflat_finrank_fractionRing_tensor : Module.finrank K (K ⊗[R] T) = Module.finrank R T :=
  (TensorProduct.isBaseChange R T K).finrank_eq

variable [IsIntegrallyClosed R]

/-- **`lem:nf-charpoly`, characterization.** The image of `χ_b = nonflatCharpoly R T b` in
`K[X]`, `K = Frac R`, is the characteristic polynomial of multiplication by `1 ⊗ b` on the
`K`-vector space `K ⊗_R T`. -/
theorem charpoly_lmul_tensor_eq_map_nonflatCharpoly (b : T) :
    LinearMap.charpoly (Algebra.lmul K (K ⊗[R] T) ((1 : K) ⊗ₜ[R] b)) =
      (nonflatCharpoly R T b).map (algebraMap R K) := by
  let _ : Field (K ⊗[R] T) := (nonflat_isField_fractionRing_tensor T K).toField
  let _ : Algebra T (K ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  have hmin : minpoly K ((1 : K) ⊗ₜ[R] b) = (minpoly R b).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K (K ⊗[R] T) hb
  rw [nonflat_charpoly_lmul_eq_minpoly_pow, hmin, nonflatCharpoly, Polynomial.map_pow,
    (minpoly.monic hb).natDegree_map, nonflat_finrank_fractionRing_tensor]

end Normal

section Properties

variable {R T : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing T] [IsDomain T]
  [Algebra R T] [FaithfulSMul R T] [Module.Finite R T]

omit [IsIntegrallyClosed R] in
variable (R T) in
/-- A domain finite over a domain `R ⊆ T` has positive rank. -/
theorem nonflat_finrank_pos_of_finite_domain : 0 < Module.finrank R T := by
  rw [← nonflat_finrank_fractionRing_tensor R T (FractionRing R)]
  have : Nontrivial (FractionRing R ⊗[R] T) :=
    ⟨(nonflat_isField_fractionRing_tensor T (FractionRing R)).exists_pair_ne⟩
  exact Module.finrank_pos

/-- **`lem:nf-charpoly` (1).** `χ_b` has degree `d = rank_R T`. -/
theorem natDegree_nonflatCharpoly (b : T) :
    (nonflatCharpoly R T b).natDegree = Module.finrank R T := by
  rw [← (nonflatCharpoly_monic (R := R) b).natDegree_map (algebraMap R (FractionRing R)),
    ← charpoly_lmul_tensor_eq_map_nonflatCharpoly (FractionRing R) b,
    LinearMap.charpoly_natDegree, nonflat_finrank_fractionRing_tensor R T (FractionRing R)]

/-- The exponent `d / deg μ_b` in the definition of `χ_b` is positive. -/
theorem nonflatCharpoly_exponent_ne_zero (b : T) :
    Module.finrank R T / (minpoly R b).natDegree ≠ 0 := by
  intro h
  have h1 := natDegree_nonflatCharpoly (R := R) b
  rw [nonflatCharpoly_def, h, pow_zero, natDegree_one] at h1
  exact (nonflat_finrank_pos_of_finite_domain R T).ne h1

/-- **`lem:nf-charpoly` (2), Cayley–Hamilton.** `χ_b(b) = 0` in `T`. -/
theorem aeval_nonflatCharpoly (b : T) : aeval b (nonflatCharpoly R T b) = 0 := by
  rw [nonflatCharpoly_def, map_pow, minpoly.aeval,
    zero_pow (nonflatCharpoly_exponent_ne_zero (R := R) b)]

/-- **`lem:nf-charpoly` (3), first half.** `χ_b(0) ∈ bT`. -/
theorem dvd_algebraMap_coeff_zero_nonflatCharpoly (b : T) :
    b ∣ algebraMap R T ((nonflatCharpoly R T b).coeff 0) := by
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := nonflatCharpoly R T b)
  have h := congrArg (aeval b) hq
  rw [map_sub, aeval_nonflatCharpoly, aeval_C, map_mul, aeval_X, zero_sub] at h
  exact ⟨-(aeval b q), by rw [mul_neg, ← h, neg_neg]⟩

omit [IsIntegrallyClosed R] [FaithfulSMul R T] in
/-- **`lem:nf-charpoly` (3), second half.** `χ_b(0) ≠ 0` if `b ≠ 0`. -/
theorem coeff_zero_nonflatCharpoly_ne_zero {b : T} (hb : b ≠ 0) :
    (nonflatCharpoly R T b).coeff 0 ≠ 0 := by
  rw [nonflatCharpoly_def, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
  refine pow_ne_zero _ fun h0 => ?_
  have hi : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  obtain ⟨q, hq⟩ := X_dvd_iff.2 h0
  have hqm : q.Monic := Monic.of_mul_monic_left monic_X (hq ▸ minpoly.monic hi)
  have hq0 : aeval b q = 0 := by
    have h := minpoly.aeval R b
    rw [hq, map_mul, aeval_X] at h
    exact (mul_eq_zero.1 h).resolve_left hb
  have h1 := natDegree_le_natDegree (minpoly.min R b hqm hq0)
  rw [hq, natDegree_X_mul hqm.ne_zero] at h1
  omega

/-- **`lem:nf-charpoly` (4), base change to a domain.** If `S` is a domain containing `R` and
`S ⊗_R T` is free over `S`, the characteristic polynomial of `1 ⊗ b` on `S ⊗_R T` over `S` is the
image of `χ_b`. -/
theorem nonflatCharpoly_map_eq_charpoly_of_injective (S : Type*) [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Module.Free S (S ⊗[R] T)] (b : T) :
    LinearMap.charpoly (Algebra.lmul S (S ⊗[R] T) ((1 : S) ⊗ₜ[R] b)) =
      (nonflatCharpoly R T b).map (algebraMap R S) := by
  let K := FractionRing R
  let K' := FractionRing S
  have : FaithfulSMul R K' := (faithfulSMul_iff_algebraMap_injective R K').2 (by
    rw [IsScalarTower.algebraMap_eq R S K']
    exact (IsFractionRing.injective S K').comp (FaithfulSMul.algebraMap_injective R S))
  let _ : Algebra K K' := FractionRing.liftAlgebra R K'
  have : IsScalarTower R K K' := FractionRing.isScalarTower_liftAlgebra R K'
  have : Module.Free K' (K' ⊗[R] T) := Module.Free.of_divisionRing K' _
  have : Module.Free K' (K' ⊗[S] (S ⊗[R] T)) := Module.Free.of_divisionRing K' _
  have : Module.Free K' (K' ⊗[K] (K ⊗[R] T)) := Module.Free.of_divisionRing K' _
  have : Module.Free K (K ⊗[R] T) := Module.Free.of_divisionRing K _
  apply Polynomial.map_injective (algebraMap S K') (IsFractionRing.injective S K')
  let e1 := Algebra.TensorProduct.cancelBaseChange R S K' K' T
  let e2 := Algebra.TensorProduct.cancelBaseChange R K K' K' T
  have h1 : e1 ((1 : K') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b)) = (1 : K') ⊗ₜ[R] b := by simp [e1]
  have h2 : e2 ((1 : K') ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b)) = (1 : K') ⊗ₜ[R] b := by simp [e2]
  rw [← nonflat_charpoly_lmul_baseChange K', ← nonflat_charpoly_lmul_algEquiv e1, h1, ← h2,
    nonflat_charpoly_lmul_algEquiv e2, nonflat_charpoly_lmul_baseChange,
    charpoly_lmul_tensor_eq_map_nonflatCharpoly, Polynomial.map_map, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain T] [FaithfulSMul R T] [Module.Finite R T] in
/-- If `T_f` is free over `R_f` and `f` becomes a unit in `S`, then `S ⊗_R T` is free over `S`. -/
theorem nonflat_free_tensor_of_isUnit {f : R}
    (hfree : Module.Free (Localization.Away f) (Localization.Away f ⊗[R] T)) (S : Type*)
    [CommRing S] [Algebra R S] (hf : IsUnit (algebraMap R S f)) : Module.Free S (S ⊗[R] T) := by
  let Rf := Localization.Away f
  let _ : Algebra Rf S := (IsLocalization.Away.lift f hf).toAlgebra
  have : IsScalarTower R Rf S := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq f hf r).symm
  exact Module.Free.of_equiv (Algebra.TensorProduct.cancelBaseChange R Rf S S T).toLinearEquiv

/-- **`lem:nf-charpoly` (4), base change along a localization.** If `T_f` is free over `R_f` and
`f` becomes a unit in the `R`-algebra `S` (e.g. `S = Q_c` or `S = Frac Q` for a ring map
`R → Q` with `f ↦ ψ(f) ≠ 0`), the characteristic polynomial of `1 ⊗ b` on `S ⊗_R T` over `S` is
the image of `χ_b`. (`S ⊗_R T` is free by `nonflat_free_tensor_of_isUnit`.) -/
theorem nonflatCharpoly_map_eq_charpoly_of_isUnit {f : R}
    (hfree : Module.Free (Localization.Away f) (Localization.Away f ⊗[R] T)) (S : Type*)
    [CommRing S] [Algebra R S] (hf : IsUnit (algebraMap R S f)) [Module.Free S (S ⊗[R] T)]
    (b : T) :
    LinearMap.charpoly (Algebra.lmul S (S ⊗[R] T) ((1 : S) ⊗ₜ[R] b)) =
      (nonflatCharpoly R T b).map (algebraMap R S) := by
  by_cases hf0 : f = 0
  · subst hf0
    have : Subsingleton S := by
      rw [map_zero, isUnit_zero_iff] at hf
      exact subsingleton_of_zero_eq_one hf
    exact Subsingleton.elim _ _
  let Rf := Localization.Away f
  have hle : Submonoid.powers f ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : FaithfulSMul R Rf :=
    (faithfulSMul_iff_algebraMap_injective R Rf).2 (IsLocalization.injective Rf hle)
  let _ : Algebra Rf S := (IsLocalization.Away.lift f hf).toAlgebra
  have : IsScalarTower R Rf S := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq f hf r).symm
  let e := Algebra.TensorProduct.cancelBaseChange R Rf S S T
  have he : e ((1 : S) ⊗ₜ[Rf] ((1 : Rf) ⊗ₜ[R] b)) = (1 : S) ⊗ₜ[R] b := by simp [e]
  rw [← he, nonflat_charpoly_lmul_algEquiv e, nonflat_charpoly_lmul_baseChange,
    nonflatCharpoly_map_eq_charpoly_of_injective Rf, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- **`lem:nf-charpoly` (4), comparison with a generically isomorphic free cover.** Let `T_f` be
free over `R_f`, let `R → Q` be a ring map and `T'` a finite free `Q`-algebra. Let `Ω` be a
`Q`-algebra with `Q → Ω` injective in which `f` becomes a unit (e.g. `Ω = Q_{c ψ(f)}` for
`0 ≠ c ∈ Q` in a domain `Q`, or `Ω = Frac Q`), and let `e : Ω ⊗_R T ≅ Ω ⊗_Q T'` be an
isomorphism of `Ω`-algebras mapping `1 ⊗ b` to `1 ⊗ b'`. Then the characteristic polynomial of
multiplication by `b'` on `T'` over `Q` is the image of `χ_b`. -/
theorem nonflatCharpoly_comparison {f : R}
    (hfree : Module.Free (Localization.Away f) (Localization.Away f ⊗[R] T))
    {Q T' Ω : Type*} [CommRing Q] [Algebra R Q] [CommRing T'] [Algebra Q T'] [Module.Free Q T']
    [Module.Finite Q T'] [CommRing Ω] [Algebra Q Ω] [Algebra R Ω] [IsScalarTower R Q Ω]
    (hΩ : Function.Injective (algebraMap Q Ω)) (hf : IsUnit (algebraMap R Ω f))
    (e : Ω ⊗[R] T ≃ₐ[Ω] Ω ⊗[Q] T') {b : T} {b' : T'}
    (he : e ((1 : Ω) ⊗ₜ[R] b) = (1 : Ω) ⊗ₜ[Q] b') :
    LinearMap.charpoly (Algebra.lmul Q T' b') = (nonflatCharpoly R T b).map (algebraMap R Q) := by
  have : Module.Free Ω (Ω ⊗[R] T) := nonflat_free_tensor_of_isUnit hfree Ω hf
  apply Polynomial.map_injective (algebraMap Q Ω) hΩ
  rw [← nonflat_charpoly_lmul_baseChange Ω, ← he, nonflat_charpoly_lmul_algEquiv e,
    nonflatCharpoly_map_eq_charpoly_of_isUnit hfree Ω hf, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- **`lem:nf-charpoly` (4), with the induced map.** The variant of `nonflatCharpoly_comparison`
in which the generic isomorphism is the base change to `Ω` of a `Q`-algebra map
`g : Q ⊗_R T → T'` (for `T' = R'` the normalized curve and `Q ⊗_R T = A_C` the curve, `g` is the
normalization map): if `Ω ⊗_Q g` is bijective, the characteristic polynomial of `g(1 ⊗ b)` on `T'`
over `Q` is the image of `χ_b`. -/
theorem nonflatCharpoly_comparison_of_bijective {f : R}
    (hfree : Module.Free (Localization.Away f) (Localization.Away f ⊗[R] T))
    {Q T' Ω : Type*} [CommRing Q] [Algebra R Q] [CommRing T'] [Algebra Q T'] [Module.Free Q T']
    [Module.Finite Q T'] [CommRing Ω] [Algebra Q Ω] [Algebra R Ω] [IsScalarTower R Q Ω]
    (hΩ : Function.Injective (algebraMap Q Ω)) (hf : IsUnit (algebraMap R Ω f))
    (g : Q ⊗[R] T →ₐ[Q] T')
    (hg : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id Ω Ω) g)) (b : T) :
    LinearMap.charpoly (Algebra.lmul Q T' (g ((1 : Q) ⊗ₜ[R] b))) =
      (nonflatCharpoly R T b).map (algebraMap R Q) := by
  let e : Ω ⊗[R] T ≃ₐ[Ω] Ω ⊗[Q] T' :=
    (Algebra.TensorProduct.cancelBaseChange R Q Ω Ω T).symm.trans (AlgEquiv.ofBijective _ hg)
  refine nonflatCharpoly_comparison hfree hΩ hf e ?_
  simp [e]

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain T] [FaithfulSMul R T] [Module.Finite R T] in
/-- Freeness of `T_f` over `R_f` persists after inverting a multiple `g` of `f`. -/
theorem nonflat_free_away_of_dvd {f g : R}
    (hfree : Module.Free (Localization.Away f) (Localization.Away f ⊗[R] T)) (hfg : f ∣ g) :
    Module.Free (Localization.Away g) (Localization.Away g ⊗[R] T) := by
  refine nonflat_free_tensor_of_isUnit hfree _ ?_
  obtain ⟨c, rfl⟩ := hfg
  exact isUnit_of_mul_isUnit_left (by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (f * c))

end Properties

/-- The multiplicity of `a` as a root of `∏_i (X - c_i)^{e_i}` is `∑_{c_i = a} e_i`. -/
theorem nonflat_rootMultiplicity_prod_X_sub_C_pow {R ι : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] (s : Finset ι) (c : ι → R) (e : ι → ℕ) (a : R) :
    (∏ i ∈ s, (X - C (c i)) ^ e i).rootMultiplicity a = ∑ i ∈ s with c i = a, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, rootMultiplicity_mul, ih, Finset.filter_insert]
    · by_cases h : c i = a
      · rw [if_pos h, Finset.sum_insert (by simp [hi]), h, rootMultiplicity_X_sub_C_pow]
      · rw [if_neg h, rootMultiplicity_eq_zero, zero_add]
        intro hr
        rw [IsRoot, eval_pow, eval_sub, eval_X, eval_C] at hr
        exact h (sub_eq_zero.1 (pow_eq_zero_iff'.1 hr).1).symm
    · exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
        (Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (X_sub_C_ne_zero _))

/-! ### Characteristic polynomials on local Artinian factors -/

section LocalCharpoly

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [FiniteDimensional F E]

/-- On the local factor `E_m` of a finite `F`-algebra `E`, an element congruent to the scalar `c`
modulo `m` has characteristic polynomial `(X - c)^{dim_F E_m}`. -/
theorem nonflat_charpoly_lmul_localization (m : MaximalSpectrum E) (b : E) (c : F)
    (hc : b - algebraMap F E c ∈ m.asIdeal) :
    LinearMap.charpoly (Algebra.lmul F (Localization.AtPrime m.asIdeal)
        (algebraMap E (Localization.AtPrime m.asIdeal) b)) =
      (X - C c) ^ Module.finrank F (Localization.AtPrime m.asIdeal) := by
  apply nonflat_charpoly_lmul_of_isNilpotent_sub
  have : IsArtinianRing (Localization.AtPrime m.asIdeal) := IsArtinianRing.of_finite F _
  rw [← mem_nilradical]
  change _ ∈ (⊥ : Ideal (Localization.AtPrime m.asIdeal)).radical
  rw [← IsArtinianRing.jacobson_eq_radical, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
  have h : algebraMap E (Localization.AtPrime m.asIdeal) b -
      algebraMap F (Localization.AtPrime m.asIdeal) c =
      algebraMap E (Localization.AtPrime m.asIdeal) (b - algebraMap F E c) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
  rw [h]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m.asIdeal)
    m.asIdeal _).2 hc

/-- **`lem:nf-local-charpoly`, general form.** Let `E` be a finite algebra over a field `F` and
`b ∈ E` with `b ≡ c_m (mod m)` for scalars `c_m ∈ F`, for every maximal ideal `m`. Then the
characteristic polynomial of multiplication by `b` on `E` is `∏_m (X - c_m)^{e_m}`, where
`e_m = dim_F E_m` is the dimension of the local factor `E_m`. -/
theorem nonflat_charpoly_lmul_eq_prod_of_sub_mem [Fintype (MaximalSpectrum E)] (b : E)
    (c : MaximalSpectrum E → F) (hc : ∀ m, b - algebraMap F E (c m) ∈ m.asIdeal) :
    LinearMap.charpoly (Algebra.lmul F E b) =
      ∏ m, (X - C (c m)) ^ Module.finrank F (Localization.AtPrime m.asIdeal) := by
  rw [← nonflat_charpoly_lmul_algEquiv (finiteAlgebraLocalizationEquiv F E),
    nonflat_charpoly_lmul_pi]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [finiteAlgebraLocalizationEquiv_apply]
  exact nonflat_charpoly_lmul_localization m b (c m) (hc m)

variable [IsAlgClosed F]

variable (F) in
/-- For a maximal ideal `m` of a finite algebra `E` over an algebraically closed field `F`, the
structure map `F → E/m` is an isomorphism. -/
def nonflatResidueEquiv (m : MaximalSpectrum E) : F ≃ₐ[F] E ⧸ m.asIdeal :=
  have := m.isMaximal
  AlgEquiv.ofBijective (Algebra.ofId F (E ⧸ m.asIdeal))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F))

variable (F) in
/-- The residue `b(m) ∈ F` of `b ∈ E` at a maximal ideal `m` of a finite algebra `E` over an
algebraically closed field `F`: the composite `E → E/m ≅ F`. -/
def nonflatResidue (m : MaximalSpectrum E) : E →ₐ[F] F :=
  (nonflatResidueEquiv F m).symm.toAlgHom.comp (Ideal.Quotient.mkₐ F m.asIdeal)

variable (F) in
theorem nonflatResidue_apply (m : MaximalSpectrum E) (b : E) :
    nonflatResidue F m b = (nonflatResidueEquiv F m).symm (Ideal.Quotient.mk m.asIdeal b) :=
  rfl

variable (F) in
/-- `b ≡ b(m) (mod m)`. -/
theorem sub_algebraMap_nonflatResidue_mem (m : MaximalSpectrum E) (b : E) :
    b - algebraMap F E (nonflatResidue F m b) ∈ m.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, nonflatResidue_apply F,
    ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  exact ((nonflatResidueEquiv F m).apply_symm_apply _).symm

/-- The residue is the unique scalar congruent to `b` modulo `m`. -/
theorem nonflatResidue_eq_iff (m : MaximalSpectrum E) (b : E) (c : F) :
    nonflatResidue F m b = c ↔ b - algebraMap F E c ∈ m.asIdeal := by
  constructor
  · rintro rfl
    exact sub_algebraMap_nonflatResidue_mem F m b
  · intro h
    have h2 := sub_algebraMap_nonflatResidue_mem F m b
    have h3 : algebraMap F E (c - nonflatResidue F m b) ∈ m.asIdeal := by
      rw [map_sub]
      convert m.asIdeal.sub_mem h2 h using 1
      ring
    by_contra hne
    have hu : IsUnit (algebraMap F E (c - nonflatResidue F m b)) :=
      (Ne.isUnit (sub_ne_zero.2 (Ne.symm hne))).map _
    exact m.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 hu)

/-- Any `F`-algebra homomorphism `E → F` whose kernel is contained in `m` computes the residue at
`m` (its kernel is then `m`). -/
theorem nonflatResidue_eq_of_ker_le (m : MaximalSpectrum E) (ψ : E →ₐ[F] F)
    (h : RingHom.ker ψ ≤ m.asIdeal) (b : E) : nonflatResidue F m b = ψ b := by
  rw [nonflatResidue_eq_iff]
  apply h
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_self]

variable (F) in
/-- **`lem:nf-local-charpoly`.** For a finite algebra `E` over an algebraically closed field `F`
and `b ∈ E`, the characteristic polynomial of multiplication by `b` is
`∏_m (X - b(m))^{e_m}`, the product over the maximal ideals `m` (the local factors `E_m`) with
`e_m = dim_F E_m`. -/
theorem charpoly_lmul_eq_prod_nonflatResidue [Fintype (MaximalSpectrum E)] (b : E) :
    LinearMap.charpoly (Algebra.lmul F E b) =
      ∏ m, (X - C (nonflatResidue F m b)) ^ Module.finrank F (Localization.AtPrime m.asIdeal) :=
  nonflat_charpoly_lmul_eq_prod_of_sub_mem b _ fun m => sub_algebraMap_nonflatResidue_mem F m b

/-- **Root multiplicities are local dimensions.** The multiplicity of `a ∈ F` as a root of the
characteristic polynomial of `b` is the sum of the dimensions `e_m` of the local factors at the
maximal ideals `m` with `b(m) = a`. -/
theorem nonflat_rootMultiplicity_charpoly_lmul [Fintype (MaximalSpectrum E)] [DecidableEq F] (b : E)
    (a : F) :
    (LinearMap.charpoly (Algebra.lmul F E b)).rootMultiplicity a =
      ∑ m with nonflatResidue F m b = a, Module.finrank F (Localization.AtPrime m.asIdeal) := by
  rw [charpoly_lmul_eq_prod_nonflatResidue F b, nonflat_rootMultiplicity_prod_X_sub_C_pow]

variable (F) in
/-- The local dimensions are the lengths of the local factors. -/
theorem nonflat_finrank_localization_eq_length (m : MaximalSpectrum E) :
    Module.finrank F (Localization.AtPrime m.asIdeal) =
      (Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal)).toNat :=
  finrank_eq_localLength

end LocalCharpoly

end EnvelopeProperty
