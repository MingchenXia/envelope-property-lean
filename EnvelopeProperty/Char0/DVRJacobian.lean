/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DVRCoordinates

/-!
# Partial derivatives and the log discrepancy at a divisor

Let `F` be a field of characteristic `0`, `K/F` a field extension and `w = (w_j)` a finite
transcendence basis of `K/F` (with `K` algebraic over `F(w)`). This file constructs the partial
derivatives `∂_j = ∂/∂w_j` as `F`-derivations of `K` with `∂_j w_i = δ_{ij}`
(`EnvelopeProperty.Char0.partialDeriv`, through the basis `dw_j` of the Kähler differentials
`Ω_{K/F}`, which holds because `K` is formally étale over `F[w]`), shows that they are unique
(`derivation_eq_zero_of_forall`), and that the Jacobian `det(∂_j z_i)` of a family `z` generating
`K` is nonzero (`jacobian_ne_zero`).

For a divisorial valuation ring `V` over `F` with uniformizer `π` and lifts `u` of a transcendence
basis of `κ_V`, the coordinates `w = (π, u)` (`dvrCoordinates`) form a transcendence basis of `K`
(`isTranscendenceBasis_dvrCoordinates`) and the partial derivatives preserve `V`
(`partialDeriv_mem`): this is the blueprint lemma `lem:c0-dvr-jacobian` (`char0.tex`), which defines
the log discrepancy `A(V) = 1 + ord_V(Jac_V)` (`logDiscrepancy`) used in the valuative bound
`prop:c0-valuative-bound` of the characteristic-zero proof of FHX Theorem 3.1 (Fang–Han–Xia, *The
envelope property for unibranch projective varieties*, §3; the role of `A(V)` is that of the
trace estimate `lem:divisorial-trace-estimate` in characteristic `p`).

## Main results

* `EnvelopeProperty.Char0.partialDeriv`, `partialDeriv_apply`: the derivations `∂_j`.
* `EnvelopeProperty.Char0.derivation_eq_zero_of_forall`, `derivation_eq_sum`: uniqueness.
* `EnvelopeProperty.Char0.jacobian_ne_zero`: `det(∂_j z_i) ≠ 0` when `F(z) = K`.
* `EnvelopeProperty.Char0.derivation_mem_of_isPrimitiveCoordinate`: a derivation which preserves
  `L` and maps `π` into `V` preserves `V = A[θ]_{𝔫'}` (setting of `lem:c0-dvr-primitive`).
* `EnvelopeProperty.Char0.partialDeriv_mem`, `jacobian_mem`: `∂_j(V) ⊆ V`, `Jac_V ∈ V`
  (`lem:c0-dvr-jacobian`).

## Implementation notes

The blueprint extends `∂/∂w_j` from `L(π) = F(w)` to `K` by the formula
`Dθ = -F_θ^D(θ)/F_θ'(θ)`. Here the derivations are produced at once from the `K`-basis `(dw_j)` of
`Ω_{K/F}` (`KaehlerDifferential.isBaseChange_of_formallyEtale`); the formula is used only to prove
`∂_j θ ∈ V`.
-/

noncomputable section

open scoped NNReal ENNReal Topology Polynomial IntermediateField

open Polynomial IsLocalRing

namespace EnvelopeProperty.Char0

/-! ### Partial derivatives along a transcendence basis -/

section PartialDeriv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]
  {σ : Type*} {w : σ → K}

/-- `K` is formally étale over `F[w]` for a transcendence basis `w` (characteristic `0`): it is a
separable algebraic extension of the localization `F(w)` of `F[w]`. -/
theorem formallyEtale_aeval_of_isTranscendenceBasis (hw : IsTranscendenceBasis F w) :
    letI := (MvPolynomial.aeval (R := F) w).toAlgebra
    Algebra.FormallyEtale (MvPolynomial σ F) K := by
  let _ := (MvPolynomial.aeval (R := F) w).toAlgebra
  have hinj : Function.Injective (algebraMap (MvPolynomial σ F) K) := hw.1
  have : FaithfulSMul (MvPolynomial σ F) K := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let _ : Algebra (FractionRing (MvPolynomial σ F)) K := FractionRing.liftAlgebra _ K
  have : IsScalarTower (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) K :=
    FractionRing.isScalarTower_liftAlgebra _ K
  have : Algebra.FormallyEtale (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors _)
  have halg : Algebra.IsAlgebraic (MvPolynomial σ F) K := by
    have := hw.isAlgebraic
    refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq hw.1.aevalEquiv.toRingEquiv.toRingHom
      (RingHom.id K) hw.1.aevalEquiv.toRingEquiv.surjective Function.injective_id ?_
    apply MvPolynomial.ringHom_ext
    · intro c
      rfl
    · intro i
      rfl
  have : Algebra.IsAlgebraic (FractionRing (MvPolynomial σ F)) K :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (MvPolynomial σ F) _)
  have : CharZero (FractionRing (MvPolynomial σ F)) :=
    charZero_of_injective_algebraMap (algebraMap F (FractionRing (MvPolynomial σ F))).injective
  have : Algebra.FormallyEtale (FractionRing (MvPolynomial σ F)) K :=
    Algebra.FormallyEtale.of_isSeparable _ K
  exact Algebra.FormallyEtale.comp _ (FractionRing (MvPolynomial σ F)) K

/-- **The differentials `dw_j` form a basis of `Ω_{K/F}`.** -/
def kaehlerBasisOfIsTranscendenceBasis (hw : IsTranscendenceBasis F w) :
    Module.Basis σ K Ω[K⁄F] :=
  letI := (MvPolynomial.aeval (R := F) w).toAlgebra
  haveI : IsScalarTower F (MvPolynomial σ F) K :=
    IsScalarTower.of_algebraMap_eq fun c => ((MvPolynomial.aeval w).commutes c).symm
  haveI := formallyEtale_aeval_of_isTranscendenceBasis hw
  (KaehlerDifferential.isBaseChange_of_formallyEtale F (MvPolynomial σ F) K).basis
    (KaehlerDifferential.mvPolynomialBasis F σ)

theorem kaehlerBasisOfIsTranscendenceBasis_apply (hw : IsTranscendenceBasis F w) (i : σ) :
    kaehlerBasisOfIsTranscendenceBasis hw i = KaehlerDifferential.D F K (w i) := by
  let _ := (MvPolynomial.aeval (R := F) w).toAlgebra
  have : IsScalarTower F (MvPolynomial σ F) K :=
    IsScalarTower.of_algebraMap_eq fun c => ((MvPolynomial.aeval w).commutes c).symm
  have := formallyEtale_aeval_of_isTranscendenceBasis hw
  rw [kaehlerBasisOfIsTranscendenceBasis, IsBaseChange.basis_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
  congr 1
  exact MvPolynomial.aeval_X w i

/-- **The partial derivative `∂_j = ∂/∂w_j`**: the `F`-derivation of `K` with
`∂_j w_i = δ_{ij}`. -/
def partialDeriv (hw : IsTranscendenceBasis F w) (j : σ) : Derivation F K K :=
  ((kaehlerBasisOfIsTranscendenceBasis hw).coord j).compDer (KaehlerDifferential.D F K)

theorem partialDeriv_apply (hw : IsTranscendenceBasis F w) [DecidableEq σ] (i j : σ) :
    partialDeriv hw j (w i) = if i = j then 1 else 0 := by
  change (kaehlerBasisOfIsTranscendenceBasis hw).coord j (KaehlerDifferential.D F K (w i)) = _
  rw [← kaehlerBasisOfIsTranscendenceBasis_apply hw, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

@[simp]
theorem partialDeriv_apply_self (hw : IsTranscendenceBasis F w) (j : σ) :
    partialDeriv hw j (w j) = 1 := by
  classical
  rw [partialDeriv_apply, if_pos rfl]

theorem partialDeriv_apply_of_ne (hw : IsTranscendenceBasis F w) {i j : σ} (h : i ≠ j) :
    partialDeriv hw j (w i) = 0 := by
  classical
  rw [partialDeriv_apply, if_neg h]

/-- **Uniqueness**: an `F`-derivation of `K` vanishing on a transcendence basis is zero. -/
theorem derivation_eq_zero_of_forall (hw : IsTranscendenceBasis F w) (D : Derivation F K K)
    (hD : ∀ i, D (w i) = 0) : D = 0 := by
  have h : D.liftKaehlerDifferential = 0 := by
    refine (kaehlerBasisOfIsTranscendenceBasis hw).ext fun i => ?_
    rw [kaehlerBasisOfIsTranscendenceBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
      hD i, LinearMap.zero_apply]
  ext x
  rw [← Derivation.liftKaehlerDifferential_comp_D, h, LinearMap.zero_apply, Derivation.zero_apply]

omit [CharZero F] in
theorem sum_smul_derivation_apply {ι : Type*} (s : Finset ι) (c : ι → K)
    (D : ι → Derivation F K K) (x : K) : (∑ j ∈ s, c j • D j) x = ∑ j ∈ s, c j * D j x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Every `F`-derivation of `K` is `∑_j D(w_j) ∂_j`. -/
theorem derivation_eq_sum [Fintype σ] (hw : IsTranscendenceBasis F w) (D : Derivation F K K) :
    D = ∑ j, D (w j) • partialDeriv hw j := by
  classical
  rw [← sub_eq_zero]
  refine derivation_eq_zero_of_forall hw _ fun i => ?_
  rw [Derivation.coe_sub, Pi.sub_apply, sum_smul_derivation_apply]
  simp only [partialDeriv_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, sub_self]

end PartialDeriv

/-! ### The Jacobian -/

section Jacobian

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The constants of an `F`-derivation of `K` form an intermediate field. -/
def derivationConstants (D : Derivation F K K) : IntermediateField F K :=
  Subalgebra.toIntermediateField
    { carrier := {x | D x = 0}
      mul_mem' := fun {a b} (ha : D a = 0) (hb : D b = 0) => by
        change D (a * b) = 0
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      add_mem' := fun {a b} (ha : D a = 0) (hb : D b = 0) => by
        change D (a + b) = 0
        rw [map_add, ha, hb, add_zero]
      algebraMap_mem' := fun c => D.map_algebraMap c }
    fun x (hx : D x = 0) => by
      change D x⁻¹ = 0
      rw [Derivation.leibniz_inv, hx, smul_zero]

/-- An `F`-derivation of `K` vanishing on generators of `K/F` is zero. -/
theorem derivation_eq_zero_of_adjoin_eq_top {ι : Type*} {z : ι → K}
    (hz : IntermediateField.adjoin F (Set.range z) = ⊤) (D : Derivation F K K)
    (hD : ∀ i, D (z i) = 0) : D = 0 := by
  have hle : IntermediateField.adjoin F (Set.range z) ≤ derivationConstants D := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hD i
  ext x
  rw [hz] at hle
  exact hle (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField F K))

variable [CharZero F] {σ : Type*} [Fintype σ] [DecidableEq σ] {w : σ → K}

/-- The Jacobian `det(∂_j z_i)` of a family `z` with respect to a transcendence basis `w`. -/
def jacobian (hw : IsTranscendenceBasis F w) (z : σ → K) : K :=
  (Matrix.of fun i j => partialDeriv hw j (z i)).det

/-- **The Jacobian of generators is nonzero**: if `F(z) = K`, then `det(∂_j z_i) ≠ 0`. -/
theorem jacobian_ne_zero (hw : IsTranscendenceBasis F w) {z : σ → K}
    (hz : IntermediateField.adjoin F (Set.range z) = ⊤) : jacobian hw z ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2
    (show (Matrix.of fun i j => partialDeriv hw j (z i)).det = 0 from h)
  have hD : ∑ j, c j • partialDeriv hw j = 0 := by
    refine derivation_eq_zero_of_adjoin_eq_top hz _ fun i => ?_
    rw [sum_smul_derivation_apply]
    have := congr_fun hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  apply hc0
  funext k
  have := congrArg (fun D : Derivation F K K => D (w k)) hD
  simp only [sum_smul_derivation_apply, partialDeriv_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Derivation.zero_apply] at this
  exact this

end Jacobian

/-! ### Derivations preserve `V` -/

section Preserve

variable {F L K : Type*} [CommRing F] [Field L] [Field K] [Algebra F K] [Algebra L K]
variable (V : Subalgebra L K) (D : Derivation F K K) (hL : ∀ ℓ : L, D (algebraMap L K ℓ) ∈ V)

/-- The elements `x ∈ V` with `D x ∈ V`, an `L`-subalgebra of `K` when `D(L) ⊆ V`. -/
def derivationStable : Subalgebra L K where
  carrier := {x | x ∈ V ∧ D x ∈ V}
  mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact V.add_mem (V.mul_mem ha.1 hb.2) (V.mul_mem hb.1 ha.2)⟩
  add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, by
    rw [map_add]
    exact V.add_mem ha.2 hb.2⟩
  algebraMap_mem' ℓ := ⟨V.algebraMap_mem ℓ, hL ℓ⟩

variable {V D hL}

theorem mem_derivationStable {x : K} : x ∈ derivationStable V D hL ↔ x ∈ V ∧ D x ∈ V :=
  Iff.rfl

/-- `x⁻¹` is stable if `x` is and `x⁻¹ ∈ V`. -/
theorem inv_mem_derivationStable {x : K} (hx : x ∈ derivationStable V D hL) (hxinv : x⁻¹ ∈ V) :
    x⁻¹ ∈ derivationStable V D hL := by
  refine ⟨hxinv, ?_⟩
  rw [Derivation.leibniz_inv, smul_eq_mul]
  exact V.mul_mem (V.neg_mem (V.pow_mem hxinv 2)) hx.2

/-- The inverse in `K` of a unit of `V` lies in `V`. -/
theorem inv_mem_of_isUnit {v : V} (hv : IsUnit v) : (v : K)⁻¹ ∈ V := by
  obtain ⟨w, rfl⟩ := hv
  rw [← coe_inv_unit]
  exact ((w⁻¹ : Vˣ) : V).2

variable (π : V) [hπ : Fact (Irreducible π)] [IsDiscreteValuationRing V]

include hL in
/-- `D(A) ⊆ V` if `D(L) ⊆ V` and `D π ∈ V`, for `A = L[π]_{(π)}`. -/
theorem curveDVR_le_derivationStable (hDπ : D π ∈ V) :
    curveDVR V π ≤ derivationStable V D hL := by
  intro a ha
  obtain ⟨Q, S, hS, rfl⟩ := (mem_curveDVR_iff V π).1 ha
  have hπS : (π : K) ∈ derivationStable V D hL := ⟨π.2, hDπ⟩
  have haeval : ∀ P : L[X], aeval (π : K) P ∈ derivationStable V D hL := fun P =>
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hπS)) (Polynomial.aeval_mem_adjoin_singleton L _)
  have hSunit : IsUnit (aeval π S) :=
    isUnit_aeval_of_mem_maximalIdeal (pi_mem_maximalIdeal V π) hS
  have hinv : (aeval (π : K) S)⁻¹ ∈ V := by
    have := inv_mem_of_isUnit hSunit
    rwa [coe_aeval_pi] at this
  rw [div_eq_mul_inv]
  exact Subalgebra.mul_mem _ (haeval Q) (inv_mem_derivationStable (haeval S) hinv)

omit hπ [IsDiscreteValuationRing V] in
/-- `P(x)` is stable for `P ∈ A[T]` and `x` stable, if `A` is stable. -/
theorem aeval_mem_derivationStable (hA : curveDVR V π ≤ derivationStable V D hL)
    {x : K} (hx : x ∈ derivationStable V D hL) (P : (curveDVR V π)[X]) :
    aeval x P ∈ derivationStable V D hL := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subalgebra.mul_mem _ (hA (P.coeff i).2) (Subalgebra.pow_mem _ hx i)

omit [IsDiscreteValuationRing V] in
theorem polynomialModule_eval_mapCoeffs_mem (P : K[X]) {x : K} (hx : x ∈ V)
    (hP : ∀ i, D (P.coeff i) ∈ V) : PolynomialModule.eval x (D.mapCoeffs P) ∈ V := by
  change ((D.mapCoeffs P).coeff.sum fun i m => x ^ i • m) ∈ V
  refine Subalgebra.sum_mem _ fun i _ => ?_
  dsimp only
  rw [smul_eq_mul]
  exact V.mul_mem (V.pow_mem hx i) (hP i)

include hL in
/-- **Derivations preserve `V`** (`lem:c0-dvr-jacobian`, `∂_j(V) ⊆ V`). Let `θ` be a primitive
coordinate (`lem:c0-dvr-primitive`). A derivation `D` of `K` with `D(L) ⊆ V` and `D π ∈ V` maps
`V` into `V`: it preserves `A = L[π]_{(π)}`, `D θ = -F_θ^D(θ)/F_θ'(θ) ∈ V` because `F_θ'(θ)` is a
unit of `V`, and `V = A[θ]_{𝔫'}`. -/
theorem derivation_mem_of_isPrimitiveCoordinate (hDπ : D π ∈ V) {θ : V}
    (hθ : IsPrimitiveCoordinate V π θ) {x : K} (hx : x ∈ V) : D x ∈ V := by
  have hA := curveDVR_le_derivationStable (hL := hL) π hDπ
  -- `D θ ∈ V`
  have hθS : (θ : K) ∈ derivationStable V D hL := by
    refine ⟨θ.2, ?_⟩
    set P := (minpoly (curveDVR V π) (θ : K)).map (algebraMap (curveDVR V π) K)
    have hP0 : eval (θ : K) P = 0 := by
      rw [eval_map_algebraMap, minpoly.aeval]
    have h := Derivation.apply_eval_eq D (θ : K) P
    rw [hP0, map_zero] at h
    have hder : eval (θ : K) (derivative P) =
        ((aeval θ (derivative (minpoly (curveDVR V π) (θ : K))) : V) : K) := by
      rw [coe_aeval_curveDVR_V, ← eval_map_algebraMap, derivative_map]
    rw [hder, smul_eq_mul] at h
    have hu := hθ.isUnit_aeval_derivative
    have hc0 : ((aeval θ (derivative (minpoly (curveDVR V π) (θ : K))) : V) : K) ≠ 0 := by
      intro h0
      exact hu.ne_zero (Subtype.ext h0)
    set c := ((aeval θ (derivative (minpoly (curveDVR V π) (θ : K))) : V) : K)
    set E := PolynomialModule.eval (θ : K) (D.mapCoeffs P)
    have h' : c * D θ = -E := by linear_combination -h
    have hDθ : D θ = -c⁻¹ * E := by
      calc D θ = c⁻¹ * (c * D θ) := by rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
        _ = -c⁻¹ * E := by rw [h']; ring
    rw [hDθ]
    refine V.mul_mem (V.neg_mem (inv_mem_of_isUnit hu))
      (polynomialModule_eval_mapCoeffs_mem P θ.2 fun i => ?_)
    rw [coeff_map]
    exact (hA (((minpoly (curveDVR V π) (θ : K)).coeff i).2)).2
  -- `V = A[θ]_{𝔫'}`
  obtain ⟨P, S, hS, hPS⟩ := hθ.exists_mul_eq_aeval ⟨x, hx⟩
  have hSK : ((aeval θ S : V) : K) ≠ 0 := fun h0 => hS.ne_zero (Subtype.ext h0)
  have hxeq : x = ((aeval θ P : V) : K) * ((aeval θ S : V) : K)⁻¹ := by
    have := congrArg Subtype.val hPS
    simp only [Subalgebra.coe_mul] at this
    rw [← this, mul_inv_cancel_right₀ hSK]
  have hPS' : ∀ Q : (curveDVR V π)[X], ((aeval θ Q : V) : K) ∈ derivationStable V D hL := by
    intro Q
    rw [coe_aeval_curveDVR_V]
    exact aeval_mem_derivationStable π hA hθS Q
  rw [hxeq]
  exact (Subalgebra.mul_mem _ (hPS' P) (inv_mem_derivationStable (hPS' S)
    (inv_mem_of_isUnit hS))).2

end Preserve

/-! ### Derivations of a subfield generated by a set -/

section Adjoin

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- If a derivation maps a set `s` into `F(s)`, it maps `F(s)` into itself. -/
theorem derivation_mem_adjoin (D : Derivation F K K) {s : Set K}
    (hs : ∀ x ∈ s, D x ∈ IntermediateField.adjoin F s) {x : K}
    (hx : x ∈ IntermediateField.adjoin F s) : D x ∈ IntermediateField.adjoin F s := by
  set E := IntermediateField.adjoin F s
  let T : IntermediateField F K := Subalgebra.toIntermediateField
    { carrier := {y | y ∈ E ∧ D y ∈ E}
      mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact E.add_mem (E.mul_mem ha.1 hb.2) (E.mul_mem hb.1 ha.2)⟩
      add_mem' := fun {a b} ha hb => ⟨E.add_mem ha.1 hb.1, by
        rw [map_add]
        exact E.add_mem ha.2 hb.2⟩
      algebraMap_mem' := fun c => ⟨E.algebraMap_mem c, by
        rw [D.map_algebraMap]
        exact E.zero_mem⟩ }
    fun y hy => ⟨E.inv_mem hy.1, by
      rw [Derivation.leibniz_inv, smul_eq_mul]
      exact E.mul_mem (E.neg_mem (pow_mem (E.inv_mem hy.1) 2)) hy.2⟩
  have hle : E ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    exact ⟨IntermediateField.subset_adjoin F s hy, hs y hy⟩
  exact (hle hx).2

end Adjoin

/-! ### Coordinates at a divisor (`lem:c0-dvr-jacobian`) -/

section Coordinates

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [CharZero F]
variable (V : Subalgebra F K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType F V]
variable {V} {ι : Type*} (π : V) (u : ι → V)

/-- The coordinates `w = (π, u)` at a divisor: `w none = π`, `w (some i) = uᵢ`. -/
def dvrCoordinates : Option ι → K :=
  fun o => Option.elim o (π : K) fun i => (u i : K)

omit [CharZero F] [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType F V] in
@[simp]
theorem dvrCoordinates_none : dvrCoordinates π u none = π :=
  rfl

omit [CharZero F] [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType F V] in
@[simp]
theorem dvrCoordinates_some (i : ι) : dvrCoordinates π u (some i) = u i :=
  rfl

variable {π u}

omit [CharZero F] in
/-- **`(π, u)` is a transcendence basis of `K/F`** if `π` is a uniformizer and the residues of
`u` form a transcendence basis of `κ_V`. -/
theorem isTranscendenceBasis_dvrCoordinates [Finite ι] (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) :
    IsTranscendenceBasis F (dvrCoordinates π u) := by
  set E := IntermediateField.adjoin F (Set.range fun i => (u i : K))
  have hEV : E.toSubalgebra ≤ V := adjoin_le_of_algebraicIndependent_residue hu.1
  -- `π` is transcendental over `F(u)`
  have hπ' : Irreducible (extendScalarsOfLEEquiv V E hEV π) :=
    (MulEquiv.irreducible_iff (extendScalarsOfLEEquiv V E hEV).toMulEquiv).2 hπ
  have htr : Transcendental E (π : K) :=
    transcendental_of_irreducible (extendScalarsOfLE V E hEV) hπ'
  rw [IntermediateField.transcendental_adjoin_iff] at htr
  have hind : AlgebraicIndependent F (dvrCoordinates π u) :=
    AlgebraicIndependent.option_iff.2 ⟨algebraicIndependent_coe_of_residue hu.1, htr⟩
  refine hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite ?_
  rw [← trdeg_residueField_add_one V, Cardinal.lift_add, ← hu.lift_cardinalMk_eq_trdeg,
    Cardinal.mk_option, Cardinal.lift_add, Cardinal.lift_one, Cardinal.lift_one]

omit [CharZero F] [IsFractionRing V K] [Algebra.EssFiniteType F V] in
/-- `L = F(u)` is contained in `V`. -/
theorem adjoin_le_dvr (hu : IsTranscendenceBasis F (residue V ∘ u)) :
    (IntermediateField.adjoin F (Set.range fun i => (u i : K))).toSubalgebra ≤ V :=
  adjoin_le_of_algebraicIndependent_residue hu.1

/-- **The partial derivatives preserve `V`** (`lem:c0-dvr-jacobian`): `∂_j(V) ⊆ V` for the
derivations `∂_j = ∂/∂w_j` attached to the coordinates `w = (π, u)`. -/
theorem partialDeriv_mem [Finite ι] (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) (j : Option ι) {x : K} (hx : x ∈ V) :
    partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) j x ∈ V := by
  classical
  set hw := isTranscendenceBasis_dvrCoordinates hπ hu
  set D := partialDeriv hw j
  set E := IntermediateField.adjoin F (Set.range fun i => (u i : K))
  have hEV : E.toSubalgebra ≤ V := adjoin_le_dvr hu
  set V' := extendScalarsOfLE V E hEV
  set π' := extendScalarsOfLEEquiv V E hEV π
  have : Fact (Irreducible π') :=
    ⟨(MulEquiv.irreducible_iff (extendScalarsOfLEEquiv V E hEV).toMulEquiv).2 hπ⟩
  have : Algebra.IsAlgebraic E (ResidueField V') := isAlgebraic_residueField_extendScalarsOfLE V hu
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨θ, hθ⟩ := exists_isPrimitiveCoordinate V' π'
  -- `D` maps the coordinates into `{0, 1}`
  have hDw : ∀ o, D (dvrCoordinates π u o) ∈ V := by
    intro o
    rw [partialDeriv_apply]
    split_ifs
    · exact V.one_mem
    · exact V.zero_mem
  -- `D(L) ⊆ L ⊆ V`
  have hL : ∀ ℓ : E, D (algebraMap E K ℓ) ∈ V' := by
    intro ℓ
    have hmem : D ℓ ∈ E := by
      refine derivation_mem_adjoin D ?_ ℓ.2
      rintro _ ⟨i, rfl⟩
      have h := partialDeriv_apply hw (some i) j
      simp only [dvrCoordinates_some] at h
      change D (u i : K) ∈ E
      rw [h]
      split_ifs
      · exact E.one_mem
      · exact E.zero_mem
    exact hEV hmem
  exact derivation_mem_of_isPrimitiveCoordinate (V := V') (hL := hL) π' (hDw none) hθ hx

/-- The Jacobian `det(∂_j z_i)` lies in `V` if the `z_i` do. -/
theorem jacobian_mem [Fintype ι] [DecidableEq ι] (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) {z : Option ι → K} (hz : ∀ i, z i ∈ V) :
    jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) z ∈ V := by
  let M : Matrix (Option ι) (Option ι) V := fun i j =>
    ⟨partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) j (z i),
      partialDeriv_mem hπ hu j (hz i)⟩
  have h := RingHom.map_det (V.val : V →+* K) M
  rw [jacobian]
  convert (M.det).2 using 1
  exact h.symm

/-- **The log discrepancy** `A(V) = 1 + ord_V(Jac_V)` of `V` with respect to `z`, for the
coordinates `(π, u)` (`lem:c0-dvr-jacobian`). -/
def logDiscrepancy [Fintype ι] [DecidableEq ι] (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) {z : Option ι → K} (hz : ∀ i, z i ∈ V) : ℕ∞ :=
  1 + IsDiscreteValuationRing.addVal V
    ⟨jacobian (isTranscendenceBasis_dvrCoordinates hπ hu) z, jacobian_mem hπ hu hz⟩

/-- `A(V)` is finite when `F(z) = K`. -/
theorem logDiscrepancy_ne_top [Fintype ι] [DecidableEq ι] (hπ : Irreducible π)
    (hu : IsTranscendenceBasis F (residue V ∘ u)) {z : Option ι → K} (hz : ∀ i, z i ∈ V)
    (hzK : IntermediateField.adjoin F (Set.range z) = ⊤) :
    logDiscrepancy hπ hu hz ≠ ⊤ := by
  rw [logDiscrepancy, ne_eq, ENat.add_eq_top, not_or]
  refine ⟨ENat.one_ne_top, ?_⟩
  rw [IsDiscreteValuationRing.addVal_eq_top_iff]
  intro h
  exact jacobian_ne_zero _ hzK (congrArg Subtype.val h)

end Coordinates

/-! ### Divisorial valuation rings in `N` variables -/

section BirationalDVR

variable {F : Type*} [Field F]

/-- The function field of a `BirationalDVR` is its fraction field. -/
instance BirationalDVR.isFractionRing_ring {B : Type*} [CommRing B] [IsDomain B] [Algebra F B]
    (V : BirationalDVR F B) : IsFractionRing V.ring (FractionRing B) :=
  V.isFractionRing

/-- The variables generate the rational function field `F(z₁, …, z_N)`. -/
theorem adjoin_range_algebraMap_X_eq_top (σ : Type*) :
    IntermediateField.adjoin F (Set.range fun i : σ =>
      algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) (MvPolynomial.X i)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ F) x
  have h : ∀ p : MvPolynomial σ F, algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) p =
      MvPolynomial.aeval (fun i : σ =>
        algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) (MvPolynomial.X i)) p := by
    intro p
    have := MvPolynomial.algHom_ext
      (f := IsScalarTower.toAlgHom F (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)))
      (g := MvPolynomial.aeval fun i : σ =>
        algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) (MvPolynomial.X i))
      (fun i => by simp)
    exact DFunLike.congr_fun this p
  rw [IntermediateField.mem_adjoin_range_iff]
  exact ⟨a, b, by rw [h, h]⟩

variable [CharZero F] {N : ℕ} (V : BirationalDVR F (MvPolynomial (Fin N) F))

omit [CharZero F] in
/-- Coordinates at a divisorial valuation ring: lifts `u₂, …, u_N` of a transcendence basis of
`κ_V`, a uniformizer `π`, and an indexing `Option (Fin (N - 1)) ≃ Fin N` of `(π, u)`. -/
theorem BirationalDVR.exists_dvrCoordinates :
    ∃ (π : V.ring) (u : Fin (N - 1) → V.ring) (_ : Option (Fin (N - 1)) ≃ Fin N),
      Irreducible π ∧ IsTranscendenceBasis F (residue V.ring ∘ u) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V.ring
  obtain ⟨u, hu⟩ := Char0.BirationalDVR.exists_lift_isTranscendenceBasis V
  have hN := (Char0.BirationalDVR.trdeg_residueField V).1
  exact ⟨π, u, (finSuccEquiv (N - 1)).symm.trans (finCongr (Nat.sub_add_cancel hN)), hπ, hu⟩

/-- **The Jacobian at a divisorial valuation ring** (`lem:c0-dvr-jacobian`). For coordinates
`w = (π, u)` indexed by `e : Option ι ≃ Fin N`, the Jacobian `Jac_V = det(∂_j z_{e i})` of the
variables `z` lies in `V` and is nonzero. -/
theorem BirationalDVR.jacobian_mem_and_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : V.ring} (hπ : Irreducible π) {u : ι → V.ring}
    (hu : IsTranscendenceBasis F (residue V.ring ∘ u)) (e : Option ι ≃ Fin N) :
    jacobian (isTranscendenceBasis_dvrCoordinates hπ hu)
        (fun o => algebraMap (MvPolynomial (Fin N) F) (FractionRing (MvPolynomial (Fin N) F))
          (MvPolynomial.X (e o)))
          ∈ V.ring ∧
      jacobian (isTranscendenceBasis_dvrCoordinates hπ hu)
        (fun o => algebraMap (MvPolynomial (Fin N) F) (FractionRing (MvPolynomial (Fin N) F))
          (MvPolynomial.X (e o)))
          ≠ 0 := by
  refine ⟨jacobian_mem hπ hu fun o => V.algebraMap_mem _, jacobian_ne_zero _ ?_⟩
  have h := adjoin_range_algebraMap_X_eq_top (F := F) (Fin N)
  convert h using 2
  ext x
  constructor
  · rintro ⟨o, rfl⟩
    exact ⟨e o, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

/-- The log discrepancy `A(V) = 1 + ord_V(Jac_V)` is finite. -/
theorem BirationalDVR.logDiscrepancy_ne_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : V.ring} (hπ : Irreducible π) {u : ι → V.ring}
    (hu : IsTranscendenceBasis F (residue V.ring ∘ u)) (e : Option ι ≃ Fin N) :
    logDiscrepancy hπ hu (z := fun o =>
      algebraMap (MvPolynomial (Fin N) F) (FractionRing (MvPolynomial (Fin N) F))
          (MvPolynomial.X (e o)))
        (fun _ => V.algebraMap_mem _) ≠ ⊤ := by
  rw [logDiscrepancy, ne_eq, ENat.add_eq_top, not_or]
  refine ⟨ENat.one_ne_top, ?_⟩
  rw [IsDiscreteValuationRing.addVal_eq_top_iff]
  intro h
  exact (Char0.BirationalDVR.jacobian_mem_and_ne_zero V hπ hu e).2 (congrArg Subtype.val h)

end BirationalDVR

end EnvelopeProperty.Char0
