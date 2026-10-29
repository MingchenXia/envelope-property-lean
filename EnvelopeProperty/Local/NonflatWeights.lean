/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.NonflatGoodLocus
import EnvelopeProperty.Local.NonflatLineFibres
import EnvelopeProperty.Local.FiniteFlatNorm
import EnvelopeProperty.Local.ProjectionStep

/-!
# The weights of a generically étale finite cover

This file formalizes `def:nf-weights` and `lem:nf-weights-basic` of the blueprint chapter
`nonflat-route.tex` (the nonflat route to Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Proposition 5.22, `prop:nonflat-norm`; Section 5,
`sec:normal-local-regularization`; the proof), and packages
the data that the proof of `prop:nf-nonflat-norm` needs from them.

## Setting

`π = Spec φ: Y = Spec A → S = Spec B` is finite, `h ∈ B` a good locus element
(`IsNonflatGoodLocus`, `lem:nf-good-locus`), `S_0 = S_h`. For `s ∈ S^an` a rigid datum is an
isometric `k`-embedding `τ: ℋ(s) → F` into an algebraically closed field (`NonflatRigidEmbedding`);
it gives the `F`-point `ξ = τ.baseEval` of `B_F = F ⊗_k B` and the rigid fibre
`π_F^{-1}(ξ) = τ.fibre φ ⊆ (Spec A_F)^an`, `A_F = F ⊗_k A`, whose points are `F`-points
(`τ.fibreEval`). The canonical rigid datum is `nonflatRigidEmbedding s` into
`nonflatRigidField s` (complete, algebraically closed, nontrivially valued).

## Main definitions (`def:nf-weights`)

* `nonflatBaseCharpoly F φ b ∈ B_F[X]`: the characteristic polynomial `χ_b` of `b ∈ A_F` over
  `B_F` (`nonflatCharpoly`).
* `NonflatRigidEmbedding.rigidMult τ φ hφ b z`: for `z ∈ π_F^{-1}(ξ)`, the multiplicity `M_z` of the
  value `b(z)` as a root of `χ_b(ξ) ∈ F[X]`.
* `NonflatRigidEmbedding.rigidWeight τ φ hφ b y = ∑_{z ∈ π_F^{-1}(ξ), r(z) = y} M_z`, where
  `r(z) = z|_A`.
* `nonflatSeparating φ hφ s`: a separating element `b_s` for the canonical rigid datum
  (`lem:nf-rigid-fibre` (4), chosen).
* `nonflatWeight φ hφ h y`: the weight `m_y(π)`; for `s = π(y) ∈ S_0^an` the multiplicity
  `Berk.flatFibreMult` of `y` (the multiplicity of `lem:finite-etale-norm` and of
  `conv:nf-setting`: the dimension of the local factor of the fibre algebra), and for
  `s ∉ S_0^an` the rigid weight for the canonical rigid datum and `b_s`.
* `nonflatNorm φ hφ h u s = ∑_{π(y) = s} m_y(π) u(y)`.

## Main results

* Without lines: `NonflatRigidEmbedding.one_le_rigidMult` (`M_z ≥ 1`: Cayley–Hamilton
  `χ_b(b) = 0` evaluated at the `F`-point `z`), `NonflatRigidEmbedding.one_le_rigidWeight`
  (`m_y ≥ 1`, from the surjectivity of `r: π_F^{-1}(ξ) → π^{-1}(s)`, `lem:nf-rigid-fibre` (3)),
  `NonflatRigidEmbedding.sum_rigidWeight` (`∑_{π(y) = s} m_y = ∑_z M_z`).
* On a line through the rigid point, in the coordinates `B_F ≅ F[x]_{h_S}` of
  `Local/NonflatGoodLocus` (`nonflatCoordMap`, `nonflatLinePoint`):
  `NonflatRigidEmbedding.comap_line_nonflatEvalPoint` and `comap_coordMap_eq_iff` (the rigid fibre
  is the fibre of `φ_F` over `ξ_B = ι^* ξ`), `map_coordCharpoly_eq` (`χ_b` over `F[x]_{h_S}` at
  `ξ₀ = ev₀ ∘ ι` is `χ_b(ξ)`), `NonflatRigidEmbedding.lineWeights` (**`lem:nf-line-weights`**:
  `∑_z M_z = d` and `N_q (U ∘ p)(ξ) = ∑_z M_z U(z)`, from `AffineLine.nonflatLine_lineWeights`) and `flatNormFun_line_eq_sum_rigidWeight`
  (`N_q (u ∘ r ∘ p)(ξ) = ∑_{π(y) = s} m_y u(y)`, the first display of `prop:nf-identification`).
* **`lem:nf-weights-basic`**: finiteness of the fibres is `finite_preimage_comap_singleton`;
  `one_le_nonflatWeight` (`m_y(π) ≥ 1`), `sum_rigidMult_nonflatSeparating` and `sum_nonflatWeight`
  (`∑_{π(y) = s} m_y(π) = d` for every `s`).
* Packaging for `prop:nf-nonflat-norm`: `nonflatNormWeights` (the structure `NormWeights` with
  `m = nonflatWeight`, given the regularizability of the norms); `nonflatNorm_of_ne_zero`,
  `nonflatNorm_awayComap`, `IsNonflatGoodLocus.nonflatNorm_awayComap_eq_normFun` (on `S_0^an`,
  `N_π u` is the norm `flatNormFun`, resp. `normFun`, of `u|_{Y_0}` along the finite free étale
  `B_h → A_{φ(h)}`, as consumed by `IsRegularizable.flatNormFun_of_free`, resp.
  `IsRegularizable.normFun`); `nonflatNorm_of_eq_zero` (off `S_0^an`, the rigid weights);
  `nonflat_coord_flatNormFun_eq`, `nonflat_coord_flatNormFun_eq_nonflatNorm` (the passage from the
  norm along `B_F → A_F` of `lem:nf-generic-fibre` to `N_π u`).

## Comparison with the blueprint

* On `S_0^an` the weight is `Berk.flatFibreMult` (the dimension of the local factor, the
  multiplicity of `conv:nf-setting`), not `Berk.fibreMult` (the residue degree); the two agree on
  `S_0^an` (the fibre algebra is étale), and the agreement is recorded in the form needed, as an
  identity of norms with `normFun` along `B_h → A_{φ(h)}`
  (`IsNonflatGoodLocus.nonflatNorm_awayComap_eq_normFun`).
* `M_z ≥ 1` and `m_y ≥ 1` are proved without lines (Cayley–Hamilton at `z` and
  `lem:nf-rigid-fibre` (3)); only `∑_z M_z = d` goes through a line admissible for `h`, as in the
  blueprint.
* The weights are defined with the canonical rigid datum and a chosen separating element; they do
  not depend on a presentation `B ≅ k[x]_{h_S}` or on a line. The proof of `∑_z M_z = d` uses the
  presentation `B ≅ k[x_i: i ∈ ULift (Fin n)]_{h_S}` (`IsAffineSpacePrincipalOpen.exists_ulift`) and
  `B_F ≅ F[x]_{h_S}`, as the author's line API is stated for `B_F = F[x]_g`; the characteristic
  polynomial is transported along this isomorphism (`nonflatCharpoly_map_ringEquiv`). The results
  using lines need `A`, `B` (hence `F_s`) in one universe.
-/

open scoped NNReal ENNReal Topology TensorProduct
open Polynomial

noncomputable section

universe u

namespace EnvelopeProperty

open Berk

/-! ### The intrinsic weights at a rigid datum -/

section RigidWeights

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

variable (F : Type*) [Field F] [Algebra k F] in
/-- The characteristic polynomial `χ_b ∈ B_F[X]` of `b ∈ A_F = F ⊗_k A` over `B_F = F ⊗_k B`
(`def:nf-weights`, `lem:nf-charpoly`), `A_F` being a `B_F`-algebra through `F ⊗ φ`. -/
def nonflatBaseCharpoly (φ : B →ₐ[k] A) (b : F ⊗[k] A) : (F ⊗[k] B)[X] :=
  letI := (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom.toAlgebra
  nonflatCharpoly (F ⊗[k] B) (F ⊗[k] A) b

namespace NonflatRigidEmbedding

variable {s : Berk k B} {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
  [IsAlgClosed F] (τ : NonflatRigidEmbedding s F) (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite)

open Classical in
/-- **The multiplicity `M_z`** (`def:nf-weights`): for `z ∈ π_F^{-1}(ξ)`, the multiplicity of the
value `b(z)` as a root of `χ_b(ξ) ∈ F[X]` (`ξ` applied to the coefficients of `χ_b`); `0` off the
rigid fibre. -/
def rigidMult (b : F ⊗[k] A) (z : Berk k (F ⊗[k] A)) : ℕ :=
  if hz : z ∈ τ.fibre φ then
    ((nonflatBaseCharpoly F φ b).map (τ.baseEval : F ⊗[k] B →+* F)).rootMultiplicity
      (τ.fibreEval φ hφ hz b)
  else 0

open Classical in
theorem rigidMult_of_mem (b : F ⊗[k] A) {z : Berk k (F ⊗[k] A)} (hz : z ∈ τ.fibre φ) :
    τ.rigidMult φ hφ b z =
      ((nonflatBaseCharpoly F φ b).map (τ.baseEval : F ⊗[k] B →+* F)).rootMultiplicity
        (τ.fibreEval φ hφ hz b) := by
  rw [rigidMult, dif_pos hz]

open Classical in
/-- **The rigid weight** `m_y = ∑_{z ∈ π_F^{-1}(ξ), r(z) = y} M_z` (`def:nf-weights`), with
`r(z) = z|_A` the restriction along `A → A_F`. -/
def rigidWeight (b : F ⊗[k] A) (y : Berk k A) : ℕ :=
  ∑ z ∈ (τ.finite_fibre φ hφ).toFinset with
    comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) z = y, τ.rigidMult φ hφ b z

/-- **`M_z ≥ 1`** (`lem:nf-line-weights`, without lines): `b(z)` is a root of `χ_b(ξ)`, by
Cayley–Hamilton `χ_b(b) = 0` (`lem:nf-charpoly` (2)) evaluated at the `F`-point `z` over `ξ`. -/
theorem one_le_rigidMult [IsDomain (F ⊗[k] B)] [IsIntegrallyClosed (F ⊗[k] B)]
    [IsDomain (F ⊗[k] A)] (hinj : Function.Injective φ) (b : F ⊗[k] A) {z : Berk k (F ⊗[k] A)}
    (hz : z ∈ τ.fibre φ) : 1 ≤ τ.rigidMult φ hφ b z := by
  let := (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom.toAlgebra
  have : Module.Finite (F ⊗[k] B) (F ⊗[k] A) := nonflat_baseChange_finite F φ hφ
  have : FaithfulSMul (F ⊗[k] B) (F ⊗[k] A) := (faithfulSMul_iff_algebraMap_injective _ _).2
    (Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hinj)
  rw [rigidMult_of_mem τ φ hφ b hz]
  have hne : (nonflatBaseCharpoly F φ b).map (τ.baseEval : F ⊗[k] B →+* F) ≠ 0 :=
    ((nonflatCharpoly_monic (R := F ⊗[k] B) b).map _).ne_zero
  refine (Polynomial.rootMultiplicity_pos hne).2 ?_
  have h0 := congrArg (τ.fibreEval φ hφ hz) (aeval_nonflatCharpoly (R := F ⊗[k] B) b)
  have hcomp : ((τ.fibreEval φ hφ hz : F ⊗[k] A →+* F)).comp
      (algebraMap (F ⊗[k] B) (F ⊗[k] A)) = (τ.baseEval : F ⊗[k] B →+* F) :=
    congrArg AlgHom.toRingHom (τ.fibreEval_comp φ hφ hz)
  rw [map_zero, Polynomial.aeval_def] at h0
  change (τ.fibreEval φ hφ hz : F ⊗[k] A →+* F) _ = 0 at h0
  rw [Polynomial.hom_eval₂, hcomp] at h0
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact h0

omit [IsAlgClosed F] in
/-- The restriction `r(z)` of a point of the rigid fibre is a point of `π^{-1}(s)`. -/
theorem comap_includeRight_mem_fibre {z : Berk k (F ⊗[k] A)} (hz : z ∈ τ.fibre φ) :
    comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) z ∈
      (finite_preimage_comap_singleton φ hφ s).toFinset :=
  (Set.Finite.mem_toFinset _).2 (τ.comap_comap_includeRight_of_mem_fibre φ hz)

/-- **`∑_{π(y) = s} m_y = ∑_{z ∈ π_F^{-1}(ξ)} M_z`**: the rigid weights regroup the
multiplicities `M_z` along `r`. -/
theorem sum_rigidWeight (b : F ⊗[k] A) :
    ∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset, τ.rigidWeight φ hφ b y =
      ∑ z ∈ (τ.finite_fibre φ hφ).toFinset, τ.rigidMult φ hφ b z := by
  classical
  unfold rigidWeight
  exact Finset.sum_fiberwise_of_maps_to (fun z hz =>
    τ.comap_includeRight_mem_fibre φ hφ ((Set.Finite.mem_toFinset _).1 hz)) _

/-- **`m_y ≥ 1`** for `y ∈ π^{-1}(s)` (`lem:nf-weights-basic`): by `lem:nf-rigid-fibre` (3) some
`z ∈ π_F^{-1}(ξ)` has `r(z) = y`, and `M_z ≥ 1`. -/
theorem one_le_rigidWeight [IsDomain (F ⊗[k] B)] [IsIntegrallyClosed (F ⊗[k] B)]
    [IsDomain (F ⊗[k] A)] (hinj : Function.Injective φ) (b : F ⊗[k] A) {y : Berk k A}
    (hy : comap φ y = s) : 1 ≤ τ.rigidWeight φ hφ b y := by
  classical
  obtain ⟨z, hz, hzy⟩ := τ.exists_mem_fibre_comap_includeRight_eq φ hφ hy
  unfold rigidWeight
  refine le_trans (τ.one_le_rigidMult φ hφ hinj b hz) ?_
  exact Finset.single_le_sum (f := fun z => τ.rigidMult φ hφ b z) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 hz, hzy⟩)

end NonflatRigidEmbedding

end RigidWeights

/-! ### The weights on a line through the rigid point (`lem:nf-line-weights`) -/

section Lines

open AffineLine ReducedComponents

variable {k : Type*} [Field k] {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
  [Algebra k B] {s : Berk k B} {F : Type u} [NormedField F] [IsUltrametricDist F] [Algebra k F]
  [IsAlgClosed F] (τ : NonflatRigidEmbedding s F) {σ : Type u} {hS : MvPolynomial σ k}
  (E : B ≃ₐ[k] Localization.Away hS) (φ : B →ₐ[k] A)

set_option hygiene false in
/-- `g = h_S` over `F`. -/
local notation "gF" => MvPolynomial.map (algebraMap k F) hS

set_option hygiene false in
/-- The coordinates `a ∈ F^σ` of the rigid point `ξ`. -/
local notation "aξ" => nonflatLinePoint E τ.baseEval

namespace NonflatRigidEmbedding

omit [IsAlgClosed F] in
/-- The rigid point `ξ` restricted to `B_F = F[x]_{h_S}`: the point `ξ_B = ι^* ξ` of the author's
line API (`t = 0` on the line through `a`), for every direction `w`. -/
theorem comap_line_nonflatEvalPoint (w : σ → F) :
    letI := (principalLineHom aξ w gF).toRingHom.toAlgebra
    haveI := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
    comap (IsScalarTower.toAlgHom k (Localization.Away gF) (OpenLineRing (subst aξ w gF)))
        (nonflatEvalPoint (fun _ hc => τ.norm_algebraMap hc) _
          (nonflat_eval_subst_zero_ne_zero E τ.baseEval w)) =
      comap ((nonflatBaseEquiv F E).symm.toAlgHom.restrictScalars k) τ.basePoint := by
  let := (principalLineHom aξ w gF).toRingHom.toAlgebra
  have := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
  apply Berk.ext_val
  intro r
  rw [comap_val_apply, comap_val_apply, nonflatEvalPoint_val_apply, basePoint_val_apply]
  have h := congrArg (fun f : Localization.Away gF →ₐ[F] F => f r)
    (nonflat_lineEval_comp E τ.baseEval w)
  simp only [AlgHom.comp_apply] at h
  rw [IsScalarTower.toAlgHom_apply]
  exact congrArg _ h

omit [IsAlgClosed F] in
/-- **The rigid fibre in coordinates**: a point `z` of `(Spec A_F)^an` lies over `ξ_B` along
`φ_F : F[x]_{h_S} → A_F` if and only if it lies in `π_F^{-1}(ξ)`. -/
theorem comap_coordMap_eq_iff (w : σ → F) (z : Berk k (F ⊗[k] A)) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    letI := (principalLineHom aξ w gF).toRingHom.toAlgebra
    haveI := nonflatLine_isScalarTower_k_base (k := k) gF (nonflatCoordMap F E φ)
    haveI := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
    comap (IsScalarTower.toAlgHom k (Localization.Away gF) (F ⊗[k] A)) z =
        comap (IsScalarTower.toAlgHom k (Localization.Away gF) (OpenLineRing (subst aξ w gF)))
          (nonflatEvalPoint (fun _ hc => τ.norm_algebraMap hc) _
            (nonflat_eval_subst_zero_ne_zero E τ.baseEval w)) ↔
      z ∈ τ.fibre φ := by
  let := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  let := (principalLineHom aξ w gF).toRingHom.toAlgebra
  have := nonflatLine_isScalarTower_k_base (k := k) gF (nonflatCoordMap F E φ)
  have := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
  rw [τ.comap_line_nonflatEvalPoint E w, mem_fibre_iff]
  have hz : comap (IsScalarTower.toAlgHom k (Localization.Away gF) (F ⊗[k] A)) z =
      comap ((nonflatBaseEquiv F E).symm.toAlgHom.restrictScalars k)
        (comap ((Algebra.TensorProduct.map (AlgHom.id F F) φ).restrictScalars k) z) :=
    Berk.ext_val fun r => rfl
  rw [hz]
  constructor
  · intro h
    apply Berk.ext_val
    intro q
    have := congrArg (fun x : Berk k (Localization.Away gF) => x.val (nonflatBaseEquiv F E q)) h
    simpa using this
  · intro h
    rw [h]

omit [IsUltrametricDist F] [IsAlgClosed F] in
/-- **`χ_b(ξ)` in coordinates**: the characteristic polynomial of `b` over `B_F = F[x]_{h_S}`
(through `φ_F`), with the line evaluation `ξ₀ = ev₀ ∘ ι` applied to its coefficients, is `χ_b(ξ)`
(the characteristic polynomial over `F ⊗_k B`, `ξ` applied). -/
theorem map_coordCharpoly_eq [IsAlgClosed k] [IsDomain A] (hS0 : hS ≠ 0)
    (hφ : (φ : B →+* A).Finite) (hinj : Function.Injective φ) (w : σ → F) (b : F ⊗[k] A) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    (nonflatCharpoly (Localization.Away gF) (F ⊗[k] A) b).map
        (((openLineEval (subst aξ w gF) 0 (nonflat_eval_subst_zero_ne_zero E τ.baseEval w) :
          OpenLineRing (subst aξ w gF) →+* F)).comp
          (principalLineHom aξ w gF : Localization.Away gF →+* OpenLineRing (subst aξ w gF))) =
      (nonflatBaseCharpoly F φ b).map (τ.baseEval : F ⊗[k] B →+* F) := by
  let := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  let := (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom.toAlgebra
  have := nonflat_isDomain_localizationAway_map (F := F) hS0
  have := nonflat_isIntegrallyClosed_localizationAway_map (F := F) hS0
  have : IsDomain (F ⊗[k] B) := Function.Injective.isDomain (nonflatBaseEquiv F E).toRingEquiv
    (nonflatBaseEquiv F E).toRingEquiv.injective
  have : IsDomain (F ⊗[k] A) := tensorProduct_isDomain_of_algClosed k F A
  have : Module.Finite (F ⊗[k] B) (F ⊗[k] A) := nonflat_baseChange_finite F φ hφ
  have : FaithfulSMul (Localization.Away gF) (F ⊗[k] A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (nonflatCoordMap_injective F E φ hinj)
  have htr := nonflatCharpoly_map_ringEquiv (R := F ⊗[k] B) (R' := Localization.Away gF)
    (T := F ⊗[k] A) (nonflatBaseEquiv F E).toRingEquiv
    (fun r => nonflatCoordMap_nonflatBaseEquiv F E φ r) b
  have hcomp : (((openLineEval (subst aξ w gF) 0 (nonflat_eval_subst_zero_ne_zero E τ.baseEval w) :
        OpenLineRing (subst aξ w gF) →+* F)).comp
        (principalLineHom aξ w gF : Localization.Away gF →+* OpenLineRing (subst aξ w gF))).comp
        ((nonflatBaseEquiv F E).toRingEquiv : F ⊗[k] B →+* Localization.Away gF) =
      (τ.baseEval : F ⊗[k] B →+* F) := RingHom.ext fun r => by
    have h := congrArg (fun f : Localization.Away gF →ₐ[F] F => f (nonflatBaseEquiv F E r))
      (nonflat_lineEval_comp E τ.baseEval w)
    simpa using h
  rw [← htr, Polynomial.map_map, hcomp]
  rfl

/-- **Line multiplicities are the weights** (`lem:nf-line-weights`, for a rigid datum). Let `h` be a
good locus element, `ξ` the rigid point of `τ` with coordinates `a = nonflatLinePoint E ξ`, `w` a
direction admissible for `h` (`ι(h_F) ≠ 0`), `Q = F[t]_p`, `q: Spec R' → Spec Q` the normalized
curve of the line (`R' = NormalizationProduct (linePreimageIdeal a w j g φ_F)`, with
`p: (Spec R')^an → (Spec A_F)^an` the restriction `ρ^an`), and `b ∈ A_F` an element with pairwise
distinct values on `π_F^{-1}(ξ)`. Then
1. `∑_{z ∈ π_F^{-1}(ξ)} M_z = d`;
2. `N_q (U ∘ p)(ξ) = ∑_{z ∈ π_F^{-1}(ξ)} M_z U(z)` for every function `U` on `(Spec A_F)^an`.
This is `AffineLine.nonflatLine_lineWeights`  in the coordinates `B_F ≅ F[x]_{h_S}`. -/
theorem lineWeights [IsAlgClosed k] [IsDomain A] [IsDomain B] [Fintype σ] (hS0 : hS ≠ 0)
    (hφ : (φ : B →+* A).Finite) (hinj : Function.Injective φ) {S : Finset A} {h : B}
    (hh : IsNonflatGoodLocus φ S h) (w : σ → F) (j : σ) (hwj : w j ≠ 0)
    (hadm : principalLineHom aξ w gF (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h)) ≠ 0)
    (b : F ⊗[k] A) (hb : ∀ (z₁ : Berk k (F ⊗[k] A)) (h₁ : z₁ ∈ τ.fibre φ)
      (z₂ : Berk k (F ⊗[k] A)) (h₂ : z₂ ∈ τ.fibre φ),
      τ.fibreEval φ hφ h₁ b = τ.fibreEval φ hφ h₂ b → z₁ = z₂) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    letI := (principalLineHom aξ w gF).toRingHom.toAlgebra
    letI := (normalizedLineProductHom aξ w j gF hwj (nonflatCoordMap F E φ)).toRingHom.toAlgebra
    letI : Module.Finite (OpenLineRing (subst aξ w gF))
        (NormalizationProduct (linePreimageIdeal aξ w j gF (nonflatCoordMap F E φ))) :=
      normalizedLineProductHom_finite aξ w j gF hwj (nonflatCoordMap F E φ)
        (nonflatCoordMap_finite F E φ hφ)
    haveI := nonflatLine_isScalarTower_k_base (k := k) gF (nonflatCoordMap F E φ)
    haveI := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
    haveI := nonflatLine_isScalarTower_k_curve (k := k) aξ w j gF hwj (nonflatCoordMap F E φ)
    (∑ z ∈ (τ.finite_fibre φ hφ).toFinset, τ.rigidMult φ hφ b z = genericDegree (φ : B →+* A)) ∧
    ∀ U : Berk k (F ⊗[k] A) → EReal,
      flatNormFun (B := OpenLineRing (subst aξ w gF))
          (fun y : Berk k (NormalizationProduct (linePreimageIdeal aξ w j gF
              (nonflatCoordMap F E φ))) =>
            U (comap ((normalizationMapAlg (Localization.Away gF)
              (linePreimageIdeal aξ w j gF (nonflatCoordMap F E φ))).restrictScalars k) y))
          (nonflatEvalPoint (fun _ hc => τ.norm_algebraMap hc) _
            (nonflat_eval_subst_zero_ne_zero E τ.baseEval w)) =
        ∑ z ∈ (τ.finite_fibre φ hφ).toFinset, ((τ.rigidMult φ hφ b z : ℝ) : EReal) * U z := by
  classical
  let φF := nonflatCoordMap F E φ
  let := φF.toRingHom.toAlgebra
  let := (principalLineHom aξ w gF).toRingHom.toAlgebra
  have hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1 := fun _ hc => τ.norm_algebraMap hc
  have hp := nonflat_eval_subst_zero_ne_zero E τ.baseEval w
  have hg := nonflat_map_ne_zero F hS0
  have hφF : φF.toRingHom.Finite := nonflatCoordMap_finite F E φ hφ
  have hiφF : Function.Injective φF := nonflatCoordMap_injective F E φ hinj
  have : IsDomain (F ⊗[k] A) := tensorProduct_isDomain_of_algClosed k F A
  let : Module.Finite (Localization.Away gF) (F ⊗[k] A) := hφF
  have : IsScalarTower k (Localization.Away gF) (F ⊗[k] A) :=
    nonflatLine_isScalarTower_k_base (k := k) gF φF
  have : IsScalarTower k (Localization.Away gF) (OpenLineRing (subst aξ w gF)) :=
    nonflatLine_isScalarTower_k_line (k := k) aξ w gF
  have hfib : nonflatFibre (F ⊗[k] A) (comap (IsScalarTower.toAlgHom k (Localization.Away gF)
      (OpenLineRing (subst aξ w gF))) (nonflatEvalPoint hF _ hp)) =
      (τ.finite_fibre φ hφ).toFinset := by
    ext z
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact τ.comap_coordMap_eq_iff E φ w z
  let wv : Berk k (F ⊗[k] A) → F := fun z =>
    if hz : z ∈ τ.fibre φ then τ.fibreEval φ hφ hz b else 0
  have hwv : ∀ z (hz : z ∈ τ.fibre φ), wv z = τ.fibreEval φ hφ hz b := fun z hz => dif_pos hz
  have hw : ∀ z ∈ nonflatFibre (F ⊗[k] A) (comap (IsScalarTower.toAlgHom k (Localization.Away gF)
      (OpenLineRing (subst aξ w gF))) (nonflatEvalPoint hF _ hp)),
      z.val (b - algebraMap (Localization.Away gF) (F ⊗[k] A)
        (algebraMap F (Localization.Away gF) (wv z))) = 0 := by
    intro z hz
    rw [hfib, Set.Finite.mem_toFinset] at hz
    rw [hwv z hz]
    have : algebraMap (Localization.Away gF) (F ⊗[k] A)
        (algebraMap F (Localization.Away gF) (τ.fibreEval φ hφ hz b)) =
        algebraMap F (F ⊗[k] A) (τ.fibreEval φ hφ hz b) := φF.commutes _
    rw [this]
    exact τ.fibreEval_val_sub φ hφ hz b
  have hsep : Set.InjOn wv ↑(nonflatFibre (F ⊗[k] A) (comap (IsScalarTower.toAlgHom k
      (Localization.Away gF) (OpenLineRing (subst aξ w gF))) (nonflatEvalPoint hF _ hp))) := by
    intro z₁ h₁ z₂ h₂ he
    rw [hfib, Finset.mem_coe, Set.Finite.mem_toFinset] at h₁ h₂
    exact hb z₁ h₁ z₂ h₂ (by rw [← hwv z₁ h₁, ← hwv z₂ h₂]; exact he)
  have key := nonflatLine_lineWeights hF aξ w j gF hwj φF hg hp hφF hiφF _ hadm
    hh.coord_etale hh.coord_free b wv hw hsep
  dsimp only at key
  obtain ⟨-, -, -, -, hsum, hnorm⟩ := key
  have hM : ∀ z ∈ (τ.finite_fibre φ hφ).toFinset,
      Polynomial.rootMultiplicity (wv z) ((nonflatCharpoly (Localization.Away gF) (F ⊗[k] A) b).map
        (((openLineEval (subst aξ w gF) 0 hp : OpenLineRing (subst aξ w gF) →+* F)).comp
          (principalLineHom aξ w gF : Localization.Away gF →+* OpenLineRing (subst aξ w gF)))) =
        τ.rigidMult φ hφ b z := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    rw [τ.map_coordCharpoly_eq E φ hS0 hφ hinj w b, hwv z hz, τ.rigidMult_of_mem φ hφ b hz]
  refine ⟨?_, fun U => ?_⟩
  · rw [hfib, hh.finrank_coord hS0] at hsum
    rw [← hsum]
    exact (Finset.sum_congr rfl hM).symm
  · rw [hnorm U, hfib]
    exact Finset.sum_congr rfl fun z hz => by rw [hM z hz]

/-- **The norm at `ξ` on an admissible line in terms of the weights** (`prop:nf-identification`,
first display): `N_q (u ∘ r ∘ p)(ξ) = ∑_{z} M_z u(r(z)) = ∑_{π(y) = s} m_y u(y)` with the rigid
weights `m_y = ∑_{r(z) = y} M_z`, for every function `u` on `Y^an`. -/
theorem flatNormFun_line_eq_sum_rigidWeight [IsAlgClosed k] [IsDomain A] [IsDomain B] [Fintype σ]
    (hS0 : hS ≠ 0) (hφ : (φ : B →+* A).Finite) (hinj : Function.Injective φ) {S : Finset A}
    {h : B} (hh : IsNonflatGoodLocus φ S h) (w : σ → F) (j : σ) (hwj : w j ≠ 0)
    (hadm : principalLineHom aξ w gF (nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] h)) ≠ 0)
    (b : F ⊗[k] A) (hb : ∀ (z₁ : Berk k (F ⊗[k] A)) (h₁ : z₁ ∈ τ.fibre φ)
      (z₂ : Berk k (F ⊗[k] A)) (h₂ : z₂ ∈ τ.fibre φ),
      τ.fibreEval φ hφ h₁ b = τ.fibreEval φ hφ h₂ b → z₁ = z₂) (u : Berk k A → EReal) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    letI := (principalLineHom aξ w gF).toRingHom.toAlgebra
    letI := (normalizedLineProductHom aξ w j gF hwj (nonflatCoordMap F E φ)).toRingHom.toAlgebra
    letI : Module.Finite (OpenLineRing (subst aξ w gF))
        (NormalizationProduct (linePreimageIdeal aξ w j gF (nonflatCoordMap F E φ))) :=
      normalizedLineProductHom_finite aξ w j gF hwj (nonflatCoordMap F E φ)
        (nonflatCoordMap_finite F E φ hφ)
    haveI := nonflatLine_isScalarTower_k_base (k := k) gF (nonflatCoordMap F E φ)
    haveI := nonflatLine_isScalarTower_k_line (k := k) aξ w gF
    haveI := nonflatLine_isScalarTower_k_curve (k := k) aξ w j gF hwj (nonflatCoordMap F E φ)
    flatNormFun (B := OpenLineRing (subst aξ w gF))
        (fun y : Berk k (NormalizationProduct (linePreimageIdeal aξ w j gF
            (nonflatCoordMap F E φ))) =>
          u (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A)
            (comap ((normalizationMapAlg (Localization.Away gF)
              (linePreimageIdeal aξ w j gF (nonflatCoordMap F E φ))).restrictScalars k) y)))
        (nonflatEvalPoint (fun _ hc => τ.norm_algebraMap hc) _
          (nonflat_eval_subst_zero_ne_zero E τ.baseEval w)) =
      ∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
        ((τ.rigidWeight φ hφ b y : ℝ) : EReal) * u y := by
  classical
  refine ((τ.lineWeights E φ hS0 hφ hinj hh w j hwj hadm b hb).2
    (fun z => u (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) z))).trans ?_
  have hcongr : ∀ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
      ((τ.rigidWeight φ hφ b y : ℝ) : EReal) * u y =
        ∑ z ∈ (τ.finite_fibre φ hφ).toFinset with
          comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) z = y,
          ((τ.rigidMult φ hφ b z : ℝ) : EReal) *
            u (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) z) := by
    intro y _
    rw [rigidWeight, ← nonflat_ereal_sum_natCast_mul]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [(Finset.mem_filter.1 hz).2]
  rw [Finset.sum_congr rfl hcongr]
  exact (Finset.sum_fiberwise_of_maps_to (fun z hz =>
    τ.comap_includeRight_mem_fibre φ hφ ((Set.Finite.mem_toFinset _).1 hz)) _).symm

end NonflatRigidEmbedding

end Lines

/-! ### The weights (`def:nf-weights`) and their basic properties (`lem:nf-weights-basic`) -/

section Weights

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite)

/-- **The separating element `b_s`** (`lem:nf-rigid-fibre` (4)) for the canonical rigid datum
`nonflatRigidEmbedding s`: its values at the points of `π_F^{-1}(ξ_s)` are pairwise distinct. -/
def nonflatSeparating (s : Berk k B) : nonflatRigidField s ⊗[k] A :=
  Classical.choose ((nonflatRigidEmbedding s).exists_fibreEval_injective φ hφ)

/-- The defining property of `nonflatSeparating`. -/
theorem nonflatSeparating_spec (s : Berk k B) (z₁ : Berk k (nonflatRigidField s ⊗[k] A))
    (h₁ : z₁ ∈ (nonflatRigidEmbedding s).fibre φ) (z₂ : Berk k (nonflatRigidField s ⊗[k] A))
    (h₂ : z₂ ∈ (nonflatRigidEmbedding s).fibre φ)
    (he : (nonflatRigidEmbedding s).fibreEval φ hφ h₁ (nonflatSeparating φ hφ s) =
      (nonflatRigidEmbedding s).fibreEval φ hφ h₂ (nonflatSeparating φ hφ s)) : z₁ = z₂ :=
  Classical.choose_spec ((nonflatRigidEmbedding s).exists_fibreEval_injective φ hφ) z₁ h₁ z₂ h₂ he

open Classical in
/-- **The weights `m_y(π)`** (`def:nf-weights`). For `y ∈ (Spec A)^an` over `s = π(y)`: if
`s ∈ S_0^an` (`|h|_s ≠ 0`), the multiplicity `Berk.flatFibreMult B y` of `y` in its fibre (the
dimension of the local factor of `ℋ(s) ⊗_B A` at `y`; on `S_0` this is the étale multiplicity of
`lem:finite-etale-norm`); otherwise the rigid weight `∑_{r(z) = y} M_z` for the canonical rigid
datum `nonflatRigidEmbedding s` and the separating element `nonflatSeparating φ hφ s`. The weights
depend on these choices, but on no function `u`. -/
def nonflatWeight (h : B) (y : Berk k A) : ℕ :=
  letI := (φ : B →+* A).toAlgebra
  haveI : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  if (comap φ y).val h = 0 then
    (nonflatRigidEmbedding (comap φ y)).rigidWeight φ hφ (nonflatSeparating φ hφ (comap φ y)) y
  else flatFibreMult B y

/-- **The norm** `N_π u(s) = ∑_{π(y) = s} m_y(π) u(y)` (`def:nf-weights`), in the form of the
field `isRegularizable_norm` of `NormWeights`. -/
def nonflatNorm (h : B) (u : Berk k A → EReal) (s : Berk k B) : EReal :=
  ∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset, ((nonflatWeight φ hφ h y : ℝ) : EReal) * u y

/-- On `S_0^an` the weight is the fibre multiplicity. -/
theorem nonflatWeight_of_ne_zero {h : B} {y : Berk k A} (hy : (comap φ y).val h ≠ 0) :
    letI := (φ : B →+* A).toAlgebra
    haveI : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    nonflatWeight φ hφ h y = flatFibreMult B y := by
  rw [nonflatWeight, if_neg hy]

/-- Off `S_0^an` the weight is the rigid weight for the canonical rigid datum. -/
theorem nonflatWeight_of_eq_zero {h : B} {y : Berk k A} (hy : (comap φ y).val h = 0) :
    nonflatWeight φ hφ h y = (nonflatRigidEmbedding (comap φ y)).rigidWeight φ hφ
      (nonflatSeparating φ hφ (comap φ y)) y := by
  rw [nonflatWeight, if_pos hy]

/-- **`m_y(π) ≥ 1`** (`lem:nf-weights-basic`). -/
theorem one_le_nonflatWeight [IsAlgClosed k] [IsDomain A] {n : ℕ}
    (hB : IsAffineSpacePrincipalOpen k B n) (hinj : Function.Injective φ) (h : B) (y : Berk k A) :
    1 ≤ nonflatWeight φ hφ h y := by
  by_cases hy : (comap φ y).val h = 0
  · rw [nonflatWeight_of_eq_zero φ hφ hy]
    have := nonflat_isDomain_baseChange_base (nonflatRigidField (comap φ y)) hB
    have := nonflat_isIntegrallyClosed_baseChange_base (nonflatRigidField (comap φ y)) hB
    have : IsDomain (nonflatRigidField (comap φ y) ⊗[k] A) :=
      tensorProduct_isDomain_of_algClosed k _ A
    exact (nonflatRigidEmbedding (comap φ y)).one_le_rigidWeight φ hφ hinj _ rfl
  · rw [nonflatWeight_of_ne_zero φ hφ hy]
    let := (φ : B →+* A).toAlgebra
    have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    have : Module.Finite B A := hφ
    exact one_le_flatFibreMult y

end Weights

section WeightsSum

variable {k : Type*} [Field k] [IsAlgClosed k] {A B : Type u} [CommRing A] [IsDomain A]
  [Algebra k A] [CommRing B] [Algebra k B] (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite)

/-- **`∑_z M_z = d`** for the canonical rigid datum of any `s` (`lem:nf-line-weights`, through a
line admissible for `h`, `lem:nf-line-exists`). -/
theorem sum_rigidMult_nonflatSeparating {n : ℕ} (hn : 1 ≤ n)
    (hB : IsAffineSpacePrincipalOpen k B n) (hinj : Function.Injective φ) {S : Finset A} {h : B}
    (hh : IsNonflatGoodLocus φ S h) (s : Berk k B) :
    ∑ z ∈ ((nonflatRigidEmbedding s).finite_fibre φ hφ).toFinset,
        (nonflatRigidEmbedding s).rigidMult φ hφ (nonflatSeparating φ hφ s) z =
      genericDegree (φ : B →+* A) := by
  have := hB.isDomain
  obtain ⟨hS, hS0, ⟨E⟩⟩ :=
    (hB.exists_ulift : ∃ hS : MvPolynomial (ULift.{u} (Fin n)) k, hS ≠ 0 ∧
      Nonempty (B ≃ₐ[k] Localization.Away hS))
  have : Nonempty (ULift.{u} (Fin n)) := ⟨⟨⟨0, hn⟩⟩⟩
  obtain ⟨w, hw0, -, hadm⟩ :=
    nonflat_exists_admissible_direction E (nonflatRigidEmbedding s).baseEval hh.ne_zero
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
  exact ((nonflatRigidEmbedding s).lineWeights E φ hS0 hφ hinj hh w j hj hadm _
    (nonflatSeparating_spec φ hφ s)).1

/-- **`∑_{π(y) = s} m_y(π) = d`** for every `s ∈ S^an` (`lem:nf-weights-basic`): over `S_0^an` by
`IsNonflatGoodLocus.sum_flatFibreMult`; off `S_0^an` the rigid weights regroup the `M_z`
(`NonflatRigidEmbedding.sum_rigidWeight`), which add up to `d`
(`sum_rigidMult_nonflatSeparating`). -/
theorem sum_nonflatWeight {n : ℕ} (hn : 1 ≤ n) (hB : IsAffineSpacePrincipalOpen k B n)
    (hinj : Function.Injective φ) {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h)
    (s : Berk k B) :
    ∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset, nonflatWeight φ hφ h y =
      genericDegree (φ : B →+* A) := by
  have := hB.isDomain
  by_cases hs : s.val h = 0
  · have hcongr : ∀ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
        nonflatWeight φ hφ h y =
          (nonflatRigidEmbedding s).rigidWeight φ hφ (nonflatSeparating φ hφ s) y := by
      intro y hy
      have hy0 := (Set.Finite.mem_toFinset _).1 hy
      have hy' : comap φ y = s := hy0
      subst hy'
      exact nonflatWeight_of_eq_zero φ hφ hs
    rw [Finset.sum_congr rfl hcongr, NonflatRigidEmbedding.sum_rigidWeight,
      sum_rigidMult_nonflatSeparating φ hφ hn hB hinj hh s]
  · let := (φ : B →+* A).toAlgebra
    have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    have hcongr : ∀ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
        nonflatWeight φ hφ h y = flatFibreMult B y := by
      intro y hy
      have hy0 := (Set.Finite.mem_toFinset _).1 hy
      have hy' : comap φ y = s := hy0
      exact nonflatWeight_of_ne_zero φ hφ (by rw [hy']; exact hs)
    rw [Finset.sum_congr rfl hcongr]
    exact hh.sum_flatFibreMult hφ hs

end WeightsSum

/-! ### The data used by `prop:nf-nonflat-norm` -/

section Packaging

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite)

/-- **The weights as `NormWeights`**: the fields `m`, `one_le`, `finite`, `sum_eq` of
`NormWeights φ S W d` (`d = genericDegree φ`) are `nonflatWeight`, `one_le_nonflatWeight`,
`finite_preimage_comap_singleton` and `sum_nonflatWeight`; the remaining field is the
regularizability of `nonflatNorm` (`prop:nf-nonflat-norm`), taken as the argument `hreg`. -/
def nonflatNormWeights [IsAlgClosed k] {A B : Type u} [CommRing A] [IsDomain A] [Algebra k A]
    [CommRing B] [Algebra k B] (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite) {n : ℕ} (hn : 1 ≤ n)
    (hB : IsAffineSpacePrincipalOpen k B n) (hinj : Function.Injective φ) {S : Finset A} {h : B}
    (hh : IsNonflatGoodLocus φ S h) {W : (Berk k A → EReal) → Prop}
    (hreg : ∀ u, W u → HasLogGrowth u →
      (∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
        ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) →
      IsRegularizable (nonflatNorm φ hφ h u)) :
    NormWeights φ S W (genericDegree (φ : B →+* A)) where
  m := nonflatWeight φ hφ h
  one_le := one_le_nonflatWeight φ hφ hB hinj h
  finite := finite_preimage_comap_singleton φ hφ
  sum_eq := sum_nonflatWeight φ hφ hn hB hinj hh
  isRegularizable_norm := hreg

@[simp]
theorem nonflatNormWeights_m [IsAlgClosed k] {A B : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [CommRing B] [Algebra k B] (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite) {n : ℕ}
    (hn : 1 ≤ n) (hB : IsAffineSpacePrincipalOpen k B n) (hinj : Function.Injective φ)
    {S : Finset A} {h : B} (hh : IsNonflatGoodLocus φ S h) {W : (Berk k A → EReal) → Prop}
    (hreg) : (nonflatNormWeights φ hφ hn hB hinj hh (W := W) hreg).m = nonflatWeight φ hφ h :=
  rfl

/-- Over `S_0^an` the norm is the flat norm `flatNormFun` along `π`. -/
theorem nonflatNorm_of_ne_zero {h : B} {s : Berk k B} (hs : s.val h ≠ 0) (u : Berk k A → EReal) :
    letI := (φ : B →+* A).toAlgebra
    haveI : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    haveI : Module.Finite B A := hφ
    nonflatNorm φ hφ h u s = flatNormFun (B := B) u s := by
  let := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite B A := hφ
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy0 := (Set.Finite.mem_toFinset _).1 hy
  have hy' : comap φ y = s := hy0
  rw [nonflatWeight_of_ne_zero φ hφ (by rw [hy']; exact hs)]

/-- **The norm off `S_0`** is the weighted sum with the rigid weights of the canonical rigid datum
(to be combined with `NonflatRigidEmbedding.flatNormFun_line_eq_sum_rigidWeight`). -/
theorem nonflatNorm_of_eq_zero {h : B} {s : Berk k B} (hs : s.val h = 0) (u : Berk k A → EReal) :
    nonflatNorm φ hφ h u s = ∑ y ∈ (finite_preimage_comap_singleton φ hφ s).toFinset,
      (((nonflatRigidEmbedding s).rigidWeight φ hφ (nonflatSeparating φ hφ s) y : ℝ) : EReal) *
        u y := by
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy0 := (Set.Finite.mem_toFinset _).1 hy
  have hy' : comap φ y = s := hy0
  have := nonflatWeight_of_eq_zero φ hφ (h := h) (y := y) (by rw [hy']; exact hs)
  rw [hy'] at this
  rw [this]

/-- `B_h → A_{φ(h)}` is a map of `k`-algebras. -/
theorem nonflat_awayMap_isScalarTower (h : B) :
    letI := (Localization.awayMap (φ : B →+* A) h).toAlgebra
    IsScalarTower k (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) := by
  let := (Localization.awayMap (φ : B →+* A) h).toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  change _ = Localization.awayMap (φ : B →+* A) h (algebraMap k (Localization.Away h) c)
  rw [IsScalarTower.algebraMap_apply k B (Localization.Away h), Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply k A
      (Localization.Away ((φ : B →+* A) h))]
  congr 1
  exact (φ.commutes c).symm

include hφ in
/-- `A_{φ(h)}` is a finite `B_h`-module (`nonflat_awayMap_finite`, as a `Module.Finite` instance). -/
theorem nonflat_awayMap_moduleFinite (h : B) :
    letI := (Localization.awayMap (φ : B →+* A) h).toAlgebra
    Module.Finite (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
  nonflat_awayMap_finite hφ h

/-- `A_{φ(h)}` is an étale `B_h`-algebra (`IsNonflatGoodLocus.awayMap_etale`, as an
`Algebra.Etale` instance). -/
theorem IsNonflatGoodLocus.awayMap_algebraEtale {S : Finset A} {h : B}
    (hh : IsNonflatGoodLocus φ S h) :
    letI := (Localization.awayMap (φ : B →+* A) h).toAlgebra
    Algebra.Etale (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
  hh.awayMap_etale

/-- **The norm over `S_0` is the norm of the localized cover** (`prop:nf-nonflat-norm`, proof:
"for `s ∈ S_0^an` the fibre algebras of `B → A` and `B_h → A_{φ(h)}` at `s` coincide"): for
`y ∈ (Spec B_h)^an`, `N_π u(y|_B) = N_{A_{φ(h)}/B_h}(u|_{Y_0})(y)`, the flat norm along the finite
map `B_h → A_{φ(h)}`. -/
theorem nonflatNorm_awayComap (h : B) (u : Berk k A → EReal) (y' : Berk k (Localization.Away h)) :
    letI := (Localization.awayMap (φ : B →+* A) h).toAlgebra
    haveI := nonflat_awayMap_isScalarTower φ h
    haveI : Module.Finite (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
      nonflat_awayMap_moduleFinite φ hφ h
    nonflatNorm φ hφ h u (awayComap h y') =
      flatNormFun (B := Localization.Away h)
        (fun z : Berk k (Localization.Away ((φ : B →+* A) h)) =>
          u (awayComap ((φ : B →+* A) h) z)) y' := by
  let := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite B A := hφ
  let := (Localization.awayMap (φ : B →+* A) h).toAlgebra
  have : IsScalarTower k (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
    nonflat_awayMap_isScalarTower φ h
  have : Module.Finite (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
    nonflat_awayMap_moduleFinite φ hφ h
  refine (nonflatNorm_of_ne_zero φ hφ (awayComap_val_ne_zero h y') u).trans ?_
  have h1 := Berk.flatNormFun_baseChange (C := Localization.Away h) (A := B) (B := A) u y'
  have h2 := Berk.nonflat_flatNormFun_comap_of_tensorMap_bijective
    (nonflatAwayTensorEquiv (φ : B →+* A) h).toAlgHom y'
    (Algebra.TensorProduct.congr AlgEquiv.refl (nonflatAwayTensorEquiv (φ : B →+* A) h)).bijective
    (fun y => u (comap ((Algebra.TensorProduct.includeRight :
      A →ₐ[B] Localization.Away h ⊗[B] A).restrictScalars k) y))
  refine h1.symm.trans (h2.symm.trans ?_)
  congr 1
  funext z
  congr 1
  apply Berk.ext_val
  intro a
  simp only [comap_val_apply, awayComap_val_apply, AlgHom.coe_restrictScalars',
    Algebra.TensorProduct.includeRight_apply]
  change z.val (nonflatAwayTensorEquiv (φ : B →+* A) h ((1 : Localization.Away h) ⊗ₜ a)) = _
  rw [nonflatAwayTensorEquiv_tmul, map_one, one_mul]

/-- **The norm over `S_0` in the étale form** `EnvelopeProperty.normFun` of
`IsRegularizable.normFun` (`lem:finite-etale-norm`): for `y ∈ (Spec B_h)^an`,
`N_π u(y|_B) = normFun (u|_{Y_0}) (y)` along the finite free étale `B_h → A_{φ(h)}`. -/
theorem IsNonflatGoodLocus.nonflatNorm_awayComap_eq_normFun {S : Finset A} {h : B}
    (hh : IsNonflatGoodLocus φ S h) (u : Berk k A → EReal) (y' : Berk k (Localization.Away h)) :
    letI := (Localization.awayMap (φ : B →+* A) h).toAlgebra
    haveI := nonflat_awayMap_isScalarTower φ h
    haveI : Module.Finite (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
      nonflat_awayMap_moduleFinite φ hφ h
    haveI : Module.Free (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
      hh.awayMap_free
    haveI : Algebra.Etale (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
      hh.awayMap_algebraEtale
    nonflatNorm φ hφ h u (awayComap h y') =
      normFun (B := Localization.Away h)
        (fun z : Berk k (Localization.Away ((φ : B →+* A) h)) =>
          u (awayComap ((φ : B →+* A) h) z)) y' := by
  let := (Localization.awayMap (φ : B →+* A) h).toAlgebra
  have := nonflat_awayMap_isScalarTower φ h
  have : Module.Finite (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
    nonflat_awayMap_moduleFinite φ hφ h
  have : Module.Free (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
    hh.awayMap_free
  have : Algebra.Etale (Localization.Away h) (Localization.Away ((φ : B →+* A) h)) :=
    hh.awayMap_algebraEtale
  exact (nonflatNorm_awayComap φ hφ h u y').trans (flatNormFun_eq_normFun _ _)

end Packaging

/-! ### Generic fibres in coordinates (`lem:nf-generic-fibre`, passage to `π`) -/

section CoordFibres

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [Algebra k A] [CommRing B]
  [Algebra k B] (F : Type*) [Field F] [Algebra k F] {σ : Type*} {hS : MvPolynomial σ k}
  (E : B ≃ₐ[k] Localization.Away hS) (φ : B →ₐ[k] A)

/-- The inclusion `B → B_F = F[x]_{h_S}`, `b ↦ ψ(1 ⊗ b)`, in coordinates. -/
def nonflatCoordBaseHom : B →ₐ[k] Localization.Away (MvPolynomial.map (algebraMap k F) hS) :=
  ((nonflatBaseEquiv F E).toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight

theorem nonflatCoordBaseHom_apply (b : B) :
    nonflatCoordBaseHom F E b = nonflatBaseEquiv F E ((1 : F) ⊗ₜ[k] b) := rfl

/-- `φ_F : B_F → A_F` is a map of `k`-algebras. -/
theorem nonflatCoordMap_isScalarTower :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    IsScalarTower k (Localization.Away (MvPolynomial.map (algebraMap k F) hS)) (F ⊗[k] A) :=
  letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k F (F ⊗[k] A),
      IsScalarTower.algebraMap_apply k F (Localization.Away (MvPolynomial.map (algebraMap k F) hS))]
    exact ((nonflatCoordMap F E φ).commutes _).symm

/-- `A_F` is a finite `B_F`-module (in coordinates, as a `Module.Finite` instance). -/
theorem nonflatCoordMap_moduleFinite (hφ : (φ : B →+* A).Finite) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    Module.Finite (Localization.Away (MvPolynomial.map (algebraMap k F) hS)) (F ⊗[k] A) :=
  nonflatCoordMap_finite F E φ hφ

/-- **Base change in coordinates** (`lem:nf-generic-fibre`, the passage from `B_F → A_F` to `π`):
for every point `z` of `(Spec B_F)^an`, `B_F = F[x]_{h_S}`, and every function `u` on `Y^an`,
`N_{A_F/B_F} (u ∘ r)(z) = N_π u (z|_B)` (flat norms, `r` the restriction along `A → A_F`):
`A_F = F ⊗_k A` is the base change `B_F ⊗_B A` of `A`, and fibre sums commute with base change
(`nonflat_flatNormFun_comap_eq_of_baseChange_bijective`). -/
theorem nonflat_coord_flatNormFun_eq (hφ : (φ : B →+* A).Finite) (u : Berk k A → EReal)
    (z : Berk k (Localization.Away (MvPolynomial.map (algebraMap k F) hS))) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    haveI := nonflatCoordMap_isScalarTower F E φ
    haveI := nonflatCoordMap_moduleFinite F E φ hφ
    letI := (φ : B →+* A).toAlgebra
    haveI : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    haveI : Module.Finite B A := hφ
    flatNormFun (B := Localization.Away (MvPolynomial.map (algebraMap k F) hS))
        (fun y : Berk k (F ⊗[k] A) =>
          u (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) y)) z =
      flatNormFun (B := B) u (comap (nonflatCoordBaseHom F E) z) := by
  set R₂ := Localization.Away (MvPolynomial.map (algebraMap k F) hS)
  set ψ := nonflatBaseEquiv F E
  let φF := nonflatCoordMap F E φ
  let iT : Algebra R₂ (F ⊗[k] A) := φF.toRingHom.toAlgebra
  have := nonflatCoordMap_isScalarTower F E φ
  have := nonflatCoordMap_moduleFinite F E φ hφ
  let iA : Algebra B A := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite B A := hφ
  let iR : Algebra B R₂ := (nonflatCoordBaseHom F E).toRingHom.toAlgebra
  have : IsScalarTower k B R₂ := IsScalarTower.of_algebraMap_eq fun c =>
    ((nonflatCoordBaseHom F E).commutes c).symm
  let iBT : Algebra B (F ⊗[k] A) := ((algebraMap R₂ (F ⊗[k] A)).comp (algebraMap B R₂)).toAlgebra
  have : IsScalarTower B R₂ (F ⊗[k] A) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k B (F ⊗[k] A) := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = φF (nonflatCoordBaseHom F E (algebraMap k B c))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k F (F ⊗[k] A),
      IsScalarTower.algebraMap_apply k F R₂]
    exact (φF.commutes _).symm
  -- `ψ(1 ⊗ b)` goes to `1 ⊗ φ(b)`
  have hφF : ∀ b : B, φF (nonflatCoordBaseHom F E b) = (1 : F) ⊗ₜ[k] φ b := fun b => by
    rw [nonflatCoordBaseHom_apply, nonflatCoordMap_nonflatBaseEquiv,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  let ρ : A →ₐ[B] F ⊗[k] A :=
    { (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A).toRingHom with
      commutes' := fun b => by
        change (1 : F) ⊗ₜ[k] φ b = φF (nonflatCoordBaseHom F E b)
        rw [hφF] }
  -- the inverse of `R₂ ⊗_B A → A_F`
  let D := R₂ ⊗[B] A
  have : IsScalarTower k F D := inferInstance
  let g' : A →ₐ[k] D :=
    { (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom with
      commutes' := fun c => by
        change (1 : R₂) ⊗ₜ[B] algebraMap k A c = algebraMap k R₂ c ⊗ₜ[B] (1 : A)
        rw [IsScalarTower.algebraMap_apply k B R₂ c, Algebra.TensorProduct.tmul_one_eq_one_tmul,
          ← IsScalarTower.algebraMap_apply k B A c] }
  let M : F ⊗[k] A →ₐ[F] D :=
    Algebra.TensorProduct.lift (Algebra.ofId F D) g' fun _ _ => Commute.all _ _
  have hM : ∀ (c : F) (a : A), M (c ⊗ₜ a) = algebraMap F R₂ c ⊗ₜ[B] a := fun c a => by
    change algebraMap F D c * ((1 : R₂) ⊗ₜ[B] a) = _
    change (algebraMap F R₂ c ⊗ₜ[B] (1 : A)) * ((1 : R₂) ⊗ₜ[B] a) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hMφ : ∀ q : F ⊗[k] B, M (Algebra.TensorProduct.map (AlgHom.id F F) φ q) =
      ψ q ⊗ₜ[B] (1 : A) := fun q => by
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add q q' hq hq' => rw [map_add, map_add, hq, hq', map_add, TensorProduct.add_tmul]
    | tmul c b =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hM]
      have hψ : ψ (c ⊗ₜ[k] b) = algebraMap F R₂ c * nonflatCoordBaseHom F E b := by
        rw [nonflatCoordBaseHom_apply, ← Algebra.smul_def, ← map_smul,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have h1 : nonflatCoordBaseHom F E b ⊗ₜ[B] (1 : A) = (1 : R₂) ⊗ₜ[B] φ b :=
        Algebra.TensorProduct.tmul_one_eq_one_tmul (R := B) (A := R₂) (B := A) b
      rw [hψ, ← mul_one (1 : A), ← Algebra.TensorProduct.tmul_mul_tmul, h1,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hbij : Function.Bijective (nonflatBaseChangeAlgHom (Q := R₂) ρ) := by
    refine Function.bijective_iff_has_inverse.2 ⟨M, fun x => ?_, fun t => ?_⟩
    · induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => rw [map_add, map_add, hx, hx']
      | tmul r a =>
        obtain ⟨q, rfl⟩ := ψ.surjective r
        rw [nonflatBaseChangeAlgHom_tmul, map_mul]
        change M (φF (ψ q)) * M ((1 : F) ⊗ₜ[k] a) = _
        rw [nonflatCoordMap_nonflatBaseEquiv, hMφ, hM, map_one,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · induction t using TensorProduct.induction_on with
      | zero => simp
      | add t t' ht ht' => rw [map_add, map_add, ht, ht']
      | tmul c a =>
        rw [hM, nonflatBaseChangeAlgHom_tmul]
        change φF (algebraMap F R₂ c) * ((1 : F) ⊗ₜ[k] a) = _
        rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact nonflat_flatNormFun_comap_eq_of_baseChange_bijective ρ hbij z u

/-- **Generic fibres and the weights**: if `z|_B ∈ S_0^an`, the flat norm of `u ∘ r` along
`B_F → A_F` at `z` is `N_π u (z|_B)` with the weights `m_y(π)` (to be combined with
`AffineLine.nonflatLine_exists_flatNormFun_eq`, `lem:nf-generic-fibre`). -/
theorem nonflat_coord_flatNormFun_eq_nonflatNorm (hφ : (φ : B →+* A).Finite) {h : B}
    (u : Berk k A → EReal) (z : Berk k (Localization.Away (MvPolynomial.map (algebraMap k F) hS)))
    (hz : (comap (nonflatCoordBaseHom F E) z).val h ≠ 0) :
    letI := (nonflatCoordMap F E φ).toRingHom.toAlgebra
    haveI := nonflatCoordMap_isScalarTower F E φ
    haveI := nonflatCoordMap_moduleFinite F E φ hφ
    flatNormFun (B := Localization.Away (MvPolynomial.map (algebraMap k F) hS))
        (fun y : Berk k (F ⊗[k] A) =>
          u (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) y)) z =
      nonflatNorm φ hφ h u (comap (nonflatCoordBaseHom F E) z) :=
  (nonflat_coord_flatNormFun_eq F E φ hφ u z).trans (nonflatNorm_of_ne_zero φ hφ hz u).symm

end CoordFibres

end EnvelopeProperty
