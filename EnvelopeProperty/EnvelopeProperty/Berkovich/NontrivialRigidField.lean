/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Gauss
import EnvelopeProperty.Berkovich.Finite
import EnvelopeProperty.Berkovich.CompleteAlgebraicClosure
import EnvelopeProperty.Berkovich.CompleteFieldEmbedding
import EnvelopeProperty.Berkovich.AlgebraScalarExtension

/-!
# Rigid data over a point: a nontrivially valued rigid field and the rigid fibre

This file formalizes `def:nf-rigid-data` and `lem:nf-rigid-fibre`(2)–(4) of the blueprint chapter
`nonflat-route.tex`, the nonflat route to Fang–Han–Xia, *The envelope property for unibranch
projective varieties*, Proposition 5.22 (`prop:nonflat-norm`; revision 832e086, Section 5,
`sec:normal-local-regularization`; the full proof is in revision d64981e). In the proof of FHX 5.22
a point `s ∈ S^an` is lifted to a rational point `ξ` of `S_F = Spec(F ⊗_k B)` over the completed
algebraic closure `F` of `ℋ(s)`; the route of `nonflat-route.tex` replaces FHX Lemma 5.21 by a
piece lemma on Gauss points (`Berkovich/LineFibrePieces`), which needs `F` to be **nontrivially
valued** (orchestrator decision P522-D3). FHX's `F` is trivially valued when `ℋ(s)` is.

## Main definitions

* `EnvelopeProperty.nonflatRationalPoint e`: the `F`-rational point `|b| = ‖e(b)‖` of an
  `F`-algebra map `e : R → F`, as a point of `Berk k R` (the convention of
  `Berkovich/FlatNormBaseChange` and `Berkovich/LineFibrePieces`: points of `(Spec R)^an` over `F`
  are points of `Berk k R` restricting to the norm of `F`).
* `EnvelopeProperty.nonflatPointEval z`: the evaluation `R → F`, `b ↦ b(z)`, at a point `z` at
  which every element is congruent to a constant (`R ⧸ supp z ≅ F`).
* `EnvelopeProperty.NonflatRigidEmbedding s F`: an isometric embedding `ℋ(s) → F` compatible with
  `k` (a rigid datum, `def:nf-rigid-data`, when `F` is complete, algebraically closed and
  nontrivially valued). From it: `algHom : B → F`, the evaluation `baseEval : F ⊗_k B → F`, the
  rational point `basePoint = ξ`, the rigid fibre `fibre φ = π_F^{-1}(ξ) ⊆ (Spec F ⊗_k A)^an` of a
  `k`-algebra map `φ : B → A`, and `fibreEval φ hφ hz : F ⊗_k A → F` at `z ∈ fibre φ`.
* `EnvelopeProperty.nonflatRigidField s`, `EnvelopeProperty.nonflatRigidEmbedding s`: the rigid
  datum of `def:nf-rigid-data`: `F_s` is the completed algebraic closure
  (`EnvelopeProperty.CompleteAlgebraicClosure`) of `ℋ(s')`, `s' = η_{s,1/2}` the Gauss point of
  radius `1/2` over `s` on `Spec B[w]` (`Berk.gauss`), and `ℋ(s) → ℋ(s') → F_s` (`Berk.H.map`).

## Main results

* `nonflatRigidField_exists_one_lt_norm`: `F_s` is nontrivially valued (`‖w⁻¹‖ = 2`), and
  `nonflatRigidField_norm_algebraMap`: its norm is trivial on `k`; these are the hypotheses `hκ`,
  `hF` of `Berkovich/LineFibrePieces`. `F_s` is complete and algebraically closed by instances.
* `lem:nf-rigid-fibre`(2): `NonflatRigidEmbedding.finite_fibre` (for `φ` finite) and
  `NonflatRigidEmbedding.exists_val_sub_eq_zero_of_mem_fibre` (points over `ξ` are `F`-rational;
  in general `nonflat_exists_val_sub_eq_zero_of_comap_eq`), with `val_eq_nnnorm_fibreEval`,
  `fibreEval_comp` (the evaluation lies over `ξ`), `eq_of_fibreEval_eq`.
* `lem:nf-rigid-fibre`(3): `NonflatRigidEmbedding.exists_mem_fibre_comap_includeRight_eq` and
  `surjOn_comap_includeRight_fibre`: `r : π_F^{-1}(ξ) → π^{-1}(s)`, `z ↦ z|_A`, is onto, for
  every algebraically closed isometric extension `F` of `ℋ(s)`. For `y` over `s`, the kernel of
  `ℋ(s) ⊗_B A → ℋ(y)` is maximal with residue field `L` finite over `ℋ(s)`; an `ℋ(s)`-embedding
  `L → F` exists as `F` is algebraically closed and is isometric because the absolute value of the
  complete field `ℋ(s)` extends uniquely to `L` (`norm_algebraic_algHom`)
  (`NonflatRigidEmbedding.exists_algHom_of_comap_eq`).
* `lem:nf-rigid-fibre`(4): `NonflatRigidEmbedding.exists_fibreEval_injective`, from the Chinese
  remainder statement `nonflat_exists_injOn_algHom` for finitely many `F`-algebra maps `R → F`.

## Comparison with the blueprint

* `lem:nf-rigid-fibre`(1) is not repeated here: `A_F` is a domain by
  `EnvelopeProperty.tensorProduct_isDomain_of_algClosed`, `B_F ≅ F[x]_{h_S}` is
  `AffineLine.principalOpenTensorEquiv`, finiteness of `B_F → A_F` is `nonflat_baseChange_finite`;
  the degree `d` uses the good locus `lem:nf-good-locus` and belongs to the weights (lane NF6).
* The fibre statements (2)–(4) hold for an arbitrary algebraically closed ultrametric field `F`
  with an isometric `k`-compatible embedding of `ℋ(s)`; completeness and nontriviality of `F` are
  not used there (completeness of `ℋ(s)` is).
* A rigid datum is recorded as the embedding `ℋ(s) → F`; the evaluation `ξ` and the rigid fibre
  are derived from it.
-/

open scoped NNReal ENNReal Topology TensorProduct Polynomial

noncomputable section

namespace EnvelopeProperty

open Berk

/-! ### Rational points of `F`-algebras -/

section RationalPoint

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1)
variable {R : Type*} [CommRing R] [Algebra k R] [Algebra F R] [IsScalarTower k F R]

/-- The **`F`-rational point** of `(Spec R)^an` defined by an `F`-algebra homomorphism
`e : R → F`: `|b| = ‖e b‖`. It restricts to the norm of `F` on `F`. -/
def nonflatRationalPoint (e : R →ₐ[F] F) : Berk k R where
  val := (NormedField.valuation (K := F)).comap (e : R →+* F)
  val_algebraMap c hc := by
    rw [Valuation.comap_apply, IsScalarTower.algebraMap_apply k F R]
    simp only [RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      NormedField.valuation_apply]
    exact NNReal.eq (by simpa using hF c hc)

/-- `|b| = ‖e(b)‖` at the rational point of `e`. -/
@[simp]
theorem nonflatRationalPoint_val_apply (e : R →ₐ[F] F) (b : R) :
    (nonflatRationalPoint hF e).val b = ‖e b‖₊ := by
  rw [nonflatRationalPoint, Valuation.comap_apply, NormedField.valuation_apply]
  rfl

/-- The rational point of `e` restricts to the norm of `F`. -/
theorem nonflatRationalPoint_val_algebraMap (e : R →ₐ[F] F) (c : F) :
    (nonflatRationalPoint hF e).val (algebraMap F R c) = ‖c‖₊ := by
  rw [nonflatRationalPoint_val_apply, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

/-- Restriction of a rational point along an `F`-algebra map. -/
theorem comap_nonflatRationalPoint {R' : Type*} [CommRing R'] [Algebra k R'] [Algebra F R']
    [IsScalarTower k F R'] (f : R' →ₐ[F] R) (e : R →ₐ[F] F) :
    comap (f.restrictScalars k) (nonflatRationalPoint hF e) =
      nonflatRationalPoint hF (e.comp f) := by
  apply Berk.ext_val
  intro b
  rw [comap_val_apply, nonflatRationalPoint_val_apply, nonflatRationalPoint_val_apply]
  rfl

/-- A rational point determines its homomorphism. -/
theorem nonflatRationalPoint_injective :
    Function.Injective (nonflatRationalPoint hF : (R →ₐ[F] F) → Berk k R) := by
  intro e e' h
  ext b
  have h1 : (nonflatRationalPoint hF e').val (b - algebraMap F R (e b)) = 0 := by
    rw [← h, nonflatRationalPoint_val_apply, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self, nnnorm_zero]
  rw [nonflatRationalPoint_val_apply, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, nnnorm_eq_zero, sub_eq_zero] at h1
  exact h1.symm

/-- **Points over a rational point are rational.** Let `F` be algebraically closed, `ψ : Q → R` an
integral homomorphism of `F`-algebras and `z` a point of `(Spec R)^an` over the rational point of
`e : Q → F`. Then every `b ∈ R` is congruent to a constant `c ∈ F` modulo the kernel of `z`: a monic
equation of `b` over `Q`, with coefficients evaluated by `e`, splits over `F`, and one of its linear
factors vanishes at `z`. -/
theorem nonflat_exists_val_sub_eq_zero_of_comap_eq [IsAlgClosed F] {Q : Type*} [CommRing Q]
    [Algebra k Q] [Algebra F Q] [IsScalarTower k F Q] (ψ : Q →ₐ[F] R)
    (hψ : (ψ : Q →+* R).IsIntegral) (e : Q →ₐ[F] F) {z : Berk k R}
    (hz : comap (ψ.restrictScalars k) z = nonflatRationalPoint hF e) (b : R) :
    ∃ c : F, z.val (b - algebraMap F R c) = 0 := by
  classical
  set φ : F →+* R := algebraMap F R
  have hx' : ∀ q : Q, z.val (ψ q) = ‖e q‖₊ := fun q => by
    rw [← nonflatRationalPoint_val_apply hF e q, ← hz]
    rfl
  have hev : ∀ q : Q, z.val (φ (e q) - ψ q) = 0 := by
    intro q
    have : φ (e q) - ψ q = ψ (algebraMap F Q (e q) - q) := by
      rw [map_sub, AlgHom.commutes]
    rw [this, hx', map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self,
      nnnorm_zero]
  obtain ⟨P, hPm, hPb⟩ := hψ b
  have hdiff : z.val ((P.map (e : Q →+* F)).eval₂ φ b) = 0 := by
    rw [Polynomial.eval₂_map]
    have h : P.eval₂ (φ.comp (e : Q →+* F)) b =
        P.eval₂ (φ.comp (e : Q →+* F)) b - P.eval₂ (ψ : Q →+* R) b := by
      rw [hPb, sub_zero]
    rw [h, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
      ← Finset.sum_sub_distrib]
    apply le_antisymm _ zero_le
    apply Valuation.map_sum_le
    intro i _
    rw [← sub_mul, map_mul, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe, hev, zero_mul]
  have hsplit := (IsAlgClosed.splits (P.map (e : Q →+* F))).eq_prod_roots_of_monic
    (hPm.map (e : Q →+* F))
  rw [hsplit, Polynomial.eval₂_multiset_prod, Multiset.map_map, map_multiset_prod,
    Multiset.prod_eq_zero_iff] at hdiff
  obtain ⟨a, ha, h0⟩ := Multiset.mem_map.1 hdiff
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
  refine ⟨c, ?_⟩
  simpa [φ] using h0

end RationalPoint

section Eval

variable {k : Type*} [Field k] {F : Type*} [NormedField F] {R : Type*} [CommRing R] [Algebra k R]
  [Algebra F R]

/-- The constants `F → R ⧸ supp z` are bijective when `z` restricts to the norm of `F` and every
element of `R` is congruent to a constant modulo `supp z`. -/
theorem nonflat_bijective_algebraMap_quotient_supp (z : Berk k R)
    (hzF : ∀ c : F, z.val (algebraMap F R c) = ‖c‖₊)
    (hz : ∀ b : R, ∃ c : F, z.val (b - algebraMap F R c) = 0) :
    Function.Bijective (Algebra.ofId F (R ⧸ z.val.supp)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h : algebraMap F R c ∈ z.val.supp := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hc
    rw [Valuation.mem_supp_iff, hzF, nnnorm_eq_zero] at h
    exact h
  · intro w
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨c, hc⟩ := hz b
    refine ⟨c, ?_⟩
    change Ideal.Quotient.mk _ (algebraMap F R c) = _
    rw [Ideal.Quotient.eq, ← neg_sub, Ideal.neg_mem_iff]
    exact (Valuation.mem_supp_iff _ _).2 hc

/-- The **evaluation** `b ↦ b(z)` at a rational point `z` (a point restricting to the norm of `F`
at which every element is congruent to a constant): the composite `R → R ⧸ supp z ≅ F`. -/
def nonflatPointEval (z : Berk k R) (hzF : ∀ c : F, z.val (algebraMap F R c) = ‖c‖₊)
    (hz : ∀ b : R, ∃ c : F, z.val (b - algebraMap F R c) = 0) : R →ₐ[F] F :=
  (AlgEquiv.ofBijective _ (nonflat_bijective_algebraMap_quotient_supp z hzF hz)).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ F z.val.supp)

/-- `b - b(z)` lies in the kernel of `z`. -/
theorem nonflatPointEval_val_sub (z : Berk k R) (hzF : ∀ c : F, z.val (algebraMap F R c) = ‖c‖₊)
    (hz : ∀ b : R, ∃ c : F, z.val (b - algebraMap F R c) = 0) (b : R) :
    z.val (b - algebraMap F R (nonflatPointEval z hzF hz b)) = 0 := by
  set E := AlgEquiv.ofBijective _ (nonflat_bijective_algebraMap_quotient_supp z hzF hz)
  have h : Ideal.Quotient.mk z.val.supp (algebraMap F R (nonflatPointEval z hzF hz b)) =
      Ideal.Quotient.mk z.val.supp b := by
    change E (E.symm (Ideal.Quotient.mkₐ F z.val.supp b)) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl
  rw [Ideal.Quotient.eq] at h
  rw [← Valuation.mem_supp_iff, ← neg_sub, Ideal.neg_mem_iff]
  exact h

/-- `|b|_z = ‖b(z)‖`. -/
theorem val_eq_nnnorm_nonflatPointEval (z : Berk k R)
    (hzF : ∀ c : F, z.val (algebraMap F R c) = ‖c‖₊)
    (hz : ∀ b : R, ∃ c : F, z.val (b - algebraMap F R c) = 0) (b : R) :
    z.val b = ‖nonflatPointEval z hzF hz b‖₊ := by
  have h := nonflatPointEval_val_sub z hzF hz b
  have hb : b = algebraMap F R (nonflatPointEval z hzF hz b) +
      (b - algebraMap F R (nonflatPointEval z hzF hz b)) := by ring
  rw [hb, Valuation.map_add_supp _ _ ((Valuation.mem_supp_iff _ _).2 h), hzF,
    map_add, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, add_sub_cancel]

end Eval

section EvalPoint

variable {k : Type*} [Field k] {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra k F]
variable (hF : ∀ c : k, c ≠ 0 → ‖algebraMap k F c‖ = 1)
variable {R : Type*} [CommRing R] [Algebra k R] [Algebra F R] [IsScalarTower k F R]

/-- A rational point is the rational point of its evaluation. -/
theorem eq_nonflatRationalPoint_nonflatPointEval (z : Berk k R)
    (hzF : ∀ c : F, z.val (algebraMap F R c) = ‖c‖₊)
    (hz : ∀ b : R, ∃ c : F, z.val (b - algebraMap F R c) = 0) :
    z = nonflatRationalPoint hF (nonflatPointEval z hzF hz) := by
  apply Berk.ext_val
  intro b
  rw [nonflatRationalPoint_val_apply]
  exact val_eq_nnnorm_nonflatPointEval z hzF hz b

/-- The evaluation at the rational point of `e` is `e`. -/
theorem nonflatPointEval_nonflatRationalPoint (e : R →ₐ[F] F)
    (hzF : ∀ c : F, (nonflatRationalPoint hF e).val (algebraMap F R c) = ‖c‖₊)
    (hz : ∀ b : R, ∃ c : F, (nonflatRationalPoint hF e).val (b - algebraMap F R c) = 0) :
    nonflatPointEval (nonflatRationalPoint hF e) hzF hz = e :=
  nonflatRationalPoint_injective hF
    (eq_nonflatRationalPoint_nonflatPointEval hF _ hzF hz).symm

end EvalPoint

section Separating

variable {F : Type*} [Field F]

/-- **Separating elements** for finitely many `F`-algebra homomorphisms `R → F`, `F` infinite:
some `b ∈ R` takes pairwise distinct values. For `e ≠ e'` choose `a` with `e a ≠ e' a`; the products
`E_e = ∏_{e' ≠ e} (a - e'(a)) / (e(a) - e'(a))` satisfy `e(E_e) = 1` and `e'(E_e) = 0`, and
`b = ∑_e c_e E_e` with pairwise distinct `c_e ∈ F` works (the Chinese remainder theorem). -/
theorem nonflat_exists_injOn_algHom [Infinite F] {R : Type*} [CommRing R] [Algebra F R]
    (S : Finset (R →ₐ[F] F)) : ∃ b : R, Set.InjOn (fun e : R →ₐ[F] F => e b) S := by
  classical
  have hsep : ∀ e e' : R →ₐ[F] F, e ≠ e' → ∃ a : R, e a ≠ e' a := fun e e' h => by
    by_contra! h'
    exact h (AlgHom.ext h')
  choose a ha using hsep
  set E : (R →ₐ[F] F) → R := fun e => ∏ e' ∈ S.erase e,
    if h : e = e' then 1 else
      algebraMap F R (e (a e e' h) - e' (a e e' h))⁻¹ * (a e e' h - algebraMap F R (e' (a e e' h)))
  have hEe : ∀ e : R →ₐ[F] F, e (E e) = 1 := by
    intro e
    rw [map_prod]
    refine Finset.prod_eq_one fun e' he' => ?_
    rw [dif_neg (Finset.ne_of_mem_erase he').symm, map_mul, map_sub, AlgHom.commutes,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply]
    exact inv_mul_cancel₀ (sub_ne_zero.2 (ha _ _ _))
  have hEe' : ∀ e ∈ S, ∀ e'' ∈ S, e'' ≠ e → (e'' : R →ₐ[F] F) (E e) = 0 := by
    intro e _ e'' he'' hne
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, he''⟩) ?_
    rw [dif_neg hne.symm]
    simp only [map_mul, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self, mul_zero]
  obtain ⟨ι⟩ := nonempty_embedding_nat (S : Set (R →ₐ[F] F))
  set c : (R →ₐ[F] F) → F := fun e =>
    if h : e ∈ S then Infinite.natEmbedding F (ι ⟨e, h⟩) else 0
  refine ⟨∑ e ∈ S, algebraMap F R (c e) * E e, fun e he e' he' h => ?_⟩
  have hval : ∀ e'' ∈ S, e'' (∑ e ∈ S, algebraMap F R (c e) * E e) = c e'' := by
    intro e'' he''
    rw [map_sum, Finset.sum_eq_single e'']
    · rw [map_mul, AlgHom.commutes, hEe, mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    · intro b hb hbe
      rw [map_mul, hEe' b hb e'' he'' (Ne.symm hbe), mul_zero]
    · intro h
      exact absurd he'' h
  simp only at h
  rw [hval e he, hval e' he'] at h
  simp only [c, dif_pos (Finset.mem_coe.1 he), dif_pos (Finset.mem_coe.1 he')] at h
  have := ι.injective ((Infinite.natEmbedding F).injective h)
  exact congrArg Subtype.val this

end Separating

/-! ### Finiteness of the base change -/

section BaseChange

variable {k : Type*} [Field k] (F : Type*) [Field F] [Algebra k F]
variable {B : Type*} [CommRing B] [Algebra k B] {A : Type*} [CommRing A] [Algebra k A]

/-- The scalar extension `F ⊗_k B → F ⊗_k A` of a finite `k`-algebra map `φ : B → A` is finite. -/
theorem nonflat_baseChange_finite (φ : B →ₐ[k] A) (hφ : (φ : B →+* A).Finite) :
    ((Algebra.TensorProduct.map (AlgHom.id F F) φ : F ⊗[k] B →ₐ[F] F ⊗[k] A) :
      F ⊗[k] B →+* F ⊗[k] A).Finite := by
  let : Algebra B A := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite B A := hφ
  exact ScalarExtension.moduleFinite k F B A

end BaseChange

/-! ### Rigid embeddings and the rigid fibre -/

section RigidEmbedding

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- An **isometric embedding** of the completed residue field `ℋ(s)` of a point `s ∈ (Spec B)^an`
into a valued field `F`, compatible with the `k`-algebra structures (`def:nf-rigid-data`). A
**rigid datum** for `s` is such an embedding into a complete, algebraically closed, nontrivially
valued field `F`; `EnvelopeProperty.nonflatRigidEmbedding` constructs one. -/
structure NonflatRigidEmbedding (s : Berk k B) (F : Type*) [NormedField F] [Algebra k F] where
  /-- The embedding `ℋ(s) → F`. -/
  toRingHom : H s →+* F
  /-- It is isometric. -/
  norm_map : ∀ c : H s, ‖toRingHom c‖ = ‖c‖
  /-- It is compatible with the `k`-algebra structures. -/
  map_algebraMap : ∀ c : k, toRingHom (algebraMap k (H s) c) = algebraMap k F c

namespace NonflatRigidEmbedding

variable {s : Berk k B} {F : Type*} [NormedField F] [Algebra k F] (τ : NonflatRigidEmbedding s F)

/-- The norm of `F` is trivial on `k`. -/
theorem norm_algebraMap (τ : NonflatRigidEmbedding s F) {c : k} (hc : c ≠ 0) :
    ‖algebraMap k F c‖ = 1 := by
  rw [← τ.map_algebraMap, τ.norm_map, norm_algebraMap_k_H s hc]

/-- The composite `B → ℋ(s) → F`. -/
def algHom : B →ₐ[k] F where
  toRingHom := τ.toRingHom.comp s.toH
  commutes' c := τ.map_algebraMap c

/-- `b(s) = τ(b mod s)`. -/
theorem algHom_apply (b : B) : τ.algHom b = τ.toRingHom (s.toH b) := rfl

/-- `‖b(s)‖ = |b|_s`. -/
theorem nnnorm_algHom (b : B) : ‖τ.algHom b‖₊ = s.val b := by
  rw [algHom_apply, ← nnnorm_toH s b]
  exact NNReal.eq (τ.norm_map _)

/-- The evaluation `ξ : B_F = F ⊗_k B → F`, `c ⊗ b ↦ c · b(s)`. -/
def baseEval : F ⊗[k] B →ₐ[F] F :=
  Algebra.TensorProduct.lift (AlgHom.id F F) τ.algHom fun _ _ => Commute.all _ _

/-- `ξ(c ⊗ b) = c · b(s)`. -/
@[simp]
theorem baseEval_tmul (c : F) (b : B) : τ.baseEval (c ⊗ₜ b) = c * τ.algHom b := rfl

variable [IsUltrametricDist F]

/-- The `F`-rational point `ξ` of `(Spec B_F)^an` over `s` (`def:nf-rigid-data`). -/
def basePoint : Berk k (F ⊗[k] B) :=
  nonflatRationalPoint (fun _ hc => τ.norm_algebraMap hc) τ.baseEval

/-- `|q|_ξ = ‖ξ(q)‖`. -/
theorem basePoint_val_apply (q : F ⊗[k] B) : τ.basePoint.val q = ‖τ.baseEval q‖₊ :=
  nonflatRationalPoint_val_apply _ _ q

/-- `|c ⊗ b|_ξ = ‖c‖ |b|_s`. -/
theorem basePoint_val_tmul (c : F) (b : B) : τ.basePoint.val (c ⊗ₜ b) = ‖c‖₊ * s.val b := by
  rw [basePoint_val_apply, baseEval_tmul, nnnorm_mul, nnnorm_algHom]

/-- `ξ` restricts to `s` on `B`. -/
theorem comap_includeRight_basePoint :
    comap (Algebra.TensorProduct.includeRight : B →ₐ[k] F ⊗[k] B) τ.basePoint = s := by
  apply Berk.ext_val
  intro b
  rw [comap_val_apply, Algebra.TensorProduct.includeRight_apply, basePoint_val_tmul, nnnorm_one,
    one_mul]

variable {A : Type*} [CommRing A] [Algebra k A] (φ : B →ₐ[k] A)

/-- The **rigid fibre** `π_F^{-1}(ξ) ⊆ (Spec A_F)^an`, `A_F = F ⊗_k A`. -/
def fibre : Set (Berk k (F ⊗[k] A)) :=
  comap ((Algebra.TensorProduct.map (AlgHom.id F F) φ).restrictScalars k) ⁻¹' {τ.basePoint}

/-- Membership in the rigid fibre: `z` lies over `ξ`. -/
theorem mem_fibre_iff {z : Berk k (F ⊗[k] A)} :
    z ∈ τ.fibre φ ↔
      comap ((Algebra.TensorProduct.map (AlgHom.id F F) φ).restrictScalars k) z = τ.basePoint :=
  Iff.rfl

/-- `lem:nf-rigid-fibre`(2): the rigid fibre is finite. -/
theorem finite_fibre (hφ : (φ : B →+* A).Finite) : (τ.fibre φ).Finite :=
  finite_preimage_comap_singleton ((Algebra.TensorProduct.map (AlgHom.id F F) φ).restrictScalars k)
    (nonflat_baseChange_finite F φ hφ) _

/-- Points of the rigid fibre restrict to the norm of `F`. -/
theorem val_algebraMap_of_mem_fibre {z : Berk k (F ⊗[k] A)} (hz : z ∈ τ.fibre φ) (c : F) :
    z.val (algebraMap F (F ⊗[k] A) c) = ‖c‖₊ := by
  have h := congrArg (fun y : Berk k (F ⊗[k] B) => y.val (algebraMap F (F ⊗[k] B) c)) hz
  simp only [comap_val_apply, AlgHom.coe_restrictScalars', AlgHom.commutes] at h
  rw [h, basePoint, nonflatRationalPoint_val_algebraMap]

/-- `lem:nf-rigid-fibre`(2): points of the rigid fibre are `F`-rational. -/
theorem exists_val_sub_eq_zero_of_mem_fibre [IsAlgClosed F] (hφ : (φ : B →+* A).Finite)
    {z : Berk k (F ⊗[k] A)} (hz : z ∈ τ.fibre φ) (b : F ⊗[k] A) :
    ∃ c : F, z.val (b - algebraMap F (F ⊗[k] A) c) = 0 :=
  nonflat_exists_val_sub_eq_zero_of_comap_eq (fun _ hc => τ.norm_algebraMap hc)
    (Algebra.TensorProduct.map (AlgHom.id F F) φ) (nonflat_baseChange_finite F φ hφ).to_isIntegral
    τ.baseEval hz b

/-- The evaluation `b ↦ b(z)` at a point `z` of the rigid fibre: an `F`-algebra map
`A_F → F` (`lem:nf-rigid-fibre`(2)). -/
def fibreEval [IsAlgClosed F] (hφ : (φ : B →+* A).Finite) {z : Berk k (F ⊗[k] A)}
    (hz : z ∈ τ.fibre φ) : F ⊗[k] A →ₐ[F] F :=
  nonflatPointEval z (τ.val_algebraMap_of_mem_fibre φ hz)
    (τ.exists_val_sub_eq_zero_of_mem_fibre φ hφ hz)

variable [IsAlgClosed F] (hφ : (φ : B →+* A).Finite) {z : Berk k (F ⊗[k] A)} (hz : z ∈ τ.fibre φ)

/-- `|b|_z = ‖b(z)‖`. -/
theorem val_eq_nnnorm_fibreEval (b : F ⊗[k] A) : z.val b = ‖τ.fibreEval φ hφ hz b‖₊ :=
  val_eq_nnnorm_nonflatPointEval _ _ _ b

/-- `b - b(z)` lies in the kernel of `z`. -/
theorem fibreEval_val_sub (b : F ⊗[k] A) :
    z.val (b - algebraMap F (F ⊗[k] A) (τ.fibreEval φ hφ hz b)) = 0 :=
  nonflatPointEval_val_sub _ _ _ b

/-- A point of the rigid fibre is the rational point of its evaluation. -/
theorem eq_nonflatRationalPoint_fibreEval :
    z = nonflatRationalPoint (fun _ hc => τ.norm_algebraMap hc) (τ.fibreEval φ hφ hz) :=
  eq_nonflatRationalPoint_nonflatPointEval _ _ _ _

/-- The evaluation at a point of the rigid fibre lies over `ξ`. -/
theorem fibreEval_comp :
    (τ.fibreEval φ hφ hz).comp (Algebra.TensorProduct.map (AlgHom.id F F) φ) = τ.baseEval := by
  apply nonflatRationalPoint_injective (fun _ hc => τ.norm_algebraMap hc)
  rw [← comap_nonflatRationalPoint, ← τ.eq_nonflatRationalPoint_fibreEval φ hφ hz]
  exact hz

/-- Points of the rigid fibre are determined by their evaluations. -/
theorem eq_of_fibreEval_eq {z' : Berk k (F ⊗[k] A)} (hz' : z' ∈ τ.fibre φ)
    (h : τ.fibreEval φ hφ hz = τ.fibreEval φ hφ hz') : z = z' := by
  rw [τ.eq_nonflatRationalPoint_fibreEval φ hφ hz, τ.eq_nonflatRationalPoint_fibreEval φ hφ hz', h]

omit [IsAlgClosed F] in
include hz in
/-- The restriction `r(z)` of a point of the rigid fibre lies over `s`. -/
theorem comap_comap_includeRight_of_mem_fibre :
    comap φ (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) z) = s := by
  rw [← τ.comap_includeRight_basePoint, ← hz]
  apply Berk.ext_val
  intro b
  simp only [comap_val_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.coe_restrictScalars', Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [IsAlgClosed F] in
/-- **Lifts of finite fibre points** (`lem:nf-rigid-fibre`(3), algebraic form). Let `F` be
algebraically closed and `φ : B → A` finite. For every point `y` of `(Spec A)^an` over `s` there is
a `k`-algebra map `τ' : A → F` extending `B → ℋ(s) → F` with `‖τ'(a)‖ = |a|_y`. The kernel `m` of
`ℋ(s) ⊗_B A → ℋ(y)` is maximal, the field `L = (ℋ(s) ⊗_B A)/m` is finite over `ℋ(s)` and carries
the absolute value pulled back from `ℋ(y)`; an `ℋ(s)`-embedding `L → F` exists as `F` is
algebraically closed, and it is isometric because the absolute value of the complete field `ℋ(s)`
extends uniquely to the finite extension `L`. -/
theorem exists_algHom_of_comap_eq [IsAlgClosed F] (hφ : (φ : B →+* A).Finite) {y : Berk k A}
    (hy : comap φ y = s) :
    ∃ τ' : A →ₐ[k] F, τ'.comp φ = τ.algHom ∧ ∀ a, ‖τ' a‖₊ = y.val a := by
  classical
  let : Algebra B A := (φ : B →+* A).toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have hφe : IsScalarTower.toAlgHom k B A = φ := AlgHom.ext fun _ => rfl
  have : Module.Finite B A := hφ
  have h : comap (IsScalarTower.toAlgHom k B A) y = s := by rw [hφe]; exact hy
  set m := RingHom.ker (Berk.fibreHom h)
  have : m.IsMaximal := Berk.isMaximal_ker_fibreHom h
  let L := H s ⊗[B] A ⧸ m
  let : Field L := Ideal.Quotient.field m
  have : Module.Finite (H s) L := Module.Finite.trans (H s ⊗[B] A) L
  have : Algebra.IsAlgebraic (H s) L := Algebra.IsAlgebraic.of_finite (H s) L
  let κ : L →+* H y := Ideal.Quotient.lift m (Berk.fibreHom h) fun _ ha => ha
  let w : Valuation L ℝ≥0 := (NormedField.valuation (K := H y)).comap κ
  have hκ : ∀ q : H s ⊗[B] A, κ (Ideal.Quotient.mk m q) = Berk.fibreHom h q := fun q =>
    Ideal.Quotient.lift_mk _ _ _
  have hw : ∀ c : H s, w (algebraMap (H s) L c) = ‖c‖₊ := by
    intro c
    change ‖κ (Ideal.Quotient.mk m (algebraMap (H s) (H s ⊗[B] A) c))‖₊ = _
    rw [hκ, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Berk.fibreHom_tmul_one]
    exact NNReal.eq (H.norm_map _ h c)
  let : NormedAlgebra (H s) F :=
    { τ.toRingHom.toAlgebra with
      norm_smul_le := fun c x => by
        change ‖τ.toRingHom c * x‖ ≤ ‖c‖ * ‖x‖
        rw [norm_mul, τ.norm_map] }
  have hτalg : ∀ c : H s, algebraMap (H s) F c = τ.toRingHom c := fun _ => rfl
  let e : L →ₐ[H s] F := IsAlgClosed.lift
  have he : ∀ a, ‖e a‖₊ = w a := fun a => norm_algebraic_algHom e w hw a
  let τ₀ : A →+* F := e.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] H s ⊗[B] A).toRingHom)
  have hτ₀ : ∀ a, τ₀ a = e (Ideal.Quotient.mk m ((1 : H s) ⊗ₜ a)) := fun _ => rfl
  have hcomp : ∀ b : B, τ₀ (φ b) = τ.algHom b := by
    intro b
    have hb : (1 : H s) ⊗ₜ[B] (φ b) = algebraMap (H s) (H s ⊗[B] A) (s.toH b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact (Berk.algebraMap_tmul_one_eq s b).symm
    rw [hτ₀, hb, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      AlgHom.commutes, hτalg, algHom_apply]
  refine ⟨{ τ₀ with commutes' := fun c => ?_ }, AlgHom.ext fun b => hcomp b, fun a => ?_⟩
  · change τ₀ (algebraMap k A c) = algebraMap k F c
    rw [← φ.commutes, hcomp, AlgHom.commutes]
  · change ‖τ₀ a‖₊ = y.val a
    rw [hτ₀, he]
    change ‖κ (Ideal.Quotient.mk m ((1 : H s) ⊗ₜ a))‖₊ = y.val a
    rw [hκ, Berk.fibreHom_one_tmul, nnnorm_toH]

omit [IsAlgClosed F] in
/-- **Surjectivity of `r : π_F^{-1}(ξ) → π^{-1}(s)`** (`lem:nf-rigid-fibre`(3)): for `F`
algebraically closed and `φ` finite, every point `y` over `s` is the restriction to `A` of a point
`z` of the rigid fibre, namely the rational point of `c ⊗ a ↦ c · τ'(a)`. -/
theorem exists_mem_fibre_comap_includeRight_eq [IsAlgClosed F] (hφ : (φ : B →+* A).Finite)
    {y : Berk k A} (hy : comap φ y = s) :
    ∃ z ∈ τ.fibre φ, comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A) z = y := by
  obtain ⟨τ', hτ'φ, hτ'⟩ := τ.exists_algHom_of_comap_eq φ hφ hy
  set E : F ⊗[k] A →ₐ[F] F :=
    Algebra.TensorProduct.lift (AlgHom.id F F) τ' fun _ _ => Commute.all _ _
  refine ⟨nonflatRationalPoint (fun _ hc => τ.norm_algebraMap hc) E, ?_, ?_⟩
  · rw [mem_fibre_iff, comap_nonflatRationalPoint]
    congr 1
    apply AlgHom.ext
    intro q
    induction q using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add q q' hq hq' => simp only [map_add, hq, hq']
    | tmul c b =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, E,
        Algebra.TensorProduct.lift_tmul, baseEval_tmul]
      rw [← AlgHom.comp_apply τ' φ, hτ'φ]
  · apply Berk.ext_val
    intro a
    rw [comap_val_apply, nonflatRationalPoint_val_apply, Algebra.TensorProduct.includeRight_apply]
    simp only [E, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]
    exact hτ' a

omit [IsAlgClosed F] in
/-- `lem:nf-rigid-fibre`(3) as a statement on sets: `r` maps the rigid fibre onto `π^{-1}(s)`. -/
theorem surjOn_comap_includeRight_fibre [IsAlgClosed F] (hφ : (φ : B →+* A).Finite) :
    Set.SurjOn (comap (Algebra.TensorProduct.includeRight : A →ₐ[k] F ⊗[k] A)) (τ.fibre φ)
      (comap φ ⁻¹' {s}) := fun y hy => by
  obtain ⟨z, hz, hzy⟩ := τ.exists_mem_fibre_comap_includeRight_eq φ hφ (Set.mem_singleton_iff.1 hy)
  exact ⟨z, hz, hzy⟩

/-- **A separating element** (`lem:nf-rigid-fibre`(4)): some `b ∈ A_F` takes pairwise distinct
values `b(z)` at the points `z` of the rigid fibre. -/
theorem exists_fibreEval_injective :
    ∃ b : F ⊗[k] A, ∀ (z₁ : Berk k (F ⊗[k] A)) (h₁ : z₁ ∈ τ.fibre φ) (z₂ : Berk k (F ⊗[k] A))
      (h₂ : z₂ ∈ τ.fibre φ), τ.fibreEval φ hφ h₁ b = τ.fibreEval φ hφ h₂ b → z₁ = z₂ := by
  classical
  set S : Finset (F ⊗[k] A →ₐ[F] F) := ((τ.finite_fibre φ hφ).toFinset.attach).image fun z =>
    τ.fibreEval φ hφ ((τ.finite_fibre φ hφ).mem_toFinset.1 z.2)
  have hS : ∀ (z : Berk k (F ⊗[k] A)) (hz : z ∈ τ.fibre φ), τ.fibreEval φ hφ hz ∈ S := by
    intro z hz
    exact Finset.mem_image.2 ⟨⟨z, (τ.finite_fibre φ hφ).mem_toFinset.2 hz⟩,
      Finset.mem_attach _ _, rfl⟩
  obtain ⟨b, hb⟩ := nonflat_exists_injOn_algHom S
  refine ⟨b, fun z₁ h₁ z₂ h₂ h => τ.eq_of_fibreEval_eq φ hφ h₁ h₂ ?_⟩
  exact hb (Finset.mem_coe.2 (hS z₁ h₁)) (Finset.mem_coe.2 (hS z₂ h₂)) h

end NonflatRigidEmbedding

end RigidEmbedding

/-! ### The rigid field of a point: a nontrivially valued extension of `ℋ(s)` -/

section GaussRigidField

open Polynomial

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- The **rigid field** `F_s` of `s ∈ (Spec B)^an` (`def:nf-rigid-data`): the completed algebraic
closure of the completed residue field `ℋ(s')` of the Gauss point `s' = η_{s,1/2}` of radius `1/2`
over `s` on `Spec B[w]`. It is complete, algebraically closed and nontrivially valued, and
`ℋ(s) → ℋ(s') → F_s` is isometric. -/
abbrev nonflatRigidField (s : Berk k B) : Type _ :=
  CompleteAlgebraicClosure (H (gauss s (1 / 2)))

/-- The Gauss point `η_{s,r}` lies over `s` (`Berk.proj_gauss`, with `proj` unfolded). -/
theorem nonflat_comap_CAlgHom_gauss (s : Berk k B) (r : ℝ≥0) :
    comap (CAlgHom : B →ₐ[k] B[X]) (gauss s r) = s :=
  proj_gauss s r

/-- The isometric embedding `ℋ(s) → ℋ(η_{s,1/2}) → F_s`: the rigid datum of `s`. -/
def nonflatRigidEmbedding (s : Berk k B) : NonflatRigidEmbedding s (nonflatRigidField s) where
  toRingHom := (algebraMap (H (gauss s (1 / 2))) (nonflatRigidField s)).comp
    (H.map (CAlgHom : B →ₐ[k] B[X]) (nonflat_comap_CAlgHom_gauss s (1 / 2)))
  norm_map c := by
    rw [RingHom.comp_apply, completeAlgebraicClosure_norm_algebraMap, H.norm_map]
  map_algebraMap c := by
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (H (gauss s (1 / 2)))
      (nonflatRigidField s)]
    congr 1
    change H.map (CAlgHom : B →ₐ[k] B[X]) (nonflat_comap_CAlgHom_gauss s (1 / 2))
        (s.toH (algebraMap k B c)) =
      (gauss s (1 / 2)).toH (algebraMap k B[X] c)
    rw [H.map_toH, AlgHom.commutes]

/-- The rigid datum of `s` is `ℋ(s) → ℋ(η_{s,1/2}) → F_s`. -/
theorem nonflatRigidEmbedding_toRingHom_apply (s : Berk k B) (c : H s) :
    (nonflatRigidEmbedding s).toRingHom c = algebraMap (H (gauss s (1 / 2))) (nonflatRigidField s)
      (H.map (CAlgHom : B →ₐ[k] B[X]) (nonflat_comap_CAlgHom_gauss s (1 / 2)) c) := rfl

/-- The norm of `F_s` is trivial on `k` (the hypothesis `hF` of `Berkovich/LineFibrePieces`). -/
theorem nonflatRigidField_norm_algebraMap (s : Berk k B) :
    ∀ c : k, c ≠ 0 → ‖algebraMap k (nonflatRigidField s) c‖ = 1 :=
  fun _ hc => (nonflatRigidEmbedding s).norm_algebraMap hc

/-- **`F_s` is nontrivially valued**: the image `κ⁻¹` of the coordinate `w`, `|w|_{s'} = 1/2`, has
norm `1/2`, so `κ` has norm `2 > 1` (the hypothesis `hκ` of `Berkovich/LineFibrePieces`). -/
theorem nonflatRigidField_exists_one_lt_norm (s : Berk k B) :
    ∃ κ : nonflatRigidField s, 1 < ‖κ‖ := by
  refine ⟨(algebraMap (H (gauss s (1 / 2))) (nonflatRigidField s) ((gauss s (1 / 2)).toH X))⁻¹, ?_⟩
  rw [norm_inv, completeAlgebraicClosure_norm_algebraMap, norm_toH, gauss_val_X]
  norm_num

end GaussRigidField

end EnvelopeProperty
