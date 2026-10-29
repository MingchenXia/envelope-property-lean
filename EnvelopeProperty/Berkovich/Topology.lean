/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Basic

/-!
# Topology of the analytification of an affine variety

Let `k` be a field with the trivial absolute value and `A` a commutative `k`-algebra. This file
establishes the basic topological properties of the analytification `Berk k A = (Spec A)^an`
(Fang–Han–Xia, *The envelope property for unibranch projective varieties*, §2.1 and §5) that the
arguments of §5 use without comment.

* `Berk.isClosedEmbedding_toFun`: `Berk k A` is a closed subspace of `A → ℝ≥0`; its image is the
  set of functions satisfying the (closed) axioms of a multiplicative ultrametric seminorm trivial
  on `k`. Conversely, `Berk.ofFun` builds a point from such a function.
* `Berk.exists_abs_le_pow_of_adjoin_eq_top`, `Berk.abs_le_max_pow_of_adjoin_eq_top`: the
  polynomial estimate `|f|_x ≤ max(1, max_l |z_l|_x) ^ d` for generators `z_l` of `A`, the
  degree `d` depending only on `f`. This is the estimate behind FHX Lemma 5.8(1) and behind the
  fact (§5.2, §5.3, `lem:polyhedral-neighborhoods`) that Fubini–Study sublevel sets and polynomial
  hulls are compact, "since they lie in closed polydiscs".
* `Berk.isCompact_setOf_forall_abs_le`: closed polydiscs `{x | |s|_x ≤ R, s ∈ S}` for a
  generating set `S` are compact (Tychonoff); conversely every compact set lies in a polydisc
  (`Berk.exists_forall_abs_le_of_isCompact`).
* Instances: for `A` of finite type, `Berk k A` is locally compact and σ-compact; for `A`
  countable (e.g. `k` countable and `A` of finite type, `countable_of_finiteType`) it is second
  countable. These are used in the proof of `lem:polyhedral-neighborhoods`(2).
* `Berk.rpow t ht x`: the scaling action `|·|_{t·x} = |·|_x ^ t` of `ℝ_{>0}` (FHX §2.1,
  `eq:scaling-action`), with `log|f|(t·x) = t · log|f|(x)`; `Berk.rpowHomeomorph` shows it acts
  by homeomorphisms.
* `Berk.zeroScale x`: the "zero scaling" `|f| = 0` if `|f|_x = 0` and `|f| = 1` otherwise (the
  trivial valuation of the residue field at the support of `x`), with `zeroScale triv = triv`.
* Basic open and closed sets defined by `|f|` and `log|f|`.
-/

open scoped NNReal ENNReal Topology

open Filter Set Topology

noncomputable section

namespace EnvelopeProperty

/-- A finitely generated algebra over a countable field is countable: it is a quotient of a
polynomial ring in finitely many variables. -/
theorem countable_of_finiteType (k : Type*) [Field k] [Countable k] (A : Type*) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance :
    Algebra.FiniteType k A)
  have : Countable (AddMonoidAlgebra k (Fin n →₀ ℕ)) :=
    Function.Surjective.countable (f := AddMonoidAlgebra.ofCoeff) fun p => ⟨p.coeff, rfl⟩
  have : Countable (MvPolynomial (Fin n) k) := this
  exact hf.countable

namespace Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### Points from functions; the image of the embedding into `A → ℝ≥0` -/

/-- The point of `Berk k A` defined by a function `φ : A → ℝ≥0` satisfying the axioms of a
multiplicative ultrametric seminorm trivial on `k`. -/
def ofFun (φ : A → ℝ≥0) (h0 : φ 0 = 0) (h1 : φ 1 = 1) (hmul : ∀ f g, φ (f * g) = φ f * φ g)
    (hadd : ∀ f g, φ (f + g) ≤ max (φ f) (φ g))
    (halg : ∀ c : k, c ≠ 0 → φ (algebraMap k A c) = 1) : Berk k A where
  val :=
    { toFun := φ
      map_zero' := h0
      map_one' := h1
      map_mul' := hmul
      map_add_le_max' := hadd }
  val_algebraMap := halg

@[simp]
theorem ofFun_val_apply (φ : A → ℝ≥0) (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    (hmul : ∀ f g, φ (f * g) = φ f * φ g) (hadd : ∀ f g, φ (f + g) ≤ max (φ f) (φ g))
    (halg : ∀ c : k, c ≠ 0 → φ (algebraMap k A c) = 1) (f : A) :
    (ofFun φ h0 h1 hmul hadd halg).val f = φ f :=
  rfl

@[simp]
theorem toFun_apply (x : Berk k A) (f : A) : toFun x f = x.val f := rfl

/-- Two points agree if they have the same absolute values. -/
theorem ext_val {x y : Berk k A} (h : ∀ f, x.val f = y.val f) : x = y :=
  Berk.ext (Valuation.ext h)

variable (k A) in
/-- The set of functions `φ : A → ℝ≥0` with `φ 0 = 0`, `φ 1 = 1`, `φ (f g) = φ f φ g`,
`φ (f + g) ≤ max (φ f) (φ g)` and `φ c = 1` for `c ∈ kˣ`: the image of `Berk k A`. -/
def rangeSet : Set (A → ℝ≥0) :=
  {φ | φ 0 = 0 ∧ φ 1 = 1 ∧ (∀ f g, φ (f * g) = φ f * φ g) ∧
    (∀ f g, φ (f + g) ≤ max (φ f) (φ g)) ∧ ∀ c : k, c ≠ 0 → φ (algebraMap k A c) = 1}

theorem range_toFun : range (toFun : Berk k A → A → ℝ≥0) = rangeSet k A := by
  ext φ
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val.map_zero, x.val.map_one, x.val.map_mul, x.val.map_add, x.val_algebraMap⟩
  · rintro ⟨h0, h1, hmul, hadd, halg⟩
    exact ⟨ofFun φ h0 h1 hmul hadd halg, rfl⟩

theorem isClosed_rangeSet : IsClosed (rangeSet k A) := by
  have e : rangeSet k A =
      {φ : A → ℝ≥0 | φ 0 = 0} ∩ {φ | φ 1 = 1} ∩ (⋂ f, ⋂ g, {φ | φ (f * g) = φ f * φ g}) ∩
        (⋂ f, ⋂ g, {φ | φ (f + g) ≤ max (φ f) (φ g)}) ∩
        (⋂ c : k, ⋂ (_ : c ≠ 0), {φ | φ (algebraMap k A c) = 1}) := by
    ext φ
    simp only [rangeSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [e]
  refine ((((isClosed_eq (continuous_apply _) continuous_const).inter
    (isClosed_eq (continuous_apply _) continuous_const)).inter
    (isClosed_iInter fun f => isClosed_iInter fun g => isClosed_eq (continuous_apply (f * g))
      ((continuous_apply f).mul (continuous_apply g)))).inter
    (isClosed_iInter fun f => isClosed_iInter fun g => isClosed_le (continuous_apply (f + g))
      ((continuous_apply f).max (continuous_apply g)))).inter
    (isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply _) continuous_const)

theorem isClosed_range_toFun : IsClosed (range (toFun : Berk k A → A → ℝ≥0)) := by
  rw [range_toFun]
  exact isClosed_rangeSet

/-- The analytification is a closed subspace of the product space `A → ℝ≥0`. -/
theorem isClosedEmbedding_toFun : IsClosedEmbedding (toFun : Berk k A → A → ℝ≥0) :=
  ⟨isEmbedding_toFun, isClosed_range_toFun⟩

@[fun_prop]
theorem continuous_val_apply (f : A) : Continuous fun x : Berk k A => x.val f :=
  continuous_abs f

/-! ### Basic open and closed sets -/

theorem isOpen_setOf_abs_ne_zero (f : A) : IsOpen {x : Berk k A | x.val f ≠ 0} :=
  isOpen_ne_fun (continuous_abs f) continuous_const

theorem isClosed_setOf_abs_eq_zero (f : A) : IsClosed {x : Berk k A | x.val f = 0} :=
  isClosed_eq (continuous_abs f) continuous_const

theorem isOpen_setOf_abs_lt (f : A) (R : ℝ≥0) : IsOpen {x : Berk k A | x.val f < R} :=
  isOpen_lt (continuous_abs f) continuous_const

theorem isOpen_setOf_lt_abs (f : A) (R : ℝ≥0) : IsOpen {x : Berk k A | R < x.val f} :=
  isOpen_lt continuous_const (continuous_abs f)

theorem isClosed_setOf_abs_le (f : A) (R : ℝ≥0) : IsClosed {x : Berk k A | x.val f ≤ R} :=
  isClosed_le (continuous_abs f) continuous_const

theorem isClosed_setOf_le_abs (f : A) (R : ℝ≥0) : IsClosed {x : Berk k A | R ≤ x.val f} :=
  isClosed_le continuous_const (continuous_abs f)

theorem isOpen_setOf_logAbs_lt (f : A) (c : EReal) : IsOpen {x : Berk k A | logAbs f x < c} :=
  isOpen_lt (continuous_logAbs f) continuous_const

theorem isOpen_setOf_lt_logAbs (f : A) (c : EReal) : IsOpen {x : Berk k A | c < logAbs f x} :=
  isOpen_lt continuous_const (continuous_logAbs f)

theorem isClosed_setOf_logAbs_le (f : A) (c : EReal) :
    IsClosed {x : Berk k A | logAbs f x ≤ c} :=
  isClosed_le (continuous_logAbs f) continuous_const

theorem isClosed_setOf_le_logAbs (f : A) (c : EReal) :
    IsClosed {x : Berk k A | c ≤ logAbs f x} :=
  isClosed_le continuous_const (continuous_logAbs f)

/-- Closed polydiscs (for any family of functions) are closed. -/
theorem isClosed_setOf_forall_abs_le (S : Set A) (R : ℝ≥0) :
    IsClosed {x : Berk k A | ∀ s ∈ S, x.val s ≤ R} := by
  have e : {x : Berk k A | ∀ s ∈ S, x.val s ≤ R} = ⋂ s ∈ S, {x | x.val s ≤ R} := by
    ext; simp
  rw [e]
  exact isClosed_biInter fun s _ => isClosed_setOf_abs_le s R

/-- Open polydiscs (for finitely many functions) are open. -/
theorem isOpen_setOf_forall_abs_lt (S : Finset A) (R : ℝ≥0) :
    IsOpen {x : Berk k A | ∀ s ∈ S, x.val s < R} := by
  have e : {x : Berk k A | ∀ s ∈ S, x.val s < R} = ⋂ s ∈ S, {x | x.val s < R} := by
    ext; simp
  rw [e]
  exact isOpen_biInter_finset fun s _ => isOpen_setOf_abs_lt s R

/-- `log|f| ≤ c` for a real `c` means `|f| ≤ exp c`. -/
theorem logAbs_le_coe_iff (f : A) (x : Berk k A) (c : ℝ) :
    logAbs f x ≤ (c : EReal) ↔ x.val f ≤ (Real.exp c).toNNReal := by
  have hne : (Real.exp c).toNNReal ≠ 0 := by
    simpa using Real.exp_pos c
  have e : (c : EReal) = ENNReal.log ((Real.exp c).toNNReal : ℝ≥0∞) := by
    rw [ENNReal.log_of_nnreal hne, Real.coe_toNNReal _ (Real.exp_pos c).le, Real.log_exp]
  rw [e, logAbs, ENNReal.log_le_log_iff, ENNReal.coe_le_coe]

/-! ### The polynomial estimate -/

/-- If `|z_i|_x ≤ M` for all `i` and `M ≥ 1`, then `|p(z)|_x ≤ M ^ deg p` for every polynomial
`p` with coefficients in `k`. -/
theorem abs_aeval_le_pow {ι : Type*} (z : ι → A) (x : Berk k A) {M : ℝ≥0} (hM : 1 ≤ M)
    (hz : ∀ i, x.val (z i) ≤ M) (p : MvPolynomial ι k) :
    x.val (MvPolynomial.aeval z p) ≤ M ^ p.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine x.val.map_sum_le fun m hm => ?_
  rw [map_mul, map_prod]
  calc x.val (algebraMap k A (p.coeff m)) * ∏ i ∈ m.support, x.val (z i ^ m i)
      ≤ 1 * ∏ i ∈ m.support, M ^ m i := by
        gcongr with i
        · exact abs_algebraMap_le_one x _
        · rw [map_pow]
          exact pow_le_pow_left₀ zero_le (hz i) _
    _ = M ^ (∑ i ∈ m.support, m i) := by rw [one_mul, Finset.prod_pow_eq_pow_sum]
    _ ≤ M ^ p.totalDegree := pow_le_pow_right₀ hM (MvPolynomial.le_totalDegree hm)

/-- **Polynomial estimate.** If `S` generates the `k`-algebra `A`, then for every `f : A` there is
`d` such that `|f|_x ≤ M ^ d` whenever `M ≥ 1` bounds `|s|_x` for all `s ∈ S`. -/
theorem exists_abs_le_pow_of_adjoin_eq_top {S : Set A} (hS : Algebra.adjoin k S = ⊤) (f : A) :
    ∃ d : ℕ, ∀ (x : Berk k A) (M : ℝ≥0), 1 ≤ M → (∀ s ∈ S, x.val s ≤ M) → x.val f ≤ M ^ d := by
  have hf : f ∈ Algebra.adjoin k S := by
    rw [hS]
    exact Algebra.mem_top
  rw [Algebra.adjoin_eq_range] at hf
  obtain ⟨p, hp⟩ := (AlgHom.mem_range _).1 hf
  refine ⟨p.totalDegree, fun x M hM hx => ?_⟩
  rw [← hp]
  exact abs_aeval_le_pow (k := k) (fun i : S => (i : A)) x hM (fun i => hx i.1 i.2) p

/-- **Polynomial estimate** (FHX Lemma 5.8(1)): for a finite generating set `S` of `A` and
`f : A` there is `d` with `|f|_x ≤ max(1, max_{s ∈ S} |s|_x) ^ d` for all `x`. -/
theorem abs_le_max_pow_of_adjoin_eq_top {S : Finset A}
    (hS : Algebra.adjoin k (S : Set A) = ⊤) (f : A) :
    ∃ d : ℕ, ∀ x : Berk k A, x.val f ≤ (max 1 (S.sup fun s => x.val s)) ^ d := by
  obtain ⟨d, hd⟩ := exists_abs_le_pow_of_adjoin_eq_top hS f
  exact ⟨d, fun x => hd x _ (le_max_left _ _) fun s hs =>
    (Finset.le_sup (f := fun s => x.val s) hs).trans (le_max_right _ _)⟩

/-- **Polynomial estimate** for a finite generating family `z : ι → A`. -/
theorem abs_le_max_pow_of_adjoin_range_eq_top {ι : Type*} [Fintype ι] {z : ι → A}
    (hz : Algebra.adjoin k (range z) = ⊤) (f : A) :
    ∃ d : ℕ, ∀ x : Berk k A, x.val f ≤ (max 1 (Finset.univ.sup fun i => x.val (z i))) ^ d := by
  obtain ⟨d, hd⟩ := exists_abs_le_pow_of_adjoin_eq_top hz f
  refine ⟨d, fun x => hd x _ (le_max_left _ _) ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (Finset.le_sup (f := fun i => x.val (z i)) (Finset.mem_univ i)).trans (le_max_right _ _)

/-! ### Compactness of polydiscs -/

/-- **Closed polydiscs are compact**: if `S` generates the `k`-algebra `A`, then
`{x | |s|_x ≤ R for all s ∈ S}` is compact. -/
theorem isCompact_setOf_forall_abs_le {S : Set A} (hS : Algebra.adjoin k S = ⊤) (R : ℝ≥0) :
    IsCompact {x : Berk k A | ∀ s ∈ S, x.val s ≤ R} := by
  choose d hd using exists_abs_le_pow_of_adjoin_eq_top hS
  rw [isInducing_toFun.isCompact_iff]
  refine (isCompact_univ_pi fun f => isCompact_Icc (a := (0 : ℝ≥0))
    (b := (max 1 R) ^ d f)).of_isClosed_subset
    (isClosedEmbedding_toFun.isClosedMap _ (isClosed_setOf_forall_abs_le S R)) ?_
  rintro _ ⟨x, hx, rfl⟩ f -
  exact ⟨zero_le, hd f x (max 1 R) (le_max_left _ _) fun s hs =>
    (hx s hs).trans (le_max_right _ _)⟩

/-- Closed polydiscs for a finite generating set are compact. -/
theorem isCompact_setOf_forall_abs_le_finset {S : Finset A}
    (hS : Algebra.adjoin k (S : Set A) = ⊤) (R : ℝ≥0) :
    IsCompact {x : Berk k A | ∀ s ∈ S, x.val s ≤ R} :=
  isCompact_setOf_forall_abs_le hS R

/-- A closed set contained in a closed polydisc (for a generating set) is compact. -/
theorem isCompact_of_isClosed_of_forall_abs_le {S : Set A}
    (hS : Algebra.adjoin k S = ⊤) {K : Set (Berk k A)} (hK : IsClosed K) (R : ℝ≥0)
    (hKR : ∀ x ∈ K, ∀ s ∈ S, x.val s ≤ R) : IsCompact K :=
  (isCompact_setOf_forall_abs_le hS R).of_isClosed_subset hK hKR

/-- Logarithmic closed polydiscs `{x | log|s|_x ≤ c for s ∈ S}`, `c ∈ ℝ`, are compact. -/
theorem isCompact_setOf_forall_logAbs_le {S : Set A} (hS : Algebra.adjoin k S = ⊤) (c : ℝ) :
    IsCompact {x : Berk k A | ∀ s ∈ S, logAbs s x ≤ c} := by
  simp only [logAbs_le_coe_iff]
  exact isCompact_setOf_forall_abs_le hS _

/-- Every function `|f|` is bounded on a compact set. -/
theorem exists_abs_le_of_isCompact {K : Set (Berk k A)} (hK : IsCompact K) (f : A) :
    ∃ R : ℝ≥0, ∀ x ∈ K, x.val f ≤ R := by
  obtain ⟨R, hR⟩ := (hK.image (continuous_abs f)).bddAbove
  exact ⟨R, fun x hx => hR ⟨x, hx, rfl⟩⟩

/-- **Every compact set lies in a closed polydisc.** -/
theorem exists_forall_abs_le_of_isCompact {K : Set (Berk k A)} (hK : IsCompact K)
    (S : Finset A) : ∃ R : ℝ≥0, K ⊆ {x | ∀ s ∈ S, x.val s ≤ R} := by
  choose R hR using exists_abs_le_of_isCompact hK
  exact ⟨S.sup R, fun x hx s hs => (hR s x hx).trans (Finset.le_sup hs)⟩

/-- Every compact set lies in the closed polydiscs of all sufficiently large radii. -/
theorem eventually_forall_abs_le_of_isCompact {K : Set (Berk k A)} (hK : IsCompact K)
    (S : Finset A) : ∀ᶠ R in atTop, K ⊆ {x : Berk k A | ∀ s ∈ S, x.val s ≤ R} := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_abs_le_of_isCompact hK S
  filter_upwards [eventually_ge_atTop R₀] with R hR x hx s hs using (hR₀ hx s hs).trans hR

/-! ### Local compactness, σ-compactness and second countability -/

theorem exists_finset_adjoin_eq_top [Algebra.FiniteType k A] :
    ∃ S : Finset A, Algebra.adjoin k (S : Set A) = ⊤ :=
  Algebra.FiniteType.out

/-- For `A` of finite type, every point has a compact neighbourhood (a closed polydisc). -/
instance instWeaklyLocallyCompactSpace [Algebra.FiniteType k A] : WeaklyLocallyCompactSpace (Berk k A) where
  exists_compact_mem_nhds x := by
    obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top (k := k) (A := A)
    refine ⟨_, isCompact_setOf_forall_abs_le hS ((S.sup fun s => x.val s) + 1), ?_⟩
    refine mem_of_superset ((isOpen_setOf_forall_abs_lt S ((S.sup fun s => x.val s) + 1)).mem_nhds
      ?_) ?_
    · exact fun s hs => (Finset.le_sup (f := fun s => x.val s) hs).trans_lt (lt_add_one _)
    · exact fun y hy s hs => (hy s hs).le

/-- For `A` of finite type, `(Spec A)^an` is locally compact. -/
instance instLocallyCompactSpace [Algebra.FiniteType k A] : LocallyCompactSpace (Berk k A) := inferInstance

/-- For `A` of finite type, `(Spec A)^an` is σ-compact: it is the union of the closed polydiscs
of radius `n ∈ ℕ`. -/
instance instSigmaCompactSpace [Algebra.FiniteType k A] : SigmaCompactSpace (Berk k A) := by
  obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top (k := k) (A := A)
  refine ⟨⟨fun n : ℕ => {x | ∀ s ∈ S, x.val s ≤ n}, fun n => isCompact_setOf_forall_abs_le hS _,
    ?_⟩⟩
  refine iUnion_eq_univ_iff.2 fun x => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (S.sup fun s => x.val s)
  exact ⟨n, fun s hs => (Finset.le_sup (f := fun s => x.val s) hs).trans hn⟩

/-- For `A` countable, `(Spec A)^an` is second countable: it embeds in the countable product
`A → ℝ≥0`. -/
instance instSecondCountableTopology [Countable A] : SecondCountableTopology (Berk k A) :=
  isInducing_toFun.secondCountableTopology

/-- For `k` countable and `A` of finite type, `(Spec A)^an` is second countable. -/
instance instSecondCountableTopologyOfCountableField [Countable k] [Algebra.FiniteType k A] :
    SecondCountableTopology (Berk k A) :=
  haveI := countable_of_finiteType k A
  isInducing_toFun.secondCountableTopology

/-! ### The scaling action -/

/-- The **scaling action** of `t > 0` (FHX §2.1, `eq:scaling-action`): `|f|_{t·x} = |f|_x ^ t`;
in additive notation `v ↦ t v`. -/
def rpow (t : ℝ) (ht : 0 < t) (x : Berk k A) : Berk k A :=
  ofFun (fun f => x.val f ^ t) (by simp [NNReal.zero_rpow ht.ne']) (by simp)
    (fun f g => by simp [NNReal.mul_rpow])
    (fun f g => by
      calc x.val (f + g) ^ t ≤ (max (x.val f) (x.val g)) ^ t :=
            NNReal.rpow_le_rpow (x.val.map_add f g) ht.le
        _ = max (x.val f ^ t) (x.val g ^ t) := (NNReal.monotone_rpow_of_nonneg ht.le).map_max)
    (fun c hc => by simp [x.val_algebraMap c hc])

@[simp]
theorem rpow_val_apply (t : ℝ) (ht : 0 < t) (x : Berk k A) (f : A) :
    (rpow t ht x).val f = x.val f ^ t :=
  rfl

theorem logAbs_rpow (t : ℝ) (ht : 0 < t) (f : A) (x : Berk k A) :
    logAbs f (rpow t ht x) = (t : EReal) * logAbs f x := by
  simp only [logAbs, rpow_val_apply, ENNReal.coe_rpow_of_nonneg _ ht.le, ENNReal.log_rpow]

@[fun_prop]
theorem continuous_rpow (t : ℝ) (ht : 0 < t) : Continuous (rpow (k := k) (A := A) t ht) := by
  rw [continuous_iff]
  intro f
  exact (NNReal.continuous_rpow_const ht.le).comp (continuous_abs f)

@[simp]
theorem rpow_one (x : Berk k A) : rpow 1 one_pos x = x := by
  refine ext_val fun f => ?_
  simp

theorem rpow_rpow (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : Berk k A) :
    rpow s hs (rpow t ht x) = rpow (t * s) (mul_pos ht hs) x := by
  refine ext_val fun f => ?_
  simp [NNReal.rpow_mul]

/-- The scaling action is by homeomorphisms. -/
def rpowHomeomorph (t : ℝ) (ht : 0 < t) : Berk k A ≃ₜ Berk k A where
  toFun := rpow t ht
  invFun := rpow t⁻¹ (inv_pos.2 ht)
  left_inv x := by
    refine ext_val fun f => ?_
    simp [NNReal.rpow_rpow_inv ht.ne']
  right_inv x := by
    refine ext_val fun f => ?_
    simp [NNReal.rpow_inv_rpow ht.ne']
  continuous_toFun := continuous_rpow t ht
  continuous_invFun := continuous_rpow t⁻¹ (inv_pos.2 ht)

@[simp]
theorem rpowHomeomorph_apply (t : ℝ) (ht : 0 < t) (x : Berk k A) :
    rpowHomeomorph t ht x = rpow t ht x :=
  rfl

/-- The trivial valuation is fixed by the scaling action. -/
theorem rpow_triv [IsDomain A] (t : ℝ) (ht : 0 < t) : rpow t ht (triv : Berk k A) = triv := by
  refine ext_val fun f => ?_
  by_cases hf : f = 0
  · simp [hf, NNReal.zero_rpow ht.ne']
  · simp [triv_val_of_ne_zero hf]

/-! ### The zero scaling -/

open Classical in
/-- The **zero scaling** of `x`: `|f| = 0` if `|f|_x = 0` and `|f| = 1` otherwise, i.e. the
trivial valuation of the residue field at the support of `x` (the limit of `t·x` as `t → 0⁺`). -/
def zeroScale (x : Berk k A) : Berk k A :=
  ofFun (fun f => if x.val f = 0 then 0 else 1) (by simp) (by simp)
    (fun f g => by
      by_cases hf : x.val f = 0 <;> by_cases hg : x.val g = 0 <;> simp [hf, hg])
    (fun f g => by
      by_cases hfg : x.val (f + g) = 0
      · simp [hfg]
      · have : x.val f ≠ 0 ∨ x.val g ≠ 0 := by
          by_contra! h
          exact hfg (le_antisymm ((x.val.map_add f g).trans (by simp [h.1, h.2])) zero_le)
        rcases this with h | h <;> simp [hfg, h])
    (fun c hc => by simp [x.val_algebraMap c hc])

theorem zeroScale_val_apply (x : Berk k A) (f : A) [Decidable (x.val f = 0)] :
    (zeroScale x).val f = if x.val f = 0 then 0 else 1 := by
  unfold zeroScale
  rw [ofFun_val_apply]
  congr

theorem zeroScale_val_of_eq_zero {x : Berk k A} {f : A} (hf : x.val f = 0) :
    (zeroScale x).val f = 0 := by
  classical
  simp [zeroScale_val_apply, hf]

theorem zeroScale_val_of_ne_zero {x : Berk k A} {f : A} (hf : x.val f ≠ 0) :
    (zeroScale x).val f = 1 := by
  classical
  simp [zeroScale_val_apply, hf]

theorem zeroScale_val_eq_zero_iff (x : Berk k A) (f : A) :
    (zeroScale x).val f = 0 ↔ x.val f = 0 := by
  by_cases hf : x.val f = 0
  · simp [zeroScale_val_of_eq_zero hf, hf]
  · simp [zeroScale_val_of_ne_zero hf, hf]

theorem zeroScale_val_le_one (x : Berk k A) (f : A) : (zeroScale x).val f ≤ 1 := by
  by_cases hf : x.val f = 0
  · simp [zeroScale_val_of_eq_zero hf]
  · simp [zeroScale_val_of_ne_zero hf]

theorem logAbs_zeroScale (f : A) (x : Berk k A) [Decidable (x.val f = 0)] :
    logAbs f (zeroScale x) = if x.val f = 0 then ⊥ else 0 := by
  by_cases hf : x.val f = 0
  · simp [logAbs, zeroScale_val_of_eq_zero hf, hf]
  · simp [logAbs, zeroScale_val_of_ne_zero hf, hf]

@[simp]
theorem zeroScale_zeroScale (x : Berk k A) : zeroScale (zeroScale x) = zeroScale x := by
  refine ext_val fun f => ?_
  by_cases hf : x.val f = 0
  · rw [zeroScale_val_of_eq_zero ((zeroScale_val_eq_zero_iff x f).2 hf),
      zeroScale_val_of_eq_zero hf]
  · rw [zeroScale_val_of_ne_zero (mt (zeroScale_val_eq_zero_iff x f).1 hf),
      zeroScale_val_of_ne_zero hf]

@[simp]
theorem zeroScale_rpow (t : ℝ) (ht : 0 < t) (x : Berk k A) :
    zeroScale (rpow t ht x) = zeroScale x := by
  refine ext_val fun f => ?_
  have h : (rpow t ht x).val f = 0 ↔ x.val f = 0 := by
    simp [NNReal.rpow_eq_zero_iff, ht.ne']
  by_cases hf : x.val f = 0
  · rw [zeroScale_val_of_eq_zero (h.2 hf), zeroScale_val_of_eq_zero hf]
  · rw [zeroScale_val_of_ne_zero (mt h.1 hf), zeroScale_val_of_ne_zero hf]

section triv

variable [IsDomain A]

/-- On a domain, the zero scaling of any point is bounded by the trivial valuation. -/
theorem zeroScale_val_le_triv (x : Berk k A) (f : A) :
    (zeroScale x).val f ≤ (triv : Berk k A).val f := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [triv_val_of_ne_zero hf]
    exact zeroScale_val_le_one x f

/-- The trivial valuation is its own zero scaling. -/
@[simp]
theorem zeroScale_triv : zeroScale (triv : Berk k A) = triv := by
  refine ext_val fun f => ?_
  by_cases hf : f = 0
  · simp [hf]
  · rw [triv_val_of_ne_zero hf]
    refine zeroScale_val_of_ne_zero (x := triv) (f := f) ?_
    rw [triv_val_of_ne_zero hf]
    exact one_ne_zero

end triv

end Berk

end EnvelopeProperty
