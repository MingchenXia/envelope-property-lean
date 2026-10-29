/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Chart

/-!
# Bigraded points: the model of `(ℙ^M × ℙ^{M'})^an`

Let `k` be a field with the trivial absolute value and
`R_{M,M'} = k[x₀, …, x_M, y₀, …, y_{M'}]`, modelled as
`MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k` (`Sum.inl j ↦ xⱼ`, `Sum.inr m ↦ y_m`), bigraded by
`deg xⱼ = (1, 0)` and `deg y_m = (0, 1)` (the weights `EnvelopeProperty.biWeight`); the
bihomogeneous component of bidegree `(a, b)` of `F` is Mathlib's
`weightedHomogeneousComponent (biWeight M M') (a, b) F`.

This file implements the blueprint nodes `def:pg-bigraded` and `lem:pg-bigraded-extension` of
`projective-general.tex` (subsection "Blowups of projective varieties"), the model in which the
blowups `X' → X` of Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
Corollary 5.26 (`cor:normal-weak-global`) are analytified (`X'^an` is modelled by bigraded normalized seminorms on `R_{M,M'}`). It is the two-grading analogue of the
model `ProjBerk` of `(ℙⁿ)^an` (`EnvelopeProperty.Projective.Basic`) and of the graded extension
`ProjBerk.ofGradedNorm` (`EnvelopeProperty.Projective.Chart`, `lem:bj-graded-extension`).

## The model (`def:pg-bigraded`)

A point of `(ℙ^M × ℙ^{M'})^an` is modelled as a point `v ∈ Berk k R_{M,M'}` (a multiplicative
ultrametric seminorm, trivial on `k`) that is

* *bigraded* (`EnvelopeProperty.IsBigraded`): `|F_{(a,b)}|_v ≤ |F|_v` for all bidegrees, which is
  equivalent (ultrametric inequality) to `|F|_v = max_{(a,b)} |F_{(a,b)}|_v`
  (`EnvelopeProperty.IsBigraded.val_eq_sup`); and
* *normalized*: `max_j |xⱼ|_v = 1 = max_m |y_m|_v`.

`EnvelopeProperty.BiProjBerk k M M'` is the type of these points with the subspace topology from
`Berk k R_{M,M'}`. It is compact (a closed subset of the polydisc `|xⱼ|, |y_m| ≤ 1`), Hausdorff,
and second countable for countable `k`; every polynomial has absolute value `≤ 1` at its points
(`BiProjBerk.val_le_one`). The justification of the model (that it is the Berkovich
analytification of `ℙ^M × ℙ^{M'}`) is as for `ProjBerk` and is not formalized
(`rmk:pg-blowup-model`).

## Bigraded extension (`lem:pg-bigraded-extension`)

A family `N p : R_{M,M'} → ℝ≥0`, `p ∈ ℕ × ℕ`, of which only the values on bihomogeneous elements
of bidegree `p` matter, with `N = 1` on nonzero constants, multiplicative and ultrametric on
bihomogeneous elements and `max_j N(xⱼ) = 1 = max_m N(y_m)` (`BiProjBerk.IsBigradedNorm`),
defines the point `|F| = max_p N p (F_p)` of the model (`BiProjBerk.ofBigradedNorm`).
Multiplicativity is the bigraded Gauss lemma: for the lexicographically **smallest** bidegrees
`α₀`, `β₀` at which the maxima for `F`, `G` are attained, `F_{α₀} G_{β₀}` is the unique dominant
term of `(FG)_{α₀ + β₀}` (`BiProjBerk.IsBigradedNorm.mul_le_bigradedFun_mul`; the blueprint uses
the largest bidegrees, either works). Conversely every point is the bigraded extension of its
values on bihomogeneous elements (`BiProjBerk.ofBigradedNorm_val`), and points agreeing on
bihomogeneous elements are equal (`BiProjBerk.ext_of_isWeightedHomogeneous`).

## Projections

`BiProjBerk.fst : BiProjBerk k M M' → ProjBerk k M` and `BiProjBerk.snd : BiProjBerk k M M' →
ProjBerk k M'` are the restrictions along `k[x] → R_{M,M'}` and `k[y] → R_{M,M'}` (`rename Sum.inl`,
`rename Sum.inr`); they are continuous. A form of degree `d` in `x` (resp. `y`) is bihomogeneous of
bidegree `(d, 0)` (resp. `(0, d)`) (`isWeightedHomogeneous_rename_inl`,
`isWeightedHomogeneous_rename_inr`), and the homogeneous components are the bihomogeneous ones
(`weightedHomogeneousComponent_rename_inl`, `weightedHomogeneousComponent_rename_inr`).

## Constructions of points used for blowups

* `BiProjBerk.ofComap φ w`: for a `k`-algebra map `φ : R_{M,M'} → B` and `w ∈ Berk k B` with
  nonzero scales `μ_x = max_j |φ(xⱼ)|_w` (`BiProjBerk.scaleX`), `μ_y = max_m |φ(y_m)|_w`
  (`BiProjBerk.scaleY`), the bigraded extension of `N_{(a,b)}(F) = |φ(F)|_w / (μ_x^a μ_y^b)`
  (`BiProjBerk.isBigradedNorm_comapNorm`). Graph points (`lem:pg-graph-point`, `φ` = substitution
  `y_m ↦ G_m`, `μ_x = 1`, `μ_y = |𝔞|_x`) and blowup-chart points (`lem:pg-blowup-chart`(2), `φ = δ`)
  are of this form.
* `BiProjBerk.trivQuot P`: for a prime `P` containing the bihomogeneous components of its
  elements and neither all `xⱼ` nor all `y_m`, the point `|F| = 0` on `P`, `|F| = 1` off `P`
  (the point `⋆'` of `lem:pg-blowup-basic`(2) for `P = I'`).
* `BiProjBerk.isClosed_setOf_forall_val_eq_zero`: zero loci `{v | |F|_v = 0, F ∈ S}` are closed.

## General lemmas on weighted components

For any weight `w : σ → Γ`: `weightSupport w F` (the finite set of weighted degrees of the
monomials of `F`), `sum_weightSupport` (`F` is the sum of its components),
`weightedHomogeneousComponent_mul` (`(FG)_γ = ∑_{α + β = γ} F_α G_β`) and
`weightedHomogeneousComponent_rename`.
-/

open scoped NNReal ENNReal Topology

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Weighted homogeneous components -/

section WeightedComponent

variable {R : Type*} [CommRing R] {σ : Type*} {Γ : Type*} [AddCommMonoid Γ] [DecidableEq Γ]

variable (w : σ → Γ) in
/-- The finite set of weighted degrees `weight w d` of the monomials `d` of `F`; the weighted
homogeneous components of `F` vanish outside it
(`weightedHomogeneousComponent_eq_zero_of_notMem`). -/
def weightSupport (F : MvPolynomial σ R) : Finset Γ :=
  F.support.image (Finsupp.weight w)

variable {w : σ → Γ}

theorem weightedHomogeneousComponent_eq_zero_of_notMem {F : MvPolynomial σ R} {p : Γ}
    (hp : p ∉ weightSupport w F) : weightedHomogeneousComponent w p F = 0 :=
  weightedHomogeneousComponent_eq_zero' p F fun d hd hdp =>
    hp (Finset.mem_image.2 ⟨d, hd, hdp⟩)

theorem mem_weightSupport_of_ne_zero {F : MvPolynomial σ R} {p : Γ}
    (hp : weightedHomogeneousComponent w p F ≠ 0) : p ∈ weightSupport w F := by
  by_contra h
  exact hp (weightedHomogeneousComponent_eq_zero_of_notMem h)

/-- A polynomial is the sum of its weighted homogeneous components. -/
theorem sum_weightSupport (F : MvPolynomial σ R) :
    ∑ p ∈ weightSupport w F, weightedHomogeneousComponent w p F = F := by
  have h := sum_weightedHomogeneousComponent w F
  rw [finsum_eq_sum_of_support_subset (s := weightSupport w F) _ fun p hp => ?_] at h
  · exact h
  · by_contra h'
    exact hp (weightedHomogeneousComponent_eq_zero_of_notMem h')

/-- The weighted homogeneous component of degree `γ` of a product:
`(FG)_γ = ∑_{α + β = γ} F_α G_β`, the sum over the pairs of weighted degrees of `F` and `G`. -/
theorem weightedHomogeneousComponent_mul (γ : Γ) (F G : MvPolynomial σ R) :
    weightedHomogeneousComponent w γ (F * G) =
      ∑ pq ∈ (weightSupport w F ×ˢ weightSupport w G).filter (fun pq => pq.1 + pq.2 = γ),
        weightedHomogeneousComponent w pq.1 F * weightedHomogeneousComponent w pq.2 G := by
  have e : F * G = ∑ p ∈ weightSupport w F, ∑ q ∈ weightSupport w G,
      weightedHomogeneousComponent w p F * weightedHomogeneousComponent w q G := by
    rw [← Finset.sum_mul_sum, sum_weightSupport, sum_weightSupport]
  rw [e, Finset.sum_filter, Finset.sum_product, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h := (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) p F).mul
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) q G)
  split_ifs with hpq
  · rw [← hpq]
    exact weightedHomogeneousComponent_eq_self h
  · exact h.weightedHomogeneousComponent_ne γ (Ne.symm hpq)

omit [DecidableEq Γ] in
/-- If all variables of `τ` are sent by `e` to variables of weight `c`, a monomial of degree
`|α|` is sent to one of weight `|α| • c`. -/
theorem weight_mapDomain {τ : Type*} (e : τ → σ) {c : Γ} (he : ∀ i, w (e i) = c)
    (α : τ →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain e α) = α.degree • c := by
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add α β hα hβ => rw [Finsupp.mapDomain_add, map_add, hα, hβ, map_add, add_smul]
  | single i n => rw [Finsupp.mapDomain_single, Finsupp.weight_single, he, Finsupp.degree_single]

/-- Renaming along `e : τ → σ`, where all `e i` have weight `c`, maps homogeneous components to
weighted homogeneous components: `(e_* f)_{d • c} = e_* (f_d)`. -/
theorem weightedHomogeneousComponent_rename {τ : Type*} (e : τ → σ) {c : Γ}
    (he : ∀ i, w (e i) = c) (hc : Function.Injective fun d : ℕ => d • c) (d : ℕ)
    (f : MvPolynomial τ R) :
    weightedHomogeneousComponent w (d • c) (rename e f) = rename e (homogeneousComponent d f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial α a =>
    rw [rename_monomial,
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial w _ a rfl),
      homogeneousComponent_of_mem (isHomogeneous_monomial a rfl), weight_mapDomain e he]
    by_cases h : d = α.degree
    · rw [if_pos (congrArg (· • c) h), if_pos h, rename_monomial]
    · rw [if_neg (fun h' => h (hc h')), if_neg h, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]

end WeightedComponent

/-! ### The bigrading of `k[x₀, …, x_M, y₀, …, y_{M'}]` -/

section Bigrading

variable {k : Type u} [Field k] {M M' : ℕ}

variable (M M') in
/-- The weights of the bigrading of `R_{M,M'} = k[x₀, …, x_M, y₀, …, y_{M'}]`:
`deg xⱼ = (1, 0)` and `deg y_m = (0, 1)`. -/
def biWeight : Fin (M + 1) ⊕ Fin (M' + 1) → ℕ × ℕ :=
  Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

@[simp]
theorem biWeight_inl (i : Fin (M + 1)) : biWeight M M' (Sum.inl i) = (1, 0) := rfl

@[simp]
theorem biWeight_inr (m : Fin (M' + 1)) : biWeight M M' (Sum.inr m) = (0, 1) := rfl

/-- The homogeneous components of a polynomial in `x` are its bihomogeneous components:
`(f(x))_{(d, 0)} = f_d(x)`. -/
theorem weightedHomogeneousComponent_rename_inl (d : ℕ) (f : MvPolynomial (Fin (M + 1)) k) :
    weightedHomogeneousComponent (biWeight M M') (d, 0)
        (rename (Sum.inl : Fin (M + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) f) =
      rename Sum.inl (homogeneousComponent d f) := by
  have h := weightedHomogeneousComponent_rename (w := biWeight M M')
    (Sum.inl : Fin (M + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) (c := (1, 0)) (fun _ => rfl)
    (fun d₁ d₂ h => by simpa using congrArg Prod.fst h) d f
  simpa using h

/-- The homogeneous components of a polynomial in `y` are its bihomogeneous components:
`(f(y))_{(0, d)} = f_d(y)`. -/
theorem weightedHomogeneousComponent_rename_inr (d : ℕ) (f : MvPolynomial (Fin (M' + 1)) k) :
    weightedHomogeneousComponent (biWeight M M') (0, d)
        (rename (Sum.inr : Fin (M' + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) f) =
      rename Sum.inr (homogeneousComponent d f) := by
  have h := weightedHomogeneousComponent_rename (w := biWeight M M')
    (Sum.inr : Fin (M' + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) (c := (0, 1)) (fun _ => rfl)
    (fun d₁ d₂ h => by simpa using congrArg Prod.snd h) d f
  simpa using h

/-- A form of degree `d` in `x` is bihomogeneous of bidegree `(d, 0)`. -/
theorem isWeightedHomogeneous_rename_inl {d : ℕ} {f : MvPolynomial (Fin (M + 1)) k}
    (hf : f.IsHomogeneous d) :
    (rename (Sum.inl : Fin (M + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) f).IsWeightedHomogeneous
      (biWeight M M') (d, 0) := by
  have e : rename (Sum.inl : Fin (M + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) f =
      weightedHomogeneousComponent (biWeight M M') (d, 0) (rename Sum.inl f) := by
    rw [weightedHomogeneousComponent_rename_inl, homogeneousComponent_eq_self hf]
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- A form of degree `d` in `y` is bihomogeneous of bidegree `(0, d)`. -/
theorem isWeightedHomogeneous_rename_inr {d : ℕ} {f : MvPolynomial (Fin (M' + 1)) k}
    (hf : f.IsHomogeneous d) :
    (rename (Sum.inr : Fin (M' + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) f).IsWeightedHomogeneous
      (biWeight M M') (0, d) := by
  have e : rename (Sum.inr : Fin (M' + 1) → Fin (M + 1) ⊕ Fin (M' + 1)) f =
      weightedHomogeneousComponent (biWeight M M') (0, d) (rename Sum.inr f) := by
    rw [weightedHomogeneousComponent_rename_inr, homogeneousComponent_eq_self hf]
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-! ### Bigraded seminorms -/

/-- A point `v` of `(𝔸^{M+1} × 𝔸^{M'+1})^an = Berk k R_{M,M'}` is **bigraded** if
`|F_{(a,b)}|_v ≤ |F|_v` for every polynomial `F` and every bidegree `(a, b)`. By the ultrametric
inequality this is equivalent to the blueprint's `|F|_v = max_{(a,b)} |F_{(a,b)}|_v`
(`IsBigraded.val_eq_sup`, `isBigraded_iff_val_eq_sup`). -/
def IsBigraded (v : Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) : Prop :=
  ∀ (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (p : ℕ × ℕ),
    v.val (weightedHomogeneousComponent (biWeight M M') p F) ≤ v.val F

/-- A bigraded seminorm is the maximum of its values on the bihomogeneous components. -/
theorem IsBigraded.val_eq_sup {v : Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)}
    (hv : IsBigraded v) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    v.val F = (weightSupport (biWeight M M') F).sup
      fun p => v.val (weightedHomogeneousComponent (biWeight M M') p F) := by
  refine le_antisymm ?_ (Finset.sup_le fun p _ => hv F p)
  conv_lhs => rw [← sum_weightSupport (w := biWeight M M') F]
  exact v.val.map_sum_le fun p hp =>
    Finset.le_sup (f := fun p => v.val (weightedHomogeneousComponent (biWeight M M') p F)) hp

theorem isBigraded_iff_val_eq_sup (v : Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) :
    IsBigraded v ↔ ∀ F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k,
      v.val F = (weightSupport (biWeight M M') F).sup
        fun p => v.val (weightedHomogeneousComponent (biWeight M M') p F) := by
  refine ⟨fun hv => hv.val_eq_sup, fun h F p => ?_⟩
  by_cases hp : p ∈ weightSupport (biWeight M M') F
  · rw [h F]
    exact Finset.le_sup (f := fun p => v.val (weightedHomogeneousComponent (biWeight M M') p F)) hp
  · rw [weightedHomogeneousComponent_eq_zero_of_notMem hp, map_zero]
    exact zero_le

theorem isClosed_setOf_isBigraded :
    IsClosed {v : Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) | IsBigraded v} := by
  have e : {v : Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) | IsBigraded v} =
      ⋂ F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k, ⋂ p : ℕ × ℕ,
        {v | v.val (weightedHomogeneousComponent (biWeight M M') p F) ≤ v.val F} := by
    ext v
    simp [IsBigraded]
  rw [e]
  exact isClosed_iInter fun F => isClosed_iInter fun p =>
    isClosed_le (Berk.continuous_val_apply _) (Berk.continuous_val_apply _)

/-- The trivial valuation is bigraded. -/
theorem isBigraded_triv :
    IsBigraded (Berk.triv : Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) := by
  classical
  intro F p
  by_cases hF : F = 0
  · simp [hF]
  · rw [Berk.triv_val_of_ne_zero hF]
    by_cases hp : weightedHomogeneousComponent (biWeight M M') p F = 0
    · rw [hp, map_zero]
      exact zero_le
    · rw [Berk.triv_val_of_ne_zero hp]

end Bigrading

/-! ### The model of `(ℙ^M × ℙ^{M'})^an` -/

variable (k : Type u) [Field k] (M M' : ℕ)

/-- The **analytification of `ℙ^M × ℙ^{M'}`** over the trivially valued field `k`
(`def:pg-bigraded`), modelled as the bigraded points `v` of
`Berk k k[x₀, …, x_M, y₀, …, y_{M'}]` normalized by `max_j |xⱼ|_v = 1 = max_m |y_m|_v`. -/
def BiProjBerk : Type u :=
  {v : Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) // IsBigraded v ∧
    Finset.univ.sup (fun i => v.val (X (Sum.inl i))) = 1 ∧
    Finset.univ.sup (fun m => v.val (X (Sum.inr m))) = 1}

namespace BiProjBerk

variable {k M M'}

/-- The topology of `(ℙ^M × ℙ^{M'})^an`: the subspace topology from `Berk k R_{M,M'}`. -/
instance : TopologicalSpace (BiProjBerk k M M') := instTopologicalSpaceSubtype

theorem isEmbedding_val :
    IsEmbedding (Subtype.val : BiProjBerk k M M' →
      Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) :=
  IsEmbedding.subtypeVal

@[fun_prop]
theorem continuous_val :
    Continuous (Subtype.val : BiProjBerk k M M' →
      Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) :=
  continuous_subtype_val

@[ext]
theorem ext {v w : BiProjBerk k M M'} (h : v.1 = w.1) : v = w := Subtype.ext h

theorem isBigraded (v : BiProjBerk k M M') : IsBigraded v.1 := v.2.1

/-- The normalization `max_j |xⱼ|_v = 1`. -/
theorem sup_val_X_inl (v : BiProjBerk k M M') :
    Finset.univ.sup (fun i => v.1.val (X (Sum.inl i))) = 1 :=
  v.2.2.1

/-- The normalization `max_m |y_m|_v = 1`. -/
theorem sup_val_X_inr (v : BiProjBerk k M M') :
    Finset.univ.sup (fun m => v.1.val (X (Sum.inr m))) = 1 :=
  v.2.2.2

theorem val_X_inl_le_one (v : BiProjBerk k M M') (i : Fin (M + 1)) :
    v.1.val (X (Sum.inl i)) ≤ 1 :=
  (Finset.le_sup (f := fun i => v.1.val (X (Sum.inl i))) (Finset.mem_univ i)).trans
    (sup_val_X_inl v).le

theorem val_X_inr_le_one (v : BiProjBerk k M M') (m : Fin (M' + 1)) :
    v.1.val (X (Sum.inr m)) ≤ 1 :=
  (Finset.le_sup (f := fun m => v.1.val (X (Sum.inr m))) (Finset.mem_univ m)).trans
    (sup_val_X_inr v).le

theorem val_X_le_one (v : BiProjBerk k M M') (i : Fin (M + 1) ⊕ Fin (M' + 1)) :
    v.1.val (X i) ≤ 1 := by
  rcases i with i | m
  · exact val_X_inl_le_one v i
  · exact val_X_inr_le_one v m

theorem exists_val_X_inl_eq_one (v : BiProjBerk k M M') :
    ∃ j, v.1.val (X (Sum.inl j)) = 1 := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    fun i => v.1.val (X (Sum.inl i) : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
  exact ⟨j, hj ▸ sup_val_X_inl v⟩

theorem exists_val_X_inr_eq_one (v : BiProjBerk k M M') :
    ∃ l, v.1.val (X (Sum.inr l)) = 1 := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    fun m => v.1.val (X (Sum.inr m) : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
  exact ⟨l, hl ▸ sup_val_X_inr v⟩

/-- Every polynomial has absolute value `≤ 1` at a point of `(ℙ^M × ℙ^{M'})^an`. -/
theorem val_le_one (v : BiProjBerk k M M') (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    v.1.val F ≤ 1 := by
  have h := Berk.abs_aeval_le_pow (k := k)
    (X : Fin (M + 1) ⊕ Fin (M' + 1) → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) v.1 le_rfl
    (val_X_le_one v) F
  rwa [aeval_X_left_apply, one_pow] at h

/-- A point of `(ℙ^M × ℙ^{M'})^an` is the maximum of its values on the bihomogeneous
components. -/
theorem val_eq_sup (v : BiProjBerk k M M') (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    v.1.val F = (weightSupport (biWeight M M') F).sup
      fun p => v.1.val (weightedHomogeneousComponent (biWeight M M') p F) :=
  v.isBigraded.val_eq_sup F

/-- A point of `(ℙ^M × ℙ^{M'})^an` is determined by its values on bihomogeneous elements. -/
theorem ext_of_isWeightedHomogeneous {v w : BiProjBerk k M M'}
    (h : ∀ (p : ℕ × ℕ) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k),
      F.IsWeightedHomogeneous (biWeight M M') p → v.1.val F = w.1.val F) : v = w := by
  refine BiProjBerk.ext (Berk.ext_val fun F => ?_)
  rw [v.val_eq_sup F, w.val_eq_sup F]
  exact Finset.sup_congr rfl fun p _ =>
    h p _ (weightedHomogeneousComponent_isWeightedHomogeneous p F)

variable (k M M') in
/-- The underlying set of `(ℙ^M × ℙ^{M'})^an` in `Berk k R_{M,M'}`. -/
def carrier : Set (Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) :=
  {v | IsBigraded v ∧ Finset.univ.sup (fun i => v.val (X (Sum.inl i))) = 1 ∧
    Finset.univ.sup (fun m => v.val (X (Sum.inr m))) = 1}

theorem range_val :
    Set.range (Subtype.val : BiProjBerk k M M' →
      Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) = carrier k M M' :=
  Subtype.range_coe

theorem isClosed_carrier : IsClosed (carrier k M M') :=
  isClosed_setOf_isBigraded.inter ((isClosed_eq
    (Continuous.finset_sup_apply fun _ _ => Berk.continuous_val_apply _) continuous_const).inter
    (isClosed_eq (Continuous.finset_sup_apply fun _ _ => Berk.continuous_val_apply _)
      continuous_const))

/-- `(ℙ^M × ℙ^{M'})^an` is a closed subset of the closed unit polydisc `|xⱼ|, |y_m| ≤ 1` of
`(𝔸^{M+1} × 𝔸^{M'+1})^an`, hence compact. -/
theorem isCompact_carrier : IsCompact (carrier k M M') :=
  Berk.isCompact_of_isClosed_of_forall_abs_le (MvPolynomial.adjoin_range_X (R := k))
    isClosed_carrier 1 (by
      rintro v hv _ ⟨i, rfl⟩
      exact val_X_le_one ⟨v, hv⟩ i)

theorem isClosedEmbedding_val :
    IsClosedEmbedding (Subtype.val : BiProjBerk k M M' →
      Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) :=
  ⟨isEmbedding_val, by rw [range_val]; exact isClosed_carrier⟩

/-- `(ℙ^M × ℙ^{M'})^an` is compact. -/
instance instCompactSpace : CompactSpace (BiProjBerk k M M') :=
  isCompact_iff_compactSpace.1 isCompact_carrier

/-- `(ℙ^M × ℙ^{M'})^an` is Hausdorff. -/
instance instT2Space : T2Space (BiProjBerk k M M') :=
  isEmbedding_val.t2Space

/-- For countable `k`, `(ℙ^M × ℙ^{M'})^an` is second countable: it is a subspace of
`Berk k R_{M,M'}`, which is second countable as `R_{M,M'}` is of finite type over `k`. -/
instance instSecondCountableTopology [Countable k] :
    SecondCountableTopology (BiProjBerk k M M') :=
  isEmbedding_val.secondCountableTopology

/-- A map into `(ℙ^M × ℙ^{M'})^an` is continuous iff all `|F|` are continuous along it. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {g : Y → BiProjBerk k M M'} :
    Continuous g ↔
      ∀ F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k, Continuous fun y => (g y).1.val F := by
  refine ⟨fun h F => (Berk.continuous_val_apply F).comp (continuous_val.comp h), fun h => ?_⟩
  exact isEmbedding_val.continuous_iff.2 (Berk.continuous_iff.2 h)

/-- The zero locus `{v | |F|_v = 0 for all F ∈ S}` of a set of polynomials is closed. -/
theorem isClosed_setOf_forall_val_eq_zero (S : Set (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) :
    IsClosed {v : BiProjBerk k M M' | ∀ F ∈ S, v.1.val F = 0} := by
  have e : {v : BiProjBerk k M M' | ∀ F ∈ S, v.1.val F = 0} =
      ⋂ F ∈ S, {v : BiProjBerk k M M' | v.1.val F = 0} := by
    ext v
    simp
  rw [e]
  exact isClosed_biInter fun F _ =>
    isClosed_eq ((Berk.continuous_val_apply F).comp continuous_val) continuous_const

/-! ### The trivial valuation -/

/-- The **trivial valuation** `v_triv ∈ (ℙ^M × ℙ^{M'})^an`: `|F| = 1` for every `F ≠ 0`. -/
def triv : BiProjBerk k M M' :=
  ⟨Berk.triv, isBigraded_triv, by
    refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
    · rw [Berk.triv_val_of_ne_zero (X_ne_zero _)]
    · refine le_trans ?_ (Finset.le_sup (f := fun i => (Berk.triv :
        Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)).val (X (Sum.inl i)))
        (Finset.mem_univ 0))
      rw [Berk.triv_val_of_ne_zero (X_ne_zero _)], by
    refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
    · rw [Berk.triv_val_of_ne_zero (X_ne_zero _)]
    · refine le_trans ?_ (Finset.le_sup (f := fun m => (Berk.triv :
        Berk k (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)).val (X (Sum.inr m)))
        (Finset.mem_univ 0))
      rw [Berk.triv_val_of_ne_zero (X_ne_zero _)]⟩

@[simp]
theorem triv_val : (triv : BiProjBerk k M M').1 = Berk.triv := rfl

theorem triv_val_of_ne_zero {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} (hF : F ≠ 0) :
    (triv : BiProjBerk k M M').1.val F = 1 :=
  Berk.triv_val_of_ne_zero hF

/-! ### The functions `log|F|` -/

/-- The function `log|F| : (ℙ^M × ℙ^{M'})^an → [-∞, 0]` attached to `F ∈ R_{M,M'}`. -/
def logAbs (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (v : BiProjBerk k M M') : EReal :=
  Berk.logAbs F v.1

theorem logAbs_def (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (v : BiProjBerk k M M') :
    logAbs F v = ENNReal.log (v.1.val F : ℝ≥0∞) := rfl

@[fun_prop]
theorem continuous_logAbs (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    Continuous (logAbs F : BiProjBerk k M M' → EReal) :=
  (Berk.continuous_logAbs F).comp continuous_val

theorem logAbs_le_zero (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
    (v : BiProjBerk k M M') : logAbs F v ≤ 0 := by
  rw [logAbs_def, ENNReal.log_le_zero_iff]
  exact_mod_cast val_le_one v F

theorem logAbs_ne_top (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
    (v : BiProjBerk k M M') : logAbs F v ≠ ⊤ :=
  Berk.logAbs_ne_top F v.1

theorem logAbs_mul (F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (v : BiProjBerk k M M') :
    logAbs (F * G) v = logAbs F v + logAbs G v :=
  Berk.logAbs_mul F G v.1

theorem logAbs_pow (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (n : ℕ)
    (v : BiProjBerk k M M') : logAbs (F ^ n) v = n * logAbs F v :=
  Berk.logAbs_pow F n v.1

theorem logAbs_eq_bot_iff (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)
    (v : BiProjBerk k M M') : logAbs F v = ⊥ ↔ v.1.val F = 0 :=
  Berk.logAbs_eq_bot_iff F v.1

theorem logAbs_triv_of_ne_zero {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} (hF : F ≠ 0) :
    logAbs F (triv : BiProjBerk k M M') = 0 :=
  Berk.logAbs_triv_of_ne_zero hF

/-! ### The projections to the factors -/

/-- The **first projection** `(ℙ^M × ℙ^{M'})^an → (ℙ^M)^an`: restriction of seminorms along
`k[x₀, …, x_M] → R_{M,M'}`. -/
def fst (v : BiProjBerk k M M') : ProjBerk k M :=
  ⟨Berk.comap (rename (Sum.inl : Fin (M + 1) → Fin (M + 1) ⊕ Fin (M' + 1))) v.1,
    (isGraded_iff _).2 fun f d => by
      simp only [Berk.comap_val_apply]
      rw [← weightedHomogeneousComponent_rename_inl]
      exact v.isBigraded _ _,
    by simpa [Berk.comap_val_apply, rename_X] using v.sup_val_X_inl⟩

/-- The **second projection** `(ℙ^M × ℙ^{M'})^an → (ℙ^{M'})^an`: restriction of seminorms along
`k[y₀, …, y_{M'}] → R_{M,M'}`. -/
def snd (v : BiProjBerk k M M') : ProjBerk k M' :=
  ⟨Berk.comap (rename (Sum.inr : Fin (M' + 1) → Fin (M + 1) ⊕ Fin (M' + 1))) v.1,
    (isGraded_iff _).2 fun f d => by
      simp only [Berk.comap_val_apply]
      rw [← weightedHomogeneousComponent_rename_inr]
      exact v.isBigraded _ _,
    by simpa [Berk.comap_val_apply, rename_X] using v.sup_val_X_inr⟩

theorem fst_val_apply (v : BiProjBerk k M M') (f : MvPolynomial (Fin (M + 1)) k) :
    (fst v).1.val f = v.1.val (rename Sum.inl f) :=
  rfl

theorem snd_val_apply (v : BiProjBerk k M M') (f : MvPolynomial (Fin (M' + 1)) k) :
    (snd v).1.val f = v.1.val (rename Sum.inr f) :=
  rfl

@[fun_prop]
theorem continuous_fst : Continuous (fst : BiProjBerk k M M' → ProjBerk k M) :=
  ProjBerk.isEmbedding_val.continuous_iff.2 ((Berk.continuous_comap _).comp continuous_val)

@[fun_prop]
theorem continuous_snd : Continuous (snd : BiProjBerk k M M' → ProjBerk k M') :=
  ProjBerk.isEmbedding_val.continuous_iff.2 ((Berk.continuous_comap _).comp continuous_val)

@[simp]
theorem fst_triv : fst (triv : BiProjBerk k M M') = ProjBerk.triv := by
  refine ProjBerk.ext (Berk.ext_val fun f => ?_)
  by_cases hf : f = 0
  · simp [hf, fst_val_apply]
  · rw [fst_val_apply, ProjBerk.triv_val_of_ne_zero hf,
      triv_val_of_ne_zero ((map_ne_zero_iff _ (rename_injective _ Sum.inl_injective)).2 hf)]

@[simp]
theorem snd_triv : snd (triv : BiProjBerk k M M') = ProjBerk.triv := by
  refine ProjBerk.ext (Berk.ext_val fun f => ?_)
  by_cases hf : f = 0
  · simp [hf, snd_val_apply]
  · rw [snd_val_apply, ProjBerk.triv_val_of_ne_zero hf,
      triv_val_of_ne_zero ((map_ne_zero_iff _ (rename_injective _ Sum.inr_injective)).2 hf)]

/-! ### Bigraded extension (`lem:pg-bigraded-extension`) -/

/-- The hypotheses of the **bigraded extension** lemma (`lem:pg-bigraded-extension`) on a family
`N p : R_{M,M'} → ℝ≥0`, `p ∈ ℕ × ℕ`, of which only the values on bihomogeneous elements of
bidegree `p` matter: `N` vanishes at `0`, is `1` on nonzero constants, is multiplicative and
ultrametric on bihomogeneous elements, and `max_j N(xⱼ) = 1 = max_m N(y_m)`. -/
structure IsBigradedNorm
    (N : ℕ × ℕ → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k → ℝ≥0) : Prop where
  map_zero : ∀ p, N p 0 = 0
  map_C : ∀ c : k, c ≠ 0 → N 0 (C c) = 1
  map_mul : ∀ {p q : ℕ × ℕ} {F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k},
    F.IsWeightedHomogeneous (biWeight M M') p → G.IsWeightedHomogeneous (biWeight M M') q →
      N (p + q) (F * G) = N p F * N q G
  map_add_le : ∀ {p : ℕ × ℕ} {F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k},
    F.IsWeightedHomogeneous (biWeight M M') p → G.IsWeightedHomogeneous (biWeight M M') p →
      N p (F + G) ≤ max (N p F) (N p G)
  sup_X_inl : Finset.univ.sup (fun i => N (1, 0) (X (Sum.inl i))) = 1
  sup_X_inr : Finset.univ.sup (fun m => N (0, 1) (X (Sum.inr m))) = 1

/-- The **bigraded extension** `|F| = max_p N p (F_p)` of a family `N` on bihomogeneous elements,
the maximum over the bihomogeneous components `F_p` of `F`. -/
def bigradedFun (N : ℕ × ℕ → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k → ℝ≥0)
    (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) : ℝ≥0 :=
  (weightSupport (biWeight M M') F).sup
    fun p => N p (weightedHomogeneousComponent (biWeight M M') p F)

namespace IsBigradedNorm

variable {N : ℕ × ℕ → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k → ℝ≥0} (hN : IsBigradedNorm N)
include hN

theorem map_neg {p : ℕ × ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') p) : N p (-F) = N p F := by
  have h := hN.map_mul (isWeightedHomogeneous_C (biWeight M M') (-1 : k)) hF
  rw [zero_add, hN.map_C _ (neg_ne_zero.2 one_ne_zero), one_mul, _root_.map_neg, map_one,
    neg_one_mul] at h
  exact h

theorem map_add_eq_of_lt {p : ℕ × ℕ} {F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') p)
    (hG : G.IsWeightedHomogeneous (biWeight M M') p) (hlt : N p G < N p F) :
    N p (F + G) = N p F := by
  refine le_antisymm ((hN.map_add_le hF hG).trans (max_le le_rfl hlt.le)) ?_
  have h := hN.map_add_le (hF.add hG) hG.neg
  rw [add_neg_cancel_right, hN.map_neg hG] at h
  rcases le_max_iff.1 h with h | h
  · exact h
  · exact absurd h (not_le.2 hlt)

theorem map_sum_le {ι : Type*} (s : Finset ι) {p : ℕ × ℕ}
    {H : ι → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hH : ∀ i ∈ s, (H i).IsWeightedHomogeneous (biWeight M M') p) :
    N p (∑ i ∈ s, H i) ≤ s.sup fun i => N p (H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hN.map_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sup_insert]
    have hs : (∑ i ∈ s, H i).IsWeightedHomogeneous (biWeight M M') p :=
      IsWeightedHomogeneous.sum _ _ _ fun i hi => hH i (Finset.mem_insert_of_mem hi)
    exact (hN.map_add_le (hH j (Finset.mem_insert_self j s)) hs).trans
      (max_le_max le_rfl (ih fun i hi => hH i (Finset.mem_insert_of_mem hi)))

/-- A sum of bihomogeneous elements of bidegree `p` with a strictly dominant term has the norm of
that term. -/
theorem map_sum_eq_of_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) {p : ℕ × ℕ}
    {H : ι → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hH : ∀ i ∈ s, (H i).IsWeightedHomogeneous (biWeight M M') p) {j : ι}
    (hj : j ∈ s) (hlt : ∀ i ∈ s, i ≠ j → N p (H i) < N p (H j)) :
    N p (∑ i ∈ s, H i) = N p (H j) := by
  rw [← Finset.add_sum_erase s H hj]
  rcases (s.erase j).eq_empty_or_nonempty with he | he
  · rw [he, Finset.sum_empty, add_zero]
  refine hN.map_add_eq_of_lt (hH j hj) (IsWeightedHomogeneous.sum _ _ _ fun i hi =>
    hH i (Finset.mem_of_mem_erase hi)) ?_
  refine (hN.map_sum_le _ fun i hi => hH i (Finset.mem_of_mem_erase hi)).trans_lt ?_
  obtain ⟨i, hi⟩ := he
  have hpos : (⊥ : ℝ≥0) < N p (H j) :=
    zero_le.trans_lt (hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  exact (Finset.sup_lt_iff hpos).2 fun i hi =>
    hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

theorem le_bigradedFun (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (p : ℕ × ℕ) :
    N p (weightedHomogeneousComponent (biWeight M M') p F) ≤ bigradedFun N F := by
  by_cases hp : p ∈ weightSupport (biWeight M M') F
  · exact Finset.le_sup (f := fun p => N p (weightedHomogeneousComponent (biWeight M M') p F)) hp
  · rw [weightedHomogeneousComponent_eq_zero_of_notMem hp, hN.map_zero]
    exact zero_le

omit hN in
theorem bigradedFun_le_iff (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) (r : ℝ≥0)
    (hN : IsBigradedNorm N) :
    bigradedFun N F ≤ r ↔ ∀ p, N p (weightedHomogeneousComponent (biWeight M M') p F) ≤ r :=
  ⟨fun h p => (hN.le_bigradedFun F p).trans h, fun h => Finset.sup_le fun p _ => h p⟩

/-- On a bihomogeneous element of bidegree `p` the bigraded extension is `N p`. -/
theorem bigradedFun_of_isWeightedHomogeneous {p : ℕ × ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') p) : bigradedFun N F = N p F := by
  refine le_antisymm ((bigradedFun_le_iff F _ hN).2 fun q => ?_) ?_
  · by_cases hq : q = p
    · rw [hq, weightedHomogeneousComponent_eq_self hF]
    · rw [hF.weightedHomogeneousComponent_ne q hq, hN.map_zero]
      exact zero_le
  · calc N p F = N p (weightedHomogeneousComponent (biWeight M M') p F) := by
          rw [weightedHomogeneousComponent_eq_self hF]
      _ ≤ bigradedFun N F := hN.le_bigradedFun F p

theorem bigradedFun_add_le (F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    bigradedFun N (F + G) ≤ max (bigradedFun N F) (bigradedFun N G) := by
  refine (bigradedFun_le_iff _ _ hN).2 fun p => ?_
  rw [map_add]
  exact (hN.map_add_le (weightedHomogeneousComponent_isWeightedHomogeneous p F)
    (weightedHomogeneousComponent_isWeightedHomogeneous p G)).trans
    (max_le_max (hN.le_bigradedFun F p) (hN.le_bigradedFun G p))

theorem bigradedFun_mul_le (F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    bigradedFun N (F * G) ≤ bigradedFun N F * bigradedFun N G := by
  refine (bigradedFun_le_iff _ _ hN).2 fun γ => ?_
  rw [weightedHomogeneousComponent_mul]
  refine (hN.map_sum_le _ fun pq hpq => ?_).trans (Finset.sup_le fun pq hpq => ?_)
  · rw [← (Finset.mem_filter.1 hpq).2]
    exact (weightedHomogeneousComponent_isWeightedHomogeneous _ F).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous _ G)
  · have h : N γ (weightedHomogeneousComponent (biWeight M M') pq.1 F *
        weightedHomogeneousComponent (biWeight M M') pq.2 G) =
        N pq.1 (weightedHomogeneousComponent (biWeight M M') pq.1 F) *
          N pq.2 (weightedHomogeneousComponent (biWeight M M') pq.2 G) := by
      rw [← (Finset.mem_filter.1 hpq).2]
      exact hN.map_mul (weightedHomogeneousComponent_isWeightedHomogeneous _ F)
        (weightedHomogeneousComponent_isWeightedHomogeneous _ G)
    rw [h]
    exact mul_le_mul' (hN.le_bigradedFun F _) (hN.le_bigradedFun G _)

/-- The maximum defining the bigraded extension is attained. -/
theorem exists_eq_bigradedFun (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    ∃ p, N p (weightedHomogeneousComponent (biWeight M M') p F) = bigradedFun N F := by
  rcases (weightSupport (biWeight M M') F).eq_empty_or_nonempty with he | he
  · refine ⟨0, ?_⟩
    rw [bigradedFun, he, Finset.sup_empty,
      weightedHomogeneousComponent_eq_zero_of_notMem (by rw [he]; exact Finset.notMem_empty _),
      hN.map_zero]
    rfl
  · obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup _ he
      fun p => N p (weightedHomogeneousComponent (biWeight M M') p F)
    exact ⟨p, hp.symm⟩

/-- The lexicographically smallest dominant bidegree: there is `(a, b)` at which the maximum
defining the bigraded extension is attained, and the maximum is not attained at any `(a', b')`
lexicographically smaller than `(a, b)`. -/
theorem exists_dominant (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    ∃ a b : ℕ, N (a, b) (weightedHomogeneousComponent (biWeight M M') (a, b) F) =
        bigradedFun N F ∧
      ∀ a' b' : ℕ, (a' < a ∨ (a' = a ∧ b' < b)) →
        N (a', b') (weightedHomogeneousComponent (biWeight M M') (a', b') F) <
          bigradedFun N F := by
  classical
  have hex : ∃ a b : ℕ, N (a, b) (weightedHomogeneousComponent (biWeight M M') (a, b) F) =
      bigradedFun N F := by
    obtain ⟨⟨a, b⟩, h⟩ := hN.exists_eq_bigradedFun F
    exact ⟨a, b, h⟩
  have hex' : ∃ b : ℕ, N (Nat.find hex, b)
      (weightedHomogeneousComponent (biWeight M M') (Nat.find hex, b) F) = bigradedFun N F :=
    Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.find hex', Nat.find_spec hex', fun a' b' h =>
    lt_of_le_of_ne (hN.le_bigradedFun F _) fun heq => ?_⟩
  rcases h with h | ⟨rfl, h⟩
  · exact Nat.find_min hex h ⟨b', heq⟩
  · exact Nat.find_min hex' h heq

/-- Multiplicativity of the bigraded extension (the bigraded Gauss lemma): for the
lexicographically smallest dominant bidegrees `(a, b)` of `F` and `(c, d)` of `G`,
`F_{(a,b)} G_{(c,d)}` is the unique dominant term of `(FG)_{(a + c, b + d)}`. -/
theorem mul_le_bigradedFun_mul (F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    bigradedFun N F * bigradedFun N G ≤ bigradedFun N (F * G) := by
  classical
  by_cases hF : bigradedFun N F = 0
  · rw [hF, zero_mul]; exact zero_le
  by_cases hG : bigradedFun N G = 0
  · rw [hG, mul_zero]; exact zero_le
  have hFpos : 0 < bigradedFun N F := pos_iff_ne_zero.2 hF
  have hGpos : 0 < bigradedFun N G := pos_iff_ne_zero.2 hG
  obtain ⟨a, b, hab, hab'⟩ := hN.exists_dominant F
  obtain ⟨c, d, hcd, hcd'⟩ := hN.exists_dominant G
  have hmemF : ((a, b) : ℕ × ℕ) ∈ weightSupport (biWeight M M') F := by
    refine mem_weightSupport_of_ne_zero fun h0 => hF ?_
    rw [← hab, h0, hN.map_zero]
  have hmemG : ((c, d) : ℕ × ℕ) ∈ weightSupport (biWeight M M') G := by
    refine mem_weightSupport_of_ne_zero fun h0 => hG ?_
    rw [← hcd, h0, hN.map_zero]
  have key : N ((a, b) + (c, d)) (weightedHomogeneousComponent (biWeight M M') (a, b) F *
      weightedHomogeneousComponent (biWeight M M') (c, d) G) =
      bigradedFun N F * bigradedFun N G := by
    rw [hN.map_mul (weightedHomogeneousComponent_isWeightedHomogeneous _ F)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ G), hab, hcd]
  have hj : (((a, b), (c, d)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈
      (weightSupport (biWeight M M') F ×ˢ weightSupport (biWeight M M') G).filter
        (fun pq => pq.1 + pq.2 = (a, b) + (c, d)) :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hmemF, hmemG⟩, rfl⟩
  refine le_trans ?_ (hN.le_bigradedFun (F * G) ((a, b) + (c, d)))
  rw [weightedHomogeneousComponent_mul, hN.map_sum_eq_of_lt _ (fun pq hpq => ?_) hj
    (fun pq hpq hne => ?_)]
  · exact key.ge
  · rw [← (Finset.mem_filter.1 hpq).2]
    exact (weightedHomogeneousComponent_isWeightedHomogeneous _ F).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous _ G)
  · obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := pq
    have hsum := (Finset.mem_filter.1 hpq).2
    have h : N ((a, b) + (c, d)) (weightedHomogeneousComponent (biWeight M M') (a', b') F *
        weightedHomogeneousComponent (biWeight M M') (c', d') G) =
        N (a', b') (weightedHomogeneousComponent (biWeight M M') (a', b') F) *
          N (c', d') (weightedHomogeneousComponent (biWeight M M') (c', d') G) := by
      rw [← hsum]
      exact hN.map_mul (weightedHomogeneousComponent_isWeightedHomogeneous _ F)
        (weightedHomogeneousComponent_isWeightedHomogeneous _ G)
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hsum
    have hcases : (a' < a ∨ (a' = a ∧ b' < b)) ∨ (c' < c ∨ (c' = c ∧ d' < d)) := by
      by_contra hcon
      apply hne
      simp only [Prod.mk.injEq]
      omega
    refine (h.trans_lt ?_).trans_eq key.symm
    rcases hcases with h1 | h1
    · calc N (a', b') (weightedHomogeneousComponent (biWeight M M') (a', b') F) *
            N (c', d') (weightedHomogeneousComponent (biWeight M M') (c', d') G)
          ≤ N (a', b') (weightedHomogeneousComponent (biWeight M M') (a', b') F) *
            bigradedFun N G := by
            gcongr; exact hN.le_bigradedFun G _
        _ < bigradedFun N F * bigradedFun N G := by
            gcongr; exact hab' a' b' h1
    · calc N (a', b') (weightedHomogeneousComponent (biWeight M M') (a', b') F) *
            N (c', d') (weightedHomogeneousComponent (biWeight M M') (c', d') G)
          ≤ bigradedFun N F *
            N (c', d') (weightedHomogeneousComponent (biWeight M M') (c', d') G) := by
            gcongr; exact hN.le_bigradedFun F _
        _ < bigradedFun N F * bigradedFun N G := by
            gcongr; exact hcd' c' d' h1

theorem bigradedFun_mul (F G : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    bigradedFun N (F * G) = bigradedFun N F * bigradedFun N G :=
  le_antisymm (hN.bigradedFun_mul_le F G) (hN.mul_le_bigradedFun_mul F G)

/-- The bigraded extension as a valuation on `R_{M,M'}`. -/
def valuation : Valuation (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) ℝ≥0 where
  toFun := bigradedFun N
  map_zero' := by
    rw [hN.bigradedFun_of_isWeightedHomogeneous (isWeightedHomogeneous_zero _ _ 0), hN.map_zero]
  map_one' := by
    rw [hN.bigradedFun_of_isWeightedHomogeneous (isWeightedHomogeneous_one k _)]
    have h := hN.map_C 1 one_ne_zero
    rwa [C_1] at h
  map_mul' := hN.bigradedFun_mul
  map_add_le_max' := hN.bigradedFun_add_le

theorem valuation_apply (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    hN.valuation F = bigradedFun N F :=
  rfl

end IsBigradedNorm

/-- **Bigraded extension** (`lem:pg-bigraded-extension`): a family `N` of norms on bihomogeneous
elements satisfying `IsBigradedNorm` defines the point `|F| = max_p N p (F_p)` of
`(ℙ^M × ℙ^{M'})^an`. -/
def ofBigradedNorm {N : ℕ × ℕ → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k → ℝ≥0}
    (hN : IsBigradedNorm N) : BiProjBerk k M M' :=
  ⟨⟨hN.valuation, fun c hc => by
      rw [hN.valuation_apply, algebraMap_eq,
        hN.bigradedFun_of_isWeightedHomogeneous (isWeightedHomogeneous_C _ c), hN.map_C c hc]⟩,
    fun F p => by
      change bigradedFun N (weightedHomogeneousComponent (biWeight M M') p F) ≤ bigradedFun N F
      rw [hN.bigradedFun_of_isWeightedHomogeneous
        (weightedHomogeneousComponent_isWeightedHomogeneous p F)]
      exact hN.le_bigradedFun F p,
    by
      change Finset.univ.sup (fun i => bigradedFun N (X (Sum.inl i))) = 1
      have h : ∀ i, bigradedFun N (X (Sum.inl i)) = N (1, 0) (X (Sum.inl i)) := fun i =>
        hN.bigradedFun_of_isWeightedHomogeneous (isWeightedHomogeneous_X k _ (Sum.inl i))
      simp_rw [h]
      exact hN.sup_X_inl,
    by
      change Finset.univ.sup (fun m => bigradedFun N (X (Sum.inr m))) = 1
      have h : ∀ m, bigradedFun N (X (Sum.inr m)) = N (0, 1) (X (Sum.inr m)) := fun m =>
        hN.bigradedFun_of_isWeightedHomogeneous (isWeightedHomogeneous_X k _ (Sum.inr m))
      simp_rw [h]
      exact hN.sup_X_inr⟩

section ofBigradedNorm

variable {N : ℕ × ℕ → MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k → ℝ≥0} (hN : IsBigradedNorm N)

theorem ofBigradedNorm_val_apply (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    (ofBigradedNorm hN).1.val F = bigradedFun N F :=
  rfl

/-- On a bihomogeneous `F` of bidegree `p`, `|F|_{ofBigradedNorm N} = N p F`. -/
theorem ofBigradedNorm_val_of_isWeightedHomogeneous {p : ℕ × ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') p) : (ofBigradedNorm hN).1.val F = N p F :=
  hN.bigradedFun_of_isWeightedHomogeneous hF

/-- The first projection of a bigraded extension, on a form `f` of degree `d` in `x`:
`|f|_{fst (ofBigradedNorm N)} = N (d, 0) f(x)`. -/
theorem fst_ofBigradedNorm_val_of_isHomogeneous {d : ℕ} {f : MvPolynomial (Fin (M + 1)) k}
    (hf : f.IsHomogeneous d) :
    (fst (ofBigradedNorm hN)).1.val f = N (d, 0) (rename Sum.inl f) :=
  hN.bigradedFun_of_isWeightedHomogeneous (isWeightedHomogeneous_rename_inl hf)

/-- The second projection of a bigraded extension, on a form `f` of degree `d` in `y`:
`|f|_{snd (ofBigradedNorm N)} = N (0, d) f(y)`. -/
theorem snd_ofBigradedNorm_val_of_isHomogeneous {d : ℕ} {f : MvPolynomial (Fin (M' + 1)) k}
    (hf : f.IsHomogeneous d) :
    (snd (ofBigradedNorm hN)).1.val f = N (0, d) (rename Sum.inr f) :=
  hN.bigradedFun_of_isWeightedHomogeneous (isWeightedHomogeneous_rename_inr hf)

end ofBigradedNorm

/-- The values of a point of `(ℙ^M × ℙ^{M'})^an` on bihomogeneous elements satisfy the hypotheses
of the bigraded extension lemma. -/
theorem isBigradedNorm_val (v : BiProjBerk k M M') :
    IsBigradedNorm fun (_ : ℕ × ℕ) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) =>
      v.1.val F where
  map_zero _ := map_zero _
  map_C c hc := by rw [← algebraMap_eq]; exact v.1.val_algebraMap c hc
  map_mul _ _ := map_mul _ _ _
  map_add_le _ _ := v.1.val.map_add _ _
  sup_X_inl := v.sup_val_X_inl
  sup_X_inr := v.sup_val_X_inr

/-- Every point of `(ℙ^M × ℙ^{M'})^an` is the bigraded extension of its values on bihomogeneous
elements. -/
theorem ofBigradedNorm_val (v : BiProjBerk k M M') :
    ofBigradedNorm (isBigradedNorm_val v) = v :=
  ext_of_isWeightedHomogeneous fun _ _ hF => ofBigradedNorm_val_of_isWeightedHomogeneous _ hF

/-! ### Rescaled pullbacks

The two constructions of points of the blowup model in the blueprint, graph points
(`lem:pg-graph-point`, `N(F) = |F(x, G)|_x / |𝔞|_x^b`) and blowup-chart points
(`lem:pg-blowup-chart`(2), `N(F) = |δ(F)|_w μ_x(w)^{-a} μ_y(w)^{-b}`), are both of the form
`N_{(a,b)}(F) = |φ(F)|_w / (μ_x^a μ_y^b)` for a `k`-algebra map `φ : R_{M,M'} → B`, a point
`w ∈ Berk k B` and the scales `μ_x = max_j |φ(xⱼ)|_w`, `μ_y = max_m |φ(y_m)|_w`; if both scales are
nonzero this is a bigraded norm (`BiProjBerk.isBigradedNorm_comapNorm`, no homogeneity of `φ` is
needed), and its bigraded extension is `BiProjBerk.ofComap φ w`. -/

section ofComap

variable {B : Type*} [CommRing B] [Algebra k B]
  (φ : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] B) (w : Berk k B)

/-- The scale `μ_x = max_j |φ(xⱼ)|_w`. -/
def scaleX : ℝ≥0 :=
  Finset.univ.sup fun j => w.val (φ (X (Sum.inl j)))

/-- The scale `μ_y = max_m |φ(y_m)|_w`. -/
def scaleY : ℝ≥0 :=
  Finset.univ.sup fun m => w.val (φ (X (Sum.inr m)))

variable {φ w} in
theorem le_scaleX (j : Fin (M + 1)) : w.val (φ (X (Sum.inl j))) ≤ scaleX φ w :=
  Finset.le_sup (f := fun j => w.val (φ (X (Sum.inl j)))) (Finset.mem_univ j)

variable {φ w} in
theorem le_scaleY (m : Fin (M' + 1)) : w.val (φ (X (Sum.inr m))) ≤ scaleY φ w :=
  Finset.le_sup (f := fun m => w.val (φ (X (Sum.inr m)))) (Finset.mem_univ m)

variable {φ w} in
theorem scaleX_ne_zero {j : Fin (M + 1)} (h : w.val (φ (X (Sum.inl j))) ≠ 0) :
    scaleX φ w ≠ 0 :=
  ne_bot_of_le_ne_bot h (le_scaleX j)

variable {φ w} in
theorem scaleY_ne_zero {m : Fin (M' + 1)} (h : w.val (φ (X (Sum.inr m))) ≠ 0) :
    scaleY φ w ≠ 0 :=
  ne_bot_of_le_ne_bot h (le_scaleY m)

/-- The rescaled pullback `N_{(a,b)}(F) = |φ(F)|_w / (μ_x^a μ_y^b)`. -/
def comapNorm (p : ℕ × ℕ) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) : ℝ≥0 :=
  w.val (φ F) / (scaleX φ w ^ p.1 * scaleY φ w ^ p.2)

/-- `max_i (f i / c) = (max_i f i) / c` over a finite set. -/
private theorem sup_div_const {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) (c : ℝ≥0) :
    (s.sup fun i => f i / c) = s.sup f / c := by
  have h := Finset.apply_sup_eq_sup_comp_of_linearOrder (s := s) (f := f) (fun t : ℝ≥0 => t / c)
    (fun a b hab => by simp only; gcongr) (by simp)
  exact h.symm

/-- The rescaled pullback is a bigraded norm when both scales are nonzero. -/
theorem isBigradedNorm_comapNorm (hx : scaleX φ w ≠ 0) (hy : scaleY φ w ≠ 0) :
    IsBigradedNorm (comapNorm φ w) where
  map_zero p := by simp [comapNorm]
  map_C c hc := by
    rw [comapNorm, ← algebraMap_eq, φ.commutes, w.val_algebraMap c hc]
    simp
  map_mul {p q F G} _ _ := by
    simp only [comapNorm, map_mul, Prod.fst_add, Prod.snd_add, pow_add]
    rw [div_mul_div_comm]
    congr 1
    ring
  map_add_le {p F G} _ _ := by
    simp only [comapNorm]
    rw [max_div_div_right zero_le]
    gcongr
    rw [map_add]
    exact w.val.map_add _ _
  sup_X_inl := by
    simp only [comapNorm, pow_one, pow_zero, mul_one]
    rw [sup_div_const]
    exact div_self hx
  sup_X_inr := by
    simp only [comapNorm, pow_one, pow_zero, one_mul]
    rw [sup_div_const]
    exact div_self hy

/-- The **rescaled pullback point**: the bigraded extension of
`N_{(a,b)}(F) = |φ(F)|_w / (μ_x^a μ_y^b)`. -/
def ofComap (hx : scaleX φ w ≠ 0) (hy : scaleY φ w ≠ 0) : BiProjBerk k M M' :=
  ofBigradedNorm (isBigradedNorm_comapNorm φ w hx hy)

variable {φ w} (hx : scaleX φ w ≠ 0) (hy : scaleY φ w ≠ 0)

/-- On a bihomogeneous `F` of bidegree `(a, b)`: `|F|_{ofComap φ w} = |φ(F)|_w / (μ_x^a μ_y^b)`. -/
theorem ofComap_val_of_isWeightedHomogeneous {a b : ℕ}
    {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    (ofComap φ w hx hy).1.val F = w.val (φ F) / (scaleX φ w ^ a * scaleY φ w ^ b) :=
  ofBigradedNorm_val_of_isWeightedHomogeneous _ hF

/-- `|F|_{ofComap φ w} = 0` if `|φ(F_p)|_w = 0` for all bihomogeneous components `F_p`. -/
theorem ofComap_val_eq_zero {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (h : ∀ p, w.val (φ (weightedHomogeneousComponent (biWeight M M') p F)) = 0) :
    (ofComap φ w hx hy).1.val F = 0 := by
  refine le_antisymm ?_ zero_le
  rw [val_eq_sup]
  refine Finset.sup_le fun p _ => ?_
  rw [ofComap, ofBigradedNorm_val_of_isWeightedHomogeneous _
    (weightedHomogeneousComponent_isWeightedHomogeneous p F), comapNorm, h p, zero_div]

/-- The first projection of a rescaled pullback point, on a form `f` of degree `d` in `x`:
`|f| = |φ(f(x))|_w / μ_x^d`. -/
theorem fst_ofComap_val_of_isHomogeneous {d : ℕ} {f : MvPolynomial (Fin (M + 1)) k}
    (hf : f.IsHomogeneous d) :
    (fst (ofComap φ w hx hy)).1.val f = w.val (φ (rename Sum.inl f)) / scaleX φ w ^ d := by
  rw [ofComap, fst_ofBigradedNorm_val_of_isHomogeneous _ hf, comapNorm, pow_zero, mul_one]

/-- The second projection of a rescaled pullback point, on a form `f` of degree `d` in `y`:
`|f| = |φ(f(y))|_w / μ_y^d`. -/
theorem snd_ofComap_val_of_isHomogeneous {d : ℕ} {f : MvPolynomial (Fin (M' + 1)) k}
    (hf : f.IsHomogeneous d) :
    (snd (ofComap φ w hx hy)).1.val f = w.val (φ (rename Sum.inr f)) / scaleY φ w ^ d := by
  rw [ofComap, snd_ofBigradedNorm_val_of_isHomogeneous _ hf, comapNorm, pow_zero, one_mul]

end ofComap

/-! ### Trivial valuations of bihomogeneous primes

For a prime `P` of `R_{M,M'}` containing the bihomogeneous components of its elements and
containing neither all `xⱼ` nor all `y_m`, the seminorm `|F| = 0` for `F ∈ P`, `|F| = 1` otherwise
(the trivial valuation of `R_{M,M'}/P`) is a point of the model (`BiProjBerk.trivQuot`); for the
ideal `I'` of the blowup this is the point `⋆'` of `lem:pg-blowup-basic`(2). -/

section trivQuot

variable (P : Ideal (MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k)) [P.IsPrime]

theorem comap_mkₐ_triv_val (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) [Decidable (F ∈ P)] :
    (Berk.comap (Ideal.Quotient.mkₐ k P) (Berk.triv : Berk k (_ ⧸ P))).val F =
      if F ∈ P then 0 else 1 := by
  rw [Berk.comap_val_apply, Ideal.Quotient.mkₐ_eq_mk]
  split_ifs with h
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
  · exact Berk.triv_val_of_ne_zero fun h' => h (Ideal.Quotient.eq_zero_iff_mem.1 h')

/-- The trivial valuation of `R_{M,M'}/P` as a point of `(ℙ^M × ℙ^{M'})^an`, for a prime `P`
containing the bihomogeneous components of its elements and containing neither all `xⱼ` nor all
`y_m`: `|F| = 0` for `F ∈ P` and `|F| = 1` otherwise. -/
def trivQuot (hP : ∀ F ∈ P, ∀ p, weightedHomogeneousComponent (biWeight M M') p F ∈ P)
    (hx : ∃ j, X (Sum.inl j) ∉ P) (hy : ∃ m, X (Sum.inr m) ∉ P) : BiProjBerk k M M' := by
  classical
  refine ⟨Berk.comap (Ideal.Quotient.mkₐ k P) Berk.triv, fun F p => ?_, ?_, ?_⟩
  · rw [comap_mkₐ_triv_val, comap_mkₐ_triv_val]
    by_cases hF : F ∈ P
    · rw [if_pos (hP F hF p), if_pos hF]
    · rw [if_neg hF]
      split_ifs <;> simp
  · obtain ⟨j, hj⟩ := hx
    refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
    · rw [comap_mkₐ_triv_val]
      split_ifs <;> simp
    · refine le_trans ?_ (Finset.le_sup (f := fun i => (Berk.comap (Ideal.Quotient.mkₐ k P)
        (Berk.triv : Berk k (_ ⧸ P))).val (X (Sum.inl i))) (Finset.mem_univ j))
      rw [comap_mkₐ_triv_val, if_neg hj]
  · obtain ⟨l, hl⟩ := hy
    refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
    · rw [comap_mkₐ_triv_val]
      split_ifs <;> simp
    · refine le_trans ?_ (Finset.le_sup (f := fun m => (Berk.comap (Ideal.Quotient.mkₐ k P)
        (Berk.triv : Berk k (_ ⧸ P))).val (X (Sum.inr m))) (Finset.mem_univ l))
      rw [comap_mkₐ_triv_val, if_neg hl]

variable {P} (hP : ∀ F ∈ P, ∀ p, weightedHomogeneousComponent (biWeight M M') p F ∈ P)
  (hx : ∃ j, X (Sum.inl j) ∉ P) (hy : ∃ m, X (Sum.inr m) ∉ P)

theorem trivQuot_val_of_mem {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} (hF : F ∈ P) :
    (trivQuot P hP hx hy).1.val F = 0 := by
  classical
  change (Berk.comap (Ideal.Quotient.mkₐ k P) Berk.triv).val F = 0
  rw [comap_mkₐ_triv_val, if_pos hF]

theorem trivQuot_val_of_notMem {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k} (hF : F ∉ P) :
    (trivQuot P hP hx hy).1.val F = 1 := by
  classical
  change (Berk.comap (Ideal.Quotient.mkₐ k P) Berk.triv).val F = 1
  rw [comap_mkₐ_triv_val, if_neg hF]

end trivQuot

end BiProjBerk

end EnvelopeProperty
