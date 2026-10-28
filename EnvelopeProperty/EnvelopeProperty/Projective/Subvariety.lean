/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ClosedImmersion
import EnvelopeProperty.Projective.Chart
import EnvelopeProperty.Projective.FS
import EnvelopeProperty.Local.FS

/-!
# Projective subvarieties `V(I) ⊆ ℙᴹ` in the Berkovich model

Let `k` be a field with the trivial absolute value, `R_M = k[x₀, …, x_M]`, and `I ⊆ R_M` a
homogeneous prime ideal not containing all `xᵢ`, with homogeneous coordinate ring `S'' = R_M / I`.
This file sets up the analytification `V(I)^an ⊆ (ℙᴹ)^an` in the model `ProjBerk k M` of
`EnvelopeProperty.Projective.Basic`, its affine charts, and the two function classes on it used
in the compactification route to FHX Lemma 5.11(5),(6) and for FHX Corollary 5.26 (Fang–Han–Xia,
*The envelope property for unibranch projective varieties*). Blueprint: `wu-discharge.tex`,
subsection `subsec:wu-compactification`, nodes `conv:wu-graded` (the part about `V(I)^an`),
`lem:wu-proj-chart` and `def:wu-proj-functions`.

## Main definitions

* `Berk.zeroLocus J`, `Berk.ofQuot`, `Berk.quotHomeomorph`: for an ideal `J` of a `k`-algebra `A`,
  `(Spec A/J)^an ≃ₜ V(J)^an = {x : |a|_x = 0 for a ∈ J} ⊆ (Spec A)^an` ("seminorms vanishing on an
  ideal are the seminorms of the quotient, with the induced topology").
* `IsHomogeneousIdeal I`: `I` contains the homogeneous components of its elements
  (`isHomogeneousIdeal_iff_isHomogeneous`: Mathlib's `Ideal.IsHomogeneous`).
* `ProjBerk.zeroLocus I = V(I)^an`, closed and compact; `ProjBerk.trivOn`: the trivial valuation
  of `R_M / I` as a point of `V(I)^an`.
* `ProjBerk.chartIdeal I σ d = I_{(σ)} = I R_σ ∩ A_σ` in the chart algebra `A_σ = chartAlg σ d` of
  `Projective/Chart.lean`, and `ProjBerk.QuotChartAlg I σ d = A_σ / I_{(σ)}`, our model of the
  degree-zero part `S''_{(σ̄)}` (no graded-localization API is needed); `quotChartMk`,
  `quotChartGen` are the classes of `τ / σ^N` and `x^α / σ`.
* `ProjBerk.quotChartMap`, `ProjBerk.quotChartInv`, `ProjBerk.quotChartHomeomorph`: the quotient
  charts `U_σ ∩ V(I)^an ≃ₜ (Spec A_σ / I_{(σ)})^an` restricting `ProjBerk.chartHomeomorph`.
* `ProjBerk.quotChartLift`, `ProjBerk.quotChartEquiv`: maps `A_σ / I_{(σ)} → C` induced by
  `φ : R_M → C` with `ker φ = I` and `φ(σ)` a unit, and the resulting identifications of
  `A_σ / I_{(σ)}` with a given algebra.
* `ProjSubvariety k M`: the bundled data `(I, homogeneous, prime, some xᵢ ∉ I)` of `X = V(I)`;
  `X.an = V(I)^an` (a compact space), `X.triv`, the charts `X.chartMap`, `X.chartInv`,
  `X.chartHomeomorph`.
* `ProjSubvariety.IsFiniteFS X a φ` (`def:wu-proj-functions`(1), `a = 1`): finite Fubini–Study
  functions `m⁻¹ max_ℓ (log|τ_ℓ| + μ_ℓ)` of class `O(a)` on `X^an`, `μ_ℓ ∈ ℚ`, the forms `τ_ℓ`
  having no common zero on `X^an`; they reuse `ProjBerk.FSData` (`Projective/FS.lean`).
* `ProjSubvariety.IsLocallyConvexAt`, `ProjSubvariety.IsLocallyConvex X a φ`
  (`def:wu-proj-functions`(2)): near every point, for some form `σ ∉ I` of degree `d ≥ 1`,
  `(φ - (a/d) log|σ|) ∘ ι_σ⁻¹` is convex PL (`IsConvexPLOn`, `Local/Defs.lean`) on the chart.

## Main results

* `ProjBerk.isCompact_zeroLocus`, `ProjSubvariety.isCompact_an` (`lem:wu-proj-chart`(1)).
* `ProjBerk.mem_chartIdeal_iff` (kernel description in the proof of `lem:wu-proj-chart`(2)):
  for `I` prime and `σ ∉ I`, `I_{(σ)} = {τ / σ^N : τ ∈ I a form of degree N d}`;
  `ProjBerk.isPrime_chartIdeal`, `ProjBerk.isDomain_quotChartAlg`,
  `ProjBerk.finiteType_quotChartAlg`.
* `ProjBerk.chartMap_mem_zeroLocus_iff`: for `I` homogeneous, `v ∈ U_σ` lies in `V(I)^an` iff
  `ι_σ(v)` vanishes on `I_{(σ)}`; hence `ProjBerk.quotChartHomeomorph` and
  `ProjSubvariety.isOpenEmbedding_chartInv`, `ProjSubvariety.chartHomeomorph`
  (`lem:wu-proj-chart`(2)).
* `ProjBerk.logAbs_quotChartMap_quotChartMk`, `ProjBerk.sup_logAbs_quotChartMap_quotChartGen` and
  their `ProjSubvariety` versions (`lem:wu-proj-chart`(3)).
* `ProjBerk.quotChartMap_trivOn`, `ProjSubvariety.chartMap_triv`,
  `ProjSubvariety.homeomorphOfAlgEquiv_chartMap_triv`, `ProjBerk.quotChartEquiv`: the generic
  form of `lem:wu-proj-chart`(4) (see below).
* `ProjSubvariety.IsFiniteFS.continuous`, `ProjSubvariety.isFiniteFS_of_fsData`;
  `ProjSubvariety.IsFiniteFS.isLocallyConvex`: finite FS functions of class `O(a)`, `a > 0`, are
  locally `O(a)`-convex (the argument used for `ψ` in the proof of `thm:wu-pl-approx-uniform`);
  `ProjSubvariety.IsLocallyConvexAt.congr`.

## Part (4) of `lem:wu-proj-chart`

This file proves the generic form: `ι_σ` maps the trivial valuation of `R_M / I` to that of the
domain `A_σ / I_{(σ)}`, hence to `v_triv` after any `k`-algebra isomorphism
`A_σ / I_{(σ)} ≃ₐ[k] A` (`ProjSubvariety.homeomorphOfAlgEquiv_chartMap_triv`); `quotChartLift` and
`quotChartEquiv` produce such isomorphisms. The situation of `def:wu-compactification` is treated
in `Projective/SubvarietyRees.lean` (`ProjBerk.IsReesPresentation`, `ProjSubvariety.affineChart`,
`ProjSubvariety.affineChart_triv`), with `S''_{(T^e)} = A` (`lem:wu-graded-closure`(5),
`lem:wu-veronese`) as a hypothesis in the form provided by `exists_veronese_normalizedRees`.
-/

open scoped NNReal ENNReal Topology

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### Generalities -/

section Generalities

/-- If every element violating `p` is dominated by an element `i₀ ∈ s` satisfying `p`, the
supremum over `s` equals the supremum over the elements satisfying `p`. -/
theorem sup_eq_sup_filter_of_le {ι α : Type*} [SemilatticeSup α] [OrderBot α] (s : Finset ι)
    (p : ι → Prop) [DecidablePred p] (F : ι → α) {i₀ : ι} (hi₀ : i₀ ∈ s) (hp₀ : p i₀)
    (h : ∀ i ∈ s, ¬ p i → F i ≤ F i₀) : s.sup F = (s.filter p).sup F := by
  refine le_antisymm (Finset.sup_le fun i hi => ?_) (Finset.sup_mono (Finset.filter_subset _ _))
  by_cases hp : p i
  · exact Finset.le_sup (Finset.mem_filter.2 ⟨hi, hp⟩)
  · exact (h i hi hp).trans (Finset.le_sup (Finset.mem_filter.2 ⟨hi₀, hp₀⟩))

/-- A finite supremum of real numbers, computed in `EReal`. -/
theorem ereal_finset_sup_coe {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (G : ι → ℝ) :
    (S.sup fun i => (G i : EReal)) = ((S.sup' hS G : ℝ) : EReal) := by
  rw [← Finset.sup'_eq_sup hS]
  exact (Finset.apply_sup'_eq_sup'_comp hS (fun x : ℝ => (x : EReal))
    fun x y => EReal.coe_strictMono.monotone.map_max).symm

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- The locus where finitely many functions do not vanish is open. -/
theorem isOpen_setOf_forall_val_ne_zero {ι : Type*} (S : Finset ι) (f : ι → A) :
    IsOpen {y : Berk k A | ∀ i ∈ S, y.val (f i) ≠ 0} := by
  have e : {y : Berk k A | ∀ i ∈ S, y.val (f i) ≠ 0} = ⋂ i ∈ S, {y | y.val (f i) ≠ 0} := by
    ext; simp
  rw [e]
  exact isOpen_biInter_finset fun i _ => Berk.isOpen_setOf_abs_ne_zero (f i)

/-- A finite maximum `max_{i ∈ S} (log|fᵢ| + qᵢ)`, `qᵢ ∈ ℚ`, is convex PL where the `fᵢ` do not
vanish. -/
theorem isConvexPLOn_sup_logAbs_add {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (f : ι → A)
    (q : ι → ℚ) :
    IsConvexPLOn {y : Berk k A | ∀ i ∈ S, y.val (f i) ≠ 0}
      fun y => S.sup fun i => Berk.logAbs (f i) y + ((q i : ℝ) : EReal) := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton i =>
    refine (((isConvexPLOn_smul_logAbs (k := k) (f i) 1).add_const (q i)).mono
      (isOpen_setOf_forall_val_ne_zero _ f) fun y hy => hy i (Finset.mem_singleton_self i)).congr
      fun y _ => ?_
    simp
  | cons i s hi hs ih =>
    have hO := isOpen_setOf_forall_val_ne_zero (k := k) (Finset.cons i s hi) f
    have h1 := ((isConvexPLOn_smul_logAbs (k := k) (f i) 1).add_const (q i)).mono hO
      fun y hy => hy i (Finset.mem_cons_self i s)
    have h2 := ih.mono hO fun y hy j hj => hy j (Finset.mem_cons_of_mem hj)
    refine (h1.max h2).congr fun y _ => ?_
    simp

end Generalities

/-! ### The analytification of a quotient -/

namespace Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] (J : Ideal A)

/- The affine zero locus and its closedness are reused from ClosedImmersion.
They are definitionally the same vanishing condition and retain their original API. -/

variable {J}

/-- The point of `(Spec A/J)^an` defined by a point of `(Spec A)^an` vanishing on `J`. -/
def ofQuot (x : Berk k A) (hx : x ∈ zeroLocus J) : Berk k (A ⧸ J) where
  val := x.val.onQuot hx
  val_algebraMap c hc := by
    rw [← Ideal.Quotient.mk_algebraMap]
    exact x.val_algebraMap c hc

@[simp]
theorem ofQuot_val_mk (x : Berk k A) (hx : x ∈ zeroLocus J) (a : A) :
    (ofQuot x hx).val (Ideal.Quotient.mk J a) = x.val a :=
  rfl

variable (J) in
theorem comap_mkₐ_mem_zeroLocus (y : Berk k (A ⧸ J)) :
    comap (Ideal.Quotient.mkₐ k J) y ∈ zeroLocus J := by
  rw [mem_zeroLocus_iff]
  intro a ha
  rw [comap_val_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

@[simp]
theorem comap_mkₐ_ofQuot (x : Berk k A) (hx : x ∈ zeroLocus J) :
    comap (Ideal.Quotient.mkₐ k J) (ofQuot x hx) = x :=
  ext_val fun _ => rfl

@[simp]
theorem ofQuot_comap_mkₐ (y : Berk k (A ⧸ J)) :
    ofQuot (comap (Ideal.Quotient.mkₐ k J) y) (comap_mkₐ_mem_zeroLocus J y) = y := by
  refine ext_val fun b => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

/-- A map into `(Spec A/J)^an` built pointwise by `ofQuot` is continuous as soon as the
underlying map into `(Spec A)^an` is. -/
theorem continuous_ofQuot {X : Type*} [TopologicalSpace X] {g : X → Berk k A}
    (hg : Continuous g) (hgJ : ∀ x, g x ∈ zeroLocus J) :
    Continuous fun x => ofQuot (g x) (hgJ x) := by
  rw [continuous_iff]
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact (continuous_abs a).comp hg

variable (J) in
/-- `(Spec A/J)^an` is homeomorphic to the zero locus `V(J)^an ⊆ (Spec A)^an`. -/
def quotHomeomorph : Berk k (A ⧸ J) ≃ₜ zeroLocus (k := k) J where
  toFun y := ⟨comap (Ideal.Quotient.mkₐ k J) y, comap_mkₐ_mem_zeroLocus J y⟩
  invFun x := ofQuot x.1 x.2
  left_inv y := ofQuot_comap_mkₐ y
  right_inv x := Subtype.ext (comap_mkₐ_ofQuot x.1 x.2)
  continuous_toFun := (continuous_comap _).subtype_mk _
  continuous_invFun := continuous_ofQuot continuous_subtype_val fun x => x.2

variable (J) in
/-- `(Spec A/J)^an → (Spec A)^an` is a closed embedding with image `V(J)^an`. -/
theorem isClosedEmbedding_comap_mkₐ :
    IsClosedEmbedding (comap (k := k) (Ideal.Quotient.mkₐ k J)) :=
  (isClosed_zeroLocus J).isClosedEmbedding_subtypeVal.comp (quotHomeomorph J).isClosedEmbedding

variable (J) in
theorem range_comap_mkₐ :
    Set.range (comap (k := k) (Ideal.Quotient.mkₐ k J)) = zeroLocus J := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨ofQuot x hx, comap_mkₐ_ofQuot x hx⟩
  rintro _ ⟨y, rfl⟩
  exact comap_mkₐ_mem_zeroLocus J y

/-- A `k`-algebra isomorphism of domains maps the trivial valuation to the trivial valuation. -/
theorem homeomorphOfAlgEquiv_triv {B : Type*} [CommRing B] [Algebra k B] [IsDomain A]
    [IsDomain B] (φ : A ≃ₐ[k] B) : homeomorphOfAlgEquiv φ triv = triv := by
  refine ext_val fun b => ?_
  rw [homeomorphOfAlgEquiv_val_apply]
  by_cases hb : b = 0
  · simp [hb]
  · rw [triv_val_of_ne_zero hb, triv_val_of_ne_zero]
    simpa using hb

end Berk

/-! ### Homogeneous ideals -/

section HomogeneousIdeal

variable {k : Type*} [Field k] {ι : Type*}

/-- An ideal of `k[xᵢ : i ∈ ι]` is **homogeneous** if it contains the homogeneous components of
its elements (`isHomogeneousIdeal_iff_isHomogeneous` compares with Mathlib's
`Ideal.IsHomogeneous` for the grading by degree). -/
def IsHomogeneousIdeal (I : Ideal (MvPolynomial ι k)) : Prop :=
  ∀ f ∈ I, ∀ d, homogeneousComponent d f ∈ I

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isHomogeneousIdeal_iff_isHomogeneous (I : Ideal (MvPolynomial ι k)) :
    IsHomogeneousIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule ι k) := by
  refine ⟨fun h i r hr => ?_, fun h f hf d => homogeneousComponent_mem_of_mem h hf d⟩
  convert h r hr i
  exact decomposition.decompose'_apply (R := k) r i

end HomogeneousIdeal

namespace ProjBerk

variable {k : Type u} [Field k] {M : ℕ}

/-! ### The zero locus `V(I)^an ⊆ (ℙᴹ)^an` -/

section ZeroLocus

variable (I : Ideal (MvPolynomial (Fin (M + 1)) k))

/-- The **zero locus** `V(I)^an = {v ∈ (ℙᴹ)^an : |f|_v = 0 for all f ∈ I}` of an ideal of
`R_M = k[x₀, …, x_M]` (`conv:wu-graded`). -/
def zeroLocus : Set (ProjBerk k M) := {v | ∀ f ∈ I, v.1.val f = 0}

theorem zeroLocus_eq_preimage : zeroLocus I = Subtype.val ⁻¹' Berk.zeroLocus I := rfl

theorem isClosed_zeroLocus : IsClosed (zeroLocus I) :=
  (Berk.isClosed_zeroLocus I).preimage continuous_val

/-- **`V(I)^an` is compact** (`lem:wu-proj-chart`(1)): it is closed in the compact space
`(ℙᴹ)^an`. -/
theorem isCompact_zeroLocus : IsCompact (zeroLocus I) :=
  (isClosed_zeroLocus I).isCompact

instance instCompactSpaceZeroLocus : CompactSpace (zeroLocus I) :=
  isCompact_iff_compactSpace.1 (isCompact_zeroLocus I)

variable {I}

/-- For a homogeneous ideal it suffices to vanish on its homogeneous elements: points of
`(ℙᴹ)^an` are graded. -/
theorem mem_zeroLocus_iff (hI : IsHomogeneousIdeal I) {v : ProjBerk k M} :
    v ∈ zeroLocus I ↔ ∀ (D : ℕ) (f : MvPolynomial (Fin (M + 1)) k), f.IsHomogeneous D → f ∈ I →
      v.1.val f = 0 := by
  refine ⟨fun h D f _ hf => h f hf, fun h f hf => ?_⟩
  rw [isGraded v f]
  exact le_antisymm (Finset.sup_le fun D _ =>
    (h D _ (homogeneousComponent_isHomogeneous D f) (hI f hf D)).le) zero_le

/-! #### The trivial valuation of `V(I)` -/

/-- The trivial valuation of `V(I)` for a homogeneous prime `I` not containing all `xᵢ`:
`|f| = 0` for `f ∈ I` and `|f| = 1` otherwise, i.e. the trivial valuation of `R_M / I`. -/
def trivOn (hI : IsHomogeneousIdeal I) [I.IsPrime]
    (hX : ∃ i, (X i : MvPolynomial (Fin (M + 1)) k) ∉ I) : ProjBerk k M :=
  ⟨Berk.comap (Ideal.Quotient.mkₐ k I) Berk.triv, by
    rw [isGraded_iff]
    intro f d
    by_cases hf : f ∈ I
    · rw [Berk.comap_val_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.2 (hI f hf d), map_zero]
      exact zero_le
    · rw [Berk.comap_val_apply, Berk.comap_val_apply, Ideal.Quotient.mkₐ_eq_mk,
        Berk.triv_val_of_ne_zero (fun h => hf (Ideal.Quotient.eq_zero_iff_mem.1 h))]
      by_cases h0 : Ideal.Quotient.mk I (homogeneousComponent d f) = 0
      · rw [h0, map_zero]; exact zero_le
      · rw [Berk.triv_val_of_ne_zero h0], by
    obtain ⟨i, hi⟩ := hX
    have hval : ∀ j,
        (Berk.comap (Ideal.Quotient.mkₐ k I) (Berk.triv : Berk k (_ ⧸ I))).val (X j) ≤ 1 := by
      intro j
      rw [Berk.comap_val_apply, Ideal.Quotient.mkₐ_eq_mk]
      by_cases h0 : Ideal.Quotient.mk I (X j : MvPolynomial (Fin (M + 1)) k) = 0
      · rw [h0, map_zero]; exact zero_le
      · rw [Berk.triv_val_of_ne_zero h0]
    refine le_antisymm (Finset.sup_le fun j _ => hval j) ?_
    refine le_trans ?_ (Finset.le_sup (f := fun j => (Berk.comap (Ideal.Quotient.mkₐ k I)
      (Berk.triv : Berk k (_ ⧸ I))).val (X j)) (Finset.mem_univ i))
    rw [Berk.comap_val_apply, Ideal.Quotient.mkₐ_eq_mk,
      Berk.triv_val_of_ne_zero (fun h => hi (Ideal.Quotient.eq_zero_iff_mem.1 h))]⟩

section trivOn

variable (hI : IsHomogeneousIdeal I) [I.IsPrime]
  (hX : ∃ i, (X i : MvPolynomial (Fin (M + 1)) k) ∉ I)

theorem trivOn_val_of_mem {f : MvPolynomial (Fin (M + 1)) k} (hf : f ∈ I) :
    (trivOn hI hX).1.val f = 0 := by
  change (Berk.triv : Berk k (_ ⧸ I)).val (Ideal.Quotient.mk I f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]

theorem trivOn_val_of_notMem {f : MvPolynomial (Fin (M + 1)) k} (hf : f ∉ I) :
    (trivOn hI hX).1.val f = 1 :=
  Berk.triv_val_of_ne_zero (k := k) (A := MvPolynomial (Fin (M + 1)) k ⧸ I)
    (fun h => hf (Ideal.Quotient.eq_zero_iff_mem.1 h))

theorem trivOn_mem_zeroLocus : trivOn hI hX ∈ zeroLocus I :=
  fun _ hf => trivOn_val_of_mem hI hX hf

end trivOn

end ZeroLocus

/-! ### The ideal `I_{(σ)}` of the chart algebra and the quotient chart algebra -/

section ChartIdeal

variable (I : Ideal (MvPolynomial (Fin (M + 1)) k)) (σ : MvPolynomial (Fin (M + 1)) k) (d : ℕ)

/-- The ideal `I_{(σ)} = I R_σ ∩ A_σ` of the chart algebra `A_σ = (R_M)_{(σ)}`
(`lem:wu-proj-chart`(2)); for `I` prime with `σ ∉ I` it consists of the fractions `τ / σ^N`
with `τ ∈ I` a form of degree `N d` (`mem_chartIdeal_iff`). -/
def chartIdeal : Ideal (chartAlg σ d) :=
  (I.map (algebraMap (MvPolynomial (Fin (M + 1)) k) (Localization.Away σ))).comap
    (chartAlg σ d).val

/-- The **quotient chart algebra** `A_σ / I_{(σ)}`, our model of the degree-zero part
`S''_{(σ̄)}` of the localization of `S'' = R_M / I` at the image `σ̄` of `σ`: the kernel of
`(R_M)_{(σ)} → S''_{(σ̄)}` is `I_{(σ)}` (`mem_chartIdeal_iff`). -/
abbrev QuotChartAlg : Type u := chartAlg σ d ⧸ chartIdeal I σ d

/-- The class `τ̄ / σ̄^N ∈ A_σ / I_{(σ)}` of `τ_{Nd} / σ^N`, where `τ_{Nd}` is the homogeneous
component of degree `N d` of `τ`. -/
def quotChartMk (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k) : QuotChartAlg I σ d :=
  Ideal.Quotient.mk _ (chartMk σ d N τ)

/-- The generator `x̄^α / σ̄` of `A_σ / I_{(σ)}` (for `|α| = d`). -/
def quotChartGen (α : Fin (M + 1) →₀ ℕ) : QuotChartAlg I σ d :=
  Ideal.Quotient.mk _ (chartGen σ d α)

variable {I σ d}

theorem mem_chartIdeal_iff_coe {a : chartAlg σ d} :
    a ∈ chartIdeal I σ d ↔
      (a : Localization.Away σ) ∈ I.map (algebraMap _ (Localization.Away σ)) :=
  Iff.rfl

/-- `τ / σ^N ∈ I_{(σ)}` for a form `τ ∈ I` of degree `N d`. -/
theorem chartMk_mem_chartIdeal {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous (N * d)) (hτI : τ ∈ I) : chartMk σ d N τ ∈ chartIdeal I σ d := by
  rw [mem_chartIdeal_iff_coe, coe_chartMk hτ, frac]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hτI)

theorem disjoint_powers_of_notMem [I.IsPrime] (hσI : σ ∉ I) :
    Disjoint (Submonoid.powers σ : Set (MvPolynomial (Fin (M + 1)) k)) I := by
  rw [Set.disjoint_left]
  rintro _ ⟨N, rfl⟩ h
  exact hσI (Ideal.IsPrime.mem_of_pow_mem ‹_› N h)

/-- `τ / σ^N ∈ I_{(σ)}` forces `τ ∈ I` when `I` is prime and `σ ∉ I`. -/
theorem mem_of_chartMk_mem_chartIdeal [I.IsPrime] (hσI : σ ∉ I) {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous (N * d))
    (h : chartMk σ d N τ ∈ chartIdeal I σ d) : τ ∈ I := by
  have h1 : algebraMap _ (Localization.Away σ) τ ∈
      I.map (algebraMap _ (Localization.Away σ)) := by
    have e : algebraMap _ (Localization.Away σ) τ =
        (chartMk σ d N τ : Localization.Away σ) * algebraMap _ _ (σ ^ N) := by
      rw [coe_chartMk hτ, frac, map_pow, mul_assoc, ← mul_pow,
        mul_comm (IsLocalization.Away.invSelf σ : Localization.Away σ),
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    rw [e]
    exact Ideal.mul_mem_right _ _ h
  have h2 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers σ)
    (Localization.Away σ) ‹I.IsPrime› (disjoint_powers_of_notMem hσI)
  rw [← h2]
  exact h1

/-- **Kernel description** (proof of `lem:wu-proj-chart`(2)): for `I` prime and `σ ∉ I` a form
of degree `d`, `I_{(σ)} = {τ / σ^N : τ ∈ I a form of degree N d}`. -/
theorem mem_chartIdeal_iff [I.IsPrime] (hσ : σ.IsHomogeneous d) (hσI : σ ∉ I)
    {a : chartAlg σ d} :
    a ∈ chartIdeal I σ d ↔ ∃ (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k),
      τ.IsHomogeneous (N * d) ∧ τ ∈ I ∧ a = chartMk σ d N τ := by
  refine ⟨fun ha => ?_, ?_⟩
  · obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_chartMk hσ a
    exact ⟨N, τ, hτ, mem_of_chartMk_mem_chartIdeal hσI hτ ha, rfl⟩
  · rintro ⟨N, τ, hτ, hτI, rfl⟩
    exact chartMk_mem_chartIdeal hτ hτI

/-- `τ̄ / σ̄^N = 0` iff `τ ∈ I`, for `I` prime, `σ ∉ I` and `τ` a form of degree `N d`. -/
theorem quotChartMk_eq_zero_iff [I.IsPrime] (hσI : σ ∉ I) {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous (N * d)) :
    quotChartMk I σ d N τ = 0 ↔ τ ∈ I := by
  rw [quotChartMk, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨mem_of_chartMk_mem_chartIdeal hσI hτ, chartMk_mem_chartIdeal hτ⟩

/-- `I_{(σ)}` is prime for `I` prime and `σ ∉ I`. -/
theorem isPrime_chartIdeal [I.IsPrime] (hσI : σ ∉ I) : (chartIdeal I σ d).IsPrime := by
  have := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers σ) (Localization.Away σ)
    I ‹_› (disjoint_powers_of_notMem hσI)
  exact Ideal.comap_isPrime _ _

/-- `A_σ / I_{(σ)}` is a domain for `I` prime and `σ ∉ I`. Not an instance, as it depends on
`σ ∉ I`. -/
theorem isDomain_quotChartAlg [I.IsPrime] (hσI : σ ∉ I) : IsDomain (QuotChartAlg I σ d) :=
  have := isPrime_chartIdeal (d := d) hσI
  Ideal.Quotient.isDomain _

/-- `A_σ / I_{(σ)}` is generated by the `x̄^α / σ̄`, `|α| = d`. -/
theorem adjoin_quotChartGen (hσ : σ.IsHomogeneous d) :
    Algebra.adjoin k (quotChartGen I σ d '' {α | α.degree = d}) = ⊤ := by
  have h := congrArg (Subalgebra.map (Ideal.Quotient.mkₐ k (chartIdeal I σ d)))
    (adjoin_chartGen hσ)
  rw [AlgHom.map_adjoin, Algebra.map_top,
    (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective k _), ← Set.image_comp] at h
  exact h

/-- `A_σ / I_{(σ)}` is a finitely generated `k`-algebra. -/
theorem finiteType_quotChartAlg (hσ : σ.IsHomogeneous d) :
    Algebra.FiniteType k (QuotChartAlg I σ d) :=
  haveI := finiteType_chartAlg hσ
  Algebra.FiniteType.trans (S := chartAlg σ d) inferInstance inferInstance

end ChartIdeal

/-! ### The quotient charts `U_σ ∩ V(I)^an ≃ₜ (Spec A_σ / I_{(σ)})^an` -/

section QuotChart

variable {I : Ideal (MvPolynomial (Fin (M + 1)) k)} {σ : MvPolynomial (Fin (M + 1)) k} {d : ℕ}

/-- On `V(I)^an ∩ U_σ`, the chart point `ι_σ(v)` vanishes on `I_{(σ)}`: the extension of `v` to
`R_σ` vanishes on `I R_σ`. -/
theorem chartMap_mem_zeroLocus {v : ProjBerk k M} (hv : v.1.val σ ≠ 0) (hvI : v ∈ zeroLocus I) :
    chartMap σ d v hv ∈ Berk.zeroLocus (chartIdeal I σ d) := by
  rw [Berk.mem_zeroLocus_iff]
  intro a ha
  have hle : I.map (algebraMap _ (Localization.Away σ)) ≤ (Berk.awayLift σ v.1 hv).val.supp := by
    refine Ideal.map_le_iff_le_comap.2 fun f hf => ?_
    rw [Ideal.mem_comap, Valuation.mem_supp_iff, Berk.awayLift_val_algebraMap]
    exact hvI f hf
  rw [chartMap_val_apply]
  exact (Valuation.mem_supp_iff _ _).1 (hle ha)

/-- Conversely, for `I` homogeneous, a point `v ∈ U_σ` whose chart point vanishes on `I_{(σ)}`
lies in `V(I)^an`: for a form `τ ∈ I` of degree `D`, `τ^d / σ^D ∈ I_{(σ)}` and
`|τ^d / σ^D|_{ι_σ(v)} = |τ|_v^d / |σ|_v^D`. -/
theorem mem_zeroLocus_of_chartMap (hI : IsHomogeneousIdeal I) (hd : 0 < d) {v : ProjBerk k M}
    (hv : v.1.val σ ≠ 0) (h : chartMap σ d v hv ∈ Berk.zeroLocus (chartIdeal I σ d)) :
    v ∈ zeroLocus I := by
  have h := (Berk.mem_zeroLocus_iff _ _).mp h
  rw [mem_zeroLocus_iff hI]
  intro D f hf hfI
  have hfd : (f ^ d).IsHomogeneous (D * d) := hf.pow d
  have h0 := h _ (chartMk_mem_chartIdeal hfd (Ideal.pow_mem_of_mem I hfI d hd))
  rw [chartMap_val_chartMk_of_isHomogeneous v hv hfd, map_pow,
    div_eq_zero_iff, or_iff_left (pow_ne_zero _ hv)] at h0
  exact pow_eq_zero_iff hd.ne' |>.1 h0

theorem chartMap_mem_zeroLocus_iff (hI : IsHomogeneousIdeal I) (hd : 0 < d) {v : ProjBerk k M}
    (hv : v.1.val σ ≠ 0) :
    chartMap σ d v hv ∈ Berk.zeroLocus (chartIdeal I σ d) ↔ v ∈ zeroLocus I :=
  ⟨mem_zeroLocus_of_chartMap hI hd hv, chartMap_mem_zeroLocus hv⟩

variable (I σ d)

/-- The **quotient chart map** `ι_σ : U_σ ∩ V(I)^an → (Spec A_σ / I_{(σ)})^an`,
`|τ̄ / σ̄^N|_{ι_σ(v)} = |τ|_v / |σ|_v^N` (`lem:wu-proj-chart`(2)). -/
def quotChartMap (v : ProjBerk k M) (hv : v.1.val σ ≠ 0) (hvI : v ∈ zeroLocus I) :
    Berk k (QuotChartAlg I σ d) :=
  Berk.ofQuot (chartMap σ d v hv) (chartMap_mem_zeroLocus hv hvI)

/-- The inverse quotient chart `(Spec A_σ / I_{(σ)})^an → U_σ ⊆ (ℙᴹ)^an`; it lands in `V(I)^an`
when `I` is homogeneous (`quotChartInv_mem_zeroLocus`). -/
def quotChartInv (hσ : σ.IsHomogeneous d) (hd : 0 < d) (y : Berk k (QuotChartAlg I σ d)) :
    ProjBerk k M :=
  chartInv σ d hσ hd (Berk.comap (Ideal.Quotient.mkₐ k _) y)

variable {I σ d}

@[simp]
theorem quotChartMap_val_mk (v : ProjBerk k M) (hv : v.1.val σ ≠ 0) (hvI : v ∈ zeroLocus I)
    (a : chartAlg σ d) :
    (quotChartMap I σ d v hv hvI).val (Ideal.Quotient.mk _ a) = (chartMap σ d v hv).val a :=
  rfl

theorem comap_quotChartMap (v : ProjBerk k M) (hv : v.1.val σ ≠ 0) (hvI : v ∈ zeroLocus I) :
    Berk.comap (Ideal.Quotient.mkₐ k _) (quotChartMap I σ d v hv hvI) = chartMap σ d v hv :=
  Berk.comap_mkₐ_ofQuot _ _

/-- `|τ̄ / σ̄^N|_{ι_σ(v)} = |τ|_v / |σ|_v^N` for a form `τ` of degree `N d`. -/
theorem quotChartMap_val_quotChartMk (v : ProjBerk k M) (hv : v.1.val σ ≠ 0)
    (hvI : v ∈ zeroLocus I) {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous (N * d)) :
    (quotChartMap I σ d v hv hvI).val (quotChartMk I σ d N τ) = v.1.val τ / v.1.val σ ^ N :=
  chartMap_val_chartMk_of_isHomogeneous v hv hτ

/-- `log|τ̄ / σ̄^N| ∘ ι_σ = log|τ| - N log|σ|` on `U_σ ∩ V(I)^an` (`lem:wu-proj-chart`(3)). -/
theorem logAbs_quotChartMap_quotChartMk (v : ProjBerk k M) (hv : v.1.val σ ≠ 0)
    (hvI : v ∈ zeroLocus I) {N : ℕ} {τ : MvPolynomial (Fin (M + 1)) k}
    (hτ : τ.IsHomogeneous (N * d)) :
    Berk.logAbs (quotChartMk I σ d N τ) (quotChartMap I σ d v hv hvI) =
      logAbs τ v - N * logAbs σ v :=
  logAbs_chartMap_chartMk v hv hτ

/-- `max_{|α| = d} log|x̄^α / σ̄| ∘ ι_σ = -log|σ|` on `U_σ ∩ V(I)^an` (`lem:wu-proj-chart`(3));
dividing by `d` gives the form `-(1/d) log|σ| = (1/d) max_{|α| = d} log|x̄^α / σ̄| ∘ ι_σ` of the
blueprint. -/
theorem sup_logAbs_quotChartMap_quotChartGen (v : ProjBerk k M) (hv : v.1.val σ ≠ 0)
    (hvI : v ∈ zeroLocus I) :
    (Finset.finsuppAntidiag Finset.univ d).sup
      (fun α => Berk.logAbs (quotChartGen I σ d α) (quotChartMap I σ d v hv hvI)) =
      -logAbs σ v :=
  sup_logAbs_chartMap_chartGen v hv

theorem quotChartInv_val_ne_zero (hσ : σ.IsHomogeneous d) (hd : 0 < d)
    (y : Berk k (QuotChartAlg I σ d)) : (quotChartInv I σ d hσ hd y).1.val σ ≠ 0 :=
  chartInv_val_ne_zero hσ hd _

theorem quotChartInv_mem_chartDomain (hσ : σ.IsHomogeneous d) (hd : 0 < d)
    (y : Berk k (QuotChartAlg I σ d)) : quotChartInv I σ d hσ hd y ∈ chartDomain σ :=
  quotChartInv_val_ne_zero hσ hd y

theorem chartMap_quotChartInv (hσ : σ.IsHomogeneous d) (hd : 0 < d)
    (y : Berk k (QuotChartAlg I σ d)) :
    chartMap σ d (quotChartInv I σ d hσ hd y) (quotChartInv_val_ne_zero hσ hd y) =
      Berk.comap (Ideal.Quotient.mkₐ k _) y :=
  chartMap_chartInv hσ hd _

theorem quotChartInv_mem_zeroLocus (hI : IsHomogeneousIdeal I) (hσ : σ.IsHomogeneous d)
    (hd : 0 < d) (y : Berk k (QuotChartAlg I σ d)) : quotChartInv I σ d hσ hd y ∈ zeroLocus I := by
  refine mem_zeroLocus_of_chartMap hI hd (quotChartInv_val_ne_zero hσ hd y) ?_
  rw [chartMap_quotChartInv]
  exact Berk.comap_mkₐ_mem_zeroLocus _ y

theorem quotChartMap_quotChartInv (hI : IsHomogeneousIdeal I) (hσ : σ.IsHomogeneous d)
    (hd : 0 < d) (y : Berk k (QuotChartAlg I σ d)) :
    quotChartMap I σ d (quotChartInv I σ d hσ hd y) (quotChartInv_val_ne_zero hσ hd y)
      (quotChartInv_mem_zeroLocus hI hσ hd y) = y := by
  refine Berk.ext_val fun b => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [quotChartMap_val_mk, chartMap_quotChartInv]
  rfl

theorem quotChartInv_quotChartMap (hσ : σ.IsHomogeneous d) (hd : 0 < d) (v : ProjBerk k M)
    (hv : v.1.val σ ≠ 0) (hvI : v ∈ zeroLocus I) :
    quotChartInv I σ d hσ hd (quotChartMap I σ d v hv hvI) = v := by
  rw [quotChartInv, comap_quotChartMap, chartInv_chartMap]

theorem continuous_quotChartInv (hσ : σ.IsHomogeneous d) (hd : 0 < d) :
    Continuous (quotChartInv I σ d hσ hd) :=
  (continuous_chartInv hσ hd).comp (Berk.continuous_comap _)

/-- Continuity of the chart map along a continuous family of points of `U_σ`. -/
theorem continuous_chartMap_comp {Y : Type*} [TopologicalSpace Y] {g : Y → ProjBerk k M}
    (hg : Continuous g) (hgσ : ∀ y, (g y).1.val σ ≠ 0) :
    Continuous fun y => chartMap σ d (g y) (hgσ y) := by
  rw [Berk.continuous_iff]
  intro a
  have h1 : Continuous fun y =>
      (⟨(g y).1, hgσ y⟩ : {x : Berk k (MvPolynomial (Fin (M + 1)) k) // x.val σ ≠ 0}) :=
    (continuous_val.comp hg).subtype_mk _
  exact (Berk.continuous_abs (a : Localization.Away σ)).comp
    ((Berk.continuous_awayLift σ).comp h1)

/-- Continuity of the quotient chart map along a continuous family of points of
`U_σ ∩ V(I)^an`. -/
theorem continuous_quotChartMap_comp {Y : Type*} [TopologicalSpace Y] {g : Y → ProjBerk k M}
    (hg : Continuous g) (hgσ : ∀ y, (g y).1.val σ ≠ 0) (hgI : ∀ y, g y ∈ zeroLocus I) :
    Continuous fun y => quotChartMap I σ d (g y) (hgσ y) (hgI y) :=
  Berk.continuous_ofQuot (continuous_chartMap_comp hg hgσ) _

theorem continuous_quotChartMap :
    Continuous fun v : ↥(chartDomain σ ∩ zeroLocus I) => quotChartMap I σ d v.1 v.2.1 v.2.2 :=
  continuous_quotChartMap_comp continuous_subtype_val (fun v => v.2.1) fun v => v.2.2

variable (I σ d) in
/-- **Quotient charts** (`lem:wu-proj-chart`(2)): for a homogeneous ideal `I` and a form `σ` of
degree `d ≥ 1`, the chart `ι_σ` restricts to a homeomorphism of `U_σ ∩ V(I)^an` onto
`(Spec A_σ / I_{(σ)})^an`, where `A_σ / I_{(σ)}` models `S''_{(σ̄)}` for `S'' = R_M / I`. -/
def quotChartHomeomorph (hI : IsHomogeneousIdeal I) (hσ : σ.IsHomogeneous d) (hd : 0 < d) :
    ↥(chartDomain σ ∩ zeroLocus I) ≃ₜ Berk k (QuotChartAlg I σ d) where
  toFun v := quotChartMap I σ d v.1 v.2.1 v.2.2
  invFun y := ⟨quotChartInv I σ d hσ hd y, quotChartInv_val_ne_zero hσ hd y,
    quotChartInv_mem_zeroLocus hI hσ hd y⟩
  left_inv v := Subtype.ext (quotChartInv_quotChartMap hσ hd v.1 v.2.1 v.2.2)
  right_inv y := quotChartMap_quotChartInv hI hσ hd y
  continuous_toFun := continuous_quotChartMap
  continuous_invFun := (continuous_quotChartInv hσ hd).subtype_mk _

section quotChartHomeomorph

variable (hI : IsHomogeneousIdeal I) (hσ : σ.IsHomogeneous d) (hd : 0 < d)

@[simp]
theorem quotChartHomeomorph_apply (v : ↥(chartDomain σ ∩ zeroLocus I)) :
    quotChartHomeomorph I σ d hI hσ hd v = quotChartMap I σ d v.1 v.2.1 v.2.2 :=
  rfl

@[simp]
theorem coe_quotChartHomeomorph_symm_apply (y : Berk k (QuotChartAlg I σ d)) :
    ((quotChartHomeomorph I σ d hI hσ hd).symm y : ProjBerk k M) = quotChartInv I σ d hσ hd y :=
  rfl

include hI in
theorem range_quotChartInv :
    Set.range (quotChartInv I σ d hσ hd) = chartDomain σ ∩ zeroLocus I := by
  refine Set.Subset.antisymm ?_ fun v hv => ⟨_, quotChartInv_quotChartMap hσ hd v hv.1 hv.2⟩
  rintro _ ⟨y, rfl⟩
  exact ⟨quotChartInv_val_ne_zero hσ hd y, quotChartInv_mem_zeroLocus hI hσ hd y⟩

include hI in
/-- The inverse quotient chart is a homeomorphism onto `U_σ ∩ V(I)^an`, which is open in
`V(I)^an`; as a map into `(ℙᴹ)^an` it is an embedding. -/
theorem isEmbedding_quotChartInv : IsEmbedding (quotChartInv I σ d hσ hd) :=
  IsEmbedding.subtypeVal.comp (quotChartHomeomorph I σ d hI hσ hd).symm.isEmbedding

end quotChartHomeomorph

/-- **The trivial valuation in the quotient charts** (generic form of `lem:wu-proj-chart`(4)):
for a homogeneous prime `I` and a form `σ ∉ I` of degree `d ≥ 1`, `ι_σ` maps the trivial
valuation of `R_M / I` to the trivial valuation of the domain `A_σ / I_{(σ)}`
(`isDomain_quotChartAlg`). -/
theorem quotChartMap_trivOn (hI : IsHomogeneousIdeal I) [I.IsPrime]
    (hX : ∃ i, (X i : MvPolynomial (Fin (M + 1)) k) ∉ I) (hσ : σ.IsHomogeneous d)
    (hσI : σ ∉ I) [IsDomain (QuotChartAlg I σ d)] :
    quotChartMap I σ d (trivOn hI hX) (by rw [trivOn_val_of_notMem hI hX hσI]; exact one_ne_zero)
      (trivOn_mem_zeroLocus hI hX) = Berk.triv := by
  refine Berk.ext_val fun b => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_chartMk hσ a
  change (quotChartMap I σ d _ _ _).val (quotChartMk I σ d N τ) =
    (Berk.triv : Berk k (QuotChartAlg I σ d)).val (quotChartMk I σ d N τ)
  rw [quotChartMap_val_quotChartMk _ _ _ hτ, trivOn_val_of_notMem hI hX hσI, one_pow, div_one]
  by_cases hτI : τ ∈ I
  · rw [trivOn_val_of_mem hI hX hτI, (quotChartMk_eq_zero_iff hσI hτ).2 hτI, map_zero]
  · rw [trivOn_val_of_notMem hI hX hτI,
      Berk.triv_val_of_ne_zero fun h => hτI ((quotChartMk_eq_zero_iff hσI hτ).1 h)]

end QuotChart

/-! ### Maps out of the quotient chart algebra -/

section Lift

variable {I : Ideal (MvPolynomial (Fin (M + 1)) k)} {σ : MvPolynomial (Fin (M + 1)) k} {d : ℕ}
  {C : Type*} [CommRing C] [Algebra k C] (φ : MvPolynomial (Fin (M + 1)) k →ₐ[k] C)

variable (I σ d) in
/-- For a `k`-algebra map `φ : R_M → C` vanishing on `I` with `φ(σ)` a unit, the induced map
`A_σ / I_{(σ)} → C`, `τ̄ / σ̄^N ↦ φ(τ) φ(σ)^{-N}`. In the situation of `def:wu-compactification`
(`φ : R_M → S'' ⊆ A[T] ⊆ A[T, T⁻¹]`, `σ = x₀ ↦ T^e`) this realizes `S''_{(z₀)}` inside
`A[T, T⁻¹]`. -/
def quotChartLift (hφI : ∀ f ∈ I, φ f = 0) (hσu : IsUnit (φ σ)) : QuotChartAlg I σ d →ₐ[k] C :=
  Ideal.Quotient.liftₐ (chartIdeal I σ d)
    (((IsLocalization.Away.liftAlgHom σ hσu : Localization.Away σ →ₐ[k] C)).comp
      (chartAlg σ d).val) (by
      intro a ha
      have hle : I.map (algebraMap _ (Localization.Away σ)) ≤
          RingHom.ker (IsLocalization.Away.lift σ hσu : Localization.Away σ →+* C) := by
        refine Ideal.map_le_iff_le_comap.2 fun f hf => ?_
        rw [Ideal.mem_comap, RingHom.mem_ker, IsLocalization.Away.lift_eq]
        exact hφI f hf
      exact (RingHom.mem_ker).1 (hle ha))

variable (hφI : ∀ f ∈ I, φ f = 0) (hσu : IsUnit (φ σ))

private theorem lift_invSelf_eq :
    (IsLocalization.Away.lift σ hσu : Localization.Away σ →+* C)
      (IsLocalization.Away.invSelf σ) = ↑(hσu.unit⁻¹) := by
  refine Units.eq_inv_of_mul_eq_one_left ?_
  have h1 : (IsLocalization.Away.lift σ hσu : Localization.Away σ →+* C)
      (algebraMap _ (Localization.Away σ) σ) = φ σ :=
    IsLocalization.Away.lift_eq σ hσu σ
  rw [IsUnit.unit_spec, ← h1, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- `τ̄ / σ̄^N ↦ φ(τ_{Nd}) φ(σ)^{-N}`. -/
theorem quotChartLift_quotChartMk (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k) :
    quotChartLift I σ d φ hφI hσu (quotChartMk I σ d N τ) =
      φ (homogeneousComponent (N * d) τ) * ↑(hσu.unit⁻¹) ^ N := by
  change (IsLocalization.Away.lift σ hσu : Localization.Away σ →+* C)
    ((chartMk σ d N τ : chartAlg σ d) : Localization.Away σ) = _
  have h1 : (IsLocalization.Away.lift σ hσu : Localization.Away σ →+* C)
      (algebraMap _ (Localization.Away σ) (homogeneousComponent (N * d) τ)) =
        φ (homogeneousComponent (N * d) τ) :=
    IsLocalization.Away.lift_eq σ hσu _
  rw [coe_chartMk', frac, map_mul, map_pow, h1, lift_invSelf_eq]

theorem quotChartLift_quotChartMk_mul_pow (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k) :
    quotChartLift I σ d φ hφI hσu (quotChartMk I σ d N τ) * φ σ ^ N =
      φ (homogeneousComponent (N * d) τ) := by
  rw [quotChartLift_quotChartMk, mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]

/-- If moreover `φ` vanishes on a form `τ` of degree `N d` only if `τ ∈ I` (e.g. `ker φ = I`),
the map `A_σ / I_{(σ)} → C` is injective. -/
theorem quotChartLift_injective (hσ : σ.IsHomogeneous d)
    (hφI' : ∀ (N : ℕ) (f : MvPolynomial (Fin (M + 1)) k), f.IsHomogeneous (N * d) → φ f = 0 →
      f ∈ I) :
    Function.Injective (quotChartLift I σ d φ hφI hσu) := by
  refine (injective_iff_map_eq_zero _).2 fun b hb => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_chartMk hσ a
  have h := quotChartLift_quotChartMk_mul_pow (d := d) φ hφI hσu N τ
  rw [quotChartMk, hb, zero_mul, homogeneousComponent_eq_self hτ] at h
  exact Ideal.Quotient.eq_zero_iff_mem.2 (chartMk_mem_chartIdeal hτ (hφI' N τ hτ h.symm))

/-- The image of `A_σ / I_{(σ)} → C` consists of the `c` with `c φ(σ)^N = φ(τ)` for a form `τ`
of degree `N d`, i.e. of the fractions `φ(τ) / φ(σ)^N`. -/
theorem mem_range_quotChartLift (hσ : σ.IsHomogeneous d) {c : C} :
    c ∈ (quotChartLift I σ d φ hφI hσu).range ↔
      ∃ (N : ℕ) (τ : MvPolynomial (Fin (M + 1)) k), τ.IsHomogeneous (N * d) ∧
        c * φ σ ^ N = φ τ := by
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨N, τ, hτ, rfl⟩ := exists_eq_chartMk hσ a
    refine ⟨N, τ, hτ, ?_⟩
    have h := quotChartLift_quotChartMk_mul_pow (d := d) φ hφI hσu N τ
    rwa [homogeneousComponent_eq_self hτ] at h
  · rintro ⟨N, τ, hτ, h⟩
    refine ⟨quotChartMk I σ d N τ, ?_⟩
    have h' := quotChartLift_quotChartMk_mul_pow (d := d) φ hφI hσu N τ
    rw [homogeneousComponent_eq_self hτ, ← h] at h'
    exact (hσu.pow N).mul_left_injective h'

variable {A : Type*} [CommRing A] [Algebra k A]

variable (I σ d) in
/-- **Identifying the quotient chart algebra**: if `φ : R_M → C` vanishes exactly on the forms of
`I` (e.g. `ker φ = I`), `φ(σ)` is a unit, and the image of `A_σ / I_{(σ)} → C` is the image of an
injective `j : A → C`, then `A_σ / I_{(σ)} ≃ₐ[k] A`. (`ProjBerk.affineChartEquiv` in
`Projective/SubvarietyRees.lean` is the case used for `lem:wu-proj-chart`(4).) -/
def quotChartEquiv (hσ : σ.IsHomogeneous d)
    (hφI' : ∀ (N : ℕ) (f : MvPolynomial (Fin (M + 1)) k), f.IsHomogeneous (N * d) → φ f = 0 →
      f ∈ I) (j : A →ₐ[k] C)
    (hj : Function.Injective j) (hrange : (quotChartLift I σ d φ hφI hσu).range = j.range) :
    QuotChartAlg I σ d ≃ₐ[k] A :=
  (AlgEquiv.ofInjective _ (quotChartLift_injective φ hφI hσu hσ hφI')).trans
    ((Subalgebra.equivOfEq _ _ hrange).trans (AlgEquiv.ofInjective j hj).symm)

theorem apply_quotChartEquiv (hσ : σ.IsHomogeneous d)
    (hφI' : ∀ (N : ℕ) (f : MvPolynomial (Fin (M + 1)) k), f.IsHomogeneous (N * d) → φ f = 0 →
      f ∈ I)
    (j : A →ₐ[k] C) (hj : Function.Injective j)
    (hrange : (quotChartLift I σ d φ hφI hσu).range = j.range) (b : QuotChartAlg I σ d) :
    j (quotChartEquiv I σ d φ hφI hσu hσ hφI' j hj hrange b) = quotChartLift I σ d φ hφI hσu b := by
  have h := AlgEquiv.ofInjective_apply j hj
    ((AlgEquiv.ofInjective j hj).symm ((Subalgebra.equivOfEq _ _ hrange)
      ((AlgEquiv.ofInjective _ (quotChartLift_injective φ hφI hσu hσ hφI')) b)))
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end Lift

/-! ### Finiteness of Fubini–Study functions -/

/-- An FS function is finite at every point where one of its sections does not vanish. -/
theorem FSData.eval_ne_bot_of_val_ne_zero {a : ℚ} (D : FSData k M a) {v : ProjBerk k M}
    {t : MvPolynomial (Fin (M + 1)) k × ℝ} (ht : t ∈ D.terms) (hv : v.1.val t.1 ≠ 0) :
    D.eval v ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot ?_ (D.termVal_le_eval_mul v ht)
  rw [termVal_def, logAbs_def, ENNReal.log_of_nnreal hv, ← EReal.coe_add, ← EReal.coe_mul]
  exact EReal.coe_ne_bot _

end ProjBerk

open ProjBerk

/-! ### Projective subvarieties -/

variable (k : Type u) [Field k] (M : ℕ) in
/-- A **projective subvariety** `X = V(I) ⊆ ℙᴹ` over `k`, given by a homogeneous prime ideal `I`
of `R_M = k[x₀, …, x_M]` not containing all `xᵢ` (`conv:wu-graded`). Its analytification is
`X^an = V(I)^an ⊆ (ℙᴹ)^an` (`ProjSubvariety.an`), and `S'' = R_M / I` is its homogeneous
coordinate ring. -/
structure ProjSubvariety where
  /-- The homogeneous ideal `I` of `X`. -/
  ideal : Ideal (MvPolynomial (Fin (M + 1)) k)
  isHomogeneousIdeal : IsHomogeneousIdeal ideal
  isPrime : ideal.IsPrime
  /-- `I` does not contain all the coordinates (it is relevant). -/
  exists_X_notMem : ∃ i, (X i : MvPolynomial (Fin (M + 1)) k) ∉ ideal

namespace ProjSubvariety

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

attribute [instance] ProjSubvariety.isPrime

/-- The analytification `X^an = V(I)^an ⊆ (ℙᴹ)^an` (`conv:wu-graded`). -/
def an : Set (ProjBerk k M) := zeroLocus X.ideal

theorem isClosed_an : IsClosed X.an := isClosed_zeroLocus X.ideal

/-- `X^an` is compact (`lem:wu-proj-chart`(1)). -/
theorem isCompact_an : IsCompact X.an := isCompact_zeroLocus X.ideal

instance instCompactSpaceAn : CompactSpace X.an := instCompactSpaceZeroLocus X.ideal

/-- The trivial valuation of `X` (the trivial valuation of `S'' = R_M / I`) as a point of
`X^an`. -/
def triv : X.an :=
  ⟨trivOn X.isHomogeneousIdeal X.exists_X_notMem,
    trivOn_mem_zeroLocus X.isHomogeneousIdeal X.exists_X_notMem⟩

theorem triv_val_of_notMem {f : MvPolynomial (Fin (M + 1)) k} (hf : f ∉ X.ideal) :
    (X.triv : ProjBerk k M).1.val f = 1 :=
  trivOn_val_of_notMem X.isHomogeneousIdeal X.exists_X_notMem hf

variable {X}

/-- A form not vanishing at a point of `X^an` is not in `I`. -/
theorem notMem_ideal_of_val_ne_zero {v : X.an} {σ : MvPolynomial (Fin (M + 1)) k}
    (hv : (v : ProjBerk k M).1.val σ ≠ 0) : σ ∉ X.ideal :=
  fun h => hv (v.2 σ h)

/-! #### Charts of `X^an` -/

section Chart

variable (X) (σ : MvPolynomial (Fin (M + 1)) k) (d : ℕ)

/-- The quotient chart map `ι_σ : U_σ ∩ X^an → (Spec A_σ / I_{(σ)})^an` (`lem:wu-proj-chart`(2)). -/
def chartMap (v : X.an) (hv : (v : ProjBerk k M).1.val σ ≠ 0) : Berk k (QuotChartAlg X.ideal σ d) :=
  quotChartMap X.ideal σ d v.1 hv v.2

/-- The inverse quotient chart `ι_σ⁻¹ : (Spec A_σ / I_{(σ)})^an → U_σ ∩ X^an ⊆ X^an`. -/
def chartInv (hσ : σ.IsHomogeneous d) (hd : 0 < d) (y : Berk k (QuotChartAlg X.ideal σ d)) :
    X.an :=
  ⟨quotChartInv X.ideal σ d hσ hd y, quotChartInv_mem_zeroLocus X.isHomogeneousIdeal hσ hd y⟩

variable {X σ d} (hσ : σ.IsHomogeneous d) (hd : 0 < d)

theorem chartInv_val_ne_zero (y : Berk k (QuotChartAlg X.ideal σ d)) :
    (X.chartInv σ d hσ hd y : ProjBerk k M).1.val σ ≠ 0 :=
  quotChartInv_val_ne_zero hσ hd y

theorem chartMap_chartInv (y : Berk k (QuotChartAlg X.ideal σ d)) :
    X.chartMap σ d (X.chartInv σ d hσ hd y) (chartInv_val_ne_zero hσ hd y) = y :=
  quotChartMap_quotChartInv X.isHomogeneousIdeal hσ hd y

theorem chartInv_chartMap (v : X.an) (hv : (v : ProjBerk k M).1.val σ ≠ 0) :
    X.chartInv σ d hσ hd (X.chartMap σ d v hv) = v :=
  Subtype.ext (quotChartInv_quotChartMap hσ hd v.1 hv v.2)

theorem continuous_chartInv : Continuous (X.chartInv σ d hσ hd) :=
  (continuous_quotChartInv hσ hd).subtype_mk _

theorem range_chartInv :
    Set.range (X.chartInv σ d hσ hd) = {v : X.an | (v : ProjBerk k M).1.val σ ≠ 0} := by
  refine Set.Subset.antisymm ?_ fun v hv => ⟨_, chartInv_chartMap hσ hd v hv⟩
  rintro _ ⟨y, rfl⟩
  exact chartInv_val_ne_zero hσ hd y

theorem isOpen_setOf_val_ne_zero :
    IsOpen {v : X.an | (v : ProjBerk k M).1.val σ ≠ 0} :=
  (isOpen_chartDomain σ).preimage continuous_subtype_val

/-- The inverse quotient chart is an open embedding of `(Spec A_σ / I_{(σ)})^an` into `X^an` with
image `U_σ ∩ X^an` (`lem:wu-proj-chart`(2)). -/
theorem isOpenEmbedding_chartInv : IsOpenEmbedding (X.chartInv σ d hσ hd) := by
  refine ⟨IsEmbedding.of_comp (continuous_chartInv hσ hd) continuous_subtype_val ?_, ?_⟩
  · exact isEmbedding_quotChartInv X.isHomogeneousIdeal hσ hd
  · rw [range_chartInv]
    exact isOpen_setOf_val_ne_zero

variable (X σ d) in
/-- **Charts of `X^an`** (`lem:wu-proj-chart`(2)): `ι_σ` is a homeomorphism from the open subset
`U_σ ∩ X^an = {v ∈ X^an : |σ|_v ≠ 0}` onto `(Spec A_σ / I_{(σ)})^an`. -/
def chartHomeomorph : {v : X.an // (v : ProjBerk k M).1.val σ ≠ 0} ≃ₜ
    Berk k (QuotChartAlg X.ideal σ d) where
  toFun v := X.chartMap σ d v.1 v.2
  invFun y := ⟨X.chartInv σ d hσ hd y, chartInv_val_ne_zero hσ hd y⟩
  left_inv v := Subtype.ext (chartInv_chartMap hσ hd v.1 v.2)
  right_inv y := chartMap_chartInv hσ hd y
  continuous_toFun := continuous_quotChartMap_comp
    (continuous_subtype_val.comp continuous_subtype_val) (fun v => v.2) fun v => v.1.2
  continuous_invFun := (continuous_chartInv hσ hd).subtype_mk _

@[simp]
theorem chartHomeomorph_apply (v : {v : X.an // (v : ProjBerk k M).1.val σ ≠ 0}) :
    X.chartHomeomorph σ d hσ hd v = X.chartMap σ d v.1 v.2 :=
  rfl

@[simp]
theorem coe_chartHomeomorph_symm_apply (y : Berk k (QuotChartAlg X.ideal σ d)) :
    ((X.chartHomeomorph σ d hσ hd).symm y : X.an) = X.chartInv σ d hσ hd y :=
  rfl

/-- The quotient chart is continuous on `U_σ ∩ X^an`. -/
theorem continuous_chartMap :
    Continuous fun v : {v : X.an // (v : ProjBerk k M).1.val σ ≠ 0} => X.chartMap σ d v.1 v.2 :=
  continuous_quotChartMap_comp (continuous_subtype_val.comp continuous_subtype_val)
    (fun v => v.2) fun v => v.1.2

/-- `|τ̄ / σ̄^N|_{ι_σ(v)} = |τ|_v / |σ|_v^N` for a form `τ` of degree `N d`. -/
theorem chartMap_val_quotChartMk (v : X.an) (hv : (v : ProjBerk k M).1.val σ ≠ 0) {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous (N * d)) :
    (X.chartMap σ d v hv).val (quotChartMk X.ideal σ d N τ) =
      (v : ProjBerk k M).1.val τ / (v : ProjBerk k M).1.val σ ^ N :=
  quotChartMap_val_quotChartMk v.1 hv v.2 hτ

/-- `log|τ̄ / σ̄^N| ∘ ι_σ = log|τ| - N log|σ|` on `U_σ ∩ X^an` (`lem:wu-proj-chart`(3)). -/
theorem logAbs_chartMap_quotChartMk (v : X.an) (hv : (v : ProjBerk k M).1.val σ ≠ 0) {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous (N * d)) :
    Berk.logAbs (quotChartMk X.ideal σ d N τ) (X.chartMap σ d v hv) =
      logAbs τ v.1 - N * logAbs σ v.1 :=
  logAbs_quotChartMap_quotChartMk v.1 hv v.2 hτ

/-- `log|τ̄ / σ̄^N| = (log|τ| - N log|σ|) ∘ ι_σ⁻¹` on `(Spec A_σ / I_{(σ)})^an`
(`lem:wu-proj-chart`(3), read on the chart). -/
theorem logAbs_quotChartMk_eq (y : Berk k (QuotChartAlg X.ideal σ d)) {N : ℕ}
    {τ : MvPolynomial (Fin (M + 1)) k} (hτ : τ.IsHomogeneous (N * d)) :
    Berk.logAbs (quotChartMk X.ideal σ d N τ) y =
      logAbs τ (X.chartInv σ d hσ hd y).1 - N * logAbs σ (X.chartInv σ d hσ hd y).1 := by
  conv_lhs => rw [← chartMap_chartInv hσ hd y]
  exact logAbs_chartMap_quotChartMk _ _ hτ

/-- `max_{|α| = d} log|x̄^α / σ̄| ∘ ι_σ = -log|σ|` on `U_σ ∩ X^an` (`lem:wu-proj-chart`(3)). -/
theorem sup_logAbs_chartMap_quotChartGen (v : X.an) (hv : (v : ProjBerk k M).1.val σ ≠ 0) :
    (Finset.finsuppAntidiag Finset.univ d).sup
      (fun α => Berk.logAbs (quotChartGen X.ideal σ d α) (X.chartMap σ d v hv)) =
      -logAbs σ v.1 :=
  sup_logAbs_quotChartMap_quotChartGen v.1 hv v.2

include hσ in
/-- `ι_σ` maps the trivial valuation of `X` to the trivial valuation of the domain
`A_σ / I_{(σ)}` (generic form of `lem:wu-proj-chart`(4)). -/
theorem chartMap_triv (hσI : σ ∉ X.ideal) [IsDomain (QuotChartAlg X.ideal σ d)] :
    X.chartMap σ d X.triv (by rw [triv_val_of_notMem X hσI]; exact one_ne_zero) = Berk.triv :=
  quotChartMap_trivOn X.isHomogeneousIdeal X.exists_X_notMem hσ hσI

include hσ in
/-- **`lem:wu-proj-chart`(4), generic form.** For any `k`-algebra isomorphism
`e : A_σ / I_{(σ)} ≃ S''_{(σ̄)} ≃ A` onto a domain `A`, the composite of `ι_σ` with `e` maps the
trivial valuation of `X` to the trivial valuation of `A`. (In the situation of
`def:wu-compactification`, `σ = x₀` and `A` is the coordinate ring of `Y`.) -/
theorem homeomorphOfAlgEquiv_chartMap_triv (hσI : σ ∉ X.ideal) {A : Type*} [CommRing A]
    [Algebra k A] [IsDomain A] (e : QuotChartAlg X.ideal σ d ≃ₐ[k] A) :
    Berk.homeomorphOfAlgEquiv e
      (X.chartMap σ d X.triv (by rw [triv_val_of_notMem X hσI]; exact one_ne_zero)) =
      Berk.triv := by
  have := isDomain_quotChartAlg (d := d) hσI
  rw [chartMap_triv hσ hσI, Berk.homeomorphOfAlgEquiv_triv]

end Chart

/-! #### Fubini–Study and locally convex functions on `X^an` (`def:wu-proj-functions`) -/

/-- **Finite Fubini–Study functions of class `O(a)`** on `X^an` (`def:wu-proj-functions`(1),
for `a = 1`): functions `Ψ = m⁻¹ max_ℓ (log|τ_ℓ| + μ_ℓ)` given by Fubini–Study data on `ℙᴹ`
(`ProjBerk.FSData`: `m ≥ 1`, forms `τ_ℓ` of degree `m a`) with rational constants `μ_ℓ`, such
that at every point of `X^an` some `τ_ℓ` does not vanish. Such a function is real valued (it is
recorded as a function `X^an → ℝ`) and continuous (`IsFiniteFS.continuous`). -/
def IsFiniteFS (X : ProjSubvariety k M) (a : ℚ) (φ : X.an → ℝ) : Prop :=
  ∃ D : ProjBerk.FSData k M a, D.IsRational ∧
    (∀ v ∈ X.an, ∃ t ∈ D.terms, v.1.val t.1 ≠ 0) ∧ ∀ v : X.an, (φ v : EReal) = D.eval v.1

/-- Fubini–Study data with rational constants whose sections have no common zero on `X^an`
define a finite FS function on `X^an`. -/
theorem isFiniteFS_of_fsData {a : ℚ} (D : ProjBerk.FSData k M a) (hD : D.IsRational)
    (hfin : ∀ v ∈ X.an, ∃ t ∈ D.terms, v.1.val t.1 ≠ 0) :
    X.IsFiniteFS a fun v => (D.eval v.1).toReal := by
  refine ⟨D, hD, hfin, fun v => ?_⟩
  obtain ⟨t, ht, hv⟩ := hfin v.1 v.2
  exact EReal.coe_toReal (D.eval_ne_top v.1) (D.eval_ne_bot_of_val_ne_zero ht hv)

/-- Finite FS functions on `X^an` are continuous (`def:wu-proj-functions`(1)). -/
theorem IsFiniteFS.continuous {a : ℚ} {φ : X.an → ℝ} (h : X.IsFiniteFS a φ) : Continuous φ := by
  obtain ⟨D, -, -, hφ⟩ := h
  have hc : Continuous fun v : X.an => (φ v : EReal) := by
    simp only [hφ]
    exact D.continuous_eval.comp continuous_subtype_val
  exact EReal.isEmbedding_coe.continuous_iff.2 hc

variable (X) in
/-- The function `(φ - (a/d) log|σ|) ∘ ι_σ⁻¹` on the quotient chart `(Spec A_σ / I_{(σ)})^an`,
for a function `φ : X^an → ℝ` and a form `σ` of degree `d ≥ 1` (`def:wu-proj-functions`(2)). -/
def chartFun (a : ℚ) (φ : X.an → ℝ) (σ : MvPolynomial (Fin (M + 1)) k) (d : ℕ)
    (hσ : σ.IsHomogeneous d) (hd : 0 < d) (y : Berk k (QuotChartAlg X.ideal σ d)) : EReal :=
  ((φ (X.chartInv σ d hσ hd y) -
    (a : ℝ) / d * Real.log ((X.chartInv σ d hσ hd y : ProjBerk k M).1.val σ : ℝ) : ℝ) : EReal)

/-- On `ι_σ(v)`, the chart function is `φ(v) - (a/d) log|σ|_v`. -/
theorem chartFun_chartMap (a : ℚ) (φ : X.an → ℝ) {σ : MvPolynomial (Fin (M + 1)) k} {d : ℕ}
    (hσ : σ.IsHomogeneous d) (hd : 0 < d) (v : X.an) (hv : (v : ProjBerk k M).1.val σ ≠ 0) :
    X.chartFun a φ σ d hσ hd (X.chartMap σ d v hv) =
      ((φ v - (a : ℝ) / d * Real.log ((v : ProjBerk k M).1.val σ : ℝ) : ℝ) : EReal) := by
  rw [chartFun, chartInv_chartMap]

variable (X) in
/-- **Local `O(a)`-convexity at a point** `x ∈ X^an` (`def:wu-proj-functions`(2)): `x` has an
open neighbourhood `W` such that, for some form `σ ∉ I` of degree `d ≥ 1` with `W ⊆ U_σ`, the
function `(φ - (a/d) log|σ|) ∘ ι_σ⁻¹` is convex PL (`IsConvexPLOn`) on
`ι_σ(W) = ι_σ⁻¹ ⁻¹' W ⊆ (Spec A_σ / I_{(σ)})^an`. -/
def IsLocallyConvexAt (a : ℚ) (φ : X.an → ℝ) (x : X.an) : Prop :=
  ∃ W : Set X.an, IsOpen W ∧ x ∈ W ∧
    ∃ (σ : MvPolynomial (Fin (M + 1)) k) (d : ℕ) (hσ : σ.IsHomogeneous d) (hd : 0 < d),
      σ ∉ X.ideal ∧ (∀ v ∈ W, (v : ProjBerk k M).1.val σ ≠ 0) ∧
      IsConvexPLOn (X.chartInv σ d hσ hd ⁻¹' W) (X.chartFun a φ σ d hσ hd)

variable (X) in
/-- **Locally `O(a)`-convex functions** on `X^an` (`def:wu-proj-functions`(2)): functions
`φ : X^an → ℝ` that are locally `O(a)`-convex at every point (`IsLocallyConvexAt`). -/
def IsLocallyConvex (a : ℚ) (φ : X.an → ℝ) : Prop :=
  ∀ x : X.an, X.IsLocallyConvexAt a φ x

/-- Local `O(a)`-convexity at `x` only depends on the function near `x`. -/
theorem IsLocallyConvexAt.congr {a : ℚ} {φ ψ : X.an → ℝ} {x : X.an}
    (h : X.IsLocallyConvexAt a ψ x) {V : Set X.an} (hV : IsOpen V) (hxV : x ∈ V)
    (heq : ∀ v ∈ V, φ v = ψ v) : X.IsLocallyConvexAt a φ x := by
  obtain ⟨W, hW, hxW, σ, d, hσ, hd, hσI, hWσ, hconv⟩ := h
  refine ⟨W ∩ V, hW.inter hV, ⟨hxW, hxV⟩, σ, d, hσ, hd, hσI, fun v hv => hWσ v hv.1, ?_⟩
  refine (hconv.mono ((hW.inter hV).preimage (continuous_chartInv hσ hd))
    fun y hy => hy.1).congr fun y hy => ?_
  rw [chartFun, chartFun, heq _ hy.2]

/-! #### Finite FS functions are locally convex -/

/-- **Finite FS functions are locally convex**: a finite Fubini–Study function of class `O(a)`,
`a > 0`, on `X^an` is locally `O(a)`-convex. Near `x`, take `σ = τ_{ℓ₀}` with `|τ_{ℓ₀}|_x ≠ 0`;
then `(Ψ - (1/m) log|σ|) ∘ ι_σ⁻¹ = (1/m) max_ℓ (log|τ̄_ℓ / σ̄| + μ_ℓ)`, the terms with
`|τ_ℓ|_x = 0` may be omitted near `x`, and the remaining `τ̄_ℓ / σ̄` do not vanish near `ι_σ(x)`
(as in the proof that FS functions are convex PL, `FSData.isConvexPLOn_univ`). -/
theorem IsFiniteFS.isLocallyConvex {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ}
    (h : X.IsFiniteFS a φ) : X.IsLocallyConvex a φ := by
  classical
  obtain ⟨D, hD, hfin, hφ⟩ := h
  intro x
  obtain ⟨t₀, ht₀, hx₀⟩ := hfin x.1 x.2
  have hσ : t₀.1.IsHomogeneous D.deg := D.isHomogeneous t₀ ht₀
  have hm : (0 : ℝ) < D.m := Nat.cast_pos.2 D.m_pos
  have hdeg : (D.deg : ℝ) = D.m * a := by exact_mod_cast D.deg_eq
  have hd : 0 < D.deg := by
    have h0 : (0 : ℚ) < D.deg := by
      rw [D.deg_eq]; exact mul_pos (by exact_mod_cast D.m_pos) ha
    exact_mod_cast h0
  set S := D.terms.filter fun t => (x : ProjBerk k M).1.val t.1 ≠ 0 with hS_def
  have ht₀S : t₀ ∈ S := Finset.mem_filter.2 ⟨ht₀, hx₀⟩
  set W : Set X.an := {v | ∀ t ∈ S, (v : ProjBerk k M).1.val t.1 ≠ 0} ∩
    ⋂ t ∈ D.terms.filter (fun t => ¬ (x : ProjBerk k M).1.val t.1 ≠ 0),
      {v | termVal t (v : ProjBerk k M) < termVal t₀ v} with hW_def
  have hW : IsOpen W := by
    refine IsOpen.inter ?_ (isOpen_biInter_finset fun t _ => isOpen_lt
      ((continuous_termVal t).comp continuous_subtype_val)
      ((continuous_termVal t₀).comp continuous_subtype_val))
    have e : ({v | ∀ t ∈ S, (v : ProjBerk k M).1.val t.1 ≠ 0} : Set X.an) =
        ⋂ t ∈ S, ({v | (v : ProjBerk k M).1.val t.1 ≠ 0} : Set X.an) := by ext; simp
    rw [e]
    exact isOpen_biInter_finset fun t _ =>
      (isOpen_chartDomain t.1).preimage continuous_subtype_val
  have hxW : x ∈ W := by
    refine ⟨fun t ht => (Finset.mem_filter.1 ht).2, Set.mem_iInter₂.2 fun t ht => ?_⟩
    have ht' := Finset.mem_filter.1 ht
    change termVal t x.1 < termVal t₀ x.1
    rw [termVal_def, (logAbs_eq_bot_iff _ _).2 (not_not.1 ht'.2), EReal.bot_add, termVal_def,
      logAbs_def, ENNReal.log_of_nnreal hx₀, ← EReal.coe_add]
    exact EReal.bot_lt_coe _
  refine ⟨W, hW, hxW, t₀.1, D.deg, hσ, hd, notMem_ideal_of_val_ne_zero hx₀,
    fun v hv => hv.1 t₀ ht₀S, ?_⟩
  -- rational constants and the functions `τ̄_ℓ / σ̄` on the chart
  set q : MvPolynomial (Fin (M + 1)) k × ℝ → ℚ :=
    fun t => if h : ∃ q : ℚ, t.2 = q then h.choose else 0 with hq_def
  have hq : ∀ t ∈ D.terms, ((q t : ℚ) : ℝ) = t.2 := by
    intro t ht
    have h' : ∃ q : ℚ, t.2 = q := hD t ht
    rw [hq_def]
    simp only [dif_pos h']
    exact h'.choose_spec.symm
  set f : MvPolynomial (Fin (M + 1)) k × ℝ → QuotChartAlg X.ideal t₀.1 D.deg :=
    fun t => quotChartMk X.ideal t₀.1 D.deg 1 t.1 with hf_def
  have hconv := (isConvexPLOn_sup_logAbs_add (k := k) ⟨t₀, ht₀S⟩ f q).smul
    (c := (D.m : ℚ)⁻¹) (by positivity)
  have hO : IsOpen (X.chartInv t₀.1 D.deg hσ hd ⁻¹' W) :=
    hW.preimage (continuous_chartInv hσ hd)
  have hτ : ∀ t ∈ D.terms, t.1.IsHomogeneous (1 * D.deg) := fun t ht => by
    rw [one_mul]; exact D.isHomogeneous t ht
  refine (hconv.mono hO ?_).congr ?_
  · intro y hy t ht
    obtain ⟨v, hv, rfl⟩ : ∃ v hv, y = X.chartMap t₀.1 D.deg v hv :=
      ⟨_, _, (chartMap_chartInv hσ hd y).symm⟩
    rw [Set.mem_preimage, chartInv_chartMap] at hy
    change (X.chartMap t₀.1 D.deg v hv).val (quotChartMk X.ideal t₀.1 D.deg 1 t.1) ≠ 0
    rw [chartMap_val_quotChartMk v hv (hτ t (Finset.mem_filter.1 ht).1), pow_one]
    exact div_ne_zero (hy.1 t ht) hv
  · intro y hy
    obtain ⟨v, hv, rfl⟩ : ∃ v hv, y = X.chartMap t₀.1 D.deg v hv :=
      ⟨_, _, (chartMap_chartInv hσ hd y).symm⟩
    rw [Set.mem_preimage, chartInv_chartMap] at hy
    rw [chartFun_chartMap]
    set ℓ := Real.log ((v : ProjBerk k M).1.val t₀.1 : ℝ) with hℓ
    set r : MvPolynomial (Fin (M + 1)) k × ℝ → ℝ :=
      fun t => Real.log ((v : ProjBerk k M).1.val t.1 : ℝ) with hr
    have hlog : ∀ t ∈ S, logAbs t.1 (v : ProjBerk k M) = ((r t : ℝ) : EReal) := fun t ht => by
      rw [logAbs_def, ENNReal.log_of_nnreal (hy.1 t ht)]
    -- the chart side
    have hchart : (S.sup fun t => Berk.logAbs (f t) (X.chartMap t₀.1 D.deg v hv) +
        ((q t : ℝ) : EReal)) = ((S.sup' ⟨t₀, ht₀S⟩ fun t => r t + t.2 - ℓ : ℝ) : EReal) := by
      rw [← ereal_finset_sup_coe ⟨t₀, ht₀S⟩]
      refine Finset.sup_congr rfl fun t ht => ?_
      rw [hf_def]
      simp only
      rw [logAbs_chartMap_quotChartMk v hv (hτ t (Finset.mem_filter.1 ht).1), hlog t ht,
        hlog t₀ ht₀S, hq t (Finset.mem_filter.1 ht).1, Nat.cast_one, one_mul, ← EReal.coe_sub,
        ← EReal.coe_add]
      congr 1
      ring
    -- the function side
    have hdrop : (D.terms.sup fun t => termVal t (v : ProjBerk k M)) =
        S.sup fun t => termVal t (v : ProjBerk k M) := by
      refine sup_eq_sup_filter_of_le _ _ _ ht₀ hx₀ fun t ht hxt => (Set.mem_iInter₂.1 hy.2 t
        (Finset.mem_filter.2 ⟨ht, hxt⟩)).le
    have hfun : (D.terms.sup fun t => termVal t (v : ProjBerk k M)) =
        ((S.sup' ⟨t₀, ht₀S⟩ fun t => r t + t.2 : ℝ) : EReal) := by
      rw [hdrop, ← ereal_finset_sup_coe ⟨t₀, ht₀S⟩]
      refine Finset.sup_congr rfl fun t ht => ?_
      rw [termVal_def, hlog t ht, ← EReal.coe_add]
    have hφv : φ v = (D.m : ℝ)⁻¹ * S.sup' ⟨t₀, ht₀S⟩ (fun t => r t + t.2) := by
      have h1 := hφ v
      rw [ProjBerk.FSData.eval_def, hfun, ← EReal.coe_mul] at h1
      exact EReal.coe_injective h1
    have hsub : (S.sup' ⟨t₀, ht₀S⟩ fun t => r t + t.2 - ℓ) =
        S.sup' ⟨t₀, ht₀S⟩ (fun t => r t + t.2) - ℓ :=
      (Finset.apply_sup'_eq_sup'_comp ⟨t₀, ht₀S⟩ (fun z : ℝ => z - ℓ)
        fun z w => (max_sub_sub_right z w ℓ).symm).symm
    rw [hchart, hsub, hφv, ← EReal.coe_mul]
    congr 1
    rw [hdeg]
    push_cast
    field_simp

end ProjSubvariety

end EnvelopeProperty
