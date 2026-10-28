/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ModelNormalization
import EnvelopeProperty.Berkovich.Finite

/-!
# Morphisms of integral multiprojective models

This file implements the blueprint nodes `def:gl-maps` and the point-level part of
`lem:gl-pullback` of `global.tex` (subsection `subsec:gl-model`) for the formalization of
Fang–Han–Xia, *The envelope property for unibranch projective varieties* (revision `832e086`,
FHX `prop:BJ-package`(4) and `subsec:prelim-finite-classes`).

## Finite morphisms (`def:gl-maps`)

A **finite morphism** `h : 𝒯 → 𝒳` of models of rank `r` (`EnvelopeProperty.MultiModel.FiniteHom`)
consists of a field extension `K ⊆ E` (an `Algebra K E` with `k → K → E` a scalar tower) and of
models `𝒳 = (K, S, z)`, `𝒯 = (E, S_T, z)` with

* `μ(S) ⊆ S_T`, where `μ : K[T] → E[T]` is the coefficientwise inclusion (`MultiModel.coeffMap`);
* `S_T` integral over `μ(S)`;
* the same coordinates: a bijection `Fin (M_c + 1) ≃ Fin (M^T_c + 1)` of coordinate indices
  matching the coordinates (`FiniteHom.coordEquiv`, `FiniteHom.coord_coordEquiv`); allowing a
  reindexing costs nothing and keeps the definition independent of definitional equalities of the
  numbers `M_c`.

The degree `[E : K]` is finite (`FiniteHom.finiteDimensional`): every element of `E` is a quotient
of homogeneous elements of `S_T` of one degree, whose coefficients are integral over `K` (take the
coefficient of `T^{n a}` in an integral equation of `f T^a`), and `E` is a finitely generated field.
So the finiteness of the degree required in `def:gl-maps` is a consequence and not a field.
The normalization in a finite extension (`rmk:gl-model-examples`(3)) and the normalization are
finite morphisms (`FiniteHom.normalizationIn`, `FiniteHom.normalization`).

## Points (`lem:gl-pullback`, point-level part)

`h^an(w) = w|_S` (`FiniteHom.anMap`) maps `𝒯^an` to `𝒳^an`: restriction along the graded inclusion
`S → S_T` (`FiniteHom.algHom`) preserves multigradedness, and the coordinates agree. It is

* continuous (`FiniteHom.continuous_anMap`) and closed (`FiniteHom.isClosedMap_anMap`);
* compatible with the charts (`lem:gl-charts`): a chart index `j` of `𝒳` gives the chart index
  `FiniteHom.chartIndex j` of `𝒯`, the chart algebras satisfy `A_j ⊆ B_j` finite
  (`FiniteHom.chartAlgHom`, `FiniteHom.finite_chartAlgHom`), and
  `ι_j(h^an(w)) = ι_j(w)|_{A_j}` (`FiniteHom.chartMap_anMap`),
  `h^an(ι_j⁻¹(y)) = ι_j⁻¹(y|_{A_j})` (`FiniteHom.anMap_chartInv`);
* surjective (`FiniteHom.anMap_surjective`): on a chart, points of `(Spec B_j)^an` over a point of
  `(Spec A_j)^an` exist (`Berk.comap_surjective_of_isIntegral`), and the inverse charts are
  compatible;
* with finite fibres (`FiniteHom.finite_anMap_preimage`): `S_T` is a finite `S`-module and the
  fibres of `(Spec S_T)^an → (Spec S)^an` are finite (`Berk.finite_preimage_comap_singleton`);
* `h^an(⋆) = ⋆`, and `⋆` is the only point over `⋆` (`FiniteHom.anMap_triv`,
  `FiniteHom.eq_triv_of_anMap_eq_triv`): a nonzero `q ∈ S_T` satisfies an integral equation over
  `S` with nonzero constant term, which forces `|q| = 1`.

Values of homogeneous elements and of the monomials `z^β` are preserved
(`FiniteHom.anMap_val_ofPiece`, `FiniteHom.zCoeff_mapDomain`, `FiniteHom.monSet_eq_map`,
`FiniteHom.sup_monSet_anMap`): this is the input for "`R_a(𝒳) ⊆ R_a(𝒯)` with the same values" in
the language of sections (`def:gl-sections`, lane G2).

**Pending on lane G2** (sections, Fubini–Study and psh functions on a model): the statements
"`φ ∘ h^an ∈ 𝓗(𝒯, a)` for `φ ∈ 𝓗(𝒳, a)`" and "`u ∘ h^an ∈ PSH(𝒯, θ)` for `u ∈ PSH(𝒳, θ)`" of
`lem:gl-pullback`. Their proofs only use the results of this file.

## Scalar restriction (`def:gl-maps`)

For algebraically closed `k₀ ⊆ k` (any field extension here), a **scalar restriction**
(`EnvelopeProperty.MultiModel.ScalarRestriction`) is a model `𝒳₀ = (K₀, S₀, z)` over `k₀` and a model
`𝒳 = (K, S, z)` over `k` with `K₀ ⊆ K`, the same coordinates, and `S = k · S₀ ≅ k ⊗_{k₀} S₀` inside
`K[T]` (`ScalarRestriction.span_eq`, `ScalarRestriction.injective_tensor`). Restriction
`r(v) = v|_{S₀}` (`ScalarRestriction.anMap`) is continuous, preserves values of homogeneous
elements and `r(⋆) = ⋆` (`ScalarRestriction.anMap_triv`).

The blueprint's `lem:gl-pullback` says that "for a scalar restriction the same holds for `r`, except
surjectivity". Finiteness of fibres and "`⋆` is the only point over `⋆`" do **not** hold for scalar
restrictions (e.g. `k₀ = ℚ̄ ⊆ k = \overline{ℚ(t)}`, `𝒳 = ℙ¹`: the divisorial point `|·| =
e^{-ord_{x = t}}` is not `⋆` but restricts to `⋆` on `k₀[x]`, since no nonzero `g ∈ k₀[x]` vanishes at
the transcendental `t`; its fibre is infinite); only continuity, preservation of values and
`r(⋆) = ⋆` (all that is used for pullbacks of psh functions) are proved here.
-/

open scoped NNReal ENNReal Topology

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

/-! ### Finite morphisms -/

section FiniteHom

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {E : Type u} [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]

/-- A **finite morphism** `h : 𝒯 → 𝒳` of models of rank `r` (`def:gl-maps`): for a field
extension `K ⊆ E`, the coefficientwise inclusion `μ : K[T] → E[T]` maps `S` into `S_T`, `S_T` is
integral over `μ(S)`, and the coordinates agree (up to the bijections `coordEquiv c` of the
coordinate indices). `h^an(w) = w|_S` is `FiniteHom.anMap`. -/
structure FiniteHom (T : MultiModel k E r) (X : MultiModel k K r) where
  /-- The bijection between the coordinate indices of degree `e_c`. -/
  coordEquiv : ∀ c, Fin (X.M c + 1) ≃ Fin (T.M c + 1)
  /-- The coordinates agree: `f^{(c)}_{coordEquiv c j}(𝒯) = f^{(c)}_j(𝒳)` in `E`. -/
  coord_coordEquiv : ∀ c j, T.coord c (coordEquiv c j) = algebraMap K E (X.coord c j)
  /-- `μ(S) ⊆ S_T`. -/
  coeffMap_mem : ∀ p ∈ X.S, coeffMap k E p ∈ T.S
  /-- `S_T` is integral over `μ(S)`. -/
  isIntegral : ∀ q ∈ T.S, IsIntegral (X.imageS E) q

namespace FiniteHom

variable {T : MultiModel k E r} {X : MultiModel k K r} (h : FiniteHom T X)

/-! #### The ring map `S → S_T` -/

include h in
/-- The inclusion `S → S_T`, `p ↦ μ(p)`. -/
def algHom : X.S →ₐ[k] T.S :=
  ((coeffMap k E).comp X.S.val).codRestrict T.S fun p => h.coeffMap_mem p.1 p.2

@[simp]
theorem coe_algHom (p : X.S) : (h.algHom p : MvPolynomial (Fin r) E) = coeffMap k E p.1 :=
  rfl

theorem algHom_injective : Function.Injective h.algHom := fun _ _ hpq =>
  Subtype.ext (coeffMap_injective (k := k) E (congrArg Subtype.val hpq))

theorem algHom_ne_zero {p : X.S} (hp : p ≠ 0) : h.algHom p ≠ 0 := fun h0 =>
  hp (h.algHom_injective (h0.trans (map_zero _).symm))

include h in
/-- `f ∈ S_a` implies `f ∈ (S_T)_a`. -/
theorem algebraMap_mem_piece {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    algebraMap K E f ∈ T.piece a := by
  rw [mem_piece, ← coeffMap_monomial (k := k)]
  exact h.coeffMap_mem _ hf

theorem algHom_ofPiece {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    h.algHom (X.ofPiece hf) = T.ofPiece (h.algebraMap_mem_piece hf) :=
  Subtype.ext (coeffMap_monomial _ _ _)

/-- The inclusion `S → S_T` is graded. -/
theorem algHom_homComp (a : Fin r →₀ ℕ) (p : X.S) :
    h.algHom (X.homComp a p) = T.homComp a (h.algHom p) := by
  apply Subtype.ext
  rw [coe_algHom, coe_homComp, coe_homComp, coe_algHom, coeffMap_monomial, coeffMap_apply,
    coeff_map]

/-- The bijection of coordinate indices `Σ c, Fin (M c + 1) ≃ Σ c, Fin (M^T c + 1)`. -/
def coordIndexEquiv : X.CoordIndex ≃ T.CoordIndex :=
  Equiv.sigmaCongrRight h.coordEquiv

@[simp]
theorem coordIndexEquiv_apply (i : X.CoordIndex) :
    h.coordIndexEquiv i = ⟨i.1, h.coordEquiv i.1 i.2⟩ :=
  rfl

theorem algHom_coordElem (i : X.CoordIndex) :
    h.algHom (X.coordElem i) = T.coordElem (h.coordIndexEquiv i) := by
  apply Subtype.ext
  rw [coe_algHom, coe_coordElem, coeffMap_monomial, coordIndexEquiv_apply, coe_coordElem,
    h.coord_coordEquiv]

/-- `S_T` is integral over `S`. -/
theorem isIntegral_algHom : (h.algHom : X.S →+* T.S).IsIntegral := by
  intro q
  obtain ⟨P, hPm, hP⟩ := (isIntegral_imageS_iff (X := X) (E := E)).1 (h.isIntegral q.1 q.2)
  refine ⟨P, hPm, Subtype.val_injective ?_⟩
  have hcomp : X.coeffMapS E = T.S.val.toRingHom.comp (h.algHom : X.S →+* T.S) :=
    RingHom.ext fun _ => rfl
  rw [hcomp] at hP
  change T.S.val.toRingHom (Polynomial.eval₂ (h.algHom : X.S →+* T.S) q P) = 0
  rw [Polynomial.hom_eval₂]
  exact hP

/-- `S_T` is a finite `S`-module (integral and of finite type). -/
theorem finite_algHom : (h.algHom : X.S →+* T.S).Finite := by
  refine h.isIntegral_algHom.to_finite (RingHom.FiniteType.of_comp_finiteType (f := algebraMap k X.S)
    ?_)
  have e : (h.algHom : X.S →+* T.S).comp (algebraMap k X.S) = algebraMap k T.S :=
    RingHom.ext fun c => h.algHom.commutes c
  rw [e]
  exact RingHom.finiteType_algebraMap.2 inferInstance

/-! #### The map on points `h^an(w) = w|_S` -/

theorem isMultigraded_comap {w : Berk k T.S} (hw : T.IsMultigraded w) :
    X.IsMultigraded (Berk.comap h.algHom w) := fun p a => by
  rw [Berk.comap_val_apply, Berk.comap_val_apply, h.algHom_homComp]
  exact hw _ a

theorem isNormalized_comap {w : Berk k T.S} (hw : T.IsNormalized w) :
    X.IsNormalized (Berk.comap h.algHom w) := fun c => by
  simp only [Berk.comap_val_apply, h.algHom_coordElem, coordIndexEquiv_apply]
  rw [← hw c, ← Finset.map_univ_equiv (h.coordEquiv c), Finset.sup_map]
  rfl

/-- **The map on points** `h^an(w) = w|_S` of a finite morphism (`def:gl-maps`). -/
def anMap (w : T.an) : X.an :=
  ⟨Berk.comap h.algHom w.1, h.isMultigraded_comap w.2.1, h.isNormalized_comap w.2.2⟩

theorem anMap_val (w : T.an) (p : X.S) : (h.anMap w).1.val p = w.1.val (h.algHom p) :=
  rfl

/-- `|f T^a|_{h^an(w)} = |f T^a|_w`. -/
theorem anMap_val_ofPiece (w : T.an) {a : Fin r →₀ ℕ} {f : K} (hf : f ∈ X.piece a) :
    (h.anMap w).1.val (X.ofPiece hf) = w.1.val (T.ofPiece (h.algebraMap_mem_piece hf)) := by
  rw [anMap_val, algHom_ofPiece]

theorem anMap_val_coordElem (w : T.an) (i : X.CoordIndex) :
    (h.anMap w).1.val (X.coordElem i) = w.1.val (T.coordElem (h.coordIndexEquiv i)) := by
  rw [anMap_val, algHom_coordElem]

/-- **`lem:gl-pullback`**: `h^an` is continuous. -/
theorem continuous_anMap : Continuous h.anMap :=
  X.continuous_iff_an.2 fun p =>
    (Berk.continuous_val_apply (h.algHom p)).comp continuous_subtype_val

/-- `h^an` is a closed map (a continuous map between compact Hausdorff spaces). -/
theorem isClosedMap_anMap : IsClosedMap h.anMap :=
  h.continuous_anMap.isClosedMap

/-- **`lem:gl-pullback`**: `h^an(⋆) = ⋆`. -/
theorem anMap_triv : h.anMap T.triv = X.triv := by
  classical
  refine Subtype.ext (Berk.ext_val fun p => ?_)
  rw [anMap_val]
  by_cases hp : p = 0
  · rw [hp, map_zero, map_zero, map_zero]
  · rw [X.triv_val_of_ne_zero hp, T.triv_val_of_ne_zero (h.algHom_ne_zero hp)]

/-- **`lem:gl-pullback`**: the only point of `𝒯^an` over `⋆` is `⋆`. A nonzero `q ∈ S_T` satisfies
an integral equation `q P'(q) = -c₀` over `S` with `c₀ ≠ 0` (divide by a power of `q`); since
`|c₀| = 1` and `|P'(q)|, |q| ≤ 1`, `|q| = 1`. -/
theorem eq_triv_of_anMap_eq_triv {w : T.an} (hw : h.anMap w = X.triv) : w = T.triv := by
  classical
  refine Subtype.ext (Berk.ext_val fun q => ?_)
  by_cases hq : q = 0
  · rw [hq, map_zero, map_zero]
  rw [T.triv_val_of_ne_zero hq]
  obtain ⟨P, hPm, hP⟩ := h.isIntegral_algHom q
  obtain ⟨Q, hPQ, hQX⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPm.ne_zero 0
  rw [map_zero, sub_zero] at hPQ hQX
  have hQm : Q.Monic := (Polynomial.monic_X.pow _).of_mul_monic_left (hPQ ▸ hPm)
  have hQ0 : Q.coeff 0 ≠ 0 := fun h0 => hQX (Polynomial.X_dvd_iff.2 h0)
  have hQq : Polynomial.eval₂ (h.algHom : X.S →+* T.S) q Q = 0 := by
    rw [hPQ, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hP
    exact (mul_eq_zero.1 hP).resolve_left (pow_ne_zero _ hq)
  rw [← Polynomial.X_mul_divX_add Q, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_C, add_eq_zero_iff_eq_neg] at hQq
  have hc : w.1.val ((h.algHom : X.S →+* T.S) (Q.coeff 0)) = 1 := by
    change w.1.val (h.algHom (Q.coeff 0)) = 1
    rw [← anMap_val, hw, X.triv_val_of_ne_zero hQ0]
  have h1 := congrArg w.1.val hQq
  rw [map_mul, Valuation.map_neg, hc] at h1
  refine le_antisymm (val_le_one w.2 q) ?_
  calc (1 : ℝ≥0) = w.1.val q * w.1.val (Polynomial.eval₂ (h.algHom : X.S →+* T.S) q Q.divX) :=
        h1.symm
    _ ≤ w.1.val q * 1 := by gcongr; exact val_le_one w.2 _
    _ = w.1.val q := mul_one _

/-- **`lem:gl-pullback`**: `h^an` has finite fibres. -/
theorem finite_anMap_preimage (v : X.an) : (h.anMap ⁻¹' {v}).Finite := by
  have hfin := Berk.finite_preimage_comap_singleton h.algHom h.finite_algHom v.1
  refine ((hfin.preimage (Set.injOn_of_injective Subtype.val_injective)).subset fun w hw => ?_)
  change Berk.comap h.algHom w.1 = v.1
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
  exact congrArg Subtype.val hw

/-! #### Charts -/

/-- The chart index of `𝒯` corresponding to a chart index of `𝒳`. -/
def chartIndex (j : X.ChartIndex) : T.ChartIndex :=
  fun c => h.coordEquiv c (j c)

theorem coord_chartIndex (j : X.ChartIndex) (c : Fin r) :
    T.coord c (h.chartIndex j c) = algebraMap K E (X.coord c (j c)) :=
  h.coord_coordEquiv c (j c)

theorem chartIndex_ne_zero {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) :
    ∀ c, T.coord c (h.chartIndex j c) ≠ 0 := fun c => by
  rw [coord_chartIndex]
  exact (map_ne_zero _).2 (hj c)

theorem chartDen_chartIndex (j : X.ChartIndex) (a : Fin r →₀ ℕ) :
    T.chartDen (h.chartIndex j) a = algebraMap K E (X.chartDen j a) := by
  simp only [chartDen, coord_chartIndex, map_prod, map_pow]

theorem algHom_chartMono (j : X.ChartIndex) (a : Fin r →₀ ℕ) :
    h.algHom (X.chartMono j a) = T.chartMono (h.chartIndex j) a := by
  rw [chartMono, algHom_ofPiece, chartMono]
  exact T.ofPiece_congr _ _ rfl (h.chartDen_chartIndex j a).symm

theorem algHom_chartElem (j : X.ChartIndex) :
    h.algHom (X.chartElem j) = T.chartElem (h.chartIndex j) := by
  rw [chartElem, map_prod, chartElem]
  exact Finset.prod_congr rfl fun c _ => h.algHom_coordElem ⟨c, j c⟩

/-- `ψ_j ∘ μ = (K → E) ∘ ψ_j` for the dehomogenizations. -/
theorem dehom_coeffMap (j : X.ChartIndex) (p : MvPolynomial (Fin r) K) :
    T.dehom (h.chartIndex j) (coeffMap k E p) = algebraMap K E (X.dehom j p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial a f =>
    rw [coeffMap_monomial, dehom_monomial, dehom_monomial, chartDen_chartIndex, map_div₀]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

/-- The inclusion `A_j ⊆ B_j` of the chart algebras of `𝒳` and `𝒯`. -/
def chartAlgHom (j : X.ChartIndex) : X.chartAlg j →ₐ[k] T.chartAlg (h.chartIndex j) :=
  ((IsScalarTower.toAlgHom k K E).comp (X.chartAlg j).val).codRestrict _ fun x => by
    obtain ⟨p, hp, hx⟩ := Subalgebra.mem_map.1 x.2
    refine Subalgebra.mem_map.2 ⟨coeffMap k E p, h.coeffMap_mem p hp, ?_⟩
    rw [h.dehom_coeffMap, hx]
    rfl

@[simp]
theorem coe_chartAlgHom (j : X.ChartIndex) (x : X.chartAlg j) :
    (h.chartAlgHom j x : E) = algebraMap K E x :=
  rfl

theorem chartAlgHom_injective (j : X.ChartIndex) : Function.Injective (h.chartAlgHom j) :=
  fun _ _ hxy => Subtype.ext ((algebraMap K E).injective (congrArg Subtype.val hxy))

/-- `B_j` is integral over `A_j`. -/
theorem isIntegral_chartAlgHom (j : X.ChartIndex) :
    (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j)).IsIntegral := by
  rintro ⟨y, hy⟩
  obtain ⟨q, hq, rfl⟩ := Subalgebra.mem_map.1 hy
  obtain ⟨P, hPm, hP⟩ := h.isIntegral_algHom ⟨q, hq⟩
  -- The dehomogenization `S → A_j`.
  let δ : X.S →+* X.chartAlg j :=
    ((X.dehom j).comp X.S.val).toRingHom.codRestrict _ fun p => Subalgebra.mem_map.2 ⟨p.1, p.2, rfl⟩
  refine ⟨P.map δ, hPm.map δ, Subtype.val_injective ?_⟩
  have e : ∀ P' : Polynomial X.S,
      ((Polynomial.eval₂ (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j))
        ⟨T.dehom (h.chartIndex j) q, hy⟩ (P'.map δ) : T.chartAlg (h.chartIndex j)) : E) =
        T.dehom (h.chartIndex j)
          ((Polynomial.eval₂ (h.algHom : X.S →+* T.S) ⟨q, hq⟩ P' : T.S) :
            MvPolynomial (Fin r) E) := by
    intro P'
    induction P' using Polynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ =>
      rw [Polynomial.map_add, Polynomial.eval₂_add, Polynomial.eval₂_add, Subalgebra.coe_add,
        Subalgebra.coe_add, map_add, h₁, h₂]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial,
        Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul,
        map_pow]
      change algebraMap K E (X.dehom j a.1) * _ = T.dehom (h.chartIndex j) (coeffMap k E a.1) * _
      rw [h.dehom_coeffMap]
  rw [e P, hP]
  simp

/-- `B_j` is a finite `A_j`-module. -/
theorem finite_chartAlgHom (j : X.ChartIndex) :
    (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j)).Finite := by
  refine (h.isIntegral_chartAlgHom j).to_finite
    (RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (X.chartAlg j)) ?_)
  have e : (h.chartAlgHom j : X.chartAlg j →+* T.chartAlg (h.chartIndex j)).comp
      (algebraMap k (X.chartAlg j)) = algebraMap k (T.chartAlg (h.chartIndex j)) :=
    RingHom.ext fun c => (h.chartAlgHom j).commutes c
  rw [e]
  exact RingHom.finiteType_algebraMap.2 inferInstance

theorem chartAlgHom_div_chartDen (j : X.ChartIndex) {a : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) :
    h.chartAlgHom j ⟨f / X.chartDen j a, div_chartDen_mem_chartAlg hf⟩ =
      ⟨algebraMap K E f / T.chartDen (h.chartIndex j) a,
        div_chartDen_mem_chartAlg (h.algebraMap_mem_piece hf)⟩ :=
  Subtype.ext (by
    rw [coe_chartAlgHom, map_div₀]
    exact congrArg (algebraMap K E f / ·) (h.chartDen_chartIndex j a).symm)

theorem chartAlgHom_coord_div (j : X.ChartIndex) (c : Fin r) (i : Fin (X.M c + 1)) :
    h.chartAlgHom j ⟨X.coord c i / X.coord c (j c), X.coord_div_mem_chartAlg j c i⟩ =
      ⟨T.coord c (h.coordEquiv c i) / T.coord c (h.chartIndex j c),
        T.coord_div_mem_chartAlg (h.chartIndex j) c (h.coordEquiv c i)⟩ :=
  Subtype.ext (by
    rw [coe_chartAlgHom, map_div₀]
    change _ = T.coord c (h.coordEquiv c i) / T.coord c (h.chartIndex j c)
    rw [coord_chartIndex, h.coord_coordEquiv])

/-- A point of `𝒯^an` lies in the chart domain of `chartIndex j` iff its image lies in `U_j`. -/
theorem mem_chartDomain_chartIndex_iff (j : X.ChartIndex) (w : T.an) :
    w ∈ T.chartDomain (h.chartIndex j) ↔ h.anMap w ∈ X.chartDomain j := by
  change w.1.val (T.chartElem _) ≠ 0 ↔ (h.anMap w).1.val (X.chartElem j) ≠ 0
  rw [anMap_val, algHom_chartElem]

/-- **Compatibility with the charts**: `ι_j(h^an(w)) = ι_j(w)|_{A_j}`. -/
theorem chartMap_anMap {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) (w : T.an)
    (hw : ∀ c, w.1.val (T.coordElem ⟨c, h.chartIndex j c⟩) ≠ 0) :
    X.chartMap hj (h.anMap w).1 (fun c => by
        rw [anMap_val_coordElem]; exact hw c) =
      Berk.comap (h.chartAlgHom j) (T.chartMap (h.chartIndex_ne_zero hj) w.1 hw) := by
  refine Berk.ext_val fun x => ?_
  obtain ⟨a, f, hf, hx⟩ := (mem_chartAlg_iff hj).1 x.2
  rw [X.chartMap_val_eq hj _ x hf hx, Berk.comap_val_apply,
    T.chartMap_val_eq (h.chartIndex_ne_zero hj) hw _ (h.algebraMap_mem_piece hf)
      (by rw [coe_chartAlgHom, hx, map_div₀, chartDen_chartIndex]),
    anMap_val_ofPiece, anMap_val, algHom_chartMono]

/-- `μ_c(y|_{A_j}) = μ_c(y)`: the scales of the inverse charts agree. -/
theorem chartScale_comap (j : X.ChartIndex) (y : Berk k (T.chartAlg (h.chartIndex j)))
    (c : Fin r) :
    X.chartScale j (Berk.comap (h.chartAlgHom j) y) c = T.chartScale (h.chartIndex j) y c := by
  rw [chartScale, chartScale, ← Finset.map_univ_equiv (h.coordEquiv c), Finset.sup_map]
  refine Finset.sup_congr rfl fun i _ => ?_
  rw [Function.comp_apply, Berk.comap_val_apply, chartAlgHom_coord_div]
  rfl

theorem chartScalePow_comap (j : X.ChartIndex) (y : Berk k (T.chartAlg (h.chartIndex j)))
    (a : Fin r →₀ ℕ) :
    X.chartScalePow j (Berk.comap (h.chartAlgHom j) y) a =
      T.chartScalePow (h.chartIndex j) y a := by
  simp only [chartScalePow, chartScale_comap]

/-- **Compatibility with the inverse charts**: `h^an(ι_j⁻¹(y)) = ι_j⁻¹(y|_{A_j})`. -/
theorem anMap_chartInv {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0)
    (y : Berk k (T.chartAlg (h.chartIndex j))) :
    h.anMap (T.chartInv (h.chartIndex j) (h.chartIndex_ne_zero hj) y) =
      X.chartInv j hj (Berk.comap (h.chartAlgHom j) y) := by
  refine Subtype.ext (ext_of_ofPiece (h.anMap _).2.1 (X.chartInv j hj _).2.1 fun a f hf => ?_)
  rw [anMap_val_ofPiece, chartInv_val_ofPiece, chartInv_val_ofPiece, chartScalePow_comap,
    Berk.comap_val_apply, chartAlgHom_div_chartDen _ _ hf]

/-- **`lem:gl-pullback`**: `h^an` is surjective. For `v ∈ U_j`, a point `y` of `(Spec B_j)^an` over
`ι_j(v)` exists since `A_j ⊆ B_j` is integral, and `h^an(ι_j⁻¹(y)) = ι_j⁻¹(ι_j(v)) = v`. -/
theorem anMap_surjective : Function.Surjective h.anMap := by
  intro v
  obtain ⟨j, hj, hv1⟩ := X.exists_chartIndex v
  have hv : v ∈ X.chartDomain j :=
    chartUnitDomain_subset (X := X) (j := j) hv1
  obtain ⟨y, hy⟩ := Berk.comap_surjective_of_isIntegral (h.chartAlgHom j)
    (h.isIntegral_chartAlgHom j) (h.chartAlgHom_injective j)
    (X.chartMap hj v.1 (mem_chartDomain_iff.1 hv))
  refine ⟨T.chartInv (h.chartIndex j) (h.chartIndex_ne_zero hj) y, ?_⟩
  rw [h.anMap_chartInv hj y, hy, chartInv_chartMap hj v hv]

/-! #### Monomials in the coordinates -/

/-- The bijection `β ↦ β ∘ coordIndexEquiv⁻¹` of multi-indices. -/
def monEquiv : (X.CoordIndex →₀ ℕ) ≃ (T.CoordIndex →₀ ℕ) :=
  Finsupp.equivCongrLeft h.coordIndexEquiv

theorem monEquiv_apply (β : X.CoordIndex →₀ ℕ) :
    h.monEquiv β = Finsupp.mapDomain h.coordIndexEquiv β :=
  Finsupp.equivMapDomain_eq_mapDomain _ _

theorem monDeg_monEquiv (β : X.CoordIndex →₀ ℕ) : T.monDeg (h.monEquiv β) = X.monDeg β := by
  rw [monEquiv_apply, monDeg, monDeg, ← Finsupp.mapDomain_comp]
  rfl

theorem zCoeff_monEquiv (β : X.CoordIndex →₀ ℕ) :
    T.zCoeff (h.monEquiv β) = algebraMap K E (X.zCoeff β) := by
  rw [monEquiv_apply, zCoeff, zCoeff, Finsupp.prod_mapDomain_index (fun _ => pow_zero _)
    fun _ _ _ => pow_add _ _ _, map_finsuppProd]
  refine Finsupp.prod_congr fun i _ => ?_
  rw [coordIndexEquiv_apply, h.coord_coordEquiv, map_pow]

/-- `Mon(b)` of `𝒯` is the image of `Mon(b)` of `𝒳`. -/
theorem monSet_eq_map (b : Fin r →₀ ℕ) :
    T.monSet b = (X.monSet b).map h.monEquiv.toEmbedding := by
  ext γ
  rw [Finset.mem_map_equiv, mem_monSet, mem_monSet, ← h.monDeg_monEquiv, Equiv.apply_symm_apply]

theorem algHom_zMon (β : X.CoordIndex →₀ ℕ) : h.algHom (X.zMon β) = T.zMon (h.monEquiv β) := by
  rw [zMon, algHom_ofPiece, zMon]
  exact T.ofPiece_congr _ _ (h.monDeg_monEquiv β).symm (h.zCoeff_monEquiv β).symm

theorem monEquiv_mem_monSet {b : Fin r →₀ ℕ} {β : X.CoordIndex →₀ ℕ} (hβ : β ∈ X.monSet b) :
    h.monEquiv β ∈ T.monSet b := by
  rw [T.mem_monSet, monDeg_monEquiv]
  exact X.mem_monSet.1 hβ

include h in
/-- **Values of sections are preserved** (`lem:gl-pullback`, "`R_a(𝒳) ⊆ R_a(𝒯)` with the same
values"): if `f z̃^β ∈ S_d` for all `β ∈ Mon(b)`, then `f z̃^γ ∈ (S_T)_d` for all
`γ ∈ Mon_T(b)`. -/
theorem mem_piece_mul_zCoeff {b d : Fin r →₀ ℕ} {f : K}
    (hf : ∀ β ∈ X.monSet b, f * X.zCoeff β ∈ X.piece d) :
    ∀ γ ∈ T.monSet b, algebraMap K E f * T.zCoeff γ ∈ T.piece d := by
  intro γ hγ
  rw [h.monSet_eq_map b, Finset.mem_map_equiv] at hγ
  have := h.algebraMap_mem_piece (hf _ hγ)
  rwa [map_mul, ← h.zCoeff_monEquiv, Equiv.apply_symm_apply] at this

/-- `|f z̃^γ T^d|_w = |f z̃^β T^d|_{h^an(w)}` for `γ` the multi-index of `𝒯` corresponding to
`β ∈ Mon(b)`. -/
theorem val_ofPiece_mul_zCoeff_monEquiv {b d : Fin r →₀ ℕ} {f : K}
    (hf : ∀ β ∈ X.monSet b, f * X.zCoeff β ∈ X.piece d) (w : T.an)
    {β : X.CoordIndex →₀ ℕ} (hβ : β ∈ X.monSet b) :
    w.1.val (T.ofPiece (h.mem_piece_mul_zCoeff hf _ (h.monEquiv_mem_monSet hβ))) =
      (h.anMap w).1.val (X.ofPiece (hf β hβ)) := by
  rw [anMap_val_ofPiece]
  congr 1
  refine T.ofPiece_congr _ _ rfl ?_
  rw [map_mul, h.zCoeff_monEquiv]

/-- **Values of sections at `h^an(w)`**: `max_{γ ∈ Mon_T(b)} |f z̃^γ T^d|_w =
max_{β ∈ Mon(b)} |f z̃^β T^d|_{h^an(w)}` (with `homNorm` the values on homogeneous
elements). -/
theorem sup_monSet_homNorm_anMap {b d : Fin r →₀ ℕ} {f : K}
    (hf : ∀ β ∈ X.monSet b, f * X.zCoeff β ∈ X.piece d) (w : T.an) :
    ((T.monSet b).sup fun γ => T.homNorm w.1 d (algebraMap K E f * T.zCoeff γ)) =
      (X.monSet b).sup fun β => X.homNorm (h.anMap w).1 d (f * X.zCoeff β) := by
  rw [h.monSet_eq_map b, Finset.sup_map]
  refine Finset.sup_congr rfl fun β hβ => ?_
  rw [Function.comp_apply, Equiv.coe_toEmbedding,
    T.homNorm_of_mem _ (h.mem_piece_mul_zCoeff hf _ (h.monEquiv_mem_monSet hβ)),
    X.homNorm_of_mem _ (hf β hβ), h.val_ofPiece_mul_zCoeff_monEquiv hf w hβ]

/-! #### The degree is finite -/

include h in
/-- The coefficient `f` of a homogeneous element `f T^a ∈ S_T` is integral over `K`: the
coefficient of `T^{n a}` in an integral equation `(f T^a)^n + ∑_{i<n} μ(p_i) (f T^a)^i = 0` over
`S` is `f^n + ∑_{i<n} (p_i)_{(n-i)a} f^i = 0`. -/
theorem isIntegral_of_mem_piece {a : Fin r →₀ ℕ} {f : E} (hf : f ∈ T.piece a) :
    IsIntegral K f := by
  obtain ⟨P, hPm, hP⟩ := (isIntegral_imageS_iff (X := X) (E := E)).1 (h.isIntegral _ hf)
  set n := P.natDegree
  set c : Fin n → K := fun i => (P.coeff i).1.coeff ((n - i) • a)
  have hterm : ∀ i : Fin n, ((X.coeffMapS E (P.coeff i)) * monomial a f ^ (i : ℕ)).coeff (n • a) =
      algebraMap K E (c i) * f ^ (i : ℕ) := by
    intro i
    have hle : (i : ℕ) • a ≤ n • a := nsmul_le_nsmul_left (zero_le) i.2.le
    have hsub : n • a - (i : ℕ) • a = (n - i) • a := by
      ext d
      simp [Nat.sub_mul]
    rw [monomial_pow, coeff_mul_monomial', if_pos hle, hsub]
    rfl
  have key := congrArg (fun q : MvPolynomial (Fin r) E => q.coeff (n • a)) hP
  rw [hPm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    coeff_add, coeff_sum, Finset.sum_range (fun i => (Polynomial.eval₂ (X.coeffMapS E)
      (monomial a f) (Polynomial.C (P.coeff i) * Polynomial.X ^ i)).coeff (n • a))] at key
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at key
  rw [Finset.sum_congr rfl fun i _ => hterm i, monomial_pow, coeff_monomial, if_pos rfl,
    coeff_zero] at key
  refine ⟨Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  exact key

include h in
/-- **The degree `[E : K]` of a finite morphism is finite** (`def:gl-maps`): every element of `E`
is a quotient of coefficients of homogeneous elements of `S_T` (integral over `K`), and `E` is a
finitely generated field extension of `k` (`fg_top_intermediateField`). -/
theorem finiteDimensional : FiniteDimensional K E := by
  obtain ⟨t, ht⟩ := T.fg_top_intermediateField
  have hint : ∀ x : E, IsIntegral K x := fun x => by
    obtain ⟨a, f, g, hf, hg, -, rfl⟩ := T.exists_eq_div x
    rw [div_eq_mul_inv]
    exact (h.isIntegral_of_mem_piece hf).mul (h.isIntegral_of_mem_piece hg).inv
  have htop : IntermediateField.adjoin K (t : Set E) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hle : IntermediateField.adjoin k (t : Set E) ≤
        (IntermediateField.adjoin K (t : Set E)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 fun y hy =>
        (IntermediateField.mem_restrictScalars k).2 (IntermediateField.subset_adjoin K _ hy)
    rw [ht] at hle
    exact (IntermediateField.mem_restrictScalars k).1 (hle IntermediateField.mem_top)
  have : FiniteDimensional K (IntermediateField.adjoin K (t : Set E)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hint x
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end FiniteHom

/-! #### Normalizations are finite morphisms -/

variable (X : MultiModel k K r) (E) in
/-- **The normalization of `𝒳` in a finite extension `E ⊇ K` is a finite morphism**
`𝒳_E → 𝒳` (`rmk:gl-model-examples`(3), `def:gl-maps`). -/
def FiniteHom.ofNormalizationIn [Infinite k] [PerfectField k] [FiniteDimensional K E] :
    FiniteHom (X.normalizationIn E) X where
  coordEquiv _ := Equiv.refl _
  coord_coordEquiv _ _ := rfl
  coeffMap_mem _ hp := X.coeffMap_mem_normalizationIn_S hp
  isIntegral _ hq := hq

variable (X : MultiModel k K r) in
/-- **The normalization `𝒳^ν → 𝒳` is a finite morphism** (`rmk:gl-model-examples`(2),
`def:gl-maps`); `ν^an` is continuous, surjective, with finite fibres (`lem:gl-pullback`). -/
def FiniteHom.ofNormalization [Infinite k] [PerfectField k] : FiniteHom X.normalization X :=
  FiniteHom.ofNormalizationIn (E := K) X

end FiniteHom


/-! ### Scalar restriction -/

section ScalarRestriction

variable {k₀ : Type u} [Field k₀] {K₀ : Type u} [Field K₀] [Algebra k₀ K₀]
  {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  [Algebra k₀ k] [Algebra K₀ K] [Algebra k₀ K] [IsScalarTower k₀ k K] [IsScalarTower k₀ K₀ K]

variable (k₀ K₀ K r) in
/-- The coefficientwise inclusion `K₀[T] → K[T]`, a `k₀`-algebra map. -/
def baseCoeffMap : MvPolynomial (Fin r) K₀ →ₐ[k₀] MvPolynomial (Fin r) K :=
  MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom k₀ K₀ K)

theorem baseCoeffMap_apply (p : MvPolynomial (Fin r) K₀) :
    baseCoeffMap k₀ K₀ K r p = MvPolynomial.map (algebraMap K₀ K) p :=
  rfl

theorem baseCoeffMap_monomial (a : Fin r →₀ ℕ) (f : K₀) :
    baseCoeffMap k₀ K₀ K r (monomial a f) = monomial a (algebraMap K₀ K f) :=
  map_monomial _ _ _

theorem baseCoeffMap_injective : Function.Injective (baseCoeffMap k₀ K₀ K r) :=
  map_injective _ (algebraMap K₀ K).injective

/-- A **scalar restriction** (`def:gl-maps`): a model `𝒳₀ = (K₀, S₀, z)` over `k₀` and a model
`𝒳 = (K, S, z)` over `k ⊇ k₀` with `K₀ ⊆ K`, the same coordinates, and `S = k · S₀ ≅ k ⊗_{k₀} S₀`
inside `K[T]`. Restriction `r(v) = v|_{S₀}` is `ScalarRestriction.anMap`. -/
structure ScalarRestriction (X₀ : MultiModel k₀ K₀ r) (X : MultiModel k K r) where
  /-- The bijection between the coordinate indices of degree `e_c`. -/
  coordEquiv : ∀ c, Fin (X₀.M c + 1) ≃ Fin (X.M c + 1)
  /-- The coordinates agree. -/
  coord_coordEquiv : ∀ c j, X.coord c (coordEquiv c j) = algebraMap K₀ K (X₀.coord c j)
  /-- `S₀ ⊆ S` (coefficientwise). -/
  baseCoeffMap_mem : ∀ p ∈ X₀.S, baseCoeffMap k₀ K₀ K r p ∈ X.S
  /-- `S = k · S₀`. -/
  span_eq : Submodule.span k (baseCoeffMap k₀ K₀ K r '' (X₀.S : Set (MvPolynomial (Fin r) K₀))) =
    Subalgebra.toSubmodule X.S
  /-- `k ⊗_{k₀} S₀ → S` is injective, so `S ≅ k ⊗_{k₀} S₀`. -/
  injective_tensor : Function.Injective
    (Algebra.TensorProduct.lift (Algebra.ofId k (MvPolynomial (Fin r) K))
      ((baseCoeffMap k₀ K₀ K r).comp X₀.S.val) fun _ _ => Commute.all _ _ :
        TensorProduct k₀ k X₀.S →ₐ[k] MvPolynomial (Fin r) K)

namespace ScalarRestriction

variable {X₀ : MultiModel k₀ K₀ r} {X : MultiModel k K r} (h : ScalarRestriction X₀ X)

include h in
/-- The inclusion `S₀ → S`, a ring map. -/
def ringHom : X₀.S →+* X.S :=
  ((baseCoeffMap k₀ K₀ K r).toRingHom.comp X₀.S.val.toRingHom).codRestrict X.S
    fun p => h.baseCoeffMap_mem p.1 p.2

@[simp]
theorem coe_ringHom (p : X₀.S) :
    (h.ringHom p : MvPolynomial (Fin r) K) = baseCoeffMap k₀ K₀ K r p.1 :=
  rfl

theorem ringHom_injective : Function.Injective h.ringHom := fun _ _ hpq =>
  Subtype.ext (baseCoeffMap_injective (congrArg Subtype.val hpq))

theorem ringHom_algebraMap (c : k₀) :
    h.ringHom (algebraMap k₀ X₀.S c) = algebraMap k X.S (algebraMap k₀ k c) := by
  apply Subtype.ext
  rw [coe_ringHom, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, AlgHom.commutes,
    MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply k₀ k K]

include h in
theorem algebraMap_mem_piece {a : Fin r →₀ ℕ} {f : K₀} (hf : f ∈ X₀.piece a) :
    algebraMap K₀ K f ∈ X.piece a := by
  rw [mem_piece, ← baseCoeffMap_monomial (k₀ := k₀)]
  exact h.baseCoeffMap_mem _ hf

theorem ringHom_ofPiece {a : Fin r →₀ ℕ} {f : K₀} (hf : f ∈ X₀.piece a) :
    h.ringHom (X₀.ofPiece hf) = X.ofPiece (h.algebraMap_mem_piece hf) :=
  Subtype.ext (baseCoeffMap_monomial _ _)

theorem ringHom_homComp (a : Fin r →₀ ℕ) (p : X₀.S) :
    h.ringHom (X₀.homComp a p) = X.homComp a (h.ringHom p) := by
  apply Subtype.ext
  rw [coe_ringHom, coe_homComp, coe_homComp, coe_ringHom, baseCoeffMap_monomial,
    baseCoeffMap_apply, coeff_map]

/-- The bijection of coordinate indices. -/
def coordIndexEquiv : X₀.CoordIndex ≃ X.CoordIndex :=
  Equiv.sigmaCongrRight h.coordEquiv

@[simp]
theorem coordIndexEquiv_apply (i : X₀.CoordIndex) :
    h.coordIndexEquiv i = ⟨i.1, h.coordEquiv i.1 i.2⟩ :=
  rfl

theorem ringHom_coordElem (i : X₀.CoordIndex) :
    h.ringHom (X₀.coordElem i) = X.coordElem (h.coordIndexEquiv i) := by
  apply Subtype.ext
  rw [coe_ringHom, coe_coordElem, baseCoeffMap_monomial, coordIndexEquiv_apply, coe_coordElem,
    h.coord_coordEquiv]

/-- The restriction `v|_{S₀}` of a point `v ∈ (Spec S)^an` (trivial on `k ⊇ k₀`). -/
def berkRestrict (v : Berk k X.S) : Berk k₀ X₀.S :=
  ⟨v.val.comap h.ringHom, fun c hc => by
    rw [Valuation.comap_apply, h.ringHom_algebraMap]
    exact v.val_algebraMap _ ((map_ne_zero _).2 hc)⟩

theorem berkRestrict_val (v : Berk k X.S) (p : X₀.S) :
    (h.berkRestrict v).val p = v.val (h.ringHom p) :=
  rfl

/-- **Restriction of points** `r(v) = v|_{S₀}` for a scalar restriction (`def:gl-maps`). -/
def anMap (v : X.an) : X₀.an :=
  ⟨h.berkRestrict v.1, fun p a => by
      rw [berkRestrict_val, berkRestrict_val, h.ringHom_homComp]
      exact v.2.1 _ a,
    fun c => by
      simp only [berkRestrict_val, h.ringHom_coordElem, coordIndexEquiv_apply]
      rw [← v.2.2 c, ← Finset.map_univ_equiv (h.coordEquiv c), Finset.sup_map]
      rfl⟩

theorem anMap_val (v : X.an) (p : X₀.S) : (h.anMap v).1.val p = v.1.val (h.ringHom p) :=
  rfl

/-- `|f T^a|_{r(v)} = |f T^a|_v`. -/
theorem anMap_val_ofPiece (v : X.an) {a : Fin r →₀ ℕ} {f : K₀} (hf : f ∈ X₀.piece a) :
    (h.anMap v).1.val (X₀.ofPiece hf) = v.1.val (X.ofPiece (h.algebraMap_mem_piece hf)) := by
  rw [anMap_val, ringHom_ofPiece]

/-- **`lem:gl-pullback`** (scalar restriction): `r` is continuous. -/
theorem continuous_anMap : Continuous h.anMap :=
  X₀.continuous_iff_an.2 fun p =>
    (Berk.continuous_val_apply (h.ringHom p)).comp continuous_subtype_val

/-- **`lem:gl-pullback`** (scalar restriction): `r(⋆) = ⋆`. -/
theorem anMap_triv : h.anMap X.triv = X₀.triv := by
  classical
  refine Subtype.ext (Berk.ext_val fun p => ?_)
  rw [anMap_val]
  by_cases hp : p = 0
  · rw [hp, map_zero, map_zero, map_zero]
  · rw [X₀.triv_val_of_ne_zero hp, X.triv_val_of_ne_zero fun h0 =>
      hp (h.ringHom_injective (h0.trans (map_zero _).symm))]

/-- The bijection of multi-indices. -/
def monEquiv : (X₀.CoordIndex →₀ ℕ) ≃ (X.CoordIndex →₀ ℕ) :=
  Finsupp.equivCongrLeft h.coordIndexEquiv

theorem monEquiv_apply (β : X₀.CoordIndex →₀ ℕ) :
    h.monEquiv β = Finsupp.mapDomain h.coordIndexEquiv β :=
  Finsupp.equivMapDomain_eq_mapDomain _ _

theorem monDeg_monEquiv (β : X₀.CoordIndex →₀ ℕ) : X.monDeg (h.monEquiv β) = X₀.monDeg β := by
  rw [monEquiv_apply, monDeg, monDeg, ← Finsupp.mapDomain_comp]
  rfl

theorem zCoeff_monEquiv (β : X₀.CoordIndex →₀ ℕ) :
    X.zCoeff (h.monEquiv β) = algebraMap K₀ K (X₀.zCoeff β) := by
  rw [monEquiv_apply, zCoeff, zCoeff, Finsupp.prod_mapDomain_index (fun _ => pow_zero _)
    fun _ _ _ => pow_add _ _ _, map_finsuppProd]
  refine Finsupp.prod_congr fun i _ => ?_
  rw [coordIndexEquiv_apply, h.coord_coordEquiv, map_pow]

theorem monSet_eq_map (b : Fin r →₀ ℕ) :
    X.monSet b = (X₀.monSet b).map h.monEquiv.toEmbedding := by
  ext γ
  rw [Finset.mem_map_equiv, mem_monSet, mem_monSet, ← h.monDeg_monEquiv, Equiv.apply_symm_apply]

theorem monEquiv_mem_monSet {b : Fin r →₀ ℕ} {β : X₀.CoordIndex →₀ ℕ} (hβ : β ∈ X₀.monSet b) :
    h.monEquiv β ∈ X.monSet b := by
  rw [X.mem_monSet, monDeg_monEquiv]
  exact X₀.mem_monSet.1 hβ

include h in
/-- Sections of `𝒳₀` are sections of `𝒳` (`lem:gl-pullback`, scalar restriction). -/
theorem mem_piece_mul_zCoeff {b d : Fin r →₀ ℕ} {f : K₀}
    (hf : ∀ β ∈ X₀.monSet b, f * X₀.zCoeff β ∈ X₀.piece d) :
    ∀ γ ∈ X.monSet b, algebraMap K₀ K f * X.zCoeff γ ∈ X.piece d := by
  intro γ hγ
  rw [h.monSet_eq_map b, Finset.mem_map_equiv] at hγ
  have := h.algebraMap_mem_piece (hf _ hγ)
  rwa [map_mul, ← h.zCoeff_monEquiv, Equiv.apply_symm_apply] at this

/-- **Values of sections at `r(v)`** (scalar restriction). -/
theorem sup_monSet_homNorm_anMap {b d : Fin r →₀ ℕ} {f : K₀}
    (hf : ∀ β ∈ X₀.monSet b, f * X₀.zCoeff β ∈ X₀.piece d) (v : X.an) :
    ((X.monSet b).sup fun γ => X.homNorm v.1 d (algebraMap K₀ K f * X.zCoeff γ)) =
      (X₀.monSet b).sup fun β => X₀.homNorm (h.anMap v).1 d (f * X₀.zCoeff β) := by
  rw [h.monSet_eq_map b, Finset.sup_map]
  refine Finset.sup_congr rfl fun β hβ => ?_
  rw [Function.comp_apply, Equiv.coe_toEmbedding,
    X.homNorm_of_mem _ (h.mem_piece_mul_zCoeff hf _ (h.monEquiv_mem_monSet hβ)),
    X₀.homNorm_of_mem _ (hf β hβ), anMap_val_ofPiece]
  congr 1
  refine X.ofPiece_congr _ _ rfl ?_
  rw [map_mul, h.zCoeff_monEquiv]

end ScalarRestriction

end ScalarRestriction

end MultiModel

end EnvelopeProperty
