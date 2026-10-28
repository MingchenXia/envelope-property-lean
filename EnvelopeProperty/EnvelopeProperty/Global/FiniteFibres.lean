/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.MorphismsPSH
import EnvelopeProperty.Berkovich.FlatFibre

/-!
# Fibres of finite morphisms of models over points with generic support

This file implements the blueprint nodes `def:gl-finite-fibres` and `lem:gl-finite-fibres` of
`global.tex` (subsection `subsec:gl-ample`) for the formalization of Fang–Han–Xia, *The envelope
property for unibranch projective varieties* (FHX, revision `832e086`, §4, `sec:finite-descent`).

Let `h : 𝒯 → 𝒳` be a finite morphism of models (`MultiModel.FiniteHom`, `def:gl-maps`), with
function fields `K ⊆ E` of finite degree `d = [E : K]`.

## Points with generic support as points of `(Spec K)^an`

A point `v ∈ 𝒳^an` with generic support defines an absolute value on `K`
(`MultiModel.fieldVal`, `def:gl-points`), i.e. a point `MultiModel.fieldPoint v` of
`(Spec K)^an = Berk k K`. On a chart `j` containing `v` it extends the chart value
(`MultiModel.fieldVal_coe_chartAlg`), and at a point with `|z^{(c)}_{j_c}|_v = 1` for all `c`,
`|f|_v = |f / z̃_j^a|_v` for sections `f ∈ R_a` (`MultiModel.secAbs_eq_fieldVal`).

## The fibre (`def:gl-finite-fibres`, `lem:gl-finite-fibres`)

For `v ∈ 𝒳^val` the fibre `h⁻¹(v)` (`FiniteHom.fibre`) is in bijection with the fibre of
`(Spec E)^an → (Spec K)^an` over `fieldPoint v` (`FiniteHom.fibreEquiv`, via
`w ↦ fieldPoint w`); the latter is in bijection with the maximal ideals of the Artinian algebra
`H(v) ⊗_K E = ∏_w B_w` (`Berk.fibreEquivMaximalSpectrum`, `H(v)` the completion of `(K, |·|_v)`).
The multiplicity `d(w/v) = dim_{H(v)} B_w` (`MultiModel.fibreDeg`) is
`Berk.flatFibreMult K (fieldPoint w)`. Then:

* `FiniteHom.hasGenericSupport_of_anMap`: the points over a point with generic support have
  generic support;
* `FiniteHom.comap_fieldPoint`: `fieldPoint w` lies over `fieldPoint (h w)`;
* `FiniteHom.eq_of_fieldPoint_eq`, `FiniteHom.exists_fieldPoint_eq`,
  `FiniteHom.fibreEquiv`: the bijection; `FiniteHom.fibreEquivFactors`,
  `FiniteHom.fibreDeg_eq_finrank`: the points over `v` correspond to the local factors `B_w`, and
  `d(w/v) = dim_{H(v)} B_w`;
* `FiniteHom.sum_fibreDeg`: `∑_{w ↦ v} d(w/v) = d`;
* `MultiModel.one_le_fibreDeg`;
* `FiniteHom.fibre_triv`: the only point over `⋆` is `⋆` (`FiniteHom.eq_triv_of_anMap_eq_triv`,
  lane G3).

The bijection is constructed on a chart: a point `y` of `(Spec E)^an` over `fieldPoint v`
restricts to a point of the chart algebra `B_j` of `𝒯`, whose inverse chart image lies over
`v` (`FiniteHom.anMap_chartInv`); conversely a point over `v` is determined by its absolute value
on `E` and the values of the coordinates (`MultiModel.eq_of_fieldVal_eq`).

## Deviation from the blueprint

The blueprint describes the fibres through the chart algebras (`B_j ⊗_{A_j} H(v) = E ⊗_K H(v)`);
here the field-level fibre of `(Spec E)^an → (Spec K)^an` is used directly, so no tensor
identification `B_j ⊗_{A_j} K ≅ E` is needed.
-/

open scoped NNReal ENNReal Topology TensorProduct

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-! ### Points with generic support as points of `(Spec K)^an` -/

variable (X) in
/-- The point of `(Spec K)^an` defined by a point `v ∈ 𝒳^an` with generic support: the absolute
value `|f / g| = |f T^a|_v / |g T^a|_v` on `K` (`def:gl-points`, `MultiModel.fieldVal`). -/
def fieldPoint (v : X.an) (hv : X.HasGenericSupport v.1) : Berk k K :=
  ⟨X.fieldVal v hv, fun _ hc => X.fieldVal_algebraMap v hv hc⟩

theorem fieldPoint_val (v : X.an) (hv : X.HasGenericSupport v.1) :
    (X.fieldPoint v hv).val = X.fieldVal v hv :=
  rfl

/-- On a chart `j` with `v ∈ U_j`, the absolute value of `v` on `K` extends the chart value
`ι_j(v)` on `A_j`. -/
theorem fieldVal_coe_chartAlg {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) (v : X.an)
    (hv : X.HasGenericSupport v.1) (hvj : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) ≠ 0)
    (x : X.chartAlg j) : X.fieldVal v hv x = (X.chartMap hj v.1 hvj).val x := by
  obtain ⟨a, f, hf, hx⟩ := (mem_chartAlg_iff hj).1 x.2
  rw [hx, X.fieldVal_div v hv hf (X.chartDen_mem_piece j a), X.chartMap_val_eq hj hvj x hf hx]
  rfl

/-- `|f T^a|_v = |f / z̃_j^a|_v` at a point with `|z^{(c)}_{j_c}|_v = 1` for all `c`. -/
theorem val_ofPiece_eq_fieldVal {j : X.ChartIndex} (v : X.an) (hv : X.HasGenericSupport v.1)
    (hv1 : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) = 1) {a : Fin r →₀ ℕ} {f : K}
    (hf : f ∈ X.piece a) : v.1.val (X.ofPiece hf) = X.fieldVal v hv (f / X.chartDen j a) := by
  rw [X.fieldVal_div v hv hf (X.chartDen_mem_piece j a)]
  change _ = v.1.val (X.ofPiece hf) / v.1.val (X.chartMono j a)
  rw [val_chartMono]
  simp [hv1]

/-- **Sections at a point with generic support**: if `|z^{(c)}_{j_c}|_v = 1` for all `c`, then
`|f|_v = |f / z̃_j^a|_v` for `f ∈ R_a` (`lem:gl-sections`(4)). -/
theorem secAbs_eq_fieldVal {j : X.ChartIndex} (hj : ∀ c, X.coord c (j c) ≠ 0) (v : X.an)
    (hv : X.HasGenericSupport v.1) (hv1 : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) = 1)
    {a : Fin r → ℤ} {f : K} (hf : f ∈ X.sections a) :
    X.secAbs v.1 a f = X.fieldVal v hv (f / X.chartDenZ j a) := by
  have hvj : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) ≠ 0 := fun c => by
    rw [hv1 c]; exact one_ne_zero
  rw [secAbs_eq_chartMap v.2.2 hj hvj hf]
  have e := fieldVal_coe_chartAlg hj v hv hvj
    ⟨f / X.chartDenZ j a, div_chartDenZ_mem_chartAlg hj hf⟩
  rw [← e]
  simp [hv1]

/-- **Points with generic support are determined by their absolute value on `K` and the values
of the coordinates.** -/
theorem eq_of_fieldVal_eq {v v' : X.an} (hv : X.HasGenericSupport v.1)
    (hv' : X.HasGenericSupport v'.1) (hf : X.fieldVal v hv = X.fieldVal v' hv')
    (hz : ∀ i : X.CoordIndex, v.1.val (X.coordElem i) = v'.1.val (X.coordElem i)) : v = v' := by
  obtain ⟨j, -, hj1⟩ := X.exists_chartIndex v
  have hj1' : ∀ c, v'.1.val (X.coordElem ⟨c, j c⟩) = 1 := fun c => by rw [← hz, hj1 c]
  refine Subtype.ext (ext_of_ofPiece v.2.1 v'.2.1 fun a f hfa => ?_)
  rw [val_ofPiece_eq_fieldVal v hv hj1 hfa, val_ofPiece_eq_fieldVal v' hv' hj1' hfa, hf]

/-! #### The multiplicities (`def:gl-finite-fibres`) -/

section FibreDeg

variable {E : Type u} [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  (T : MultiModel k E r)

variable (K) in
open Classical in
/-- **The multiplicity `d(w/v)`** (`def:gl-finite-fibres`) of a point `w ∈ 𝒯^an` with generic
support in its fibre over `v = h(w)`, for a finite morphism `h : 𝒯 → 𝒳` with function fields
`K ⊆ E`: `dim_{H(v)} B_w`, where `H(v) ⊗_K E = ∏_w B_w` is the decomposition of the Artinian
algebra `H(v) ⊗_K E` into local factors, `H(v)` the completion of `(K, |·|_v)`. In Lean it is
`Berk.flatFibreMult K (fieldPoint w)` (the dimension of the local factor of
`H(fieldPoint v) ⊗_K E` at `fieldPoint w`); it is `0` for points without generic support. It
depends only on `w` and the subfield `K ⊆ E`. -/
def fibreDeg (w : T.an) : ℕ :=
  if hw : T.HasGenericSupport w.1 then Berk.flatFibreMult K (T.fieldPoint w hw) else 0

variable {T}

theorem fibreDeg_of_hasGenericSupport {w : T.an} (hw : T.HasGenericSupport w.1) :
    T.fibreDeg K w = Berk.flatFibreMult K (T.fieldPoint w hw) := by
  rw [fibreDeg, dif_pos hw]

/-- The multiplicities of points with generic support are positive. -/
theorem one_le_fibreDeg [FiniteDimensional K E] {w : T.an} (hw : T.HasGenericSupport w.1) :
    1 ≤ T.fibreDeg K w := by
  rw [fibreDeg_of_hasGenericSupport hw]
  exact Berk.one_le_flatFibreMult _

end FibreDeg

/-! ### Fibres of finite morphisms -/

namespace FiniteHom

variable {E : Type u} [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  {T : MultiModel k E r} (h : FiniteHom T X)

/-- **`lem:gl-finite-fibres`**: the points over a point with generic support have generic
support. A nonzero `q ∈ S_T` satisfies an integral equation `q P'(q) = -c₀` over `S` with
`c₀ ≠ 0`, and `|c₀|_{h(w)} ≠ 0`. -/
theorem hasGenericSupport_of_anMap {w : T.an} (hw : X.HasGenericSupport (h.anMap w).1) :
    T.HasGenericSupport w.1 := by
  classical
  intro q hq h0
  obtain ⟨P, hPm, hP⟩ := h.isIntegral_algHom q
  obtain ⟨Q, hPQ, hQX⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPm.ne_zero 0
  rw [map_zero, sub_zero] at hPQ hQX
  have hQ0 : Q.coeff 0 ≠ 0 := fun h0 => hQX (Polynomial.X_dvd_iff.2 h0)
  have hQq : Polynomial.eval₂ (h.algHom : X.S →+* T.S) q Q = 0 := by
    rw [hPQ, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hP
    exact (mul_eq_zero.1 hP).resolve_left (pow_ne_zero _ hq)
  rw [← Polynomial.X_mul_divX_add Q, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_C, add_eq_zero_iff_eq_neg] at hQq
  have hc : w.1.val ((h.algHom : X.S →+* T.S) (Q.coeff 0)) ≠ 0 := by
    change w.1.val (h.algHom (Q.coeff 0)) ≠ 0
    rw [← anMap_val]
    exact hw _ hQ0
  have h1 := congrArg w.1.val hQq
  rw [map_mul, h0, zero_mul, Valuation.map_neg] at h1
  exact hc h1.symm

/-- `fieldPoint w` lies over `fieldPoint (h w)`: the absolute value of `w` on `E` restricts to the
absolute value of `h^an(w)` on `K`. -/
theorem comap_fieldPoint (w : T.an) (hw : T.HasGenericSupport w.1)
    (hv : X.HasGenericSupport (h.anMap w).1) :
    Berk.comap (IsScalarTower.toAlgHom k K E) (T.fieldPoint w hw) =
      X.fieldPoint (h.anMap w) hv := by
  refine Berk.ext_val fun x => ?_
  have key := X.eq_fieldVal (h.anMap w) hv ((T.fieldVal w hw).comap (algebraMap K E))
    fun a f g hf hg _ => by
      rw [Valuation.comap_apply, map_div₀, T.fieldVal_div w hw (h.algebraMap_mem_piece hf)
        (h.algebraMap_mem_piece hg), anMap_val_ofPiece, anMap_val_ofPiece]
  rw [Berk.comap_val_apply, fieldPoint_val, fieldPoint_val, ← key]
  rfl

/-- Two points of `𝒯^an` over the same point with the same absolute value on `E` are equal. -/
theorem eq_of_fieldPoint_eq {w w' : T.an} (hww' : h.anMap w = h.anMap w')
    (hw : T.HasGenericSupport w.1) (hw' : T.HasGenericSupport w'.1)
    (he : T.fieldPoint w hw = T.fieldPoint w' hw') : w = w' := by
  refine eq_of_fieldVal_eq hw hw' (congrArg Berk.val he) fun i => ?_
  obtain ⟨i', rfl⟩ := h.coordIndexEquiv.surjective i
  rw [← anMap_val_coordElem, ← anMap_val_coordElem, hww']

/-- **`lem:gl-finite-fibres`, surjectivity**: every point `y` of `(Spec E)^an` over
`fieldPoint v` is `fieldPoint w` for a point `w ∈ 𝒯^an` over `v`. On a chart `j` with
`|z^{(c)}_{j_c}|_v = 1`, `w` is the inverse chart image of the restriction of `y` to the chart
algebra `B_j` of `𝒯`. -/
theorem exists_fieldPoint_eq (v : X.an) (hv : X.HasGenericSupport v.1) (y : Berk k E)
    (hy : Berk.comap (IsScalarTower.toAlgHom k K E) y = X.fieldPoint v hv) :
    ∃ (w : T.an) (hw : T.HasGenericSupport w.1), h.anMap w = v ∧ T.fieldPoint w hw = y := by
  obtain ⟨j, hj, hv1⟩ := X.exists_chartIndex v
  have hvj : ∀ c, v.1.val (X.coordElem ⟨c, j c⟩) ≠ 0 := fun c => by
    rw [hv1 c]; exact one_ne_zero
  have hj' := h.chartIndex_ne_zero hj
  set y' : Berk k (T.chartAlg (h.chartIndex j)) := Berk.comap (T.chartAlg (h.chartIndex j)).val y
  set w := T.chartInv (h.chartIndex j) hj' y'
  have hcomap : Berk.comap (h.chartAlgHom j) y' = X.chartMap hj v.1 hvj := by
    refine Berk.ext_val fun x => ?_
    rw [Berk.comap_val_apply, Berk.comap_val_apply, Subalgebra.coe_val, coe_chartAlgHom,
      ← fieldVal_coe_chartAlg hj v hv hvj x, ← fieldPoint_val, ← hy]
    rfl
  have hwv : h.anMap w = v := by
    rw [h.anMap_chartInv hj y', hcomap, chartInv_chartMap hj v (mem_chartDomain_iff.2 hvj)]
  have hw : T.HasGenericSupport w.1 := h.hasGenericSupport_of_anMap (by rw [hwv]; exact hv)
  refine ⟨w, hw, hwv, Berk.ext_val fun e => ?_⟩
  have hwj : ∀ c, w.1.val (T.coordElem ⟨c, h.chartIndex j c⟩) ≠ 0 :=
    T.chartInv_val_coordElem_ne_zero hj' y'
  have hB : ∀ x : T.chartAlg (h.chartIndex j),
      (T.fieldPoint w hw).val x = y.val x := fun x => by
    rw [fieldPoint_val, fieldVal_coe_chartAlg hj' w hw hwj x]
    have := T.chartMap_chartInv hj' y'
    rw [show (T.chartMap hj' w.1 hwj) = y' from this]
    rfl
  have := T.isFractionRing_chartAlg hj'
  obtain ⟨x₁, x₂, -, rfl⟩ := IsFractionRing.div_surjective (T.chartAlg (h.chartIndex j)) e
  rw [map_div₀, map_div₀]
  exact congrArg₂ (· / ·) (hB x₁) (hB x₂)

/-! #### The fibre -/

/-- The fibre `h⁻¹(v) ⊆ 𝒯^an`, a finite set (`lem:gl-pullback`). -/
def fibre (v : X.an) : Finset T.an :=
  (h.finite_anMap_preimage v).toFinset

theorem mem_fibre {v : X.an} {w : T.an} : w ∈ h.fibre v ↔ h.anMap w = v := by
  rw [fibre, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]

/-- **`lem:gl-finite-fibres`**: the fibre over `⋆` is `{⋆}` (`lem:gl-pullback`). -/
theorem fibre_triv : h.fibre X.triv = {T.triv} := by
  ext w
  rw [mem_fibre, Finset.mem_singleton]
  exact ⟨h.eq_triv_of_anMap_eq_triv, fun hw => hw ▸ h.anMap_triv⟩

/-- **`lem:gl-finite-fibres`**: for `v ∈ 𝒳^val`, the points `w ∈ 𝒯^an` over `v` correspond
bijectively, through `w ↦ fieldPoint w`, to the points of `(Spec E)^an` over `fieldPoint v`, hence
to the local factors of `H(v) ⊗_K E` (`Berk.fibreEquivMaximalSpectrum`). -/
def fibreEquiv (v : X.an) (hv : X.HasGenericSupport v.1) :
    h.anMap ⁻¹' {v} ≃
      Berk.comap (IsScalarTower.toAlgHom k K E) ⁻¹' {X.fieldPoint v hv} where
  toFun w := ⟨T.fieldPoint w.1 (h.hasGenericSupport_of_anMap (by rw [w.2]; exact hv)), by
    rw [Set.mem_preimage, Set.mem_singleton_iff,
      h.comap_fieldPoint w.1 _ (by rw [w.2]; exact hv)]
    congr 1
    exact w.2⟩
  invFun y := ⟨(h.exists_fieldPoint_eq v hv y.1 y.2).choose,
    (h.exists_fieldPoint_eq v hv y.1 y.2).choose_spec.choose_spec.1⟩
  left_inv w := by
    obtain ⟨hw, hwv, hwy⟩ := (h.exists_fieldPoint_eq v hv _
      (Set.mem_singleton_iff.1 (Set.mem_preimage.1 (by
        rw [Set.mem_preimage, Set.mem_singleton_iff,
          h.comap_fieldPoint w.1 (h.hasGenericSupport_of_anMap (by rw [w.2]; exact hv))
            (by rw [w.2]; exact hv)]
        congr 1
        exact w.2)))).choose_spec
    refine Subtype.ext (h.eq_of_fieldPoint_eq (hwv.trans w.2.symm) hw _ hwy)
  right_inv y := by
    obtain ⟨hw, -, hwy⟩ := (h.exists_fieldPoint_eq v hv y.1 y.2).choose_spec
    exact Subtype.ext hwy

theorem coe_fibreEquiv_apply (v : X.an) (hv : X.HasGenericSupport v.1)
    (w : h.anMap ⁻¹' {v}) :
    (h.fibreEquiv v hv w : Berk k E) =
      T.fieldPoint w.1 (h.hasGenericSupport_of_anMap (by rw [w.2]; exact hv)) :=
  rfl

variable [FiniteDimensional K E]

/-- **`lem:gl-finite-fibres`**: for `v ∈ 𝒳^val`, the points `w ∈ 𝒯^an` over `v` correspond
bijectively to the local factors `B_w` of `H(v) ⊗_K E`, i.e. to its maximal ideals. -/
def fibreEquivFactors (v : X.an) (hv : X.HasGenericSupport v.1) :
    h.anMap ⁻¹' {v} ≃ MaximalSpectrum (Berk.H (X.fieldPoint v hv) ⊗[K] E) :=
  (h.fibreEquiv v hv).trans (Berk.fibreEquivMaximalSpectrum (X.fieldPoint v hv))

/-- **`def:gl-finite-fibres`**: `d(w/v) = dim_{H(v)} B_w` for the local factor `B_w` of
`H(v) ⊗_K E` corresponding to `w` (`FiniteHom.fibreEquivFactors`). -/
theorem fibreDeg_eq_finrank (v : X.an) (hv : X.HasGenericSupport v.1) (w : h.anMap ⁻¹' {v}) :
    T.fibreDeg K w.1 = Module.finrank (Berk.H (X.fieldPoint v hv))
      (Localization.AtPrime (h.fibreEquivFactors v hv w).asIdeal) := by
  rw [fibreDeg_of_hasGenericSupport (h.hasGenericSupport_of_anMap (by rw [w.2]; exact hv))]
  exact Berk.flatFibreMult_eq (Set.mem_singleton_iff.1 (h.fibreEquiv v hv w).2)

/-- **`lem:gl-finite-fibres`**: `∑_{h(w) = v} d(w/v) = d = [E : K]` for `v ∈ 𝒳^val`. -/
theorem sum_fibreDeg (v : X.an) (hv : X.HasGenericSupport v.1) :
    ∑ w ∈ h.fibre v, T.fibreDeg K w = Module.finrank K E := by
  rw [← Berk.sum_flatFibreMult_of_free (k := k) (B := K) (A := E) (X.fieldPoint v hv)]
  refine Finset.sum_bij (fun w hw => (h.fibreEquiv v hv ⟨w, (h.mem_fibre).1 hw⟩ : Berk k E))
    (fun w hw => (Set.Finite.mem_toFinset _).2 (h.fibreEquiv v hv ⟨w, (h.mem_fibre).1 hw⟩).2)
    (fun w₁ h₁ w₂ h₂ he => ?_) (fun y hy => ?_) (fun w hw => ?_)
  · have := (h.fibreEquiv v hv).injective (Subtype.ext he)
    exact congrArg Subtype.val this
  · obtain ⟨⟨w, hw⟩, hwy⟩ := (h.fibreEquiv v hv).surjective ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩
    exact ⟨w, (h.mem_fibre).2 hw, congrArg Subtype.val hwy⟩
  · rw [coe_fibreEquiv_apply, fibreDeg_of_hasGenericSupport]

end FiniteHom

end MultiModel

end EnvelopeProperty
