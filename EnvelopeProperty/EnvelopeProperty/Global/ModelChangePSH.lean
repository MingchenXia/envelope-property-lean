/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.MorphismsPSH
import EnvelopeProperty.Global.ModelChange

/-!
# Change of model with the same coordinates: sections and psh functions

This file implements the parts of the blueprint node `lem:gl-model-change` of `global.tex`
(subsection `subsec:gl-model`) concerning sections, Fubini–Study functions, psh functions and the
semiample cone, for the formalization of Fang–Han–Xia, *The envelope property for unibranch
projective varieties* (revision `832e086`, FHX `prop:BJ-package`), in the case of models with the
same coordinates.

## Setting

`𝒳 = (K, S, z)` and `𝒳' = (K, S', z)` with `S ⊆ S' ⊆ S^ν` and the same coordinates are a finite
morphism `h : 𝒳' → 𝒳` with `E = K` (`MultiModel.FiniteHom`; e.g. the normalization
`FiniteHom.ofNormalization`). Assume that the chart algebras `A_j` of `𝒳` are integrally closed.

## Results

* `FiniteHom.isAdmissible_of_self` (the ideal argument, `exists_mem_piece_mul_zCoeff`, applied to
  the finitely many `f z̃^β`, `β ∈ Mon(b)`): every section of `𝒳'` is a section of `𝒳`, so
  `R_a(𝒳') = R_a(𝒳)` (`FiniteHom.sections_eq_of_self`) with equal values
  (`FiniteHom.secAbs_anMap`).
* `FiniteHom.anMap_injective_of_self`: `h^an` is injective (a point of `𝒳'^an` is determined by
  the values `|f|`, `f ∈ S'_d ⊆ R_d(𝒳)`), so `FiniteHom.anHomeomorphOfSelf : 𝒳'^an ≃ₜ 𝒳^an`.
* `FiniteHom.isFS_comp_iff_of_self`: `𝓗(𝒳', a) = 𝓗(𝒳, a) ∘ h^an` (`FiniteHom.pushFSData`).
* `FiniteHom.isPSH_comp_iff_of_self`: `PSH(𝒳', θ) = PSH(𝒳, θ) ∘ h^an`;
  `FiniteHom.hasEnvelopeProperty_iff_of_self`: `EP_{𝒳'}(θ) ⟺ EP_𝒳(θ)`;
  `FiniteHom.semiampleCone_eq_of_self`: `C(𝒳') = C(𝒳)`, hence `N(𝒳') = N(𝒳)`.
* For the normalization (`MultiModel.normalization`), with integrally closed chart algebras:
  `MultiModel.isPSH_normalization_iff`, `MultiModel.hasEnvelopeProperty_normalization_iff`
  (used in the proof of `cor:sg-smooth-model`(a)).

The general case of `lem:gl-model-change` (different, mutually integral coordinates, `S' ⊆ S^ν`)
is in `EnvelopeProperty.Global.ModelChange` (points) and
`EnvelopeProperty.Global.ModelChangeSections` (sections, psh functions, cones); this file treats
finite morphisms `𝒳' → 𝒳` with the same coordinates up to reindexing.
-/

open scoped NNReal ENNReal Topology

open Topology MvPolynomial

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {X X' : MultiModel k K r}

namespace FiniteHom

variable (h : FiniteHom X' X)

theorem coeffMap_self (p : MvPolynomial (Fin r) K) : coeffMap k K p = p := by
  rw [coeffMap_apply, Algebra.algebraMap_self, map_id]

include h in
/-- `S'` is integral over `S`. -/
theorem isIntegral_S_of_self {p : MvPolynomial (Fin r) K} (hp : p ∈ X'.S) : IsIntegral X.S p := by
  have := h.isIntegral p hp
  rwa [X.imageS_self] at this

include h in
/-- **The ideal argument for sections** (`lem:gl-model-change`): if the chart algebras of `𝒳` are
integrally closed, every admissible degree of `f` for `𝒳'` becomes admissible for `𝒳` after
adding some `B`. -/
theorem isAdmissible_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {a : Fin r → ℤ} {b : Fin r →₀ ℕ} {f : K} (hf : X'.IsAdmissible a b f) :
    ∃ B : Fin r →₀ ℕ, X.IsAdmissible a (b + B) f := by
  classical
  set D := addDeg a b
  -- For each `β ∈ Mon(b)`, `f z̃^β ∈ S'_D`, so `f z̃^β z̃^δ ∈ S_{D + b_β}` for `δ ∈ Mon(b_β)`.
  have hβ : ∀ β ∈ X.monSet b, f * X.zCoeff β ∈ X'.piece D := by
    intro β hβ
    have := hf.mul_zCoeff_mem (h.monEquiv_mem_monSet hβ)
    rwa [h.zCoeff_monEquiv, Algebra.algebraMap_self, RingHom.id_apply] at this
  have hex : ∀ β : X.CoordIndex →₀ ℕ, ∃ bβ : Fin r →₀ ℕ, β ∈ X.monSet b →
      ∀ δ ∈ X.monSet bβ, f * X.zCoeff β * X.zCoeff δ ∈ X.piece (D + bβ) := by
    intro β
    by_cases hβm : β ∈ X.monSet b
    · obtain ⟨bβ, hbβ⟩ := exists_mem_piece_mul_zCoeff hX (h.isIntegral_S_of_self (hβ β hβm))
      exact ⟨bβ, fun _ => hbβ⟩
    · exact ⟨0, fun h' => absurd h' hβm⟩
  choose bβ hbβ using hex
  set B := ∑ β ∈ X.monSet b, bβ β
  refine ⟨B, ⟨fun c => ?_, fun γ hγ => ?_⟩⟩
  · have := hf.nonneg c
    simp only [Finsupp.add_apply, Nat.cast_add]
    omega
  · rw [addDeg_add hf.1]
    obtain ⟨β, δ, rfl, h₁, h₂⟩ := exists_add_of_monDeg_eq_add ((X.mem_monSet).1 hγ)
    have hβm : β ∈ X.monSet b := (X.mem_monSet).2 h₁
    have hle : bβ β ≤ B := Finset.single_le_sum (f := bβ) (fun _ _ => zero_le) hβm
    obtain ⟨δ₁, δ₂, rfl, h₃, h₄⟩ := exists_add_of_monDeg_eq_add (b := bβ β) (e := B - bβ β)
      (by rw [h₂, add_tsub_cancel_of_le hle])
    have := mul_mem_piece (hbβ β hβm δ₁ ((X.mem_monSet).2 h₃)) (X.zCoeff_mem_piece δ₂)
    rw [h₄, add_assoc, add_tsub_cancel_of_le hle, mul_assoc, ← zCoeff_add, mul_assoc,
      ← zCoeff_add] at this
    exact this

include h in
/-- **`R_a(𝒳') = R_a(𝒳)`** (`lem:gl-model-change`), for integrally closed chart algebras of `𝒳`. -/
theorem sections_eq_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    (a : Fin r → ℤ) : X'.sections a = X.sections a := by
  ext f
  refine ⟨fun ⟨b, hb⟩ => ?_, fun hf => ?_⟩
  · obtain ⟨B, hB⟩ := h.isAdmissible_of_self hX hb
    exact hB.mem_sections
  · have := h.mem_sections hf
    rwa [Algebra.algebraMap_self, RingHom.id_apply] at this

/-- Values of sections of `𝒳'`: `|f|_w = |f|_{h^an(w)}`. -/
theorem secAbs_anMap_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    (w : X'.an) {a : Fin r → ℤ} {f : K} (hf : f ∈ X'.sections a) :
    X'.secAbs w.1 a f = X.secAbs (h.anMap w).1 a f := by
  rw [h.sections_eq_of_self hX] at hf
  have := h.secAbs_anMap w hf
  rwa [Algebra.algebraMap_self, RingHom.id_apply] at this

theorem logSecAbs_anMap_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    (w : X'.an) {a : Fin r → ℤ} {f : K} (hf : f ∈ X'.sections a) :
    X'.logSecAbs w.1 a f = X.logSecAbs (h.anMap w).1 a f := by
  rw [logSecAbs, logSecAbs, h.secAbs_anMap_of_self hX w hf]

/-- **`h^an` is injective** for integrally closed chart algebras of `𝒳`: `|f T^d|_w = |f|_{h^an(w)}`
for `f ∈ S'_d`. -/
theorem anMap_injective_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j)) :
    Function.Injective h.anMap := by
  intro w₁ w₂ hw
  refine Subtype.ext (ext_of_ofPiece w₁.2.1 w₂.2.1 fun d f hf => ?_)
  have hsec := mem_sections_of_mem_piece (a := fun c => (d c : ℤ)) (fun _ => rfl) hf
  rw [← secAbs_of_mem_piece w₁.2.2 (fun _ => rfl) hf, ← secAbs_of_mem_piece w₂.2.2 (fun _ => rfl) hf,
    h.secAbs_anMap_of_self hX w₁ hsec, h.secAbs_anMap_of_self hX w₂ hsec, hw]

/-- **`𝒳'^an ≃ₜ 𝒳^an`** (`lem:gl-model-change`, same coordinates). -/
def anHomeomorphOfSelf
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j)) :
    X'.an ≃ₜ X.an :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective h.anMap ⟨h.anMap_injective_of_self hX, h.anMap_surjective⟩)
    h.continuous_anMap

@[simp]
theorem anHomeomorphOfSelf_apply
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    (w : X'.an) : h.anHomeomorphOfSelf hX w = h.anMap w :=
  rfl

/-- The Fubini–Study data of `𝒳'` as data of `𝒳` (the same terms). -/
def pushFSData
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {a : Fin r → ℚ} (D : X'.FSData a) : X.FSData a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms
  mem_sections t ht := by
    rw [← h.sections_eq_of_self hX]
    exact D.mem_sections t ht

theorem eval_pushFSData
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {a : Fin r → ℚ} (D : X'.FSData a) (w : X'.an) :
    (h.pushFSData hX D).eval (h.anMap w) = D.eval w := by
  rw [FSData.eval_def, FSData.eval_def]
  congr 1
  refine Finset.sup_congr rfl fun t ht => ?_
  rw [termVal_def, termVal_def, h.logSecAbs_anMap_of_self hX w (D.mem_sections t ht)]
  rfl

/-- **`𝓗(𝒳', a) = 𝓗(𝒳, a) ∘ h^an`** (`lem:gl-model-change`). -/
theorem isFS_comp_iff_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {a : Fin r → ℚ} {φ : X.an → EReal} : X'.IsFS a (φ ∘ h.anMap) ↔ X.IsFS a φ := by
  refine ⟨fun hφ => ?_, fun hφ => ?_⟩
  · obtain ⟨D, hD0, hD⟩ := hφ
    refine ⟨h.pushFSData hX D, hD0, fun v => ?_⟩
    obtain ⟨w, rfl⟩ := h.anMap_surjective v
    rw [eval_pushFSData, ← hD w]
    rfl
  · have := h.isFS_comp hφ
    exact this

/-- **`PSH(𝒳', θ) = PSH(𝒳, θ) ∘ h^an`** (`lem:gl-model-change`). -/
theorem isPSH_comp_iff_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {θ : Fin r → ℝ} {u : X.an → EReal} : X'.IsPSH θ (u ∘ h.anMap) ↔ X.IsPSH θ u :=
  FSSystemC.isPSH_comp_iff (F := X.fsSystem) (G := X'.fsSystem) (h.anHomeomorphOfSelf hX)
    h.anMap_triv fun _ _ => (h.isFS_comp_iff_of_self hX).symm

include h in
/-- **`EP_{𝒳'}(θ) ⟺ EP_𝒳(θ)`** (`lem:gl-model-change`). -/
theorem hasEnvelopeProperty_iff_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {θ : Fin r → ℝ} : X'.HasEnvelopeProperty θ ↔ X.HasEnvelopeProperty θ :=
  FSSystemC.hasEnvelopeProperty_iff (F := X.fsSystem) (G := X'.fsSystem)
    (h.anHomeomorphOfSelf hX) h.anMap_triv fun _ _ => (h.isFS_comp_iff_of_self hX).symm

include h in
/-- **`C(𝒳') = C(𝒳)`** (`lem:gl-model-change`): base point free families correspond. -/
theorem semiampleCone_eq_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j)) :
    X'.semiampleCone = X.semiampleCone := by
  have hbpf : ∀ (d : Fin r → ℤ) (s : Finset K), X'.IsBasePointFree d s ↔ X.IsBasePointFree d s := by
    intro d s
    refine ⟨fun hs => ⟨fun f hf => (h.sections_eq_of_self hX d) ▸ hs.1 f hf, fun v => ?_⟩,
      fun hs => ⟨fun f hf => (h.sections_eq_of_self hX d).symm ▸ hs.1 f hf, fun w => ?_⟩⟩
    · obtain ⟨w, rfl⟩ := h.anMap_surjective v
      obtain ⟨f, hf, hne⟩ := hs.2 w
      exact ⟨f, hf, by rwa [← h.secAbs_anMap_of_self hX w (hs.1 f hf)]⟩
    · obtain ⟨f, hf, hne⟩ := hs.2 (h.anMap w)
      refine ⟨f, hf, ?_⟩
      rwa [h.secAbs_anMap_of_self hX w ((h.sections_eq_of_self hX d).symm ▸ hs.1 f hf)]
  ext a
  simp only [mem_semiampleCone, hbpf]

include h in
theorem nefCone_eq_of_self
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j)) :
    X'.nefCone = X.nefCone := by
  rw [nefCone, nefCone, h.semiampleCone_eq_of_self hX]

end FiniteHom

/-! ### The normalization -/

variable [Infinite k] [PerfectField k]

/-- **Psh functions on the normalization** (`lem:gl-model-change` for `𝒳^ν → 𝒳`): if the chart
algebras of `𝒳` are integrally closed, `PSH(𝒳^ν, θ) = PSH(𝒳, θ) ∘ ν^an`. -/
theorem isPSH_normalization_iff
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {θ : Fin r → ℝ} {u : X.an → EReal} :
    X.normalization.IsPSH θ (u ∘ (FiniteHom.ofNormalization X).anMap) ↔ X.IsPSH θ u :=
  (FiniteHom.ofNormalization X).isPSH_comp_iff_of_self hX

/-- **`EP_{𝒳^ν}(θ) ⟺ EP_𝒳(θ)`** if the chart algebras of `𝒳` are integrally closed
(`lem:gl-model-change`; `cor:sg-smooth-model`(a)). -/
theorem hasEnvelopeProperty_normalization_iff
    (hX : ∀ j : X.ChartIndex, (∀ c, X.coord c (j c) ≠ 0) → IsIntegrallyClosed (X.chartAlg j))
    {θ : Fin r → ℝ} : X.normalization.HasEnvelopeProperty θ ↔ X.HasEnvelopeProperty θ :=
  (FiniteHom.ofNormalization X).hasEnvelopeProperty_iff_of_self hX

end MultiModel

end EnvelopeProperty
