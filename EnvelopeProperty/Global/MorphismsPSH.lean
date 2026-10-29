/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ModelPSH
import EnvelopeProperty.Global.Morphisms

/-!
# Pullbacks of Fubini–Study and psh functions along morphisms of models

This file implements the parts of the blueprint node `lem:gl-pullback` of `global.tex`
(subsection `subsec:gl-model`) that concern sections, Fubini–Study functions and psh functions, for
the formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX `prop:BJ-package`(4); BJ22 Theorem 4.7). The point-level part (`h^an`
continuous, surjective, with finite fibres, `h^an(⋆) = ⋆`) is in
`EnvelopeProperty.Global.Morphisms`.

## Transport of psh functions between Fubini–Study systems

For Fubini–Study systems `F` on `A` and `G` on `B` (`EnvelopeProperty.FSSystemC`) and a continuous
map `g : B → A` with `g(⋆) = ⋆` pulling `𝓗_F(a)` back into `𝓗_G(a)`,
`FSSystemC.IsPSH.comp_of_isFS`: `u ∘ g ∈ PSH_G(θ)` for `u ∈ PSH_F(θ)` (pull back the decreasing
nets; `u ∘ g` is usc and finite at `⋆`). For a homeomorphism `e : B ≃ₜ A` identifying the
Fubini–Study families, `FSSystemC.isPSH_comp_iff` and `FSSystemC.hasEnvelopeProperty_iff`: the
psh classes and the envelope property correspond (`uscReg (f ∘ e) = uscReg f ∘ e`,
`EnvelopeProperty.uscReg_comp_homeomorph`). More generally, for systems of possibly different
ranks and a homeomorphism identifying `PSH_G(θ_G)` with `PSH_F(θ_F)`,
`FSSystemC.hasEnvelopeProperty_iff_of_isPSH_comp_iff`: `EP_G(θ_G) ↔ EP_F(θ_F)` (used for the
Segre–Veronese model, `EnvelopeProperty.Global.VeronesePSH`).

## Finite morphisms (`lem:gl-pullback`)

For a finite morphism `h : 𝒯 → 𝒳` (`MultiModel.FiniteHom`):

* `FiniteHom.isAdmissible`, `FiniteHom.mem_sections`: `R_a(𝒳) ⊆ R_a(𝒯)` (`f ↦ f` in `K ⊆ E`), with
  the same values `|f|_w = |f|_{h^an(w)}` (`FiniteHom.secAbs_anMap`, `FiniteHom.logSecAbs_anMap`);
* `FiniteHom.pullFSData`, `FiniteHom.isFS_comp`, `FiniteHom.isFinFS_comp`:
  `φ ∘ h^an ∈ 𝓗(𝒯, a)` for `φ ∈ 𝓗(𝒳, a)` (and for `𝓗_fin`);
* `FiniteHom.isPSH_comp`: `u ∘ h^an ∈ PSH(𝒯, θ)` for `u ∈ PSH(𝒳, θ)`.

## Scalar restriction (`lem:gl-pullback`)

The same for a scalar restriction `r : 𝒳^an → 𝒳₀^an` (`MultiModel.ScalarRestriction`):
`ScalarRestriction.mem_sections`, `ScalarRestriction.secAbs_anMap`,
`ScalarRestriction.isFS_comp`, `ScalarRestriction.isFinFS_comp`, `ScalarRestriction.isPSH_comp`.
-/

open scoped NNReal ENNReal Topology

open Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

/-! ### The usc regularization and homeomorphisms -/

/-- The usc regularization commutes with homeomorphisms: `(f ∘ e)^⋆ = f^⋆ ∘ e`. -/
theorem uscReg_comp_homeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {γ : Type*} [CompleteLinearOrder γ] (e : B ≃ₜ A) (f : A → γ) :
    uscReg (f ∘ e) = uscReg f ∘ e := by
  funext x
  change limsup (f ∘ e) (𝓝 x) = limsup f (𝓝 (e x))
  rw [Filter.limsup_comp, e.map_nhds_eq]

/-! ### Transport of psh functions -/

namespace FSSystemC

variable {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] {r : ℕ}
  {F : FSSystemC A r} {G : FSSystemC B r}

/-- **Pullback of psh functions** along a continuous map `g : B → A` with `g(⋆) = ⋆` that pulls
Fubini–Study functions back to Fubini–Study functions of the same class: pull back the decreasing
nets. -/
theorem IsPSH.comp_of_isFS {g : B → A} (hg : Continuous g) (htriv : g G.triv = F.triv)
    (hFS : ∀ a φ, F.IsFS a φ → G.IsFS a (φ ∘ g)) {θ : Fin r → ℝ} {u : A → EReal}
    (hu : F.IsPSH θ u) : G.IsPSH θ (u ∘ g) := by
  have hne := hu.apply_triv_ne_bot
  obtain ⟨-, husc, ι, hpre, hdir, hnon, a, f, hf, ha, hanti, hinf⟩ := hu
  refine ⟨⟨G.triv, by rw [Function.comp_apply, htriv]; exact hne⟩, husc.comp hg, ι, hpre, hdir,
    hnon, a, fun i => f i ∘ g, fun i => hFS _ _ (hf i), ha, fun x => hanti (g x),
    fun x => hinf (g x)⟩

/-- **Psh functions under a homeomorphism identifying the Fubini–Study families.** -/
theorem isPSH_comp_iff (e : B ≃ₜ A) (htriv : e G.triv = F.triv)
    (hFS : ∀ a φ, F.IsFS a φ ↔ G.IsFS a (φ ∘ e)) {θ : Fin r → ℝ} {u : A → EReal} :
    G.IsPSH θ (u ∘ e) ↔ F.IsPSH θ u := by
  refine ⟨fun h => ?_, fun h => h.comp_of_isFS e.continuous htriv fun a φ hφ => (hFS a φ).1 hφ⟩
  have htriv' : e.symm F.triv = G.triv := by rw [← htriv, Homeomorph.symm_apply_apply]
  have hFS' : ∀ a ψ, G.IsFS a ψ → F.IsFS a (ψ ∘ e.symm) := fun a ψ hψ => by
    refine (hFS a _).2 ?_
    have : (ψ ∘ e.symm) ∘ e = ψ := funext fun x => by simp
    rw [this]; exact hψ
  have := h.comp_of_isFS e.symm.continuous htriv' hFS'
  have e1 : (u ∘ e) ∘ e.symm = u := funext fun x => by simp
  rwa [e1] at this

/-- **The envelope property under a homeomorphism identifying the Fubini–Study families.** -/
theorem hasEnvelopeProperty_of_homeomorph (e : B ≃ₜ A) (htriv : e G.triv = F.triv)
    (hFS : ∀ a φ, F.IsFS a φ ↔ G.IsFS a (φ ∘ e)) {θ : Fin r → ℝ}
    (hG : G.HasEnvelopeProperty θ) : F.HasEnvelopeProperty θ := by
  intro S hS hpsh hbdd
  set S' : Set (B → EReal) := (fun u => u ∘ e) '' S
  have hS' : S'.Nonempty := hS.image _
  have hpsh' : ∀ u' ∈ S', G.IsPSH θ u' := by
    rintro _ ⟨u, hu, rfl⟩
    exact (isPSH_comp_iff e htriv hFS).2 (hpsh u hu)
  have hbdd' : ∃ C : ℝ, ∀ u' ∈ S', ∀ x, u' x ≤ C := by
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, by rintro _ ⟨u, hu, rfl⟩ x; exact hC u hu (e x)⟩
  have h := hG S' hS' hpsh' hbdd'
  have hsup : (fun x => ⨆ u' ∈ S', u' x) = (fun y => ⨆ u ∈ S, u y) ∘ e := by
    funext x
    change (⨆ u' ∈ (fun u => u ∘ e) '' S, u' x) = ⨆ u ∈ S, u (e x)
    rw [iSup_image]
    rfl
  rw [hsup, uscReg_comp_homeomorph] at h
  exact (isPSH_comp_iff e htriv hFS).1 h

/-- The envelope property is invariant under a homeomorphism identifying the Fubini–Study
families. -/
theorem hasEnvelopeProperty_iff (e : B ≃ₜ A) (htriv : e G.triv = F.triv)
    (hFS : ∀ a φ, F.IsFS a φ ↔ G.IsFS a (φ ∘ e)) {θ : Fin r → ℝ} :
    G.HasEnvelopeProperty θ ↔ F.HasEnvelopeProperty θ := by
  refine ⟨hasEnvelopeProperty_of_homeomorph e htriv hFS, fun h => ?_⟩
  have htriv' : e.symm F.triv = G.triv := by rw [← htriv, Homeomorph.symm_apply_apply]
  have hFS' : ∀ a ψ, G.IsFS a ψ ↔ F.IsFS a (ψ ∘ e.symm) := fun a ψ => by
    rw [hFS a]
    have : (ψ ∘ e.symm) ∘ e = ψ := funext fun x => by simp
    rw [this]
  exact hasEnvelopeProperty_of_homeomorph e.symm htriv' hFS' h

/-! ### Transport along homeomorphisms identifying psh classes

Systems of possibly different ranks: used for the Segre–Veronese model, where
`PSH(𝒳_(a), t) = PSH(𝒳, t a)`. -/

section Rank

variable {s s' : ℕ} {F' : FSSystemC A s} {G' : FSSystemC B s'}

/-- **The envelope property under a homeomorphism identifying the psh classes**: if
`e : B ≃ₜ A` satisfies `u ∘ e ∈ PSH_G(θ_G) ↔ u ∈ PSH_F(θ_F)` for all `u`, then
`EP_G(θ_G) → EP_F(θ_F)`. -/
theorem hasEnvelopeProperty_of_isPSH_comp_iff (e : B ≃ₜ A) {θF : Fin s → ℝ} {θG : Fin s' → ℝ}
    (he : ∀ u : A → EReal, G'.IsPSH θG (u ∘ e) ↔ F'.IsPSH θF u)
    (hG : G'.HasEnvelopeProperty θG) : F'.HasEnvelopeProperty θF := by
  intro S hS hpsh hbdd
  set S' : Set (B → EReal) := (fun u => u ∘ e) '' S
  have hS' : S'.Nonempty := hS.image _
  have hpsh' : ∀ u' ∈ S', G'.IsPSH θG u' := by
    rintro _ ⟨u, hu, rfl⟩
    exact (he u).2 (hpsh u hu)
  have hbdd' : ∃ C : ℝ, ∀ u' ∈ S', ∀ x, u' x ≤ C := by
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, by rintro _ ⟨u, hu, rfl⟩ x; exact hC u hu (e x)⟩
  have h := hG S' hS' hpsh' hbdd'
  have hsup : (fun x => ⨆ u' ∈ S', u' x) = (fun y => ⨆ u ∈ S, u y) ∘ e := by
    funext x
    change (⨆ u' ∈ (fun u => u ∘ e) '' S, u' x) = ⨆ u ∈ S, u (e x)
    rw [iSup_image]
    rfl
  rw [hsup, uscReg_comp_homeomorph] at h
  exact (he _).1 h

/-- **The envelope property is invariant under a homeomorphism identifying the psh classes**
(systems of possibly different ranks). -/
theorem hasEnvelopeProperty_iff_of_isPSH_comp_iff (e : B ≃ₜ A) {θF : Fin s → ℝ}
    {θG : Fin s' → ℝ} (he : ∀ u : A → EReal, G'.IsPSH θG (u ∘ e) ↔ F'.IsPSH θF u) :
    G'.HasEnvelopeProperty θG ↔ F'.HasEnvelopeProperty θF := by
  refine ⟨hasEnvelopeProperty_of_isPSH_comp_iff e he, fun h => ?_⟩
  refine hasEnvelopeProperty_of_isPSH_comp_iff e.symm (fun w => ?_) h
  have hw : (w ∘ e.symm) ∘ e = w := funext fun x => by simp
  rw [← he, hw]

end Rank

end FSSystemC

namespace MultiModel

/-! ### Finite morphisms -/

section FiniteHom

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  {E : Type u} [Field E] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  {T : MultiModel k E r} {X : MultiModel k K r}

namespace FiniteHom

variable (h : FiniteHom T X)

include h in
/-- Admissible degrees of `𝒳` are admissible for `𝒯`. -/
theorem isAdmissible {a : Fin r → ℤ} {b : Fin r →₀ ℕ} {f : K} (hf : X.IsAdmissible a b f) :
    T.IsAdmissible a b (algebraMap K E f) :=
  ⟨hf.1, h.mem_piece_mul_zCoeff hf.2⟩

include h in
/-- **`R_a(𝒳) ⊆ R_a(𝒯)`** (`lem:gl-pullback`). -/
theorem mem_sections {a : Fin r → ℤ} {f : K} (hf : f ∈ X.sections a) :
    algebraMap K E f ∈ T.sections a := by
  obtain ⟨b, hb⟩ := hf
  exact (h.isAdmissible hb).mem_sections

/-- **Values of sections** (`lem:gl-pullback`): `|f|_w = |f|_{h^an(w)}` for `f ∈ R_a(𝒳)`. -/
theorem secAbs_anMap (w : T.an) {a : Fin r → ℤ} {f : K} (hf : f ∈ X.sections a) :
    T.secAbs w.1 a (algebraMap K E f) = X.secAbs (h.anMap w).1 a f := by
  obtain ⟨b, hb⟩ := hf
  rw [secAbs_eq w.2.2 (h.isAdmissible hb), secAbs_eq (h.anMap w).2.2 hb, secAbsAt, secAbsAt,
    h.sup_monSet_homNorm_anMap hb.2 w]

theorem logSecAbs_anMap (w : T.an) {a : Fin r → ℤ} {f : K} (hf : f ∈ X.sections a) :
    T.logSecAbs w.1 a (algebraMap K E f) = X.logSecAbs (h.anMap w).1 a f := by
  rw [logSecAbs, logSecAbs, h.secAbs_anMap w hf]

open Classical in
/-- The pullback of Fubini–Study data: the same `m`, degree and constants, the sections viewed in
`E ⊇ K`. -/
def pullFSData {a : Fin r → ℚ} (D : X.FSData a) : T.FSData a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun t => (algebraMap K E t.1, t.2)
  mem_sections t ht := by
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
    exact h.mem_sections (D.mem_sections t' ht')

theorem eval_pullFSData {a : Fin r → ℚ} (D : X.FSData a) (w : T.an) :
    (h.pullFSData D).eval w = D.eval (h.anMap w) := by
  classical
  rw [FSData.eval_def, FSData.eval_def]
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) * (D.terms.image fun t => (algebraMap K E t.1, t.2)).sup
    (fun t => T.termVal D.deg t w) = _
  rw [Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun t ht => ?_
  rw [Function.comp_apply, termVal_def, termVal_def, h.logSecAbs_anMap w (D.mem_sections t ht)]

/-- **`φ ∘ h^an ∈ 𝓗(𝒯, a)` for `φ ∈ 𝓗(𝒳, a)`** (`lem:gl-pullback`). -/
theorem isFS_comp {a : Fin r → ℚ} {φ : X.an → EReal} (hφ : X.IsFS a φ) :
    T.IsFS a (φ ∘ h.anMap) := by
  classical
  obtain ⟨D, ⟨t, ht, ht0⟩, hD⟩ := hφ
  refine ⟨h.pullFSData D, ⟨(algebraMap K E t.1, t.2), Finset.mem_image.2 ⟨t, ht, rfl⟩,
    (map_ne_zero _).2 ht0⟩, fun w => ?_⟩
  rw [Function.comp_apply, hD, eval_pullFSData]

/-- `φ ∘ h^an ∈ 𝓗_fin(𝒯, a)` for `φ ∈ 𝓗_fin(𝒳, a)`. -/
theorem isFinFS_comp {a : Fin r → ℚ} {φ : X.an → EReal} (hφ : X.IsFinFS a φ) :
    T.IsFinFS a (φ ∘ h.anMap) := by
  classical
  obtain ⟨D, hrat, hbpf, hD⟩ := hφ
  refine ⟨h.pullFSData D, fun t ht => ?_, fun w => ?_, fun w => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
    exact hrat t' ht'
  · obtain ⟨t, ht, hne⟩ := hbpf (h.anMap w)
    refine ⟨(algebraMap K E t.1, t.2), Finset.mem_image.2 ⟨t, ht, rfl⟩, ?_⟩
    change T.secAbs w.1 D.deg (algebraMap K E t.1) ≠ 0
    rw [h.secAbs_anMap w (D.mem_sections t ht)]
    exact hne
  · rw [Function.comp_apply, hD, eval_pullFSData]

/-- **`u ∘ h^an ∈ PSH(𝒯, θ)` for `u ∈ PSH(𝒳, θ)`** (`lem:gl-pullback`). -/
theorem isPSH_comp {θ : Fin r → ℝ} {u : X.an → EReal} (hu : X.IsPSH θ u) :
    T.IsPSH θ (u ∘ h.anMap) :=
  FSSystemC.IsPSH.comp_of_isFS h.continuous_anMap h.anMap_triv
    (fun _ _ hφ => h.isFS_comp hφ) hu

end FiniteHom

end FiniteHom

/-! ### Scalar restriction -/

section ScalarRestriction

variable {k₀ : Type u} [Field k₀] {K₀ : Type u} [Field K₀] [Algebra k₀ K₀]
  {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  [Algebra k₀ k] [Algebra K₀ K] [Algebra k₀ K] [IsScalarTower k₀ k K] [IsScalarTower k₀ K₀ K]
  {X₀ : MultiModel k₀ K₀ r} {X : MultiModel k K r}

namespace ScalarRestriction

variable (h : ScalarRestriction X₀ X)

include h in
theorem isAdmissible {a : Fin r → ℤ} {b : Fin r →₀ ℕ} {f : K₀} (hf : X₀.IsAdmissible a b f) :
    X.IsAdmissible a b (algebraMap K₀ K f) :=
  ⟨hf.1, h.mem_piece_mul_zCoeff hf.2⟩

include h in
/-- **`R_a(𝒳₀) ⊆ R_a(𝒳)`** (`lem:gl-pullback`, scalar restriction). -/
theorem mem_sections {a : Fin r → ℤ} {f : K₀} (hf : f ∈ X₀.sections a) :
    algebraMap K₀ K f ∈ X.sections a := by
  obtain ⟨b, hb⟩ := hf
  exact (h.isAdmissible hb).mem_sections

/-- **Values of sections** (scalar restriction): `|f|_v = |f|_{r(v)}`. -/
theorem secAbs_anMap (v : X.an) {a : Fin r → ℤ} {f : K₀} (hf : f ∈ X₀.sections a) :
    X.secAbs v.1 a (algebraMap K₀ K f) = X₀.secAbs (h.anMap v).1 a f := by
  obtain ⟨b, hb⟩ := hf
  rw [secAbs_eq v.2.2 (h.isAdmissible hb), secAbs_eq (h.anMap v).2.2 hb, secAbsAt, secAbsAt,
    h.sup_monSet_homNorm_anMap hb.2 v]

theorem logSecAbs_anMap (v : X.an) {a : Fin r → ℤ} {f : K₀} (hf : f ∈ X₀.sections a) :
    X.logSecAbs v.1 a (algebraMap K₀ K f) = X₀.logSecAbs (h.anMap v).1 a f := by
  rw [logSecAbs, logSecAbs, h.secAbs_anMap v hf]

open Classical in
/-- The pullback of Fubini–Study data along a scalar restriction. -/
def pullFSData {a : Fin r → ℚ} (D : X₀.FSData a) : X.FSData a where
  m := D.m
  m_pos := D.m_pos
  deg := D.deg
  deg_eq := D.deg_eq
  terms := D.terms.image fun t => (algebraMap K₀ K t.1, t.2)
  mem_sections t ht := by
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
    exact h.mem_sections (D.mem_sections t' ht')

theorem eval_pullFSData {a : Fin r → ℚ} (D : X₀.FSData a) (v : X.an) :
    (h.pullFSData D).eval v = D.eval (h.anMap v) := by
  classical
  rw [FSData.eval_def, FSData.eval_def]
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) * (D.terms.image fun t => (algebraMap K₀ K t.1, t.2)).sup
    (fun t => X.termVal D.deg t v) = _
  rw [Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun t ht => ?_
  rw [Function.comp_apply, termVal_def, termVal_def, h.logSecAbs_anMap v (D.mem_sections t ht)]

/-- **`φ ∘ r ∈ 𝓗(𝒳, a)` for `φ ∈ 𝓗(𝒳₀, a)`** (`lem:gl-pullback`, scalar restriction). -/
theorem isFS_comp {a : Fin r → ℚ} {φ : X₀.an → EReal} (hφ : X₀.IsFS a φ) :
    X.IsFS a (φ ∘ h.anMap) := by
  classical
  obtain ⟨D, ⟨t, ht, ht0⟩, hD⟩ := hφ
  refine ⟨h.pullFSData D, ⟨(algebraMap K₀ K t.1, t.2), Finset.mem_image.2 ⟨t, ht, rfl⟩,
    (map_ne_zero _).2 ht0⟩, fun v => ?_⟩
  rw [Function.comp_apply, hD, eval_pullFSData]

theorem isFinFS_comp {a : Fin r → ℚ} {φ : X₀.an → EReal} (hφ : X₀.IsFinFS a φ) :
    X.IsFinFS a (φ ∘ h.anMap) := by
  classical
  obtain ⟨D, hrat, hbpf, hD⟩ := hφ
  refine ⟨h.pullFSData D, fun t ht => ?_, fun v => ?_, fun v => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
    exact hrat t' ht'
  · obtain ⟨t, ht, hne⟩ := hbpf (h.anMap v)
    refine ⟨(algebraMap K₀ K t.1, t.2), Finset.mem_image.2 ⟨t, ht, rfl⟩, ?_⟩
    change X.secAbs v.1 D.deg (algebraMap K₀ K t.1) ≠ 0
    rw [h.secAbs_anMap v (D.mem_sections t ht)]
    exact hne
  · rw [Function.comp_apply, hD, eval_pullFSData]

/-- **`u ∘ r ∈ PSH(𝒳, θ)` for `u ∈ PSH(𝒳₀, θ)`** (`lem:gl-pullback`, scalar restriction). -/
theorem isPSH_comp {θ : Fin r → ℝ} {u : X₀.an → EReal} (hu : X₀.IsPSH θ u) :
    X.IsPSH θ (u ∘ h.anMap) :=
  FSSystemC.IsPSH.comp_of_isFS h.continuous_anMap h.anMap_triv
    (fun _ _ hφ => h.isFS_comp hφ) hu

end ScalarRestriction

end ScalarRestriction

end MultiModel

end EnvelopeProperty
