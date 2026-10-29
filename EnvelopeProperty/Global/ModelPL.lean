/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ModelPSH
import EnvelopeProperty.Projective.FSSystemPL

/-!
# PL functions on a model

Let `𝒳 = (K, S, z)` be an integral multiprojective model of rank `r` (`EnvelopeProperty.MultiModel`,
`def:gl-model`). This file implements the blueprint node `lem:gl-pl` of the global chapter
`global.tex` (subsection `subsec:gl-comparison`) of the formalization of Fang–Han–Xia, *The
envelope property for unibranch projective varieties* (FHX), following
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22,
Lemma 2.3, Theorem 2.2).

## Main definitions

* `FSSystemC.toFSSystemNonneg F`: the restriction of a Fubini–Study system with semiample cone `C`
  (`def:gl-fs-system`) to the classes `a ∈ ℚ^r_{≥0} ⊆ C`, a Fubini–Study system in the sense of
  `def:pg-fs-system` (`EnvelopeProperty.FSSystem`); its finite Fubini–Study functions are those of
  `F` with nonnegative classes.
* `MultiModel.plSystem X`, `MultiModel.IsPL X f` (`lem:gl-pl`): `PL(𝒳)` is the set of differences
  of functions in `⋃_{a ∈ ℚ^r_{≥0}} 𝓗_fin(𝒳, a)` (`MultiModel.isPL_iff`), i.e. the PL functions of
  `X.plSystem = X.fsSystem.toFSSystemNonneg`. All results of
  `EnvelopeProperty.Projective.FSSystemPL` apply to it.

## Main results (`lem:gl-pl`)

* `MultiModel.exists_isFinFS_ne`, `MultiModel.separatesPoints_isPL`: two distinct points
  `v ≠ w` of `𝒳^an` differ on a homogeneous `p ∈ S_a` (both are multigraded), and
  `max(log|p|, -N) ∈ 𝓗_fin(𝒳, a)` separates them for `N` large. Hence `PL(𝒳)` separates points.
* `PL(𝒳)` is a `ℚ`-vector space of continuous real functions containing `ℚ` and stable under finite
  maxima and minima (`FSSystem.plSubmodule`, `FSSystem.isPL_const`, `FSSystem.IsPL.max`,
  `FSSystem.IsPL.min`, `FSSystem.IsPL.continuous` for `X.plSystem`);
* `MultiModel.dense_setOf_isPL`, `MultiModel.exists_isPL_abs_sub_lt`: density in `C⁰(𝒳^an)`
  (lattice Stone–Weierstrass);
* `MultiModel.exists_isPL_gt`, `MultiModel.directedOn_isPL_gt`, `MultiModel.iInf_isPL_gt`,
  `MultiModel.exists_antitone_isPL_net`, `MultiModel.le_of_forall_isPL_gt`: for a usc
  `h: 𝒳^an → [-∞, ∞)`, the PL functions `ψ > h` form a nonempty downward directed family with
  infimum `h` (Urysohn's lemma).

## Deviations from the blueprint

None in the statements; `lem:gl-pl` is obtained by specializing the general results of
`EnvelopeProperty.Projective.FSSystemPL` to the restricted system, rather than
reproving them for `FSSystemC`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace FSSystemC

variable {K : Type u} [TopologicalSpace K] {r : ℕ}

/-- The restriction of a Fubini–Study system with semiample cone to the nonnegative classes
`a ∈ ℚ^r_{≥0} ⊆ C`: a Fubini–Study system in the sense of `def:pg-fs-system`. -/
def toFSSystemNonneg (F : FSSystemC K r) : FSSystem K r where
  triv := F.triv
  IsFS a f := 0 ≤ a ∧ F.IsFS a f
  IsFinFS a f := 0 ≤ a ∧ F.IsFinFS a f
  continuous_of_isFS h := h.2.continuous
  nonneg_of_isFS h := h.1
  apply_triv_ne_bot h := h.2.apply_triv_ne_bot
  apply_triv_ne_top h := h.2.apply_triv_ne_top
  le_apply_triv h x := h.2.le_apply_triv x
  isFS_of_isFinFS h := ⟨h.1, h.2.isFS⟩
  ne_bot_of_isFinFS h := h.2.ne_bot
  isFS_mono h hab := ⟨h.1.trans hab, h.2.mono hab⟩
  isFinFS_mono h hab := ⟨h.1.trans hab, h.2.mono hab⟩
  isFS_const ha c := ⟨ha, F.isFS_const (F.nonneg_mem_C _ ha) c⟩
  isFinFS_const ha c := ⟨ha, F.isFinFS_const (F.nonneg_mem_C _ ha) c⟩
  isFS_max hf hg := ⟨hf.1, hf.2.max hg.2⟩
  isFinFS_max hf hg := ⟨hf.1, hf.2.max hg.2⟩
  isFS_add hf hg := ⟨add_nonneg hf.1 hg.1, hf.2.add hg.2⟩
  isFinFS_add hf hg := ⟨add_nonneg hf.1 hg.1, hf.2.add hg.2⟩
  isFS_smul hc h := ⟨smul_nonneg hc.le h.1, h.2.smul hc⟩
  isFinFS_smul hc h := ⟨smul_nonneg hc.le h.1, h.2.smul hc⟩
  exists_antitone_isFinFS h := by
    obtain ⟨g, hg, hanti, hinf⟩ := h.2.exists_antitone_isFinFS (F.nonneg_mem_C _ h.1)
    exact ⟨g, fun n => ⟨h.1, hg n⟩, hanti, hinf⟩

variable (F : FSSystemC K r)

@[simp]
theorem toFSSystemNonneg_triv : F.toFSSystemNonneg.triv = F.triv :=
  rfl

theorem toFSSystemNonneg_isFS_iff {a : Fin r → ℚ} {f : K → EReal} :
    F.toFSSystemNonneg.IsFS a f ↔ 0 ≤ a ∧ F.IsFS a f :=
  Iff.rfl

theorem toFSSystemNonneg_isFinFS_iff {a : Fin r → ℚ} {f : K → EReal} :
    F.toFSSystemNonneg.IsFinFS a f ↔ 0 ≤ a ∧ F.IsFinFS a f :=
  Iff.rfl

end FSSystemC

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  (X : MultiModel k K r)

/-! ### PL functions (`lem:gl-pl`) -/

/-- The Fubini–Study system of `𝒳` restricted to the nonnegative classes, whose PL functions are
`PL(𝒳)`. -/
abbrev plSystem : FSSystem X.an r :=
  X.fsSystem.toFSSystemNonneg

/-- **PL functions on `𝒳^an`** (`lem:gl-pl`): differences `φ - ψ` of finite Fubini–Study functions
`φ ∈ 𝓗_fin(𝒳, a)`, `ψ ∈ 𝓗_fin(𝒳, b)` with `a, b ∈ ℚ^r_{≥0}` (`MultiModel.isPL_iff`). -/
abbrev IsPL (f : X.an → ℝ) : Prop :=
  X.plSystem.IsPL f

variable {X}

theorem isPL_iff {f : X.an → ℝ} :
    X.IsPL f ↔ ∃ (a b : Fin r → ℚ) (φ ψ : X.an → EReal), 0 ≤ a ∧ 0 ≤ b ∧ X.IsFinFS a φ ∧
      X.IsFinFS b ψ ∧ ∀ v, f v = (φ v).toReal - (ψ v).toReal := by
  constructor
  · rintro ⟨a, b, φ, ψ, ⟨ha, hφ⟩, ⟨hb, hψ⟩, hf⟩
    exact ⟨a, b, φ, ψ, ha, hb, hφ, hψ, hf⟩
  · rintro ⟨a, b, φ, ψ, ha, hb, hφ, hψ, hf⟩
    exact ⟨a, b, φ, ψ, ⟨ha, hφ⟩, ⟨hb, hψ⟩, hf⟩

/-- A finite Fubini–Study function of a nonnegative class is PL. -/
theorem IsFinFS.isPL {a : Fin r → ℚ} {φ : X.an → EReal} (h : X.IsFinFS a φ) (ha : 0 ≤ a) :
    X.IsPL fun v => (φ v).toReal :=
  FSSystem.IsFinFS.isPL (F := X.plSystem) ⟨ha, h⟩

/-- **`lem:gl-pl`, separation**: two distinct points `v ≠ w` of `𝒳^an` are separated by a finite
Fubini–Study function `max(log|p|, -N)` of a class `a ∈ ℕ^r`, where `p ∈ S_a` has
`|p T^a|_v ≠ |p T^a|_w`. -/
theorem exists_isFinFS_ne {v w : X.an} (h : v ≠ w) :
    ∃ (a : Fin r → ℚ) (φ : X.an → EReal), 0 ≤ a ∧ X.IsFinFS a φ ∧ φ v ≠ φ w ∧
      φ v ≠ ⊥ ∧ φ w ≠ ⊥ := by
  -- a homogeneous element on which `v` and `w` differ
  obtain ⟨a, f, hf, hne⟩ : ∃ (a : Fin r →₀ ℕ) (f : K) (hf : f ∈ X.piece a),
      v.1.val (X.ofPiece hf) ≠ w.1.val (X.ofPiece hf) := by
    by_contra hcon
    push Not at hcon
    exact h (Subtype.ext (ext_of_ofPiece v.2.1 w.2.1 hcon))
  set d : Fin r → ℤ := fun c => (a c : ℤ) with hd
  have hfd : f ∈ X.sections d := mem_sections_of_mem_piece (fun _ => rfl) hf
  have hsec : ∀ u : X.an, X.secAbs u.1 d f = u.1.val (X.ofPiece hf) := fun u =>
    secAbs_of_mem_piece u.2.2 (fun _ => rfl) hf
  set a' : Fin r → ℚ := fun c => ((d c : ℤ) : ℚ) with ha'
  have ha'0 : 0 ≤ a' := fun c => by simp [ha', hd]
  -- the cut-off level `N`
  obtain ⟨N, hN⟩ := exists_nat_gt (max (-Real.log (v.1.val (X.ofPiece hf) : ℝ))
    (-Real.log (w.1.val (X.ofPiece hf) : ℝ)))
  obtain ⟨Dc, hDcr, hDcb, hDc⟩ := isFinFS_iff.1
    (X.isFinFS_const (X.nonneg_mem_semiampleCone ha'0) (-(N : ℚ)))
  let D := (FSData.single hfd 0).sup Dc
  have hDr : D.IsRational := by
    refine FSData.IsRational.sup (fun t ht => ⟨0, ?_⟩) hDcr
    rw [show t = (f, 0) from Finset.mem_singleton.1 ht]
    simp
  have heval : ∀ u : X.an, D.eval u = max (X.logSecAbs u.1 d f) ((-(N : ℝ) : ℝ) : EReal) := by
    intro u
    rw [FSData.eval_sup, FSData.eval_single, termVal_def, ← hDc u]
    push_cast
    simp
  have hφ : X.IsFinFS a' D.eval := isFinFS_iff.2 ⟨D, hDr, fun u h0 => by
    have := heval u
    rw [h0] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 (this ▸ le_max_right _ _)), fun _ => rfl⟩
  -- the value of `max(log|f|, -N)` where `-log|f| < N`
  have hval : ∀ u : X.an, -Real.log (u.1.val (X.ofPiece hf) : ℝ) < N → D.eval u =
      if u.1.val (X.ofPiece hf) = 0 then ((-(N : ℝ) : ℝ) : EReal)
      else ((Real.log (u.1.val (X.ofPiece hf) : ℝ) : ℝ) : EReal) := by
    intro u hu
    rw [heval, logSecAbs, hsec u]
    split_ifs with h0
    · rw [h0, ENNReal.coe_zero, ENNReal.log_zero, max_eq_right bot_le]
    · rw [ENNReal.log_of_nnreal h0, max_eq_left]
      exact EReal.coe_le_coe_iff.2 (by linarith)
  have hv := hval v ((le_max_left _ _).trans_lt hN)
  have hw := hval w ((le_max_right _ _).trans_lt hN)
  refine ⟨a', D.eval, ha'0, hφ, fun heq => hne ?_, ?_, ?_⟩
  · rw [hv, hw] at heq
    have hNv : ¬ -Real.log (v.1.val (X.ofPiece hf) : ℝ) ≥ N :=
      not_le.2 ((le_max_left _ _).trans_lt hN)
    have hNw : ¬ -Real.log (w.1.val (X.ofPiece hf) : ℝ) ≥ N :=
      not_le.2 ((le_max_right _ _).trans_lt hN)
    split_ifs at heq with h1 h2 h2
    · rw [h1, h2]
    · exfalso
      have := EReal.coe_injective heq
      exact hNw (by linarith)
    · exfalso
      have := EReal.coe_injective heq
      exact hNv (by linarith)
    · have hlog := EReal.coe_injective heq
      have hpos1 : (0 : ℝ) < v.1.val (X.ofPiece hf) := by exact_mod_cast pos_iff_ne_zero.2 h1
      have hpos2 : (0 : ℝ) < w.1.val (X.ofPiece hf) := by exact_mod_cast pos_iff_ne_zero.2 h2
      exact NNReal.coe_injective (Real.log_injOn_pos hpos1 hpos2 hlog)
  · exact FSSystemC.IsFinFS.ne_bot (F := X.fsSystem) hφ v
  · exact FSSystemC.IsFinFS.ne_bot (F := X.fsSystem) hφ w

variable (X) in
/-- **`lem:gl-pl`, separation**: `PL(𝒳)` separates the points of `𝒳^an`; a single finite
Fubini–Study function of a nonnegative class already separates two given points. -/
theorem separatesPoints_isPL : {f : X.an → ℝ | X.IsPL f}.SeparatesPoints := by
  intro v w h
  obtain ⟨a, φ, ha, hφ, hne, hv, hw⟩ := exists_isFinFS_ne h
  refine ⟨fun x => (φ x).toReal, hφ.isPL ha, fun heq => hne ?_⟩
  have htop : ∀ x, φ x ≠ ⊤ := fun x => FSSystemC.IsFS.ne_top (F := X.fsSystem) hφ.isFS x
  rw [← EReal.coe_toReal (htop v) hv, ← EReal.coe_toReal (htop w) hw]
  exact congrArg _ heq

/-! ### Density and approximation of usc functions (`lem:gl-pl`) -/

variable (X) in
/-- **`lem:gl-pl`, density**: `PL(𝒳)` is dense in `C⁰(𝒳^an)`. -/
theorem dense_setOf_isPL : Dense {f : C(X.an, ℝ) | X.IsPL f} :=
  FSSystem.dense_setOf_isPL (separatesPoints_isPL X)

/-- **`lem:gl-pl`, density**: every continuous function on `𝒳^an` is a uniform limit of PL
functions. -/
theorem exists_isPL_abs_sub_lt {f : X.an → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ, X.IsPL ψ ∧ ∀ x, |f x - ψ x| < ε :=
  FSSystem.exists_isPL_abs_sub_lt (separatesPoints_isPL X) hf hε

/-- **`lem:gl-pl`**: a usc function `h : 𝒳^an → [-∞, ∞)` lies below some PL function. -/
theorem exists_isPL_gt {h : X.an → EReal} (hh : UpperSemicontinuous h) (htop : ∀ x, h x ≠ ⊤) :
    ∃ ψ, X.IsPL ψ ∧ ∀ x, h x < ψ x :=
  FSSystem.exists_isPL_gt (F := X.plSystem) hh htop

variable (X) in
/-- **`lem:gl-pl`**: the PL functions `ψ > h` form a downward directed family. -/
theorem directedOn_isPL_gt (h : X.an → EReal) :
    DirectedOn (· ≥ ·) {ψ : X.an → ℝ | X.IsPL ψ ∧ ∀ x, h x < ψ x} :=
  FSSystem.directedOn_isPL_gt (F := X.plSystem) h

/-- **`lem:gl-pl`**: a usc function `h : 𝒳^an → [-∞, ∞)` is the infimum of the PL functions
`ψ > h`. -/
theorem iInf_isPL_gt {h : X.an → EReal} (hh : UpperSemicontinuous h) (htop : ∀ x, h x ≠ ⊤)
    (x : X.an) : ⨅ (ψ : X.an → ℝ) (_ : X.IsPL ψ ∧ ∀ w, h w < ψ w), (ψ x : EReal) = h x :=
  FSSystem.iInf_isPL_gt (separatesPoints_isPL X) hh htop x

/-- **`lem:gl-pl`** as a decreasing net of PL functions `ψ_i > h` with limit `h`. -/
theorem exists_antitone_isPL_net {h : X.an → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ x, h x ≠ ⊤) :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (ψ : ι → X.an → ℝ), (∀ i, X.IsPL (ψ i)) ∧ (∀ i w, h w < ψ i w) ∧
        (∀ w, Antitone fun i => ψ i w) ∧ ∀ w, h w = ⨅ i, (ψ i w : EReal) :=
  FSSystem.exists_antitone_isPL_net (separatesPoints_isPL X) hh htop

/-- **`lem:gl-pl`**, comparison with usc functions: if `u ≤ ψ` for every PL function `ψ > h`,
where `h : 𝒳^an → [-∞, ∞)` is usc, then `u ≤ h`. -/
theorem le_of_forall_isPL_gt {h u : X.an → EReal} (hh : UpperSemicontinuous h)
    (htop : ∀ x, h x ≠ ⊤) (hu : ∀ ψ, X.IsPL ψ → (∀ w, h w < ψ w) → ∀ x, u x ≤ ψ x) : u ≤ h :=
  FSSystem.le_of_forall_isPL_gt (separatesPoints_isPL X) hh htop hu

end MultiModel

end EnvelopeProperty
