/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Source.PSHDictionary
import EnvelopeProperty.Source.PresentationFS
import EnvelopeProperty.Source.ClassPromotion
import EnvelopeProperty.Source.Presentations

/-! # Psh functions of a variety and of the model of a presentation

Let `p : X ⟶ Spec k` be projective with `X` integral. A *presentation* of `X`
(`def:pm-presentation`) is a finite family `q_c : X → ℙ^{d_c}` over `k`, `c = 0, …, r`, with
`q_0` a closed immersion; its factor lines are `F_c = q_c^* 𝒪(1)`, its coefficient map is
`π : ℝ^{r+1} → N¹(X)_ℝ`, `π(θm) = ∑_c θm_c [F_c]`, and its multiprojective model
`𝒫 = FiniteProjectiveNativeFieldModels.model q p hp` comes with the homeomorphism
`H : X^an ≃ 𝒫^an` (`OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph`).

This file proves that BJ22's psh functions on `X^an` (`Variety.IsPSH`, BJ22 Definition 4.1,
`bj22-trivval:defi:psh`) are the psh functions of the model (`MultiModel.IsPSH`, `def:gl-psh`):

* `Variety.isPSH_iff_presentation` (`thm:var-psh-comparison`): for `θm ∈ ℝ^{r+1}` and
  `φ : X^an → [-∞, ∞]`, `φ ∈ PSH(X, π(θm))` iff `φ ∘ H⁻¹ ∈ PSH(𝒫, θm)`;
* `Variety.hasEnvelopeProperty_iff_presentation` (`cor:var-ep-comparison`):
  `EP_X(π(θm)) ↔ EP_𝒫(θm)`;
* `Variety.isPSH_presentation_iff_of_eq`, `Variety.hasEnvelopeProperty_presentation_iff_of_eq`:
  `PSH(𝒫, θm)` and `EP_𝒫(θm)` depend only on the class `π(θm)`.

## Proof

Both statements are instances of the abstract comparison through a Fubini–Study dictionary
(`Variety.isPSH_iff_of_fsDictionary`, `Variety.hasEnvelopeProperty_iff_of_fsDictionary`,
`lem:var-psh-comparison-dictionary`, in `EnvelopeProperty.Source.PSHDictionary`), with
`F = 𝒫.fsSystem`, `e = H`, the factor lines `F_c` and the ample direction `w = e_0`
(`[F_0]` is very ample, `Variety.isAmple_presentationFactorLine_zero`). Its two hypotheses are
(`lem:var-presentation-fs-transfer`):
(A) a model Fubini–Study function of class `a` is, through `H`, a native one of class `π(a)`:
the FS dictionary `Variety.isFS_iff_presentation` and `Variety.numericalClass_eq_lineFamilyMap`;
(B) if `D` is a nonzero native datum with `π(a) - [D]` ample, then `φ_D ∘ H⁻¹` is a model
Fubini–Study function of class `a`: write `n a = z ∈ ℤ^{r+1}`; finite class promotion
(`NativeNumericalFubiniStudy.FSData.exists_promotion`, FHX `lem:finite-class-promotion`) moves
`D` into a power `L(z)^{⊗t} ≅ L(t z)` of the signed line `L(z)` with denominator `n t`, and the FS
dictionary applies.
-/

open AlgebraicGeometry CategoryTheory Filter Topology
open Scheme.Modules
open Alterations
open scoped NNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty.Variety

open NativeRealNumericalClasses NativeNumericalFubiniStudy

/-! ### Auxiliary facts -/

/-- A rational vector has a positive integral multiple with integer coordinates. -/
private theorem exists_nat_mul_eq_int {ι : Type*} [Fintype ι] (b : ι → ℚ) :
    ∃ n : ℕ, 0 < n ∧ ∃ z : ι → ℤ, ∀ i, (z i : ℚ) = n * b i := by
  refine ⟨∏ i, (b i).den, Finset.prod_pos fun i _ => (b i).den_pos, ?_⟩
  have key : ∀ i, ∃ z : ℤ, (z : ℚ) = ((∏ i, (b i).den : ℕ) : ℚ) * b i := by
    intro i
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i => (b i).den) (Finset.mem_univ i)
    refine ⟨(m : ℤ) * (b i).num, ?_⟩
    rw [hm]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose z hz using key
  exact ⟨z, hz⟩

private local instance pshComparisonProper {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### Presentations -/

section Presentation

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {r : ℕ} (d : Fin (r + 1) → ℕ)
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k)) [IsProjective p]
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p) [IsClosedImmersion (q 0)]

omit [IsIntegral X] in
include hp in
/-- The first coordinate direction of a presentation is ample: `π(e_0) = [q_0^* 𝒪(1)]`. -/
theorem lineFamilyMap_presentation_single_mem_ampleCone :
    lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q)
      (Pi.single 0 1) ∈ ampleCone p := by
  have h := ampleLineClass_mem_ampleCone p _ (isAmple_presentationFactorLine_zero q p hp)
  convert h using 1
  rw [lineFamilyMap_apply, Finset.sum_eq_single (0 : Fin (r + 1))]
  · simp
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- **(A) for a presentation**: a model Fubini–Study function of class `a` is, through `H`, the
function of a nonzero native datum of class `π(a)` (`thm:pm-fs-dictionary`, `lem:pm-fs-class`). -/
theorem exists_fsData_of_isFS_presentation (a : Fin (r + 1) → ℚ)
    (ψ : (letI := p.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q p hp).an) → EReal) :
    letI := p.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q p hp).fsSystem.IsFS a ψ →
      ∃ D : NativeNumericalFubiniStudy.FSData X, D.Nonzero ∧
        D.numericalClass p = lineFamilyMap p (presentationFactorLine d q)
          (presentationFactorLine_isInvertible d q) (fun c => (a c : ℝ)) ∧
        ∀ y, ψ (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp y) =
          D.eval p y := by
  intro h
  obtain ⟨D, hD, ⟨deg, hdeg, ⟨e⟩⟩, hψ⟩ :=
    (isFS_iff_presentation d q p hp (fun c => (0 : Fin (d c + 1))) a ψ).mp h
  exact ⟨D, hD, numericalClass_eq_lineFamilyMap d q p (fun c => (0 : Fin (d c + 1))) D deg hdeg e,
    hψ⟩

/-- **(B) for a presentation**, by finite class promotion (`lem:var-class-promotion`, FHX
`lem:finite-class-promotion`): if `D` is a nonzero native datum and `π(a) - [D]` is ample, then
`D ∘ H⁻¹` is a model Fubini–Study function of class `a`. Write `n a = z ∈ ℤ^{r+1}`, `n > 0`;
promote `D` into a power `L(z)^{⊗t}` of the signed line `L(z)` (whose class `n⁻¹ [L(z)]` is
`π(a)`); then `L(z)^{⊗t} ≅ L(t z)` and the FS dictionary applies with denominator `n t`. -/
theorem isFS_presentation_of_sub_mem_ampleCone (a : Fin (r + 1) → ℚ)
    (D : NativeNumericalFubiniStudy.FSData X) (hD : D.Nonzero)
    (h : lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q)
      (fun c => (a c : ℝ)) - D.numericalClass p ∈ ampleCone p) :
    letI := p.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q p hp).fsSystem.IsFS a fun v =>
      D.eval p ((OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph
        q p hp).symm v) := by
  obtain ⟨n, hn, z, hz⟩ := exists_nat_mul_eq_int a
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hzR (c : Fin (r + 1)) : (z c : ℝ) = n * (a c : ℝ) := by exact_mod_cast hz c
  have hcl : (n : ℝ)⁻¹ • lineClass p (signedProjectiveLine d q (fun c => (0 : Fin (d c + 1))) z)
      (signedProjectiveLine_isInvertible d q (fun c => (0 : Fin (d c + 1))) z) =
      lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q)
        (fun c => (a c : ℝ)) := by
    rw [lineClass_signedProjectiveLine p q (fun c => (0 : Fin (d c + 1))) z, ← _root_.map_smul]
    congr 1
    funext c
    rw [Pi.smul_apply, smul_eq_mul, hzR c, inv_mul_cancel_left₀ hn0]
  obtain ⟨t, -, E, hE, hEm, ⟨eE⟩, hEeval⟩ := D.exists_promotion p hD
    (signedProjectiveLine d q (fun c => (0 : Fin (d c + 1))) z)
    (signedProjectiveLine_isInvertible d q (fun c => (0 : Fin (d c + 1))) z) n hn
    (by rw [hcl]; exact h)
  refine (isFS_iff_presentation d q p hp (fun c => (0 : Fin (d c + 1))) a _).mpr
    ⟨E, hE, ⟨t • z, fun c => ?_, ⟨eE ≪≫ (signedProjectiveLinePowerIso d q
      (fun c => (0 : Fin (d c + 1))) z t).symm⟩⟩, fun y => ?_⟩
  · have htz : (t • z) c = (t : ℤ) * z c := by simp
    rw [htz, hEm, Int.cast_mul, Int.cast_natCast, hz c, Nat.cast_mul]
    ring
  · simp only [Homeomorph.symm_apply_apply, hEeval]

/-- **BJ22 psh functions are the psh functions of a presentation model**
(`thm:var-psh-comparison`): for `θm ∈ ℝ^{r+1}` and `φ : X^an → [-∞, ∞]`,
`φ ∈ PSH(X, ∑_c θm_c [q_c^* 𝒪(1)])` iff `φ ∘ H⁻¹ ∈ PSH(𝒫, θm)`. -/
theorem isPSH_iff_presentation (θm : Fin (r + 1) → ℝ) (φ : An p → EReal) :
    letI := p.stalkAlgebra (genericPoint X)
    IsPSH p (lineFamilyMap p (presentationFactorLine d q)
        (presentationFactorLine_isInvertible d q) θm) φ ↔
      (FiniteProjectiveNativeFieldModels.model q p hp).IsPSH θm
        (φ ∘ (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph
          q p hp).symm) := by
  let := p.stalkAlgebra (genericPoint X)
  exact isPSH_iff_of_fsDictionary p (FiniteProjectiveNativeFieldModels.model q p hp).fsSystem
    (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp)
    (presentationFactorLine d q) (presentationFactorLine_isInvertible d q) (Pi.single 0 1)
    (lineFamilyMap_presentation_single_mem_ampleCone d q p hp)
    (exists_fsData_of_isFS_presentation d q p hp)
    (fun a D hD h => isFS_presentation_of_sub_mem_ampleCone d q p hp a D hD h) θm φ

/-- **The envelope property of a variety and of a presentation model**
(`cor:var-ep-comparison`): `EP_X(∑_c θm_c [q_c^* 𝒪(1)]) ↔ EP_𝒫(θm)`. -/
theorem hasEnvelopeProperty_iff_presentation (θm : Fin (r + 1) → ℝ) :
    letI := p.stalkAlgebra (genericPoint X)
    HasEnvelopeProperty p (lineFamilyMap p (presentationFactorLine d q)
        (presentationFactorLine_isInvertible d q) θm) ↔
      (FiniteProjectiveNativeFieldModels.model q p hp).HasEnvelopeProperty θm := by
  let := p.stalkAlgebra (genericPoint X)
  exact hasEnvelopeProperty_iff_of_fsDictionary p
    (FiniteProjectiveNativeFieldModels.model q p hp).fsSystem
    (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp)
    (presentationFactorLine d q) (presentationFactorLine_isInvertible d q) (Pi.single 0 1)
    (lineFamilyMap_presentation_single_mem_ampleCone d q p hp)
    (exists_fsData_of_isFS_presentation d q p hp)
    (fun a D hD h => isFS_presentation_of_sub_mem_ampleCone d q p hp a D hD h) θm

/-- `PSH(𝒫, θm)` depends only on the class `∑_c θm_c [q_c^* 𝒪(1)] ∈ N¹(X)_ℝ`. -/
theorem isPSH_presentation_iff_of_eq {θm θm' : Fin (r + 1) → ℝ}
    (h : lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q) θm =
      lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q) θm')
    (u : (letI := p.stalkAlgebra (genericPoint X);
      (FiniteProjectiveNativeFieldModels.model q p hp).an) → EReal) :
    letI := p.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q p hp).IsPSH θm u ↔
      (FiniteProjectiveNativeFieldModels.model q p hp).IsPSH θm' u := by
  have hu : u = (u ∘ OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph
      q p hp) ∘ (OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph
        q p hp).symm := funext fun v => by
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  rw [hu, ← isPSH_iff_presentation d q p hp θm, ← isPSH_iff_presentation d q p hp θm', h]

/-- `EP_𝒫(θm)` depends only on the class `∑_c θm_c [q_c^* 𝒪(1)] ∈ N¹(X)_ℝ`. -/
theorem hasEnvelopeProperty_presentation_iff_of_eq {θm θm' : Fin (r + 1) → ℝ}
    (h : lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q) θm =
      lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q)
        θm') :
    letI := p.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q p hp).HasEnvelopeProperty θm ↔
      (FiniteProjectiveNativeFieldModels.model q p hp).HasEnvelopeProperty θm' := by
  rw [← hasEnvelopeProperty_iff_presentation d q p hp θm,
    ← hasEnvelopeProperty_iff_presentation d q p hp θm', h]

end Presentation

end EnvelopeProperty.Variety
