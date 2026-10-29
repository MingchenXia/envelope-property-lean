/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.RationalLatticeSheaf
import EnvelopeProperty.Projective.FSSystemPL

/-!
# The local membership property for global PL functions

The rational vector lattice of global Fubini--Study differences is a sheaf on a compact
space whenever it separates points. All rational-lattice hypotheses are discharged by the
existing FS-system operations and Stone--Weierstrass density. This supplies the topological
gluing reduction in FHX Lemma 5.5, without assuming local positivity.
-/

noncomputable section

namespace EnvelopeProperty.FSSystem

universe u

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] {r : ℕ} (F : FSSystem K r)

/-- Global PL functions provide exact local cutoffs, with no positivity hypothesis. -/
theorem exists_isPL_cutoff (hsep : {f : K → ℝ | F.IsPL f}.SeparatesPoints)
    {U : Set K} (hU : IsOpen U) {x : K} (hx : x ∈ U) :
    ∃ b, F.IsPL b ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∉ U, b y = 0) ∧
      ∃ V : Set K, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, b y = 1 := by
  let : T2Space K := t2Space_of_separatesPoints hsep
  exact RationalFunctionLattice.exists_cutoff F.plSubmodule (isPL_const F)
    (fun f hf g hg => (show F.IsPL f from hf).min hg)
    (fun f hf g hg => (show F.IsPL f from hf).max hg)
    (fun f hf => (show F.IsPL f from hf).continuous)
    (fun f hf ε hε => exists_isPL_abs_sub_lt hsep hf hε) hU hx

/-- A real function locally equal to global PL expressions is globally PL. -/
theorem isPL_of_locally_isPL (hsep : {g : K → ℝ | F.IsPL g}.SeparatesPoints) {f : K → ℝ}
    (hlocal : ∀ x, ∃ (U : Set K) (g : K → ℝ), IsOpen U ∧ x ∈ U ∧ F.IsPL g ∧
      ∀ y ∈ U, f y = g y) : F.IsPL f := by
  let : T2Space K := t2Space_of_separatesPoints hsep
  exact RationalFunctionLattice.mem_of_locally_mem F.plSubmodule (isPL_const F)
    (fun f hf g hg => (show F.IsPL f from hf).min hg)
    (fun f hf g hg => (show F.IsPL f from hf).max hg)
    (fun f hf => (show F.IsPL f from hf).continuous)
    (fun f hf ε hε => exists_isPL_abs_sub_lt hsep hf hε) hlocal

end EnvelopeProperty.FSSystem
