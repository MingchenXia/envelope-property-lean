/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Actual global directed ideal-sheaf suprema are attained

Compactness produces an actual finite affine cover of the ORIGINAL scheme.
Noetherianity on these actual section rings produces actual constituent indices;
directedness combines those finitely many indices into one global constituent.
-/

noncomputable section
namespace AlgebraicGeometry.Scheme.IdealSheafData
open CategoryTheory TopologicalSpace
open scoped Classical
universe u v
variable {X : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X]

/-- On an actual quasi-compact locally Noetherian ORIGINAL scheme, every
nonempty directed family of actual original ideal sheaves attains its whole
global supremum at an ACTUAL family member. -/
theorem exists_eq_iSup_of_directed {α : Type v} [Nonempty α]
    (F : α → X.IdealSheafData) (hF : Directed (· ≤ ·) F) :
    ∃ a, (⨆ b, F b) = F a := by
  let 𝒰 := X.affineCover.finiteSubcover
  let U : 𝒰.I₀ → X.affineOpens := fun i =>
    ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩
  have hU : ⨆ i, (U i).1 = ⊤ := 𝒰.iSup_opensRange
  have hmax (i : 𝒰.I₀) : ∃ a, ∀ b, (F b).ideal (U i) ≤ (F a).ideal (U i) := by
    have : IsNoetherianRing Γ(X, U i) := IsLocallyNoetherian.component_noetherian (U i)
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := set_has_maximal_iff_noetherian.2
      (inferInstance : IsNoetherianRing Γ(X, U i))
      {J | ∃ a, (F a).ideal (U i) = J} ⟨(F (Classical.arbitrary α)).ideal (U i), _, rfl⟩
    refine ⟨a, fun b => ?_⟩
    obtain ⟨c, hac, hbc⟩ := hF a b
    have heq : (F a).ideal (U i) = (F c).ideal (U i) := by
      by_contra hne
      exact ha _ ⟨c, rfl⟩ (lt_of_le_of_ne (hac (U i)) hne)
    rw [heq]
    exact hbc (U i)
  choose a ha using hmax
  have hbound (t : Finset 𝒰.I₀) : ∃ c, ∀ i ∈ t, F (a i) ≤ F c := by
    induction t using Finset.induction_on with
    | empty => exact ⟨Classical.arbitrary α, by simp⟩
    | @insert i t hit ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨c, hic, hbc⟩ := hF (a i) b
      refine ⟨c, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hic
      · exact (hb j hj).trans hbc
  let _ : Fintype 𝒰.I₀ := Fintype.ofFinite _
  obtain ⟨c, hc⟩ := hbound Finset.univ
  refine ⟨c, le_antisymm (iSup_le fun b => ?_) (le_iSup F c)⟩
  apply le_of_iSup_eq_top U hU
  intro i
  exact (ha i b).trans ((hc i (Finset.mem_univ i)) (U i))

end AlgebraicGeometry.Scheme.IdealSheafData
