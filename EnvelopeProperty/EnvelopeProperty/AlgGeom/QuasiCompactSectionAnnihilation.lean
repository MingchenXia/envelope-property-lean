import Hironaka.Scheme.Modules.Sections
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Genuine denominator annihilation on an original quasi-compact open -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u
noncomputable section

/-- Original compactness derives a finite original affine cover inside the
SAME actual open. No supplied cover or finiteness certificate is required. -/
theorem exists_finite_affine_cover_of_isCompact (X : Scheme.{u}) (V : X.Opens)
    (hV : IsCompact (V : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.affineOpens),
      (∀ i, (U i).1 ≤ V) ∧ (⨆ i, (U i).1) = V := by
  classical
  let I := {U : X.affineOpens // U.1 ≤ V}
  have hcover : (V : Set X) ⊆ ⋃ i : I, (i.1.1 : Set X) := by
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    exact Set.mem_iUnion.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun i : I ↦ (i.1.1 : Set X))
    (fun i ↦ i.1.1.isOpen) hcover
  refine ⟨s, inferInstance, fun i ↦ i.1.1, fun i ↦ i.1.2, le_antisymm ?_ ?_⟩
  · exact iSup_le fun i ↦ i.1.2
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

namespace Modules

/-- Actual quasicoherence and compactness derive a genuine annihilating
power for an ENTIRE original section vanishing on its actual basic open. -/
theorem exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isCompact
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (V : X.Opens) (hV : IsCompact (V : Set X))
    (r : Γ(X, V)) (m : Γ(M, V))
    (hm : M.presheaf.map (homOfLE (X.basicOpen_le r)).op m = 0) :
    ∃ n : ℕ, r ^ n • m = 0 := by
  classical
  obtain ⟨ι, hι, U, hU, hcover⟩ := X.exists_finite_affine_cover_of_isCompact V hV
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let ri (i : ι) : Γ(X, (U i).1) := X.presheaf.map (homOfLE (hU i)).op r
  let mi (i : ι) : Γ(M, (U i).1) := M.presheaf.map (homOfLE (hU i)).op m
  have hlocal (i : ι) : ∃ n : ℕ, ri i ^ n • mi i = 0 := by
    apply exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
      M (U i) (ri i) (mi i)
    let hle : X.basicOpen (ri i) ≤ X.basicOpen r :=
      X.basicOpen_restrict (homOfLE (hU i)) r
    change M.presheaf.map (homOfLE (X.basicOpen_le (ri i))).op
      (M.presheaf.map (homOfLE (hU i)).op m) = 0
    rw [← M.presheaf.map_comp_apply]
    have heq : (homOfLE (hU i)).op ≫
        (homOfLE (X.basicOpen_le (ri i))).op =
      (homOfLE (X.basicOpen_le r)).op ≫ (homOfLE hle).op := Subsingleton.elim _ _
    rw [heq, M.presheaf.map_comp_apply, hm, map_zero]
  choose ni hni using hlocal
  let N := Finset.univ.sup ni
  have hN (i : ι) : ri i ^ N • mi i = 0 := by
    have hi : ni i ≤ N := Finset.le_sup (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hi, pow_add, mul_smul, hni, smul_zero]
  refine ⟨N, ?_⟩
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  have hx' : x ∈ ⨆ i, (U i).1 := by rwa [hcover]
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx'
  refine ⟨(U i).1, hU i, hxi, ?_⟩
  rw [map_zero]
  change M.val.map (homOfLE (hU i)).op (r ^ N • m) = 0
  have hs : M.val.map (homOfLE (hU i)).op (r ^ N • m) =
      X.presheaf.map (homOfLE (hU i)).op (r ^ N) • mi i :=
    M.val.map_smul (homOfLE (hU i)).op (r ^ N) m
  refine hs.trans ?_
  exact (congrArg (fun a : Γ(X, (U i).1) ↦ a • mi i)
    (map_pow (X.presheaf.map (homOfLE (hU i)).op).hom r N)).trans (hN i)

end Modules

end
end AlgebraicGeometry.Scheme
