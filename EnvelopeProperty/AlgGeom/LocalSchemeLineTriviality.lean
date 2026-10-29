/-
Copyright (c) 2026. All rights reserved.
-/
import ModularCurves.Picard.InvertibleSheaf

/-! # Actual global trivializations of line sheaves over local spectra -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules

/-- The ORIGINAL cover-local invertibility on the spectrum of an actual
local ring supplies an ACTUAL global original module-sheaf trivialization. -/
theorem IsInvertible.nonempty_iso_unit_on_localSpec
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : (Spec (CommRingCat.of R)).Modules} (hM : IsInvertible M) :
    Nonempty (M ≅ unitObj (Spec (CommRingCat.of R))) := by
  let X := Spec (CommRingCat.of R)
  obtain ⟨ι, U, hU, htriv⟩ := hM
  have hx : (IsLocalRing.closedPoint R : X) ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hUi : U i = ⊤ := (IsLocalRing.closedPoint_mem_iff (U i)).mp hi
  obtain ⟨e⟩ : Nonempty ((Modules.pullback (⊤ : X.Opens).ι).obj M ≅
      unitObj (⊤ : X.Opens).toScheme) := hUi ▸ htriv i
  let j := X.topIso.inv
  have hj : j ≫ (⊤ : X.Opens).ι = 𝟙 X := X.topIso.inv_hom_id
  exact ⟨(pullbackId X).symm.app M ≪≫ (pullbackCongr hj).symm.app M ≪≫
    (pullbackComp j (⊤ : X.Opens).ι).symm.app M ≪≫
    (Modules.pullback j).mapIso e ≪≫ pullbackUnitIso j⟩

end AlgebraicGeometry.Scheme.Modules
