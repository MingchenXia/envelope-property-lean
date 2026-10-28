/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.AffineCartierModulePullback
import EnvelopeProperty.AlgGeom.CartierInvariantLinearization

/-! # Entire actual affine ideal pullback image without flatness -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

/-- The genuine entire original coefficient image of the ACTUAL pulled
ideal-module inclusion on the original affine global section module. -/
def affinePullbackInclusionRange (I : Y.IdealSheafData) (f : X ⟶ Y) :
    Ideal Γ(X, (⊤ : X.Opens)) :=
  LinearMap.range (((I.comap f).toSubmodule.obj (op (⊤ : X.Opens))).subtype.comp
    ((I.toModulesComapPullbackMap f).val.app (op ⊤)).hom)

/-- The entire actual affine pullback image is the ENTIRE original
geometric comap ideal, WITHOUT any flatness or invertibility premise. -/
theorem affinePullbackInclusionRange_eq (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.affinePullbackInclusionRange f = (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ := by
  apply le_antisymm
  · rintro a ⟨s, rfl⟩
    exact ((I.comap f).toModulesSectionsEquiv ⟨⊤, isAffineOpen_top X⟩
      ((I.toModulesComapPullbackMap f).app ⊤ s)).property
  · rw [I.comap_ideal_top_of_isAffine_native f]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    let s : Γ(I.toModules, (⊤ : Y.Opens)) :=
      (I.toModulesSectionsEquiv ⟨⊤, isAffineOpen_top Y⟩).symm ⟨a, ha⟩
    refine ⟨Scheme.Modules.affinePullbackUnitTop f I.toModules s, ?_⟩
    exact I.toModulesComapPullbackMap_affineUnitTop f s

/-- The true actual affine ideal-module comparison is surjective on ALL
original global sections, INCLUDING genuine nonflat original morphisms. -/
theorem affine_toModulesComapPullbackMap_appTop_surjective
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    Function.Surjective ((I.toModulesComapPullbackMap f).app (⊤ : X.Opens)) := by
  intro t
  have ht : (t : (I.comap f).toSubmodule.obj (op (⊤ : X.Opens))).1 ∈
      I.affinePullbackInclusionRange f := by
    rw [I.affinePullbackInclusionRange_eq f]
    exact ((I.comap f).toModulesSectionsEquiv ⟨⊤, isAffineOpen_top X⟩ t).property
  obtain ⟨s, hs⟩ := ht
  refine ⟨s, ?_⟩
  apply Subtype.ext
  exact hs

end AlgebraicGeometry.Scheme.IdealSheafData
