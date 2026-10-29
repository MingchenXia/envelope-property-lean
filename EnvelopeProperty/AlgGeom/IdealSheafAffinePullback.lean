/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Original geometric ideal pullback on affine global sections

The original affine ideal-image producer is shared unchanged by ordinary
project files and module-style imports. Its full original name, statement,
docstring and proof are retained.
-/

public section
open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- The actual scheme ideal pullback has the genuine section-ring image on affine schemes. -/
theorem comap_ideal_top_of_isAffine_native [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  let K := (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom
  let J : X.IdealSheafData := ofIdealTop K
  have hJ : I ≤ J.map f := by
    apply le_of_isAffine
    rw [ideal_map_of_isAffineHom]
    simpa [J, ofIdealTop_ideal, Scheme.Hom.appTop] using
      (Ideal.le_comap_map : I.ideal ⟨⊤, isAffineOpen_top Y⟩ ≤ K.comap f.appTop.hom)
  have hleft := ((le_map_iff_comap_le (I := J) (J := I) (f := f)).mp hJ) ⟨⊤, isAffineOpen_top X⟩
  have hright := (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩
  rw [ideal_map_of_isAffineHom] at hright
  apply le_antisymm
  · simpa [J, ofIdealTop_ideal] using hleft
  · exact Ideal.map_le_iff_le_comap.mpr hright

end AlgebraicGeometry.Scheme.IdealSheafData
