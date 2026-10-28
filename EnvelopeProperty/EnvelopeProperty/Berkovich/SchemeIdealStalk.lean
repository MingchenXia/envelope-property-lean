/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Stalk
import DeJongAlterations.Geometry.ProjectiveIdealStalk
import Hironaka.Scheme.IdealSheaf.Defs

/-!
# Actual stalk ideals of genuine scheme ideal-sheaf data

Take the supremum of every actual affine-neighborhood germ image. The real
localization law and genuine affine refinement prove that it equals ANY
affine-neighborhood image and preserve the actual ideal arithmetic. No stalk
equality, finite cover or Noetherian hypothesis is assumed.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/- The common definition and affine-germ API come from the native de Jong library.
The arithmetic below applies to that same supremum of affine germ-images. -/

/-- The zero ideal-sheaf data has the actual zero stalk ideal. -/
@[simp]
theorem paperStalkIdeal_bot (x : X) : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  rw [stalkIdeal_eq_affine _ x ⟨U, hU⟩ hx]
  simp

/-- The unit ideal-sheaf data has the actual unit stalk ideal. -/
@[simp]
theorem paperStalkIdeal_top (x : X) : stalkIdeal (⊤ : X.IdealSheafData) x = ⊤ := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  rw [stalkIdeal_eq_affine _ x ⟨U, hU⟩ hx, ideal_top]
  exact Ideal.map_top _

/-- Genuine ideal-sheaf sums commute with the intrinsic stalk construction. -/
theorem paperStalkIdeal_sup (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x = stalkIdeal I x ⊔ stalkIdeal J x := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  simp only [stalkIdeal_eq_affine _ x ⟨U, hU⟩ hx, ideal_sup, Pi.sup_apply, Ideal.map_sup]

/-- Genuine ideal-sheaf products commute with the intrinsic stalk construction. -/
theorem paperStalkIdeal_mul (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I * J) x = stalkIdeal I x * stalkIdeal J x := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  simp only [stalkIdeal_eq_affine _ x ⟨U, hU⟩ hx, ideal_mul, Pi.mul_apply, Ideal.map_mul]

/-- All powers, including zero, commute with the actual stalk-ideal construction. -/
theorem paperStalkIdeal_pow (I : X.IdealSheafData) (x : X) (n : ℕ) :
    stalkIdeal (I ^ n) x = stalkIdeal I x ^ n := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  simp only [stalkIdeal_eq_affine _ x ⟨U, hU⟩ hx, ideal_pow, Pi.pow_apply, Ideal.map_pow]

end AlgebraicGeometry.Scheme.IdealSheafData
