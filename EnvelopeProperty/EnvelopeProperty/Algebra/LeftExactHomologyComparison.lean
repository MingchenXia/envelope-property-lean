import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Canonical native homology comparison from actual preserved kernels -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.LeftExactHomologyComparison
open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Abelian C] [Abelian D]
variable (S : ShortComplex C) (F : C ⥤ D)
variable [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]

private instance mappedCycles_mono : Mono (F.map S.iCycles) :=
  mono_of_isLimit_fork (isLimitForkMapOfIsLimit' F S.iCycles_g S.cyclesIsKernel)

/-- The actual preserved kernel, without any preservation of cokernels. -/
def cyclesIso : (S.map F).cycles ≅ F.obj S.cycles :=
  ((S.map F).isoCyclesOfIsLimit
    (isLimitForkMapOfIsLimit' F S.iCycles_g S.cyclesIsKernel)).symm

/-- The entire original cycle inclusion is retained. -/
@[reassoc]
theorem cyclesIso_hom_iCycles :
    (cyclesIso S F).hom ≫ F.map S.iCycles = (S.map F).iCycles := by
  unfold cyclesIso
  exact (S.map F).isoCyclesOfIsLimit_inv_ι
    (isLimitForkMapOfIsLimit' F S.iCycles_g S.cyclesIsKernel)

/-- The original boundary map, not an assumed representative comparison. -/
theorem toCycles_comparison :
    (S.map F).toCycles ≫ (cyclesIso S F).hom = F.map S.toCycles := by
  apply (cancel_mono (F.map S.iCycles)).mp
  rw [Category.assoc, cyclesIso_hom_iCycles, ShortComplex.toCycles_i,
    ← F.map_comp, ShortComplex.toCycles_i]
  rfl

private theorem boundary_zero :
    (S.map F).toCycles ≫ ((cyclesIso S F).hom ≫ F.map S.homologyπ) = 0 := by
  rw [← Category.assoc, toCycles_comparison, ← F.map_comp,
    ShortComplex.toCycles_comp_homologyπ, F.map_zero]

/-- Canonical comparison of actual native homology, with no right-exactness assumption. -/
def map : (S.map F).homology ⟶ F.obj S.homology :=
  (S.map F).descHomology ((cyclesIso S F).hom ≫ F.map S.homologyπ) (boundary_zero S F)

/-- Every original native cycle has exactly its original class image. -/
@[reassoc]
theorem homologyπ_map :
    (S.map F).homologyπ ≫ map S F = (cyclesIso S F).hom ≫ F.map S.homologyπ :=
  (S.map F).π_descHomology _ _

variable {S} {T : ShortComplex C}

private theorem cycles_naturality (φ : S ⟶ T) :
    ShortComplex.cyclesMap (F.mapShortComplex.map φ) ≫ (cyclesIso T F).hom =
      (cyclesIso S F).hom ≫ F.map (ShortComplex.cyclesMap φ) := by
  apply (cancel_mono (F.map T.iCycles)).mp
  simp only [Category.assoc, cyclesIso_hom_iCycles, ShortComplex.cyclesMap_i,
    ← F.map_comp, ShortComplex.cyclesMap_i]
  rw [F.map_comp, ← Category.assoc, cyclesIso_hom_iCycles]
  exact ShortComplex.cyclesMap_i (F.mapShortComplex.map φ)

/-- The whole comparison commutes with every actual original short-complex map. -/
theorem naturality (φ : S ⟶ T) :
    ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫ map T F =
      map S F ≫ F.map (ShortComplex.homologyMap φ) := by
  apply (cancel_epi (S.map F).homologyπ).mp
  calc
    (S.map F).homologyπ ≫
        (ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫ map T F) =
        ShortComplex.cyclesMap (F.mapShortComplex.map φ) ≫
          ((T.map F).homologyπ ≫ map T F) :=
      (ShortComplex.homologyπ_naturality_assoc (F.mapShortComplex.map φ) _)
    _ = ShortComplex.cyclesMap (F.mapShortComplex.map φ) ≫
        ((cyclesIso T F).hom ≫ F.map T.homologyπ) := by rw [homologyπ_map]
    _ = (cyclesIso S F).hom ≫ F.map (ShortComplex.cyclesMap φ) ≫ F.map T.homologyπ := by
      rw [← Category.assoc, cycles_naturality, Category.assoc]
    _ = (cyclesIso S F).hom ≫ F.map S.homologyπ ≫
        F.map (ShortComplex.homologyMap φ) := by
      rw [← F.map_comp, ← ShortComplex.homologyπ_naturality, F.map_comp]
    _ = (S.map F).homologyπ ≫ (map S F ≫ F.map (ShortComplex.homologyMap φ)) :=
      (homologyπ_map_assoc S F (F.map (ShortComplex.homologyMap φ))).symm

variable {F} (G : C ⥤ D) [G.PreservesZeroMorphisms] [PreservesFiniteLimits G]

private theorem cycles_natTrans_naturality (τ : F ⟶ G) :
    ShortComplex.cyclesMap (S.mapNatTrans τ) ≫ (cyclesIso S G).hom =
      (cyclesIso S F).hom ≫ τ.app S.cycles := by
  apply (cancel_mono (G.map S.iCycles)).mp
  rw [Category.assoc, cyclesIso_hom_iCycles, ShortComplex.cyclesMap_i,
    Category.assoc, ← τ.naturality, ← Category.assoc, cyclesIso_hom_iCycles]
  rfl

/-- In particular, genuine restriction transformations retain the original homology square. -/
theorem natTrans_naturality (τ : F ⟶ G) :
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫ map S G =
      map S F ≫ τ.app S.homology := by
  apply (cancel_epi (S.map F).homologyπ).mp
  rw [← Category.assoc, ShortComplex.homologyπ_naturality, Category.assoc,
    homologyπ_map, ← Category.assoc, cycles_natTrans_naturality, Category.assoc,
    ← τ.naturality, ← Category.assoc, ← homologyπ_map, Category.assoc]

end EnvelopeProperty.LeftExactHomologyComparison
