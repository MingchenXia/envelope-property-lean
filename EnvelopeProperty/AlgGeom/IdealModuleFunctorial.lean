/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierIdealModules
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Actual functorial module maps for the geometric ideal comap

The existing ideal module is the true whole section kernel of its actual
closed immersion. The actual pullback closed square then supplies ideal-module
section functoriality and the genuine canonical module pullback comparison.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- An actual section of the genuine kernel ideal vanishes under the entire
original scheme section map, without a quasi-compactness assumption. -/
theorem ker_isLocallyMem_app_eq_zero (f : Y ⟶ X) (W : X.Opens) (s : Γ(X, W))
    (hs : f.ker.IsLocallyMem W s) : (f.app W).hom s = 0 := by
  apply Y.IsSheaf.section_ext
  intro z hz
  obtain ⟨V, hV, hzV, hVWset⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := W) (x := f z) hz
  have hVW : V ≤ W := hVWset
  have hzero : (f.app V).hom (X.presheaf.map (homOfLE hVW).op s) = 0 :=
    f.ideal_ker_le ⟨V, hV⟩ (hs ⟨V, hV⟩ hVW)
  refine ⟨f ⁻¹ᵁ V, fun _ hp => hVW hp, hzV, ?_⟩
  have hnat : (f.app V).hom (X.presheaf.map (homOfLE hVW).op s) =
      Y.presheaf.map ((Opens.map f.base).map (homOfLE hVW)).op ((f.app W).hom s) :=
    congrArg (fun q : Γ(X, W) ⟶ Γ(Y, f ⁻¹ᵁ V) => q.hom s)
      (f.naturality (homOfLE hVW).op)
  change Y.presheaf.map ((Opens.map f.base).map (homOfLE hVW)).op
    ((f.app W).hom s) = _
  rw [map_zero]
  exact hnat.symm.trans hzero

/-- The whole actual ideal-module section condition is exactly vanishing under
the original actual closed-subscheme section map, on every original open. -/
theorem isLocallyMem_iff_subscheme_app_eq_zero (I : X.IdealSheafData)
    (W : X.Opens) (s : Γ(X, W)) :
    I.IsLocallyMem W s ↔ (I.subschemeι.app W).hom s = 0 := by
  constructor
  · intro hs
    apply ker_isLocallyMem_app_eq_zero I.subschemeι W s
    rwa [I.ker_subschemeι]
  · intro hs V hVW
    rw [← I.ker_subschemeι, Scheme.Hom.ker_apply]
    change (I.subschemeι.app V).hom (X.presheaf.map (homOfLE hVW).op s) = 0
    rw [← ConcreteCategory.comp_apply, I.subschemeι.naturality, ConcreteCategory.comp_apply, hs,
      map_zero]

/-- The actual scheme section map carries each entire original ideal-module
section into the actual geometric ideal comap on the whole original preimage. -/
theorem isLocallyMem_comap_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    (W : Y.Opens) (s : Γ(Y, W)) (hs : I.IsLocallyMem W s) :
    (I.comap f).IsLocallyMem (f ⁻¹ᵁ W) ((f.app W).hom s) := by
  apply (isLocallyMem_iff_subscheme_app_eq_zero (I.comap f) _ _).mpr
  have hm : ((I.comap f).map f).IsLocallyMem W s :=
    fun V hVW => I.le_map_comap f V (hs V hVW)
  exact ker_isLocallyMem_app_eq_zero ((I.comap f).subschemeι ≫ f) W s hm

/-- The actual ideal module includes in the original actual structure module. -/
def toModulesInclusion (I : X.IdealSheafData) :
    I.toModules ⟶ SheafOfModules.unit X.ringCatSheaf where
  val := I.toSubmodule.ι

/-- The actual ideal-module inclusion is a genuine monomorphism. -/
instance toModulesInclusion_mono (I : X.IdealSheafData) : Mono I.toModulesInclusion := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  change Mono I.toSubmodule.ι
  infer_instance

/-- The original whole scheme section maps restrict to a genuine actual
module morphism into the pushforward of the actual geometric ideal comap. -/
def toModulesComapPushforwardMap (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.toModules ⟶ (Scheme.Modules.pushforward f).obj (I.comap f).toModules where
  val := PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := fun s => ⟨(f.app W.unop).hom s.1,
            isLocallyMem_comap_app I f W.unop s.1 s.2⟩
          map_zero' := Subtype.ext (map_zero (f.app W.unop).hom)
          map_add' := fun s t => Subtype.ext (map_add (f.app W.unop).hom s.1 t.1) }
      naturality {U V} h := by
        ext s
        apply Subtype.ext
        change (f.app V.unop).hom (Y.presheaf.map h s.1) =
          X.presheaf.map ((Opens.map f.base).map h.unop).op ((f.app U.unop).hom s.1)
        exact congrArg (fun q : Γ(Y, U.unop) ⟶ Γ(X, f ⁻¹ᵁ V.unop) => q.hom s.1)
          (f.naturality h) }
    (by
      intro W r s
      apply Subtype.ext
      change (f.app W.unop).hom
        ((show Γ(Y, W.unop) from r) * (show Γ(Y, W.unop) from s.1)) =
        (f.app W.unop).hom (show Γ(Y, W.unop) from r) *
          (f.app W.unop).hom (show Γ(Y, W.unop) from s.1)
      exact map_mul (f.app W.unop).hom _ _)

/-- The actual canonical ideal-module map retains every entire original
section as its image under the true original scheme section map. -/
theorem toModulesComapPushforwardMap_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    (W : Y.Opens) (s : Γ(I.toModules, W)) :
    (show (I.comap f).toSubmodule.obj (op (f ⁻¹ᵁ W)) from
      (I.toModulesComapPushforwardMap f).app W s).1 =
      (f.app W).hom (s : I.toSubmodule.obj (op W)).1 := rfl

/-- The canonical genuine module pullback comparison for the actual geometric
ideal comap, constructed by the actual pullback/pushforward adjunction. -/
def toModulesComapPullbackMap (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj I.toModules ⟶ (I.comap f).toModules :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv I.toModules
    (I.comap f).toModules).symm (I.toModulesComapPushforwardMap f)

/-- The actual entire pushforward map is compatible with both true ideal
inclusions and the genuine structure-sheaf section map. -/
theorem toModulesComapPushforwardMap_inclusion (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.toModulesComapPushforwardMap f ≫
        (Scheme.Modules.pushforward f).map (I.comap f).toModulesInclusion =
      I.toModulesInclusion ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

/-- The canonical genuine module pullback comparison lies over the actual
canonical structure-module pullback map, on the whole original source. -/
theorem toModulesComapPullbackMap_inclusion (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.toModulesComapPullbackMap f ≫ (I.comap f).toModulesInclusion =
      (Scheme.Modules.pullback f).map I.toModulesInclusion ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  change _ = I.toModulesInclusion ≫
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  simpa only [toModulesComapPullbackMap, Equiv.apply_symm_apply] using
    I.toModulesComapPushforwardMap_inclusion f

end AlgebraicGeometry.Scheme.IdealSheafData
