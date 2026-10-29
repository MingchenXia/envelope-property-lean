/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.IdealModulePullbackComp
import EnvelopeProperty.AlgGeom.AffineCartierModulePullback

/-! # Actual global canonical flat pullback of Cartier ideal module sheaves -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- Genuine affine pairs make the actual whole restriction of the original
canonical flat Cartier comparison an isomorphism. -/
theorem IsInvertible.toModulesComapPullbackMap_isIso_on_affine_pair
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f : X ⟶ Y) [Flat f]
    (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    IsIso ((Scheme.Modules.restrictFunctor U.1.ι).map (I.toModulesComapPullbackMap f)) := by
  let r := f.resLE V.1 U.1 hUV
  have : IsAffine U.1 := U.2
  have : IsAffine V.1 := V.2
  have hr : IsIso ((I.comap V.1.ι).toModulesComapPullbackMap r) :=
    (hI.comap_of_flat V.1.ι).affine_toModulesComapPullbackMap_isIso r
  have hc : IsIso (I.toModulesComapPullbackMap (r ≫ V.1.ι)) :=
    I.toModulesComapPullbackMap_isIso_comp r V.1.ι
      (I.toModulesComapPullbackMap_isIso_of_isOpenImmersion V.1.ι) hr
  have hc' : IsIso (I.toModulesComapPullbackMap (U.1.ι ≫ f)) := by
    exact (congrArg (fun q : U.1.toScheme ⟶ Y =>
      IsIso (I.toModulesComapPullbackMap q)) (f.resLE_comp_ι hUV)).mp hc
  have hp : IsIso ((Scheme.Modules.pullback U.1.ι).map (I.toModulesComapPullbackMap f)) :=
    I.toModulesComapPullbackMap_isIso_pullback_of_comp U.1.ι f hc'
      ((I.comap f).toModulesComapPullbackMap_isIso_of_isOpenImmersion U.1.ι)
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.1.ι) _).mpr hp

/-- The genuine original canonical ideal-module comparison is an isomorphism
for every actual effective Cartier ideal under every actual flat scheme morphism. -/
theorem IsInvertible.toModulesComapPullbackMap_isIso
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f : X ⟶ Y) [Flat f] :
    IsIso (I.toModulesComapPullbackMap f) := by
  classical
  have hloc : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      IsIso ((Scheme.Modules.restrictFunctor U.1.ι).map (I.toModulesComapPullbackMap f)) := by
    intro x
    obtain ⟨V, hV⟩ := exists_affineOpens_mem (f x)
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ V.1 from hV)
    exact ⟨⟨W, hW⟩, hxW,
      hI.toModulesComapPullbackMap_isIso_on_affine_pair f V ⟨W, hW⟩ hWV⟩
  choose U hxU hU using hloc
  apply Scheme.Modules.isIso_of_isIso_restrict (I.toModulesComapPullbackMap f)
    (fun x => (U x).1) _ hU
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- Actual global canonical flat base-change isomorphism of the original
Cartier ideal module and the entire genuine geometric ideal pullback module. -/
def IsInvertible.flatPullbackModuleIso {I : Y.IdealSheafData} (hI : I.IsInvertible)
    (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).obj I.toModules ≅ (I.comap f).toModules := by
  let := hI.toModulesComapPullbackMap_isIso f
  exact asIso (I.toModulesComapPullbackMap f)

end AlgebraicGeometry.Scheme.IdealSheafData
