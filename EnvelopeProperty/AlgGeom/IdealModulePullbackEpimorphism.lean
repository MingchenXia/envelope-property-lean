import EnvelopeProperty.AlgGeom.IdealModuleQuasicoherent
import EnvelopeProperty.AlgGeom.SchemeModuleAffineEpimorphisms
import EnvelopeProperty.AlgGeom.AffineIdealPullbackImage
import ModularCurves.ForMathlib.SchemeModuleEpiCover

/-! # The actual geometric ideal-module pullback comparison is always epic -/
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y Z : Scheme.{u}}

private theorem affineComparison_epi [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) : Epi (I.toModulesComapPullbackMap f) := by
  let : (I.comap f).toModules.IsQuasicoherent := (I.comap f).isQuasicoherent_toModules
  exact EnvelopeProperty.SchemeModuleAffineEpimorphisms.epi_of_appTop_surjective
    (I.toModulesComapPullbackMap f) (I.affine_toModulesComapPullbackMap_appTop_surjective f)

private theorem comparison_epi_comp (I : Z.IdealSheafData)
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso (I.toModulesComapPullbackMap g)]
    [Epi ((I.comap g).toModulesComapPullbackMap f)] :
    Epi (I.toModulesComapPullbackMap (f ≫ g)) := by
  have hc : Epi ((Scheme.Modules.pullbackComp f g).hom.app I.toModules ≫
      I.toModulesComapPullbackMap (f ≫ g) ≫
      (toModulesEqualityIso _ _ (I.comap_comp f g)).hom) := by
    rw [I.toModulesComapPullbackMap_comp f g]
    infer_instance
  have ht : Epi (I.toModulesComapPullbackMap (f ≫ g) ≫
      (toModulesEqualityIso _ _ (I.comap_comp f g)).hom) :=
    @epi_of_epi _ _ _ _ _ ((Scheme.Modules.pullbackComp f g).hom.app I.toModules) _ hc
  exact (epi_comp_iff_of_isIso _ _).mp ht

private theorem comparison_pullback_epi_of_comp (I : Z.IdealSheafData)
    (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (I.toModulesComapPullbackMap (f ≫ g))]
    [IsIso ((I.comap g).toModulesComapPullbackMap f)] :
    Epi ((Scheme.Modules.pullback f).map (I.toModulesComapPullbackMap g)) := by
  have hc : Epi ((Scheme.Modules.pullback f).map (I.toModulesComapPullbackMap g) ≫
      (I.comap g).toModulesComapPullbackMap f) := by
    rw [← I.toModulesComapPullbackMap_comp f g]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).mp hc

/-- For EVERY original geometric ideal and EVERY actual scheme morphism,
the SAME original canonical ideal-module pullback comparison is epic.
No flatness, Cartier, Noetherian, finite-type or domain premise is used. -/
theorem toModulesComapPullbackMap_epi (I : Y.IdealSheafData) (f : X ⟶ Y) :
    Epi (I.toModulesComapPullbackMap f) := by
  classical
  have hloc : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      Epi ((Scheme.Modules.restrictFunctor V.1.ι).map (I.toModulesComapPullbackMap f)) := by
    intro x
    obtain ⟨U, hxU⟩ := exists_affineOpens_mem (f x)
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ U.1 from hxU)
    let V : X.affineOpens := ⟨W, hW⟩
    have hVU : V.1 ≤ f ⁻¹ᵁ U.1 := hWU
    let r := f.resLE U.1 V.1 hVU
    let : IsAffine U.1.toScheme := U.2
    let : IsAffine V.1.toScheme := V.2
    let : IsIso (I.toModulesComapPullbackMap U.1.ι) :=
      I.toModulesComapPullbackMap_isIso_of_isOpenImmersion U.1.ι
    let : Epi ((I.comap U.1.ι).toModulesComapPullbackMap r) := affineComparison_epi _ r
    have hc : Epi (I.toModulesComapPullbackMap (r ≫ U.1.ι)) := comparison_epi_comp I r U.1.ι
    have hc' : Epi (I.toModulesComapPullbackMap (V.1.ι ≫ f)) :=
      (congrArg (fun q => Epi (I.toModulesComapPullbackMap q))
        (f.resLE_comp_ι hVU)).mp hc
    let : Epi (I.toModulesComapPullbackMap (V.1.ι ≫ f)) := hc'
    let : IsIso ((I.comap f).toModulesComapPullbackMap V.1.ι) :=
      (I.comap f).toModulesComapPullbackMap_isIso_of_isOpenImmersion V.1.ι
    have hp : Epi ((Scheme.Modules.pullback V.1.ι).map (I.toModulesComapPullbackMap f)) :=
      comparison_pullback_epi_of_comp I V.1.ι f
    let : Epi ((Scheme.Modules.pullback V.1.ι).map (I.toModulesComapPullbackMap f)) := hp
    let a := Scheme.Modules.restrictFunctorIsoPullback V.1.ι
    have he : Epi ((Scheme.Modules.restrictFunctor V.1.ι).map
        (I.toModulesComapPullbackMap f) ≫ a.hom.app (I.comap f).toModules) := by
      rw [a.hom.naturality]
      infer_instance
    exact ⟨V, hxW, (epi_comp_iff_of_isIso _ _).mp he⟩
  choose V hxV hV using hloc
  apply Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top
    (fun x => (V x).1) _ (I.toModulesComapPullbackMap f) hV
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr ⟨x, hxV x⟩

end AlgebraicGeometry.Scheme.IdealSheafData
