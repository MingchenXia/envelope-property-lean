import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationExact
import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology

/-! # Actual higher vanishing on the original line section's nonzero open

Eventual global vanishing of the SAME original line twists gives genuine
ordinary higher sheaf cohomology vanishing on the literal original
nonzero-section open. All finite covers, tuple denominators, zero-clearing,
original module comparisons and native higher-H comparisons are internal.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits (IsZero)
open TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization
open CanonicalGeometry SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- In EVERY positive degree, eventual global vanishing of actual original
F tensor L^m implies actual ordinary native higher cohomology vanishing of
SAME original F restricted to the literal nonzero-open of SAME original s.
Only original geometry and original eventual GLOBAL vanishing are inputs;
no caller affine cover, local matching, localization or LOCAL acyclicity
certificate is assumed. -/
theorem sectionOpen_restrict_H_succ_subsingleton {X : Scheme.{u}} [CompactSpace X]
    [X.IsSeparated] (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    (hH : ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H (F ⊗ bundleTensorPower L m).sheaf (q + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H
      (F.restrict (sectionOpen L hL s).ι).sheaf (q + 1)) := by
  classical
  obtain ⟨I, hI, U, hU, hUa, he, hExact⟩ := exists_finite_normalized_cech_exactAt L hL s F q hH
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let V := sectionOpen L hL s
  let M := (pullback V.ι).obj F
  let G := (pushforward V.ι).obj M
  let UV : I → V.toScheme.Opens := fun i => V.ι ⁻¹ᵁ U i
  let : V.toScheme.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from V.ι]
    infer_instance⟩
  let : M.IsQuasicoherent := (isQuasicoherent V.toScheme).prop_of_iso
    ((restrictFunctorIsoPullback V.ι).app F) inferInstance
  have hUV : IsOpenCover UV := V.ι.iSup_preimage_eq_top hU
  have hUVa (i : I) : IsAffineOpen (UV i) :=
    sectionOpen_preimage_affine_of_frame L hL s ⟨U i, hUa i⟩ (he i).some
  have hz : IsZero ((baseCechComplex (𝟙 X) G U).homology (q + 1)) := hExact.isZero_homology
  have hzo : IsZero ((orderedBaseCechComplex (𝟙 X) G U).homology (q + 1)) :=
    IsZero.of_iso hz (baseCechOrderedHomologyIso (𝟙 X) G U (q + 1)).symm
  have hzV : IsZero ((orderedBaseCechComplex (V.ι ≫ 𝟙 X) M UV).homology (q + 1)) :=
    IsZero.of_iso hzo (HomologicalComplex.homologyMapIso
      (orderedBaseCechComplexPushforwardIso V.ι (𝟙 X) M U) (q + 1))
  have hM : Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) :=
    (AffinePushforwardCohomology.subsingleton_H_iff_ordered_zero (V.ι ≫ 𝟙 X) M UV hUV hUVa q).mpr hzV
  let E := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology V.toScheme) (q + 1)).mapIso
    ((SheafOfModules.toSheaf V.toScheme.ringCatSheaf).mapIso ((restrictFunctorIsoPullback V.ι).app F))
  let : Subsingleton ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology V.toScheme)
    (q + 1)).obj ((SheafOfModules.toSheaf V.toScheme.ringCatSheaf).obj M)) := hM
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso E.hom).1 (Subsingleton.elim _ _)⟩

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
