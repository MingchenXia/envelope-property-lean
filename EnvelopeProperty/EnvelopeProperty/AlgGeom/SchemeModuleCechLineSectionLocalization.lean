import EnvelopeProperty.AlgGeom.SchemeLineSectionLocalFrames
import EnvelopeProperty.AlgGeom.SchemeSectionPreservingGluing
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionPowers

/-! # Canonical division by the original line section on its actual nonzero open

The actual section itself supplies the frame on its whole nonzero open.
Every original tensor power and every normalized restriction retains that
same section. No caller frame, open comparison or matching certificate is used.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization

open SchemeLineSectionEvaluation CanonicalGeometry
open SchemeGlobalSectionTensorPowerNorms CyclicSectionGlobalCoverRootSectionPowers

attribute [local instance] Scheme.Modules.monoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance actualPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullback f).Monoidal := pullbackMonoidal f

variable {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L)

/-- The literal complement of the zero ideal of the SAME original line section. -/
def sectionOpen : X.Opens := (LineSectionZeroIdeal.zeroIdeal L hL s).support.compl

private theorem section_isIso_of_everywhere_nonzero {Y : Scheme.{u}}
    (N : Y.Modules) (hN : IsInvertible N) (t : unitObj Y ⟶ N)
    (ht : ∀ y : Y, y ∉ (LineSectionZeroIdeal.zeroIdeal N hN t).support) :
    IsIso t := by
  classical
  choose U hx e he using fun y : Y =>
    SchemeLineSectionLocalFrames.exists_section_frame_at N hN t y (ht y)
  let E (y : Y) : (pullback (U y).ι).obj N ≅
      (pullback (U y).ι).obj (unitObj Y) :=
    e y ≪≫ (pullbackUnitIso (U y).ι).symm
  let a : PUnit.{u + 1} → (unitObj Y ⟶ N) := fun _ => t
  let b : PUnit.{u + 1} → (unitObj Y ⟶ unitObj Y) := fun _ => 𝟙 _
  have hb (y : Y) : IsIso (pullbackSectionHom (U y).ι (b PUnit.unit)) := by
    dsimp only [b, pullbackSectionHom]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    infer_instance
  have hp (y : Y) (j : PUnit.{u + 1}) :
      pullbackSectionHom (U y).ι (a j) ≫ (E y).hom =
        pullbackSectionHom (U y).ι (b j) := by
    change pullbackSectionHom (U y).ι t ≫
        (e y).hom ≫ (pullbackUnitIso (U y).ι).inv =
      (pullbackUnitIso (U y).ι).inv ≫ (pullback (U y).ι).map (𝟙 _)
    rw [← Category.assoc, he y, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  let g : N ≅ unitObj Y := SchemeSectionPreservingGluing.glueOfSections
    U (fun y => ⟨y, hx y⟩) E a b (fun _ => PUnit.unit) hb hp
  have hg : t ≫ g.hom = 𝟙 _ :=
    SchemeSectionPreservingGluing.glueOfSections_section
      U (fun y => ⟨y, hx y⟩) E a b (fun _ => PUnit.unit) hb hp PUnit.unit
  have hi : IsIso (t ≫ g.hom) := by rw [hg]; infer_instance
  let := hi
  exact IsIso.of_isIso_comp_right t g.hom

private theorem sectionOpen_isIso :
    IsIso (pullbackSectionHom (sectionOpen L hL s).ι s) := by
  let V := sectionOpen L hL s
  apply section_isIso_of_everywhere_nonzero ((pullback V.ι).obj L) (hL.pullback V.ι)
    (pullbackSectionHom V.ι s)
  intro y
  rw [SchemeLineZeroSupportPullback.support_pullback V.ι L hL s]
  exact y.property

/-- The section itself canonically frames its WHOLE actual nonzero open. -/
def sectionFrame :
    (pullback (sectionOpen L hL s).ι).obj L ≅ unitObj (sectionOpen L hL s).toScheme :=
  letI := sectionOpen_isIso L hL s
  (asIso (pullbackSectionHom (sectionOpen L hL s).ι s)).symm

/-- The SAME original section is exactly one in its canonical whole-open frame. -/
theorem sectionFrame_section :
    pullbackSectionHom (sectionOpen L hL s).ι s ≫ (sectionFrame L hL s).hom = 𝟙 _ := by
  let := sectionOpen_isIso L hL s
  exact (asIso (pullbackSectionHom (sectionOpen L hL s).ι s)).hom_inv_id

/-- The genuine native power of the SAME original whole-open section frame. -/
def powerSectionFrame (m : ℕ) :
    (pullback (sectionOpen L hL s).ι).obj (bundleTensorPower L m) ≅
      unitObj (sectionOpen L hL s).toScheme :=
  SchemePulledPowerFrames.pullbackPowerFrame (sectionOpen L hL s).ι
    (sectionFrame L hL s) m

/-- Every SAME original section power has coefficient one on its actual open. -/
theorem powerSectionFrame_section (m : ℕ) :
    pullbackSectionHom (sectionOpen L hL s).ι (powerSectionHom s m) ≫
      (powerSectionFrame L hL s m).hom = 𝟙 _ := by
  unfold powerSectionFrame SchemePulledPowerFrames.pullbackPowerFrame
  rw [Iso.trans_hom, ← Category.assoc, pullback_powerSectionHom]
  have h := powerSectionHom_frame
    (pullbackSectionHom (sectionOpen L hL s).ι s) (sectionFrame L hL s) 1
    (by rw [sectionFrame_section, ModularCurves.unitEndomorphismOfTopSection_one]) m
  simpa only [one_pow, ModularCurves.unitEndomorphismOfTopSection_one] using h

private def actualRightUnit {Y : Scheme.{u}} (M : Y.Modules) : M ⊗ unitObj Y ≅ M :=
  (Iso.refl M ⊗ᵢ (ModularCurves.monoidalUnitObjIso Y).symm) ≪≫ ρ_ M

/-- Division of the WHOLE original module twist by the SAME original s^m. -/
def normalizedTwistIso (F : X.Modules) (m : ℕ) :
    (pullback (sectionOpen L hL s).ι).obj (F ⊗ bundleTensorPower L m) ≅
      (pullback (sectionOpen L hL s).ι).obj F :=
  (Functor.Monoidal.μIso (pullback (sectionOpen L hL s).ι)
    F (bundleTensorPower L m)).symm ≪≫
      (Iso.refl _ ⊗ᵢ powerSectionFrame L hL s m) ≪≫ actualRightUnit _

private def normalizedRestrictIso (F : X.Modules) (m : ℕ) :
    (F ⊗ bundleTensorPower L m).restrict (sectionOpen L hL s).ι ≅
      F.restrict (sectionOpen L hL s).ι :=
  (restrictFunctorIsoPullback (sectionOpen L hL s).ι).app _ ≪≫
    normalizedTwistIso L hL s F m ≪≫
      ((restrictFunctorIsoPullback (sectionOpen L hL s).ι).app F).symm

/-- The actual WHOLE original sheaf restriction, normalized by the original s^m. -/
def normalizedRestriction (F : X.Modules) (m : ℕ) :
    F ⊗ bundleTensorPower L m ⟶
      (pushforward (sectionOpen L hL s).ι).obj (F.restrict (sectionOpen L hL s).ι) :=
  (restrictAdjunction (sectionOpen L hL s).ι).unit.app _ ≫
    (pushforward (sectionOpen L hL s).ι).map (normalizedRestrictIso L hL s F m).hom

include hL in
/-- Original compactness internally makes an actual finite affine cover on
which the SAME original invertible line has genuine original pullback frames. -/
theorem exists_finite_affine_frame_cover [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧
        ∀ i, Nonempty ((pullback (U i).1.ι).obj L ≅ unitObj (U i).1.toScheme) := by
  classical
  choose U hx _ he _ using fun x : X =>
    SchemeCommonAffineLineFrames.exists_in_open L (unitObj X) hL isInvertible_unit x ⊤
      (by trivial)
  have hc : (Set.univ : Set X) ⊆ ⋃ x : X, ((U x).1 : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((U x).1 : Set X)) (fun x => (U x).1.isOpen) hc
  refine ⟨a, inferInstance, fun x => U x.1, ?_, fun x => he x.1⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ha (Set.mem_univ x))
  obtain ⟨hya, hxy⟩ := Set.mem_iUnion.mp hy
  exact Opens.mem_iSup.mpr ⟨⟨y, hya⟩, hxy⟩

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
