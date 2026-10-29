import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeBaseScalars
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections

/-!
# Original coordinate sections generate the native line on its cover

The sections are the sheaf-glued inverse of original saturated
coordinates. Their whole unit maps equal the produced inverse frames on the
original coordinate cover. Route: owned `native-coordinate-generators-route.tex`.
-/
open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModularCurves
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CanonicalGeometry
local instance (Y : Scheme.{u}) : ∀ U, IsMulCommutative (Y.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (Y.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- A local coefficient identifies the entire section morphism
in its over-site frame. -/
theorem sectionHom_over_comp_frame {Y : Scheme.{u}} [IsIntegral Y]
    (M : Y.Modules) (U : Y.Opens) (e : LocalBundleFrame M U)
    (s : Γ(M, ⊤)) (r : Γ(Y, U))
    (h : localFrameCoefficients e
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = r) :
    (SchemeModuleGlobalSections.sectionHom M s).over U ≫ e.hom =
      (SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U r).asHom := by
  apply (SheafOfModules.dualUnitSectionsEquiv Y.ringCatSheaf U).injective
  change _ = (SheafOfModules.dualUnitSectionsEquiv Y.ringCatSheaf U)
    ((SheafOfModules.dualUnitSectionsEquiv Y.ringCatSheaf U).symm r)
  rw [Equiv.apply_symm_apply]
  change e.hom.val.app (.op (Over.mk (𝟙 U)))
    ((SchemeModuleGlobalSections.sectionHom M s).val.app (.op U)
      (show Y.presheaf.obj (.op U) from 1)) = r
  change localFrameCoefficients e
    ((1 : Γ(Y, U)) • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = r
  simpa only [one_smul] using h

/-- Coefficient one gives the whole inverse frame, not merely a pointwise
nonvanishing assertion. -/
theorem sectionHom_over_eq_frame_inv {Y : Scheme.{u}} [IsIntegral Y]
    (M : Y.Modules) (U : Y.Opens) (e : LocalBundleFrame M U)
    (s : Γ(M, ⊤))
    (h : localFrameCoefficients e
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = 1) :
    (SchemeModuleGlobalSections.sectionHom M s).over U = e.inv := by
  apply (cancel_mono e.hom).mp
  rw [e.inv_hom_id]
  apply (SheafOfModules.dualUnitSectionsEquiv Y.ringCatSheaf U).injective
  change e.hom.val.app (.op (Over.mk (𝟙 U)))
    ((SchemeModuleGlobalSections.sectionHom M s).val.app (.op U)
      (show Y.presheaf.obj (.op U) from 1)) = (1 : Γ(Y, U))
  change localFrameCoefficients e
    ((1 : Γ(Y, U)) • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = 1
  simpa only [one_smul] using h

private theorem map_isIso_of_actual_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (α : A ⟶ B) [IsIso (G.map α)] :
    IsIso (F.map α) := by
  rw [← NatIso.naturality_2 e α]
  infer_instance

/-- Over-site local invertibility implies invertibility of the
open-subscheme restriction of the same original morphism. -/
theorem isIso_restrict_of_isIso_over {Y : Scheme.{u}} {P Q : Y.Modules}
    (α : P ⟶ Q) (U : Y.Opens) [IsIso (α.over U)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  have : IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U ⋙
      (Scheme.Modules.overEquiv U).functor).map α) :=
    inferInstanceAs (IsIso ((Scheme.Modules.overEquiv U).functor.map (α.over U)))
  exact map_isIso_of_actual_natIso (Scheme.Modules.overFunctorEquiv U).symm α

/-- Sheaf pullback to an original open preserves this proved local
invertibility through the restriction/pullback comparison. -/
theorem isIso_pullback_of_isIso_over {Y : Scheme.{u}} {P Q : Y.Modules}
    (α : P ⟶ Q) (U : Y.Opens) [IsIso (α.over U)] :
    IsIso ((Scheme.Modules.pullback U.ι).map α) := by
  have := isIso_restrict_of_isIso_over α U
  exact map_isIso_of_actual_natIso (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm α
end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- Each original coordinate is in the original full saturated degree-one
space, independently of native frame or section matching data. -/
def nativeRankOneOriginalCoordinateSection (t : Fin (X.M 0 + 1)) :
    X.sections (1 : Fin 1 → ℤ) :=
  ⟨X.coord 0 t, X.mem_sections_of_mem_piece (d := Finsupp.single 0 1)
    (by intro c; have hc : c = 0 := Subsingleton.elim _ _; subst c; simp)
    (X.coord_mem_piece 0 t)⟩

/-- The same original coordinate becomes a native global section
by the proved sheaf-gluing inverse. -/
def nativeRankOneCoordinateGlobalSection (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (t : Fin (X.M 0 + 1)) :
    Γ(X.nativeRankOneCoordinateLine j, ⊤) :=
  X.nativeRankOneGlobalSectionOfOriginal j hj (X.nativeRankOneOriginalCoordinateSection t)

/-- Its global rational coefficient is literally the original coordinate. -/
theorem nativeRankOneCoordinateGlobalSection_coefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (t : Fin (X.M 0 + 1)) :
    X.nativeRankOneGlobalSectionCoefficient i hi j hj
      (X.nativeRankOneCoordinateGlobalSection j hj t) = X.coord 0 t :=
  X.nativeRankOneGlobalSectionOfOriginal_coefficient i hi j hj _

/-- Its local frame coefficient is the same original c_t/c_i. -/
theorem nativeRankOneCoordinateGlobalSection_local (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (t : Fin (X.M 0 + 1)) :
    localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame i hi j hj)
      ((X.nativeRankOneCoordinateLine j).presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
        (X.nativeRankOneCoordinateGlobalSection j hj t)) =
      (X.nativeRankOneOriginalSectionsIso i hi).hom
        ⟨X.coord 0 t / X.coord 0 (i 0), X.coord_div_mem_chartAlg i 0 t⟩ := by
  unfold nativeRankOneCoordinateGlobalSection
  rw [X.nativeRankOneGlobalSectionOfOriginal_restrict i hi j hj _,
    X.nativeRankOneLocalSectionOfOriginal_coefficient i hi j hj _]
  rfl

/-- The global coordinate unit map of the native line. -/
def nativeRankOneCoordinateGlobalUnitHom (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (t : Fin (X.M 0 + 1)) :
    Scheme.Modules.unitObj X.nativeRankOneScheme ⟶ X.nativeRankOneCoordinateLine j :=
  SchemeModuleGlobalSections.sectionHom _ (X.nativeRankOneCoordinateGlobalSection j hj t)

/-- The entire coordinate unit map in the frame has the
original coordinate ratio as scalar. -/
theorem nativeRankOneCoordinateGlobalUnitHom_frame (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (t : Fin (X.M 0 + 1)) :
    (X.nativeRankOneCoordinateGlobalUnitHom j hj t).over
        (X.nativeRankOneCoordinateOpen (i 0)) ≫
      (X.nativeRankOneCoordinateLineOverFrame i hi j hj).hom =
      (SheafOfModules.overUnitScalarEnd X.nativeRankOneScheme.ringCatSheaf
        (X.nativeRankOneCoordinateOpen (i 0))
        ((X.nativeRankOneOriginalSectionsIso i hi).hom
          ⟨X.coord 0 t / X.coord 0 (i 0), X.coord_div_mem_chartAlg i 0 t⟩)).asHom :=
  sectionHom_over_comp_frame _ _ _ _ _
    (X.nativeRankOneCoordinateGlobalSection_local i hi j hj t)

/-- The self-coordinate unit map is exactly the inverse
frame on its original coordinate open. -/
theorem nativeRankOneCoordinateGlobalUnitHom_self (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    (X.nativeRankOneCoordinateGlobalUnitHom j hj (i 0)).over
        (X.nativeRankOneCoordinateOpen (i 0)) =
      (X.nativeRankOneCoordinateLineOverFrame i hi j hj).inv := by
  apply sectionHom_over_eq_frame_inv
  rw [X.nativeRankOneCoordinateGlobalSection_local i hi j hj (i 0)]
  have hone : (⟨X.coord 0 (i 0) / X.coord 0 (i 0),
      X.coord_div_mem_chartAlg i 0 (i 0)⟩ : X.chartAlg i) = 1 :=
    Subtype.ext (div_self (hi 0))
  rw [hone, map_one]

/-- The original coordinates give locally invertible global unit
maps on the native scheme, with the original nonzero chart cover. -/
theorem nativeRankOne_existsCoordinateGlobalGenerator (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (y : X.nativeRankOneScheme) :
    ∃ (i : X.ChartIndex) (_hi : ∀ c, X.coord c (i c) ≠ 0),
      y ∈ X.nativeRankOneCoordinateOpen (i 0) ∧
      IsIso ((X.nativeRankOneCoordinateGlobalUnitHom j hj (i 0)).over
        (X.nativeRankOneCoordinateOpen (i 0))) := by
  have hy : y ∈ ⨆ t : Fin (X.M 0 + 1), X.nativeRankOneCoordinateOpen t := by
    rw [X.nativeRankOne_iSup_coordinateOpen]
    trivial
  obtain ⟨t, ht⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have ht0 : X.coord 0 t ≠ 0 := by
    intro hz
    have he : X.coordElem ⟨0, t⟩ = 0 := Subtype.ext (by simp [hz])
    change X.coordElem ⟨0, t⟩ ∉ y.asHomogeneousIdeal at ht
    exact ht (he ▸ zero_mem y.asHomogeneousIdeal.toIdeal)
  let i : X.ChartIndex := fun c => (Subsingleton.elim (0 : Fin 1) c) ▸ t
  have hi : ∀ c, X.coord c (i c) ≠ 0 := by
    intro c
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    exact ht0
  refine ⟨i, hi, ht, ?_⟩
  rw [X.nativeRankOneCoordinateGlobalUnitHom_self i hi j hj]
  infer_instance

/-- The same coordinate unit map is invertible after sheaf
pullback to its original coordinate open. -/
theorem nativeRankOneCoordinateGlobalUnitHom_pullback_isIso (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    IsIso ((Scheme.Modules.pullback (X.nativeRankOneCoordinateOpen (i 0)).ι).map
      (X.nativeRankOneCoordinateGlobalUnitHom j hj (i 0))) := by
  have : IsIso ((X.nativeRankOneCoordinateGlobalUnitHom j hj (i 0)).over
      (X.nativeRankOneCoordinateOpen (i 0))) := by
    rw [X.nativeRankOneCoordinateGlobalUnitHom_self i hi j hj]
    infer_instance
  exact isIso_pullback_of_isIso_over _ _
end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.CanonicalGeometry.sectionHom_over_comp_frame
#print axioms EnvelopeProperty.CanonicalGeometry.sectionHom_over_comp_frame
#check @EnvelopeProperty.CanonicalGeometry.sectionHom_over_eq_frame_inv
#print axioms EnvelopeProperty.CanonicalGeometry.sectionHom_over_eq_frame_inv
#check @EnvelopeProperty.CanonicalGeometry.isIso_restrict_of_isIso_over
#print axioms EnvelopeProperty.CanonicalGeometry.isIso_restrict_of_isIso_over
#check @EnvelopeProperty.CanonicalGeometry.isIso_pullback_of_isIso_over
#print axioms EnvelopeProperty.CanonicalGeometry.isIso_pullback_of_isIso_over
#check @EnvelopeProperty.MultiModel.nativeRankOneOriginalCoordinateSection
#print axioms EnvelopeProperty.MultiModel.nativeRankOneOriginalCoordinateSection
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalSection
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalSection
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalSection_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalSection_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalSection_local
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalSection_local
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom_frame
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom_frame
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom_self
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom_self
#check @EnvelopeProperty.MultiModel.nativeRankOne_existsCoordinateGlobalGenerator
#print axioms EnvelopeProperty.MultiModel.nativeRankOne_existsCoordinateGlobalGenerator
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom_pullback_isIso
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateGlobalUnitHom_pullback_isIso
