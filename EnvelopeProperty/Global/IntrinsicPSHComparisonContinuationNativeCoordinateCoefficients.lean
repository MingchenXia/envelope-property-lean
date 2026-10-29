import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeCoordinateFrames
import EnvelopeProperty.AlgGeom.Canonical.LineSectionRatios
import EnvelopeProperty.Global.WeightedNorm

/-!
# Actual coordinate-frame coefficients and native global sections

The actual over-site frame is used directly. No open-subscheme carrier
normalization or frame-matching certificate is involved. The mathematical
route is in the owned audit `native-coordinate-coefficients-route.tex`.
-/

open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModularCurves
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CanonicalGeometry

/-- Evaluate an entire actual scalar-map identity directly in its over-site
frame. This uses only true naturality and evaluation at one. -/
theorem localFrameCoefficients_unitHom_apply_one
    {Y : Scheme.{u}} [IsIntegral Y] (M : Y.Modules) (U : Y.Opens)
    (f : Scheme.Modules.unitObj Y ⟶ M) (e : LocalBundleFrame M U)
    (r : Γ(Y, U))
    (h : f.over U ≫ e.hom =
      (SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U r).asHom) :
    localFrameCoefficients e
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (f.val.app (.op ⊤) (show Γ(Y, ⊤) from 1))) = r := by
  let m := f.val.app (.op ⊤) (show Y.presheaf.obj (.op ⊤) from 1)
  change e.hom.val.app (.op (Over.mk (𝟙 U)))
    (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m) = r
  have hnat := PresheafOfModules.naturality_apply f.val
    (homOfLE (le_top : U ≤ ⊤)).op (show Y.presheaf.obj (.op ⊤) from 1)
  let oneU : (Scheme.Modules.unitObj Y).val.obj (.op U) :=
    show Y.presheaf.obj (.op U) from 1
  have honeRestrict : (Scheme.Modules.unitObj Y).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op
      (show Y.presheaf.obj (.op ⊤) from 1) = oneU := by
    change Y.presheaf.map (homOfLE le_top).op 1 = 1
    exact map_one _
  have hnat' : f.val.app (.op U) oneU =
      M.presheaf.map (homOfLE le_top).op m :=
    (congrArg (fun a => f.val.app (.op U) a) honeRestrict.symm).trans hnat
  have happ := congrArg (fun q => q.val.app (.op (Over.mk (𝟙 U)))) h
  let oneRing : Y.ringCatSheaf.obj.obj (.op U) := by
    change Y.presheaf.obj (.op U)
    exact 1
  have hone := ConcreteCategory.congr_hom happ oneRing
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hone
  erw [SheafOfModules.overUnitScalarEnd_app_apply] at hone
  have hover : (f.over U).val.app (.op (Over.mk (𝟙 U))) oneRing =
      f.val.app (.op U) oneU := rfl
  let rRing : Y.ringCatSheaf.obj.obj (.op U) := by
    change Y.presheaf.obj (.op U)
    exact r
  have hrOver : Y.ringCatSheaf.obj.map
      (Opposite.unop (.op (Over.mk (𝟙 U)))).hom.op r = rRing := by
    rw [Subsingleton.elim (Opposite.unop (.op (Over.mk (𝟙 U)))).hom.op
      (𝟙 (Opposite.op U))]
    exact (ConcreteCategory.congr_hom (Y.ringCatSheaf.obj.map_id (.op U)) r).trans rfl
  rw [hrOver] at hone
  have honeMul : oneRing * rRing = rRing := by
    change (1 : Y.presheaf.obj (.op U)) * r = r
    exact one_mul r
  change e.hom.val.app (.op (Over.mk (𝟙 U)))
    ((f.over U).val.app (.op (Over.mk (𝟙 U))) oneRing) = oneRing * rRing at hone
  rw [honeMul] at hone
  exact (congrArg (fun a => e.hom.val.app (.op (Over.mk (𝟙 U))) a)
    hnat'.symm).trans
      ((congrArg (fun a => e.hom.val.app (.op (Over.mk (𝟙 U))) a)
        hover.symm).trans hone)

end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- The actual local regular coefficient of the canonical original pole
section in its produced genuine over-site frame. -/
theorem nativeRankOneCoordinatePoleSection_coefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame i hi j hj)
      ((X.nativeRankOneCoordinateLine j).presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
        (X.nativeRankOneCoordinatePoleSection j)) =
      X.nativeRankOneHyperplaneLocalEquation (i 0) j :=
  localFrameCoefficients_unitHom_apply_one (X.nativeRankOneCoordinateLine j)
    (X.nativeRankOneCoordinateOpen (i 0)) (X.nativeRankOneCoordinatePoleUnitHom j)
    (X.nativeRankOneCoordinateLineOverFrame i hi j hj)
    (X.nativeRankOneHyperplaneLocalEquation (i 0) j)
    (X.nativeRankOneCoordinatePoleUnitHom_frame i hi j hj)

/-- The genuine canonical section is nonzero, proved from its literal
original coordinate coefficient on an actual nonempty chart. -/
theorem nativeRankOneCoordinatePoleSection_ne_zero (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) : X.nativeRankOneCoordinatePoleSection j ≠ 0 := by
  obtain ⟨i, hi⟩ := X.exists_chartIndex_ne_zero
  intro hz
  have hc := X.nativeRankOneCoordinatePoleSection_coefficient i hi j hj
  rw [hz, map_zero, map_zero] at hc
  exact X.nativeRankOneHyperplaneLocalEquation_ne_zero i hi j hj hc.symm

/-- Its actual generic frame coefficient is the literal original ratio. -/
theorem nativeRankOneCoordinatePoleSection_generic (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    letI := X.nativeRankOneCoordinateOpen_nonempty i hi
    globalSectionToFunctionField (X.nativeRankOneCoordinateLineOverFrame i hi j hj)
      (X.nativeRankOneCoordinatePoleSection j) =
      X.nativeRankOneFunctionFieldEquiv i hi (X.coord 0 j / X.coord 0 (i 0)) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  change X.nativeRankOneGenericGerm i hi
    (localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame i hi j hj)
      ((X.nativeRankOneCoordinateLine j).presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
        (X.nativeRankOneCoordinatePoleSection j))) = _
  rw [X.nativeRankOneCoordinatePoleSection_coefficient]
  exact X.nativeRankOneHyperplaneLocalEquation_generic i hi j

/-- Every actual local section has its intrinsic normalized rational
coefficient computed by the actual original coordinate frame. -/
theorem nativeRankOneCoordinateSectionRatio_formula (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (s : Γ(X.nativeRankOneCoordinateLine j, X.nativeRankOneCoordinateOpen (i 0))) :
    letI := X.nativeRankOneCoordinateOpen_nonempty i hi
    sectionRatio (X.nativeRankOneCoordinateLine j) (X.nativeRankOneCoordinateLine_isInvertible j hj)
      (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj)
      (X.nativeRankOneCoordinateOpen (i 0)) s =
      X.nativeRankOneGenericGerm i hi
        (localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame i hi j hj) s) /
        X.nativeRankOneFunctionFieldEquiv i hi (X.coord 0 j / X.coord 0 (i 0)) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  rw [sectionRatio_frame_formula _ _ _ _ (X.nativeRankOneCoordinateLineOverFrame i hi j hj),
    X.nativeRankOneCoordinatePoleSection_generic]
  rfl

/-- The original rational coefficient of every actual native global
coordinate-line section, normalized by the canonical original section. -/
def nativeRankOneGlobalSectionCoefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (s : Γ(X.nativeRankOneCoordinateLine j, ⊤)) : K :=
  X.coord 0 j * (X.nativeRankOneFunctionFieldEquiv i hi).symm
    (sectionRatio (X.nativeRankOneCoordinateLine j) (X.nativeRankOneCoordinateLine_isInvertible j hj)
      (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj) ⊤ s)

/-- On every original nonzero chart, the entire original rational coefficient
has exactly the actual regular frame coefficient, transported back by the
proved actual chart-ring isomorphism. -/
theorem nativeRankOneGlobalSectionCoefficient_local (i l : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (hl : ∀ c, X.coord c (l c) ≠ 0)
    (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (s : Γ(X.nativeRankOneCoordinateLine j, ⊤)) :
    X.nativeRankOneGlobalSectionCoefficient i hi j hj s / X.coord 0 (l 0) =
      ((X.nativeRankOneOriginalSectionsIso l hl).inv
        (localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame l hl j hj)
          ((X.nativeRankOneCoordinateLine j).presheaf.map
            (homOfLE (le_top : X.nativeRankOneCoordinateOpen (l 0) ≤ ⊤)).op s)) : X.chartAlg l) := by
  have := X.nativeRankOneCoordinateOpen_nonempty l hl
  let t := (X.nativeRankOneCoordinateLine j).presheaf.map
    (homOfLE (le_top : X.nativeRankOneCoordinateOpen (l 0) ≤ ⊤)).op s
  let b := localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame l hl j hj) t
  have hq := (sectionRatio_restrict (X.nativeRankOneCoordinateLine j)
    (X.nativeRankOneCoordinateLine_isInvertible j hj)
    (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj)
    (le_top : X.nativeRankOneCoordinateOpen (l 0) ≤ ⊤) s).symm
  rw [X.nativeRankOneCoordinateSectionRatio_formula l hl j hj] at hq
  have he := congrArg (X.nativeRankOneFunctionFieldEquiv l hl).symm hq
  rw [map_div₀, X.nativeRankOneFunctionFieldEquiv_symm_germ,
    RingEquiv.symm_apply_apply] at he
  unfold nativeRankOneGlobalSectionCoefficient
  rw [X.nativeRankOneFunctionFieldEquiv_independent i l hi hl, he]
  change X.coord 0 j *
    (((X.nativeRankOneOriginalSectionsIso l hl).inv b : X.chartAlg l) /
      (X.coord 0 j / X.coord 0 (l 0))) / X.coord 0 (l 0) = _
  field_simp [hj, hl 0]; rfl

/-- Every actual native global section is an ORIGINAL saturated degree-one
section; the full saturation criterion is proved from all actual charts. -/
theorem nativeRankOneGlobalSectionCoefficient_mem_sections (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (s : Γ(X.nativeRankOneCoordinateLine j, ⊤)) :
    X.nativeRankOneGlobalSectionCoefficient i hi j hj s ∈ X.sections (1 : Fin 1 → ℤ) := by
  apply X.mem_sections_of_forall_div_chartDenZ
  intro l hl
  have hden : X.chartDenZ l (1 : Fin 1 → ℤ) = X.coord 0 (l 0) := by
    simp only [chartDenZ, Fin.prod_univ_one, Pi.one_apply, zpow_one]
  rw [hden, X.nativeRankOneGlobalSectionCoefficient_local i l hi hl j hj s]
  exact Subtype.property _

/-- The actual native H0 coefficient is faithful; no injectivity hypothesis
is supplied. -/
theorem nativeRankOneGlobalSectionCoefficient_injective (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    Function.Injective (X.nativeRankOneGlobalSectionCoefficient i hi j hj) := by
  intro s t h
  apply sectionRatio_injective (X.nativeRankOneCoordinateLine j)
    (X.nativeRankOneCoordinateLine_isInvertible j hj)
    (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj) ⊤
  apply (X.nativeRankOneFunctionFieldEquiv i hi).symm.injective
  exact mul_left_cancel₀ hj h

end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.CanonicalGeometry.localFrameCoefficients_unitHom_apply_one
#print axioms EnvelopeProperty.CanonicalGeometry.localFrameCoefficients_unitHom_apply_one
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleSection_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleSection_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleSection_ne_zero
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleSection_ne_zero
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleSection_generic
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleSection_generic
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateSectionRatio_formula
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateSectionRatio_formula
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_local
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_local
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_mem_sections
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_mem_sections
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_injective
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionCoefficient_injective
