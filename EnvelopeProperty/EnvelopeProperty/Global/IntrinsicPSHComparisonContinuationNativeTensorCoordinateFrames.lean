import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeCoordinateCoefficients
import EnvelopeProperty.AlgGeom.Canonical.BundleTensorLocalization
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading

/-!
# Actual tensor-coordinate frames and canonical section powers

The generic tensor-frame readback proof is adapted from indexed
BingWangEntropy/LineBundleSectionRing.lean, SHA256
2f485143af9c6856f7a090f2b843198b8ec79d1c0c0fa47a04405e3f213ce460.
It uses the SAME already ported actual sheafified tensor/localization objects.
Actual native coordinate applications discharge the coefficient identity
with the previously proved true original dual-generator frame.
Route: owned `native-tensor-coordinate-frames-route.tex`.
-/
open scoped Classical TensorProduct
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CanonicalGeometry
variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The constructed open-site recovery isomorphism has the actual adjunction
counit as its forward map. -/
private theorem bundleOverCounitIso_hom (U : X.Opens)
    (S : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    (bundleOverCounitIso U S).hom =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app S := by
  unfold bundleOverCounitIso
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse open comparison is the actual adjoint lift of the restricted
global sheafification unit. -/
private theorem bundleOverSheafificationIso_inv (P : X.PresheafOfModules) (U : X.Opens) :
    (bundleOverSheafificationIso P U).inv =
      (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).map
        (bundleSheafificationOverMap P U) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
        (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U) := by
  unfold bundleOverSheafificationIso
  simp only [Iso.symm_inv, Iso.trans_hom, asIso_hom, bundleOverCounitIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison corresponds to the restricted unit under the
actual open-site sheafification adjunction. -/
private theorem bundleOverSheafificationIso_inv_homEquiv (P : X.PresheafOfModules) (U : X.Opens) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv
      (bundlePresheafOver P U)
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U)
      (bundleOverSheafificationIso P U).inv = bundleSheafificationOverMap P U := by
  rw [bundleOverSheafificationIso_inv]
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv (bundlePresheafOver P U)
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U)
      |>.apply_symm_apply
      (bundleSheafificationOverMap P U)

set_option backward.isDefEq.respectTransparency false in
/-- The open comparison carries the restricted global unit to the local unit. -/
private theorem bundleOverSheafificationIso_unit (P : X.PresheafOfModules) (U : X.Opens) :
    bundleSheafificationOverMap P U ≫ (bundleOverSheafificationIso P U).hom.val =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).unit.app (bundlePresheafOver P U) := by
  have h := bundleOverSheafificationIso_inv_homEquiv P U
  rw [Adjunction.homEquiv_apply] at h
  rw [← h, Category.assoc]
  change _ ≫ (bundleOverSheafificationIso P U).inv.val ≫
    (bundleOverSheafificationIso P U).hom.val = _
  rw [← SheafOfModules.comp_val, Iso.inv_hom_id]
  rfl

local instance (U : X.Opens) :
    MonoidalCategory (PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
  PresheafOfModules.monoidalCategory (R := (Over.forget U).op ⋙ X.sheaf.obj)

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor-frame map before sheafification. -/
private def tensorFramePresheafIso {L N : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) :
    bundlePresheafOver (bundleTensorPresheaf L N) U ≅
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val :=
  bundleOverTensorPresheafIso L N U ≪≫
    MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
      ((SheafOfModules.forget _).mapIso f) ≪≫
    MonoidalCategory.leftUnitor (SheafOfModules.unit (X.ringCatSheaf.over U)).val

set_option backward.isDefEq.respectTransparency false in
/-- The constructed tensor frame is the actual adjoint lift of its tensor
coefficient map, transported across open restriction. -/
private theorem LocalBundleFrame.tensor_hom {L N : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) :
    (e.tensor f).hom =
      (bundleOverSheafificationIso (bundleTensorPresheaf L N) U).hom ≫
      (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).map
        (tensorFramePresheafIso e f).hom ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
        (SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  unfold LocalBundleFrame.tensor tensorFramePresheafIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, bundleOverCounitIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Applying the tensor frame to the actual sheafification unit recovers the
presheaf tensor coefficient morphism. -/
private theorem LocalBundleFrame.tensor_unit {L N : X.Modules} {U : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) :
    bundleSheafificationOverMap (bundleTensorPresheaf L N) U ≫ (e.tensor f).hom.val =
      (tensorFramePresheafIso e f).hom := by
  rw [LocalBundleFrame.tensor_hom]
  simp only [SheafOfModules.comp_val]
  rw [← Category.assoc, ← Category.assoc, bundleOverSheafificationIso_unit, Category.assoc]
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv
      (bundlePresheafOver (bundleTensorPresheaf L N) U)
      (SheafOfModules.unit (X.ringCatSheaf.over U)) |>.apply_symm_apply
        (tensorFramePresheafIso e f).hom

set_option backward.isDefEq.respectTransparency false in
/-- The actual presheaf tensor-frame map multiplies pure-tensor coefficients. -/
private theorem tensorFramePresheafIso_tmul {L N : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) (i : V ⟶ U)
    (s : bundleSections L V) (t : bundleSections N V) :
    ((tensorFramePresheafIso e f).hom.app (op (Over.mk i))).hom
      (s ⊗ₜ[X.sheaf.obj.obj (op V)] t) = e.coefficients i s * f.coefficients i t := by
  change (MonoidalCategory.leftUnitor
    (ModuleCat.of (X.sheaf.obj.obj (op V)) (X.sheaf.obj.obj (op V)))).hom
      (e.coefficients i s ⊗ₜ[X.sheaf.obj.obj (op V)] f.coefficients i t) = _
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constructed local tensor frame multiplies coefficients of the actual
sheafified pure-tensor section. -/
theorem LocalBundleFrame.tensor_coefficients {L N : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame N U) (i : V ⟶ U)
    (s : bundleSections L V) (t : bundleSections N V) :
    (e.tensor f).coefficients i (tensorSection L N V s t) =
      e.coefficients i s * f.coefficients i t := by
  have h := congrArg (fun q => (q.app (op (Over.mk i))).hom
    (s ⊗ₜ[X.sheaf.obj.obj (op V)] t)) (e.tensor_unit f)
  exact h.trans (tensorFramePresheafIso_tmul e f i s t)

/-- The SAME actual global section tensor powers: genuine structure section
one in degree zero and actual sheafified section tensors thereafter. -/
def actualSectionTensorPower (L : X.Modules) (s : Γ(L, ⊤)) :
    (m : ℕ) → Γ(bundleTensorPower L m, ⊤)
  | 0 => show Γ(X, ⊤) from 1
  | m + 1 => bundlePowerSectionMul L m ⊤ (actualSectionTensorPower L s m) s

/-- Actual section tensor powers have precisely the powers of their actual
original coefficient in the genuinely produced tensor-power frame. -/
theorem actualSectionTensorPower_coefficients (L : X.Modules) (U : X.Opens)
    (e : LocalBundleFrame L U) (s : Γ(L, ⊤)) (r : Γ(X, U))
    (h : e.coefficients (𝟙 U)
      (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = r) (m : ℕ) :
    (e.tensorPower m).coefficients (𝟙 U)
      ((bundleTensorPower L m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (actualSectionTensorPower L s m)) = r ^ m := by
  induction m with
  | zero =>
    rw [pow_zero]
    change X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1 = 1
    exact map_one _
  | succ m ih =>
    change ((e.tensorPower m).tensor e).coefficients (𝟙 U)
      ((bundleTensorPower L (m + 1)).val.map (homOfLE (le_top : U ≤ ⊤)).op
        (bundlePowerSectionMul L m ⊤ (actualSectionTensorPower L s m) s)) = _
    rw [bundlePowerSectionMul_restrict]
    change ((e.tensorPower m).tensor e).coefficients (𝟙 U)
      (tensorSection (bundleTensorPower L m) L U
        ((bundleTensorPower L m).val.map (homOfLE (le_top : U ≤ ⊤)).op
          (actualSectionTensorPower L s m))
        (L.val.map (homOfLE (le_top : U ≤ ⊤)).op s)) = _
    rw [LocalBundleFrame.tensor_coefficients]
    change (e.tensorPower m).coefficients (𝟙 U)
      ((bundleTensorPower L m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (actualSectionTensorPower L s m)) *
      e.coefficients (𝟙 U) (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) = _
    rw [ih, h, pow_succ]
end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- The actual original coordinate frame in EVERY genuine tensor power,
constructed by the SAME sheafification/open-site tensor comparison. -/
def nativeRankOneCoordinateTensorFrame (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ) :
    LocalBundleFrame (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
      (X.nativeRankOneCoordinateOpen (i 0)) :=
  LocalBundleFrame.tensorPower (X.nativeRankOneCoordinateLineOverFrame i hi j hj) m

/-- The SAME actual canonical dual-coordinate section in every genuine
actual tensor power of the SAME native coordinate line. -/
def nativeRankOneCoordinatePoleTensorPower (j : Fin (X.M 0 + 1)) (m : ℕ) :
    Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤) :=
  actualSectionTensorPower _ (X.nativeRankOneCoordinatePoleSection j) m

/-- Its true actual tensor-frame coefficient is EXACTLY the power of the
SAME original actual coordinate-hyperplane equation. -/
theorem nativeRankOneCoordinatePoleTensorPower_coefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ) :
    localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame i hi j hj m)
      ((bundleTensorPower (X.nativeRankOneCoordinateLine j) m).presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
        (X.nativeRankOneCoordinatePoleTensorPower j m)) =
      X.nativeRankOneHyperplaneLocalEquation (i 0) j ^ m :=
  actualSectionTensorPower_coefficients _ _ (X.nativeRankOneCoordinateLineOverFrame i hi j hj)
    (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneHyperplaneLocalEquation (i 0) j)
    (X.nativeRankOneCoordinatePoleSection_coefficient i hi j hj) m

/-- Every true canonical coordinate tensor-power section is nonzero,
including degree zero, from its actual nonzero original chart coefficient. -/
theorem nativeRankOneCoordinatePoleTensorPower_ne_zero (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (m : ℕ) : X.nativeRankOneCoordinatePoleTensorPower j m ≠ 0 := by
  obtain ⟨i, hi⟩ := X.exists_chartIndex_ne_zero
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  intro hz
  have hc := X.nativeRankOneCoordinatePoleTensorPower_coefficient i hi j hj m
  rw [hz, map_zero, map_zero] at hc
  exact pow_ne_zero m (X.nativeRankOneHyperplaneLocalEquation_ne_zero i hi j hj) hc.symm

/-- Its actual native function-field frame coefficient is the literal
original coordinate ratio to the SAME tensor degree. -/
theorem nativeRankOneCoordinatePoleTensorPower_generic (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ) :
    letI := X.nativeRankOneCoordinateOpen_nonempty i hi
    globalSectionToFunctionField (X.nativeRankOneCoordinateTensorFrame i hi j hj m)
      (X.nativeRankOneCoordinatePoleTensorPower j m) =
      X.nativeRankOneFunctionFieldEquiv i hi ((X.coord 0 j / X.coord 0 (i 0)) ^ m) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  change X.nativeRankOneGenericGerm i hi
    (localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame i hi j hj m)
      ((bundleTensorPower (X.nativeRankOneCoordinateLine j) m).presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
        (X.nativeRankOneCoordinatePoleTensorPower j m))) = _
  rw [X.nativeRankOneCoordinatePoleTensorPower_coefficient i hi j hj m, map_pow,
    X.nativeRankOneHyperplaneLocalEquation_generic i hi j, map_pow]

/-- Every TRUE actual local tensor-power section has its intrinsic rational
coefficient normalized by the SAME actual canonical coordinate tensor power. -/
theorem nativeRankOneCoordinateTensorSectionRatio_formula (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ)
    (s : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m,
      X.nativeRankOneCoordinateOpen (i 0))) :
    letI := X.nativeRankOneCoordinateOpen_nonempty i hi
    sectionRatio (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
      (X.nativeRankOneCoordinatePoleTensorPower j m)
      (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m)
      (X.nativeRankOneCoordinateOpen (i 0)) s =
      X.nativeRankOneGenericGerm i hi
        (localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame i hi j hj m) s) /
        X.nativeRankOneFunctionFieldEquiv i hi ((X.coord 0 j / X.coord 0 (i 0)) ^ m) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  rw [sectionRatio_frame_formula _ _ _ _
    (X.nativeRankOneCoordinateTensorFrame i hi j hj m),
    X.nativeRankOneCoordinatePoleTensorPower_generic i hi j hj m]
  rfl
end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.CanonicalGeometry.LocalBundleFrame.tensor_coefficients
#print axioms EnvelopeProperty.CanonicalGeometry.LocalBundleFrame.tensor_coefficients
#check @EnvelopeProperty.CanonicalGeometry.actualSectionTensorPower
#print axioms EnvelopeProperty.CanonicalGeometry.actualSectionTensorPower
#check @EnvelopeProperty.CanonicalGeometry.actualSectionTensorPower_coefficients
#print axioms EnvelopeProperty.CanonicalGeometry.actualSectionTensorPower_coefficients
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateTensorFrame
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateTensorFrame
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower_ne_zero
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower_ne_zero
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower_generic
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinatePoleTensorPower_generic
#check @EnvelopeProperty.MultiModel.nativeRankOneCoordinateTensorSectionRatio_formula
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoordinateTensorSectionRatio_formula
