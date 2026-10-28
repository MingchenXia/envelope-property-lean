import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeTensorCoordinateFrames
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeBaseScalars

/-!
# ORIGINAL full saturated coefficients in every actual native tensor degree

Actual inverse tensor frames construct local sections from full original
R_(m·1). Actual intrinsic rational coefficients of all native H0 sections
recover full original saturation and the SAME genuine base-scalar laws.
No gluing, matching, saturation or injectivity certificate is assumed.
Route: owned `native-tensor-section-coefficients-route.tex`.
-/
open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

private theorem originalTensorDegreeDen (i : X.ChartIndex) (m : ℕ) :
    X.chartDenZ i (m • (1 : Fin 1 → ℤ)) = X.coord 0 (i 0) ^ m := by
  rw [X.chartDenZ_nsmul]
  simp only [chartDenZ, Fin.prod_univ_one, Pi.one_apply, zpow_one]

private theorem originalTensorRatio_mem (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    (f : K) / X.coord 0 (i 0) ^ m ∈ X.chartAlg i := by
  simpa only [originalTensorDegreeDen X i m] using
    X.div_chartDenZ_mem_chartAlg hi f.property

/-- EVERY ORIGINAL full saturated tensor-degree coefficient gives an ACTUAL
local section in the SAME produced original native tensor coordinate frame. -/
def nativeRankOneTensorLocalSectionOfOriginal (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m,
      X.nativeRankOneCoordinateOpen (i 0)) :=
  (localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame i hi j hj m)).symm
    ((X.nativeRankOneOriginalSectionsIso i hi).hom
      ⟨(f : K) / X.coord 0 (i 0) ^ m, originalTensorRatio_mem X i hi m f⟩)

/-- The ACTUAL local coefficient is the literal ORIGINAL f/c_i^m. -/
theorem nativeRankOneTensorLocalSectionOfOriginal_coefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame i hi j hj m)
      (X.nativeRankOneTensorLocalSectionOfOriginal i hi j hj m f) =
      (X.nativeRankOneOriginalSectionsIso i hi).hom
        ⟨(f : K) / X.coord 0 (i 0) ^ m, originalTensorRatio_mem X i hi m f⟩ :=
  (localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame i hi j hj m)).apply_symm_apply _

/-- EVERY original local tensor section has the SAME true intrinsic
rational coefficient E_i(f/c_j^m), including tensor degree zero. -/
theorem nativeRankOneTensorLocalSectionOfOriginal_ratio (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (f : X.sections (m • (1 : Fin 1 → ℤ))) :
    letI := X.nativeRankOneCoordinateOpen_nonempty i hi
    sectionRatio (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
      (X.nativeRankOneCoordinatePoleTensorPower j m)
      (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m)
      (X.nativeRankOneCoordinateOpen (i 0))
      (X.nativeRankOneTensorLocalSectionOfOriginal i hi j hj m f) =
      X.nativeRankOneFunctionFieldEquiv i hi ((f : K) / X.coord 0 j ^ m) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  rw [X.nativeRankOneCoordinateTensorSectionRatio_formula i hi j hj m _,
    X.nativeRankOneTensorLocalSectionOfOriginal_coefficient i hi j hj m f,
    ← X.nativeRankOneFunctionFieldEquiv_coefficient i hi _, ← map_div₀]
  congr 1
  rw [div_pow]
  field_simp [hj, hi 0]

/-- The literal ORIGINAL rational coefficient of EVERY actual global
section of the SAME native coordinate tensor power. -/
def nativeRankOneTensorGlobalSectionCoefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (m : ℕ) (s : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤)) : K :=
  X.coord 0 j ^ m * (X.nativeRankOneFunctionFieldEquiv i hi).symm
    (sectionRatio (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
      (X.nativeRankOneCoordinatePoleTensorPower j m)
      (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m) ⊤ s)

/-- On EVERY original nonzero chart, the literal global coefficient has
EXACTLY the actual original regular tensor-frame coefficient. -/
theorem nativeRankOneTensorGlobalSectionCoefficient_local (i l : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (hl : ∀ c, X.coord c (l c) ≠ 0)
    (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ)
    (s : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤)) :
    X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m s / X.coord 0 (l 0) ^ m =
      ((X.nativeRankOneOriginalSectionsIso l hl).inv
        (localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame l hl j hj m)
          ((bundleTensorPower (X.nativeRankOneCoordinateLine j) m).presheaf.map
            (homOfLE (le_top : X.nativeRankOneCoordinateOpen (l 0) ≤ ⊤)).op s)) : X.chartAlg l) := by
  have := X.nativeRankOneCoordinateOpen_nonempty l hl
  let t := (bundleTensorPower (X.nativeRankOneCoordinateLine j) m).presheaf.map
    (homOfLE (le_top : X.nativeRankOneCoordinateOpen (l 0) ≤ ⊤)).op s
  let b := localFrameCoefficients (X.nativeRankOneCoordinateTensorFrame l hl j hj m) t
  have hq := (sectionRatio_restrict (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
    (X.nativeRankOneCoordinatePoleTensorPower j m)
    (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m)
    (le_top : X.nativeRankOneCoordinateOpen (l 0) ≤ ⊤) s).symm
  rw [X.nativeRankOneCoordinateTensorSectionRatio_formula l hl j hj m] at hq
  have he := congrArg (X.nativeRankOneFunctionFieldEquiv l hl).symm hq
  rw [map_div₀, X.nativeRankOneFunctionFieldEquiv_symm_germ,
    RingEquiv.symm_apply_apply] at he
  unfold nativeRankOneTensorGlobalSectionCoefficient
  rw [X.nativeRankOneFunctionFieldEquiv_independent i l hi hl, he]
  change X.coord 0 j ^ m *
    (((X.nativeRankOneOriginalSectionsIso l hl).inv b : X.chartAlg l) /
      (X.coord 0 j / X.coord 0 (l 0)) ^ m) / X.coord 0 (l 0) ^ m = _
  rw [div_pow]
  field_simp [hj, hl 0]
  rfl

/-- EVERY actual native tensor-power global section belongs to the ORIGINAL
FULL saturated R_(m·1), by the independent genuine all-chart saturation criterion. -/
theorem nativeRankOneTensorGlobalSectionCoefficient_mem_sections (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ)
    (s : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤)) :
    X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m s ∈
      X.sections (m • (1 : Fin 1 → ℤ)) := by
  apply X.mem_sections_of_forall_div_chartDenZ
  intro l hl
  rw [originalTensorDegreeDen X l m,
    X.nativeRankOneTensorGlobalSectionCoefficient_local i l hi hl j hj m s]
  exact Subtype.property _

/-- The true original coefficient of actual WHOLE native tensor-power H0
is faithful, derived from actual intrinsic rational-section injectivity. -/
theorem nativeRankOneTensorGlobalSectionCoefficient_injective (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ) :
    Function.Injective (X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m) := by
  intro s t h
  apply sectionRatio_injective (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
    (X.nativeRankOneCoordinatePoleTensorPower j m)
    (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m) ⊤
  apply (X.nativeRankOneFunctionFieldEquiv i hi).symm.injective
  exact mul_left_cancel₀ (pow_ne_zero m hj) h

/-- The literal original coefficient is additive on actual native tensor H0. -/
theorem nativeRankOneTensorGlobalSectionCoefficient_add (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ)
    (s t : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤)) :
    X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m (s + t) =
      X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m s +
        X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m t := by
  simp only [nativeRankOneTensorGlobalSectionCoefficient, map_add, mul_add]

/-- The SAME true original structural base constants act with their literal
original scalar on ALL actual tensor H0 coefficients. No transported action. -/
theorem nativeRankOneTensorGlobalSectionCoefficient_base_smul (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) (m : ℕ)
    (a : k) (s : Γ(bundleTensorPower (X.nativeRankOneCoordinateLine j) m, ⊤)) :
    X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m (X.nativeRankOneBaseConstants a • s) =
      algebraMap k K a * X.nativeRankOneTensorGlobalSectionCoefficient i hi j hj m s := by
  unfold nativeRankOneTensorGlobalSectionCoefficient
  rw [(sectionRatio (bundleTensorPower (X.nativeRankOneCoordinateLine j) m)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible
      (X.nativeRankOneCoordinateLine_isInvertible j hj) m)
    (X.nativeRankOneCoordinatePoleTensorPower j m)
    (X.nativeRankOneCoordinatePoleTensorPower_ne_zero j hj m) ⊤).map_smulₛₗ]
  simp only [smul_eq_mul]
  rw [← X.nativeRankOneFunctionFieldEquiv_baseConstants i hi a, map_mul,
    RingEquiv.symm_apply_apply]
  ring
end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.MultiModel.nativeRankOneTensorLocalSectionOfOriginal
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorLocalSectionOfOriginal
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorLocalSectionOfOriginal_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorLocalSectionOfOriginal_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorLocalSectionOfOriginal_ratio
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorLocalSectionOfOriginal_ratio
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_local
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_local
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_mem_sections
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_mem_sections
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_injective
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_injective
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_add
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_add
#check @EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_base_smul
#print axioms EnvelopeProperty.MultiModel.nativeRankOneTensorGlobalSectionCoefficient_base_smul
