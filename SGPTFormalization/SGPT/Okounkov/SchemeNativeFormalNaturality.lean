import SGPT.Okounkov.SchemeNativeFormalGerm
import SGPT.Okounkov.SchemeNativeMorphismCoordinates
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Whole original Taylor naturality for the same actual scheme morphism

The formal substitution is manufactured from the literal Taylor series of
the actual centered coordinate pullbacks. Coordinate-local uniqueness of
the existing original Taylor map gives the entire germ equality. The actual
native and algebraic stalk squares are then reused, without a replacement map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter Set
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
open HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
open HironakaActualFormalCoordinatePowerDivision HironakaActualOriginalFormalHSTransfer
open HironakaRelativeNormalMonomialBasis
open scoped Topology

/-- The actual whole formal variable ideal is precisely the literal residue-evaluation kernel. -/
theorem formalVariables_eq_ker_constantCoeff (n : ℕ) :
    actualFormalCoordinateIdeal n univ =
      RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) ℂ →+* ℂ) := by
  have hv : actualFormalCoordinateIdeal n univ = genuineFormalVariables n := by
    simp only [actualFormalCoordinateIdeal, genuineFormalVariables, image_univ]
  rw [hv]
  ext F
  change F ∈ genuineFormalVariables n ↔ MvPowerSeries.constantCoeff F = 0
  constructor
  · intro hF
    exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n 1 F).mp
      (by simpa only [pow_one] using hF) 0 (by simp [normalExponentDegree])
  · intro hF
    have hpow : F ∈ genuineFormalVariables n ^ 1 := by
      apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n 1 F).mpr
      intro a ha
      have hzero : a = 0 := by
        ext i
        have hi : a i ≤ normalExponentDegree a := by
          exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
        have hz : a i = 0 := by omega
        exact hz
      subst a
      exact hF
    simpa only [pow_one] using hpow

section Centered

variable {n m : ℕ} (F : ComplexModel n → ComplexModel m)
  (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) (hF0 : F 0 = 0)

/-- Literal Taylor series of the SAME actual centered coordinate pullbacks. -/
def centeredFormalCoordinateImages (i : Fin m) : MvPowerSeries (Fin n) ℂ :=
  actualUnshiftedTaylorAlgHom n (compAlgHom F hF hF0 (coordinateGerm i))

/-- The actual centered map internally supplies the zero constant coefficients needed for substitution. -/
theorem centeredFormalCoordinateImages_constantCoeff (i : Fin m) :
    MvPowerSeries.constantCoeff (centeredFormalCoordinateImages F hF hF0 i) = 0 := by
  rw [centeredFormalCoordinateImages, actualUnshiftedTaylor_constantCoeff]
  change (F 0) i = 0
  rw [hF0]
  rfl

/-- Each actual coordinate pullback has its true whole formal variable-ideal membership. -/
theorem centeredFormalCoordinateImages_mem_variables (i : Fin m) :
    centeredFormalCoordinateImages F hF hF0 i ∈ actualFormalCoordinateIdeal n univ := by
  rw [formalVariables_eq_ker_constantCoeff]
  exact centeredFormalCoordinateImages_constantCoeff F hF hF0 i

/-- Genuine formal substitution, manufactured from the actual holomorphic map. -/
def centeredFormalPullback : MvPowerSeries (Fin m) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (centeredFormalCoordinateImages_constantCoeff F hF hF0))

/-- Every actual formal variable has its literal original coordinate Taylor image. -/
theorem centeredFormalPullback_X (i : Fin m) :
    centeredFormalPullback F hF hF0 (MvPowerSeries.X i) =
      centeredFormalCoordinateImages F hF hF0 i :=
  MvPowerSeries.substAlgHom_X _ i

/-- The genuine actual formal pullback preserves the WHOLE formal variable ideal. -/
theorem centeredFormalPullback_map_variables_le :
    (actualFormalCoordinateIdeal m univ).map (centeredFormalPullback F hF hF0).toRingHom ≤
      actualFormalCoordinateIdeal n univ := by
  rw [actualFormalCoordinateIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨_, ⟨i, _, rfl⟩, rfl⟩
  change centeredFormalPullback F hF hF0 (MvPowerSeries.X i) ∈ _
  rw [centeredFormalPullback_X]
  exact centeredFormalCoordinateImages_mem_variables F hF hF0 i

/-- ALL formal coefficients, including nonconvergent series, retain literal residue evaluation. -/
theorem centeredFormalPullback_constantCoeff (s : MvPowerSeries (Fin m) ℂ) :
    MvPowerSeries.constantCoeff (centeredFormalPullback F hF hF0 s) =
      MvPowerSeries.constantCoeff s := by
  let hs := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (centeredFormalCoordinateImages_constantCoeff F hF hF0)
  have hz := MvPowerSeries.constantCoeff_subst_eq_zero hs
    (centeredFormalCoordinateImages_constantCoeff F hF hF0)
    (f := s - MvPowerSeries.C (MvPowerSeries.constantCoeff s)) (by simp)
  rw [← MvPowerSeries.substAlgHom_apply hs] at hz
  change MvPowerSeries.constantCoeff
    (centeredFormalPullback F hF hF0 (s - MvPowerSeries.C (MvPowerSeries.constantCoeff s))) = 0 at hz
  have hc (c : ℂ) : centeredFormalPullback F hF hF0 (MvPowerSeries.C c) = MvPowerSeries.C c :=
    (centeredFormalPullback F hF hF0).commutes c
  rw [map_sub, map_sub, hc, MvPowerSeries.constantCoeff_C, sub_eq_zero] at hz
  exact hz

/-- The ENTIRE original germ map commutes with the genuine actual formal substitution. -/
theorem actualUnshiftedTaylor_comp (g : HolGerm (ComplexModel m)) :
    actualUnshiftedTaylorAlgHom n (compAlgHom F hF hF0 g) =
      centeredFormalPullback F hF hF0 (actualUnshiftedTaylorAlgHom m g) := by
  have he : (actualUnshiftedTaylorAlgHom n).comp (compAlgHom F hF hF0) =
      (centeredFormalPullback F hF hF0).comp (actualUnshiftedTaylorAlgHom m) := by
    apply actualGermAlgHom_eq_of_coordinate_images
    · intro i
      change actualUnshiftedTaylorAlgHom n (compAlgHom F hF hF0 (coordinateGerm i)) =
        centeredFormalPullback F hF hF0 (actualUnshiftedTaylorAlgHom m (coordinateGerm i))
      rw [actualUnshiftedTaylor_coordinate, centeredFormalPullback_X]
      rfl
    · intro i
      change actualUnshiftedTaylorAlgHom n (compAlgHom F hF hF0 (coordinateGerm i)) ∈ _
      rw [← actualUnshiftedTaylor_map_maximalIdeal n]
      apply Ideal.mem_map_of_mem
      apply (HolGerm.mem_maximalIdeal_iff _).mpr
      change (F 0) i = 0
      rw [hF0]
      rfl
  exact DFunLike.congr_fun he g

end Centered

section Scheme

variable {X Y : Scheme} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]
  [IsSeparated (h ≫ f)] [QuasiCompact (h ≫ f)] [IsSeparated f] [QuasiCompact f]

local instance formalNaturalitySourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance formalNaturalityTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance formalNaturalitySourceCharts :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTNChartedSpace (h ≫ f) n
local instance formalNaturalityTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m
local instance formalNaturalitySourceManifold : IsComplexManifold n (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTN_isComplexManifold (h ≫ f) n
local instance formalNaturalityTargetManifold : IsComplexManifold m (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f m

variable (p : SchemeComplexPoint (h ≫ f))

/-- The genuine formal map of the SAME original morphism in its actual default centered charts. -/
def schemeMorphismFormalPullback : MvPowerSeries (Fin m) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  centeredFormalPullback (schemeMorphismCenteredCoordinateMap f h n m p)
    (schemeMorphismCenteredCoordinateMap_holomorphic f h n m p)
    (schemeMorphismCenteredCoordinateMap_zero f h n m p)

/-- Its actual variable images are exactly the original coordinate pullback Taylor series. -/
theorem schemeMorphismFormalPullback_X (i : Fin m) :
    schemeMorphismFormalPullback f h n m p (MvPowerSeries.X i) =
      actualUnshiftedTaylorAlgHom n
        (compAlgHom (schemeMorphismCenteredCoordinateMap f h n m p)
          (schemeMorphismCenteredCoordinateMap_holomorphic f h n m p)
          (schemeMorphismCenteredCoordinateMap_zero f h n m p) (coordinateGerm i)) :=
  centeredFormalPullback_X _ _ _ i

/-- The SAME original formal scheme map preserves residue evaluation of EVERY entire formal series. -/
theorem schemeMorphismFormalPullback_constantCoeff (s : MvPowerSeries (Fin m) ℂ) :
    MvPowerSeries.constantCoeff (schemeMorphismFormalPullback f h n m p s) =
      MvPowerSeries.constantCoeff s :=
  centeredFormalPullback_constantCoeff _ _ _ s

/-- Every arbitrary ENTIRE native germ commutes with the SAME actual formal pullback. -/
theorem schemeNativeTaylor_naturality
    (g : NativeHolGerm m (SchemeComplexPoint f) (schemeComplexPointMap (h ≫ f) f h rfl p)) :
    NativeHolGerm.taylor p (schemeMorphismNativeGermPullback f h n m p g) =
      schemeMorphismFormalPullback f h n m p
        (NativeHolGerm.taylor (schemeComplexPointMap (h ≫ f) f h rfl p) g) := by
  change actualUnshiftedTaylorAlgHom n
    (NativeHolGerm.chartEquiv p (schemeMorphismNativeGermPullback f h n m p g)) = _
  rw [schemeMorphismNativeGermPullback_chart]
  exact actualUnshiftedTaylor_comp _ _ _ _

/-- The ENTIRE original algebraic stalk square commutes with literal formal Taylor substitution. -/
theorem schemeNativeFormalGerm_naturality
    (a : Y.presheaf.stalk
      (schemeComplexPointImage f (schemeComplexPointMap (h ≫ f) f h rfl p))) :
    schemeNativeFormalGerm (h ≫ f) n p
        ((h.stalkMap (schemeComplexPointImage (h ≫ f) p)).hom a) =
      schemeMorphismFormalPullback f h n m p
        (schemeNativeFormalGerm f m (schemeComplexPointMap (h ≫ f) f h rfl p) a) := by
  change NativeHolGerm.taylor p (schemeNativeStalkGerm (h ≫ f) n p _) = _
  rw [schemeNativeStalkGerm_naturality f h n m p a]
  exact schemeNativeTaylor_naturality f h n m p _

/-- Both extensions of every WHOLE native ideal agree for the SAME original morphism. -/
theorem schemeNativeTaylor_map_ideal
    (I : Ideal (NativeHolGerm m (SchemeComplexPoint f)
      (schemeComplexPointMap (h ≫ f) f h rfl p))) :
    (I.map (NativeHolGerm.taylor (schemeComplexPointMap (h ≫ f) f h rfl p))).map
        (schemeMorphismFormalPullback f h n m p).toRingHom =
      (I.map (schemeMorphismNativeGermPullback f h n m p)).map (NativeHolGerm.taylor p) := by
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun k => I.map k)
  apply RingHom.ext
  intro g
  exact (schemeNativeTaylor_naturality f h n m p g).symm

/-- Both extensions of every WHOLE original algebraic stalk ideal retain the actual stalk map. -/
theorem schemeNativeFormalGerm_map_ideal
    (I : Ideal (Y.presheaf.stalk
      (schemeComplexPointImage f (schemeComplexPointMap (h ≫ f) f h rfl p)))) :
    (I.map (schemeNativeFormalGerm f m (schemeComplexPointMap (h ≫ f) f h rfl p))).map
        (schemeMorphismFormalPullback f h n m p).toRingHom =
      (I.map (h.stalkMap (schemeComplexPointImage (h ≫ f) p)).hom).map
        (schemeNativeFormalGerm (h ≫ f) n p) := by
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun k => I.map k)
  apply RingHom.ext
  intro a
  exact (schemeNativeFormalGerm_naturality f h n m p a).symm

end Scheme

end SGPT.Okounkov
