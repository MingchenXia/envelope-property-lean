import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeStalkFlatness
import EnvelopeProperty.ComplexGeometry.Germs.SchemeComplexPointStalkEvaluation
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HironakaActualTaylorCoordinateNaturality
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HironakaActualTaylorFaithfullyFlat

/-!
# The actual original native Taylor map and faithfully flat scheme coefficients

Taylor series are those of the actual preferred centered chart. The existing
unshifted Taylor map transports the literal equality `0+n=n`, retaining its
original indexed variables. No comparison certificate or global integrality
assumption is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter Set
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HironakaHolomorphicJetMonomialSpan HironakaActualCoefficientPresentationCentrePower
open HironakaActualOriginalFormalTaylor HironakaActualTaylorFaithfullyFlat
open HironakaActualTaylorCoordinateNaturality HironakaActualFormalCoordinatePowerDivision
open scoped Topology

/-- The existing genuine Taylor map remains faithfully flat after its literal dimension transport. -/
theorem actualUnshiftedTaylor_faithfullyFlat (n : ℕ) :
    (actualUnshiftedTaylorAlgHom n).toRingHom.FaithfullyFlat := by
  have hc (m : ℕ) (hm : m = n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (hf : f.toRingHom.FaithfullyFlat) :
      (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f).toRingHom.FaithfullyFlat := by
    subst m
    exact hf
  exact hc (0+n) (Nat.zero_add n) (originalTaylorAlgHom n)
    (originalTaylorAlgHom_faithfullyFlat n)

/-- The genuine constant coefficient is the original whole germ's value. -/
theorem actualUnshiftedTaylor_constantCoeff {n : ℕ} (g : HolGerm (ComplexModel n)) :
    MvPowerSeries.constantCoeff (actualUnshiftedTaylorAlgHom n g) = HolGerm.eval g := by
  obtain ⟨h, he⟩ := exists_coordinate_decomposition g
  have hτ := congrArg (fun a => MvPowerSeries.constantCoeff (actualUnshiftedTaylorAlgHom n a)) he
  have hc (c : ℂ) : actualUnshiftedTaylorAlgHom n (HolGerm.constHom c) = MvPowerSeries.C c :=
    (actualUnshiftedTaylorAlgHom n).commutes c
  simpa only [map_add, map_sum, map_mul, actualUnshiftedTaylor_coordinate,
    hc, MvPowerSeries.constantCoeff_C,
    MvPowerSeries.constantCoeff_X, zero_mul, Finset.sum_const_zero, add_zero] using hτ

/-- The WHOLE original maximal ideal extends to exactly the actual formal variable ideal. -/
theorem actualUnshiftedTaylor_map_maximalIdeal (n : ℕ) :
    (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))).map
        (actualUnshiftedTaylorAlgHom n).toRingHom = actualFormalCoordinateIdeal n univ := by
  apply le_antisymm
  · apply map_actualGerm_maximalIdeal_le_formal_coordinates
    intro i
    rw [actualUnshiftedTaylor_coordinate]
    exact Ideal.subset_span ⟨i, mem_univ _, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    rw [← actualUnshiftedTaylor_coordinate n i]
    apply Ideal.mem_map_of_mem
    exact (HolGerm.mem_maximalIdeal_iff _).mpr rfl

namespace NativeHolGerm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (p : M)

/-- Genuine Taylor series of arbitrary original native germs in their SAME preferred centered chart. -/
def taylor : NativeHolGerm n M p →+* MvPowerSeries (Fin n) ℂ :=
  (actualUnshiftedTaylorAlgHom n).toRingHom.comp (chartEquiv p).toRingHom

/-- Actual constant functions retain their same original complex coefficients. -/
theorem taylor_const (c : ℂ) : taylor (n := n) p (constHom c) = MvPowerSeries.C c := by
  change actualUnshiftedTaylorAlgHom n (HolGerm.constHom c) = _
  exact (actualUnshiftedTaylorAlgHom n).commutes c

/-- Taylor's constant coefficient is evaluation at the SAME original native point. -/
theorem taylor_constantCoeff (g : NativeHolGerm n M p) :
    MvPowerSeries.constantCoeff (taylor p g) = eval g := by
  exact (actualUnshiftedTaylor_constantCoeff _).trans (eval_chartEquiv g)

/-- The actual native Taylor map is faithfully flat without additional coordinate data. -/
theorem taylor_faithfullyFlat : (taylor (n := n) p).FaithfullyFlat := by
  let B := HolGerm (ComplexModel n)
  let S := MvPowerSeries (Fin n) ℂ
  let : Algebra (NativeHolGerm n M p) B := (chartEquiv p).toRingHom.toAlgebra
  let : Algebra B S := (actualUnshiftedTaylorAlgHom n).toRingHom.toAlgebra
  let : Algebra (NativeHolGerm n M p) S := (taylor p).toAlgebra
  let : IsScalarTower (NativeHolGerm n M p) B S :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.FaithfullyFlat (NativeHolGerm n M p) B :=
    RingHom.FaithfullyFlat.of_bijective (chartEquiv (n := n) p).bijective
  let : Module.FaithfullyFlat B S := actualUnshiftedTaylor_faithfullyFlat n
  exact Module.FaithfullyFlat.trans (NativeHolGerm n M p) B S

/-- The WHOLE native maximal ideal has exactly the genuine formal variable image. -/
theorem taylor_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (NativeHolGerm n M p)).map (taylor p) =
      actualFormalCoordinateIdeal n univ := by
  have he : (IsLocalRing.maximalIdeal (NativeHolGerm n M p)).map
      (chartEquiv p).toRingHom = IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) :=
    IsLocalRing.map_ringEquiv_maximalIdeal (chartEquiv p)
  rw [taylor, ← Ideal.map_map, he]
  exact actualUnshiftedTaylor_map_maximalIdeal n

/-- Every arbitrary entire native ideal contracts from its actual Taylor extension. -/
theorem mem_ideal_iff_taylor (I : Ideal (NativeHolGerm n M p)) (g : NativeHolGerm n M p) :
    g ∈ I ↔ taylor p g ∈ I.map (taylor p) := by
  let : Algebra (NativeHolGerm n M p) (MvPowerSeries (Fin n) ℂ) := (taylor p).toAlgebra
  let : Module.FaithfullyFlat (NativeHolGerm n M p) (MvPowerSeries (Fin n) ℂ) :=
    taylor_faithfullyFlat (n := n) p
  exact Iff.symm (SetLike.ext_iff.mp
    (Ideal.comap_map_eq_self_of_faithfullyFlat (B := MvPowerSeries (Fin n) ℂ) I) g)

end NativeHolGerm

section Scheme

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance formalSchemePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance formalSchemePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance formalSchemePointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

variable (p : SchemeComplexPoint f)

local instance formalSchemeAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The actual ORIGINAL algebraic stalk coefficient map to its native formal series. -/
def schemeNativeFormalGerm :
    X.presheaf.stalk (schemeComplexPointImage f p) →+* MvPowerSeries (Fin n) ℂ :=
  (NativeHolGerm.taylor p).comp (schemeNativeStalkGerm f n p)

/-- The original entire algebraic stalk residue remains the literal formal constant coefficient. -/
theorem schemeNativeFormalGerm_constantCoeff
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    MvPowerSeries.constantCoeff (schemeNativeFormalGerm f n p a) =
      schemeComplexPointStalkEval f p a := by
  exact (NativeHolGerm.taylor_constantCoeff p _).trans (schemeNativeStalkGerm_eval f n p a)

/-- Every original affine regular coefficient has its literal preferred-chart Taylor series. -/
theorem schemeNativeFormalGerm_regular (a : SchemeCoordinateAffineRing f n p) :
    schemeNativeFormalGerm f n p (schemeCoordinateStalkEquiv f n p
      (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p) a)) =
      actualUnshiftedTaylorAlgHom n
        (schemeCoordinateModelGermEquiv n (schemeCoordinateRegularGerm f n p a)) := by
  change actualUnshiftedTaylorAlgHom n
    (NativeHolGerm.chartEquiv p (schemeNativeStalkGerm f n p _)) = _
  rw [schemeNativeStalkGerm_regular, schemeNativeRegularGerm_chart]

/-- Each actual original centered algebraic generator becomes its SAME indexed formal variable. -/
theorem schemeNativeFormalGerm_centered (i : Fin n) :
    schemeNativeFormalGerm f n p (schemeCoordinateStalkEquiv f n p
      (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p)
        (schemeCoordinateCenteredFreeGenerator f n p i))) = MvPowerSeries.X i := by
  rw [schemeNativeFormalGerm_regular, schemeCoordinateCenteredFreeGenerator_germ,
    schemeCoordinateModelGermEquiv_coordinate]
  exact actualUnshiftedTaylor_coordinate n i

/-- Original native stalk flatness and genuine Taylor flatness prove actual faithful flatness. -/
theorem schemeNativeFormalGerm_faithfullyFlat : (schemeNativeFormalGerm f n p).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _
    (schemeNativeStalkGerm_faithfullyFlat f n p) (NativeHolGerm.taylor_faithfullyFlat (n := n) p)

end Scheme

end HolomorphicGerms
