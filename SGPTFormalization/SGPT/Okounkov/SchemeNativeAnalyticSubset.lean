import SGPT.Okounkov.SchemeNativeStalkFlatness
import TranscendentalNakamaye.FirstPass.AnalyticSubsetTopology
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Original algebraic closed sets in the actual native complex manifold

The actual standard-smooth affine ring is noetherian. Its actual finite
equations, evaluated through the SAME preferred chart inverse, manufacture
genuine analytic presentations of every original Zariski closed subset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra BingWangEntropy Set Filter
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open scoped Topology Manifold

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

local instance nativeClosedSetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

/-- The original algebraic closed-set trace uses the SAME actual scheme point image. -/
def schemeNativeAlgebraicTrace (Z : Set X) : Set (SchemeComplexPoint f) :=
  schemeComplexPointImage f ⁻¹' Z

variable (p : SchemeComplexPoint f)

local instance nativeClosedSetAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The actual preferred affine ring is noetherian by genuine standard smoothness. -/
theorem schemeNativeCoordinateRing_noetherian : IsNoetherianRing (SchemeCoordinateAffineRing f n p) := by
  let := standardSmoothComplexAffineChart_isStandardSmooth f n p
  let : Algebra.IsStandardSmooth ℂ (SchemeCoordinateAffineRing f n p) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  exact Algebra.FiniteType.isNoetherianRing ℂ (SchemeCoordinateAffineRing f n p)

/-- Literal original affine evaluation in the SAME unshifted preferred native chart. -/
def schemeNativeAffineCoordinateFunction (a : SchemeCoordinateAffineRing f n p)
    (z : ComplexModel n) : ℂ :=
  schemeAnalyticCoordinateChartInverseAlgebraPoint f n p (schemeCoordinateModelEquiv n z) a

/-- The original coefficient function is analytic on the actual whole chart target. -/
theorem schemeNativeAffineCoordinateFunction_analytic
    (a : SchemeCoordinateAffineRing f n p) :
    AnalyticOnNhd ℂ (schemeNativeAffineCoordinateFunction f n p a)
      (schemeAnalyticTNChart f n p).target := by
  intro z hz
  have hz' : schemeCoordinateModelEquiv n z ∈ (schemeAnalyticCoordinateChart f n p).target := by
    simpa only [schemeAnalyticTNChart_target, Set.mem_preimage] using hz
  exact (schemeAnalyticCoordinateChart_inverse_eval_analyticOnNhd f n p a
    (schemeCoordinateModelEquiv n z) hz').comp
      ((schemeCoordinateModelEquiv n).toContinuousLinearMap.analyticAt z)

/-- On its genuine source the SAME original affine lift supplies the exact coefficient value. -/
theorem schemeNativeAffineCoordinateFunction_source
    (a : SchemeCoordinateAffineRing f n p) (y : SchemeComplexPoint f)
    (hy : y ∈ (schemeAnalyticTNChart f n p).source) :
    schemeNativeAffineCoordinateFunction f n p a (schemeAnalyticTNChart f n p y) =
      standardSmoothComplexPointOpenChart f n p y a := by
  have hy' : y ∈ (schemeAnalyticCoordinateChart f n p).source := by
    simpa only [schemeAnalyticTNChart_source] using hy
  change schemeAnalyticCoordinateChartInverseAlgebraPoint f n p
    (schemeCoordinateModelEquiv n
      ((schemeCoordinateModelEquiv n).symm (schemeAnalyticCoordinateChart f n p y))) a = _
  rw [ContinuousLinearEquiv.apply_symm_apply,
    schemeAnalyticCoordinateChartInverseAlgebraPoint_apply f n p y hy']

private theorem affineEvaluation_mem_prime_iff {A : CommRingCat} (q : A →+* ℂ) (a : A) :
    a ∈ (Spec.map (CommRingCat.ofHom q) default).asIdeal ↔ q a = 0 := by
  have hd : (default : Spec (.of ℂ)) = (⊥ : PrimeSpectrum ℂ) := Subsingleton.elim _ _
  rw [hd]
  rfl

private theorem schemeNativeAffineLift_image (y : SchemeComplexPoint f)
    (hy : y ∈ (schemeAnalyticTNChart f n p).source) :
    (standardSmoothComplexAffineChart f n p).val.map
      (Spec.map (CommRingCat.ofHom (standardSmoothComplexPointOpenChart f n p y).toRingHom) default) =
        schemeComplexPointImage f y := by
  have hy' : y ∈ (schemeAnalyticCoordinateChart f n p).source := by
    simpa only [schemeAnalyticTNChart_source] using hy
  have hyS : y ∈ (standardSmoothComplexPointOpenChart f n p).source := by
    rw [schemeAnalyticCoordinateChart_source] at hy'
    exact hy'.1
  have he := congrArg Subtype.val ((standardSmoothComplexPointOpenChart f n p).left_inv hyS)
  rw [standardSmoothComplexPointOpenChart_symm_val] at he
  have hp := congrArg (fun h : Spec (.of ℂ) ⟶ X => h default) he
  rw [Scheme.Hom.comp_apply] at hp
  exact hp

/-- Every original algebraic closed set has actual finite original affine equations on the preferred source. -/
theorem exists_schemeNativeClosedEquations (Z : Set X) (hZ : IsClosed Z) :
    ∃ (k : ℕ) (a : Fin k → SchemeCoordinateAffineRing f n p),
      ∀ y ∈ (schemeAnalyticTNChart f n p).source,
        y ∈ schemeNativeAlgebraicTrace f Z ↔
          ∀ i, schemeNativeAffineCoordinateFunction f n p (a i)
            (schemeAnalyticTNChart f n p y) = 0 := by
  let c := (standardSmoothComplexAffineChart f n p).val
  let : IsNoetherianRing (SchemeCoordinateAffineRing f n p) :=
    schemeNativeCoordinateRing_noetherian f n p
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (c.map ⁻¹' Z)).mp
    (hZ.preimage c.map.continuous)
  obtain ⟨k, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  refine ⟨k, a, ?_⟩
  intro y hy
  simp_rw [schemeNativeAffineCoordinateFunction_source f n p _ y hy]
  change schemeComplexPointImage f y ∈ Z ↔
    ∀ i, standardSmoothComplexPointOpenChart f n p y (a i) = 0
  rw [← schemeNativeAffineLift_image f n p y hy]
  change Spec.map (CommRingCat.ofHom (standardSmoothComplexPointOpenChart f n p y).toRingHom)
    default ∈ c.map ⁻¹' Z ↔ ∀ i, standardSmoothComplexPointOpenChart f n p y (a i) = 0
  rw [hI, ← ha, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro h i
    exact (affineEvaluation_mem_prime_iff _ _).mp (h ⟨i, rfl⟩)
  · intro h
    rintro _ ⟨i, rfl⟩
    exact (affineEvaluation_mem_prime_iff _ _).mpr (h i)

section Analytic

variable [IsSeparated f] [QuasiCompact f]

local instance nativeClosedSetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance nativeClosedSetManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- Every original Zariski closed set is a genuine analytic subset in the actual original native manifold. -/
theorem schemeNativeAlgebraicTrace_isComplexAnalyticSubset (Z : Set X) (hZ : IsClosed Z) :
    IsComplexAnalyticSubset (n := n) (schemeNativeAlgebraicTrace f Z) := by
  intro x
  obtain ⟨k, a, ha⟩ := exists_schemeNativeClosedEquations f n x Z hZ
  refine ⟨{
    generatorCount := k
    generator := fun i => schemeNativeAffineCoordinateFunction f n x (a i)
    coordinateNeighborhood := (schemeAnalyticTNChart f n x).target
    isOpen_coordinateNeighborhood := (schemeAnalyticTNChart f n x).open_target
    center_mem_coordinateNeighborhood := (schemeAnalyticTNChart f n x).map_source
      (by rw [schemeAnalyticTNChart_source]; exact schemeAnalyticCoordinateChart_point_mem_source f n x)
    coordinateNeighborhood_subset_target := subset_rfl
    generator_holomorphic := fun i =>
      (schemeNativeAffineCoordinateFunction_analytic f n x (a i)).differentiableOn
    zeroLocus := ?_ }⟩
  intro y hy _
  exact ha y hy

include n in
/-- Proper original closed subsets of an integral source have no native analytic interior.
The nonzero original local coefficient survives by the ACTUAL faithfully flat native stalk map. -/
theorem schemeNativeAlgebraicTrace_interior_eq_empty [IsIntegral X]
    (Z : Set X) (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    interior (schemeNativeAlgebraicTrace f Z) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let c := (standardSmoothComplexAffineChart f n x).val
  let A := SchemeCoordinateAffineRing f n x
  let L := SchemeCoordinateLocalRing f n x
  let : IsDomain A := schemeCoordinateAffineRing_isDomain f n x
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (c.map ⁻¹' Z)).mp
    (hZ.preimage c.map.continuous)
  have hRange : (Set.range c.map).Nonempty :=
    ⟨schemeComplexPointImage f x, (standardSmoothComplexAffineChart f n x).property.1⟩
  obtain ⟨_, ⟨u, rfl⟩, huZ⟩ := nonempty_preirreducible_inter
    (IsOpenImmersion.isOpen_range c.map) hZ.isOpen_compl hRange (Set.nonempty_compl.mpr hZne)
  have hIne : I ≠ ⊥ := by
    intro hbot
    apply huZ
    change u ∈ c.map ⁻¹' Z
    rw [hI, hbot, PrimeSpectrum.zeroLocus_bot]
    exact mem_univ _
  obtain ⟨a, haI, ha0⟩ := I.ne_bot_iff.mp hIne
  have hgzero : schemeNativeRegularGerm f n x a = 0 := by
    apply Subtype.ext
    rw [schemeNativeRegularGerm_source]
    apply Germ.coe_eq.mpr
    have hxS : x ∈ (schemeAnalyticTNChart f n x).source := by
      rw [schemeAnalyticTNChart_source]
      exact schemeAnalyticCoordinateChart_point_mem_source f n x
    filter_upwards [mem_interior_iff_mem_nhds.mp hx,
      (schemeAnalyticTNChart f n x).open_source.mem_nhds hxS] with y hyZ hyS
    have hymem : Spec.map
        (CommRingCat.ofHom (standardSmoothComplexPointOpenChart f n x y).toRingHom) default ∈
          c.map ⁻¹' Z := by
      change c.map _ ∈ Z
      rw [schemeNativeAffineLift_image f n x y hyS]
      exact hyZ
    rw [hI, PrimeSpectrum.mem_zeroLocus] at hymem
    exact (affineEvaluation_mem_prime_iff _ _).mp (hymem haI)
  let b := schemeCoordinateStalkEquiv f n x (algebraMap A L a)
  have hb : b = 0 := by
    apply (schemeNativeStalkGerm_faithfullyFlat f n x).injective
    rw [map_zero]
    change schemeNativeStalkGerm f n x
      (schemeCoordinateStalkEquiv f n x (algebraMap A L a)) = 0
    rw [schemeNativeStalkGerm_regular]
    exact hgzero
  have hloc : algebraMap A L a = 0 := by
    apply (schemeCoordinateStalkEquiv f n x).injective
    simpa only [map_zero] using hb
  exact ha0 (FaithfulSMul.algebraMap_injective A L (by simpa only [map_zero] using hloc))

end Analytic

end SGPT.Okounkov
