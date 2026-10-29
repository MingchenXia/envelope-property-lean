import EnvelopeProperty.Char0.AnalyticMultiplierPositiveLevels
import EnvelopeProperty.Char0.NativeMultiplierGermTransform
import EnvelopeProperty.Char0.NativeAffineIdealWeight

/-! # Independent-level DEL for actual whole native ideals of original affine tuples -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Char0.NativeMultiplierProduct
open CategoryTheory AlgebraicGeometry ComplexSchemes Filter Set MeasureTheory HolomorphicGerms
open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicIdealSheaves NativeMultiplierGermTransform
open scoped Topology Manifold ContDiff ENNReal

section Native
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The actual independent weighted sum is quasi-PSH by its original local decompositions. -/
theorem weightedSum_quasiPSH {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun y => (r : EReal)*u y+(s : EReal)*v y) := by
  intro e z hz
  obtain ⟨P,a,hP,ha,heu⟩ := hu e z hz
  obtain ⟨Q,b,hQ,hb,hev⟩ := hv e z hz
  refine ⟨fun w => (r : EReal)*P w+(s : EReal)*Q w,fun w => r*a w+s*b w,
    (hP.const_mul hr).add (hQ.const_mul hs),?_,?_⟩
  · filter_upwards [ha,hb] with w haw hbw
    exact (contDiffAt_const.mul haw).add (contDiffAt_const.mul hbw)
  · filter_upwards [heu,hev] with w huw hvw
    change (r : EReal)*chartFunction u e w+(s : EReal)*chartFunction v e w = _
    rw [huw,hvw,EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr hr.le) (EReal.coe_ne_top r),
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hs.le) (EReal.coe_ne_top s),
      EReal.coe_add,EReal.coe_mul,EReal.coe_mul]
    ac_rfl

/-- Existing independent-level DEL gives an inclusion of ENTIRE ideals in the SAME native germ ring. -/
theorem native_weighted_sum_le_mul {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (x : M) :
    nativeMultiplierIdeal (weightedSum_quasiPSH hu.1 hv.1 hr hs) 1 one_pos x ≤
      nativeMultiplierIdeal hu.1 r hr x * nativeMultiplierIdeal hv.1 s hs x := by
  intro g hg
  obtain ⟨F,hF,rfl⟩ := NativeHolGerm.exists_eq_mk (n := n) g
  have hmem := (nativeMultiplierIdeal_mem_mk_iff
    (weightedSum_quasiPSH hu.1 hv.1 hr hs) one_pos x F hF).mp hg
  obtain ⟨_,N,t,a,ht,ha,heq⟩ :=
    AnalyticMultiplierSubadditivity.multiplierIdeal_weighted_sum_le_mul hu hv hr hs x F hmem
  choose p q hp hq htEq using ht
  have htHol : ∀ i, HolomorphicAt n (t i) x := by
    intro i
    rw [htEq i]
    exact (hp i).1.mul (hq i).1
  have hspan : NativeHolGerm.mk F hF ∈ Ideal.span
      (Set.range fun i => NativeHolGerm.mk (t i) (htHol i)) :=
    (NativeAffineIdealWeight.mem_native_span_mk_iff t htHol F hF).mpr
      ⟨hF,N,t,a,fun i => Set.mem_range_self i,ha,heq⟩
  apply (Ideal.span_le.mpr ?_) hspan
  rintro h ⟨i,rfl⟩
  have htNative : NativeHolGerm.mk (t i) (htHol i) =
      NativeHolGerm.mk (p i) (hp i).1 * NativeHolGerm.mk (q i) (hq i).1 := by
    apply Subtype.ext
    exact congrArg (Germ.ofFun : (M → ℂ) → Germ (𝓝 x) ℂ) (htEq i)
  change NativeHolGerm.mk (t i) (htHol i) ∈
    nativeMultiplierIdeal hu.1 r hr x * nativeMultiplierIdeal hv.1 s hs x
  rw [htNative]
  exact Ideal.mul_mem_mul
    ((nativeMultiplierIdeal_mem_mk_iff hu.1 hr x (p i) (hp i).1).mpr (hp i))
    ((nativeMultiplierIdeal_mem_mk_iff hv.1 hs x (q i) (hq i).1).mpr (hq i))
end Native

section Affine
variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
local instance affineProductTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance affineProductCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance affineProductManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- The actual original affine native multiplier ideal in the standard exp(-2cu) convention. -/
def affineMultiplierIdeal {m : ℕ} (a : Fin m → R) (c : ℝ) (hc : 0 < c) (x : SchemeComplexPoint f) :
    Ideal (NativeHolGerm n (SchemeComplexPoint f) x) :=
  nativeMultiplierIdeal (NativeAffineIdealWeight.weight_quasiPSH f n a) (2*c) (by positivity) x

/-- The actual independent-level sum of the original affine ideal weights. -/
def affineWeightedSumIdeal {m k : ℕ} (a : Fin m → R) (b : Fin k → R)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (x : SchemeComplexPoint f) :
    Ideal (NativeHolGerm n (SchemeComplexPoint f) x) :=
  nativeMultiplierIdeal (weightedSum_quasiPSH
    (NativeAffineIdealWeight.weight_quasiPSH f n a) (NativeAffineIdealWeight.weight_quasiPSH f n b)
    (by positivity : 0 < 2*r) (by positivity : 0 < 2*s)) 1 one_pos x

/-- The SAME original product tuple has exactly the whole native ideal of the same-level weighted sum. -/
theorem affine_product_eq_weighted_sum {m k : ℕ} (a : Fin m → R) (b : Fin k → R)
    (c : ℝ) (hc : 0 < c) (x : SchemeComplexPoint f) :
    affineMultiplierIdeal f n (NativeAffineIdealWeight.productGenerators a b) c hc x =
      affineWeightedSumIdeal f n a b c c hc hc x := by
  ext g
  obtain ⟨F,hF,rfl⟩ := NativeHolGerm.exists_eq_mk (n := n) g
  rw [affineMultiplierIdeal,affineWeightedSumIdeal,nativeMultiplierIdeal_mem_mk_iff,
    nativeMultiplierIdeal_mem_mk_iff]
  have heq : (fun y => (((2*c : ℝ) : EReal))*NativeAffineIdealWeight.weight f a y+
      (((2*c : ℝ) : EReal))*NativeAffineIdealWeight.weight f b y) =
      fun y => (((2*c : ℝ) : EReal))*NativeAffineIdealWeight.weight f
        (NativeAffineIdealWeight.productGenerators a b) y := by
    funext y
    rw [NativeAffineIdealWeight.weight_product]
    exact (EReal.left_distrib_of_nonneg_of_ne_top (by positivity) (EReal.coe_ne_top _) _ _).symm
  rw [heq]
  change (HolomorphicAt n F x ∧ _) ↔ (HolomorphicAt n F x ∧ _)
  apply and_congr_right
  intro _
  change MultiplierIntegrableAt
    (chartFunction (NativeAffineIdealWeight.weight f (NativeAffineIdealWeight.productGenerators a b))
      (complexChartAt (n := n) x)) (2*c) _ _ volume ↔
    MultiplierIntegrableAt (fun z => (((2*c : ℝ) : EReal)) *
      chartFunction (NativeAffineIdealWeight.weight f (NativeAffineIdealWeight.productGenerators a b))
        (complexChartAt (n := n) x) z) 1 _ _ volume
  simpa only [one_mul] using
    (PositiveCurrentTraceMultiplier.multiplierIntegrableAt_coe_mul_iff
      (w := chartFunction (NativeAffineIdealWeight.weight f (NativeAffineIdealWeight.productGenerators a b))
        (complexChartAt (n := n) x))
      (c := 1) (t := 2*c) (f := fun z => F ((complexChartAt (n := n) x).val.symm z))
      (z := (complexChartAt (n := n) x).val x) (μ := volume) one_pos (by positivity)).symm

variable [IsDomain R]

/-- Independent positive original ideal levels satisfy actual whole native ring ideal subadditivity. -/
theorem affine_weighted_sum_le_mul {m k : ℕ} (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (a : Fin m → R) (b : Fin k → R)
    (ha : Ideal.span (Set.range a) = I) (hb : Ideal.span (Set.range b) = J)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (x : SchemeComplexPoint f) :
    affineWeightedSumIdeal f n a b r s hr hs x ≤
      affineMultiplierIdeal f n a r hr x * affineMultiplierIdeal f n b s hs x := by
  have hna : Ideal.span (Set.range a) ≠ ⊥ := fun hz => hI (ha.symm.trans hz)
  have hnb : Ideal.span (Set.range b) ≠ ⊥ := fun hz => hJ (hb.symm.trans hz)
  exact native_weighted_sum_le_mul
    (NativeAffineIdealWeight.weight_isGlobalQuasiPshPotential f n a hna)
    (NativeAffineIdealWeight.weight_isGlobalQuasiPshPotential f n b hnb) (by positivity) (by positivity) x

/-- The actual original product tuple satisfies whole native ideal subadditivity at every positive standard level. -/
theorem affine_product_le_mul {m k : ℕ} (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (a : Fin m → R) (b : Fin k → R)
    (ha : Ideal.span (Set.range a) = I) (hb : Ideal.span (Set.range b) = J)
    (c : ℝ) (hc : 0 < c) (x : SchemeComplexPoint f) :
    affineMultiplierIdeal f n (NativeAffineIdealWeight.productGenerators a b) c hc x ≤
      affineMultiplierIdeal f n a c hc x * affineMultiplierIdeal f n b c hc x := by
  rw [affine_product_eq_weighted_sum f n a b c hc x]
  exact affine_weighted_sum_le_mul f n I J hI hJ a b ha hb c c hc hc x

end Affine
end EnvelopeProperty.Char0.NativeMultiplierProduct
