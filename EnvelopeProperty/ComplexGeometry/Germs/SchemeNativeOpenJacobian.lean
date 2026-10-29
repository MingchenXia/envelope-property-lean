import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeMorphismCoordinates
import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeOpenImmersionInverse
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HolomorphicGermJacobian

/-! # Actual centered-chart Jacobians of original open immersions -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HolomorphicGerms.NativeOpenJacobian

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter Manifold
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HironakaHolomorphicJetChartInvariance HolomorphicGermJacobian HolomorphicMaps
open scoped Topology Manifold ContDiff

section Manifold
variable {n : ℕ} {M N L : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
  [TopologicalSpace L] [ChartedSpace (ComplexModel n) L] [IsComplexManifold n L]

omit [IsComplexManifold n M] [IsComplexManifold n N] in
/-- The derivative of the actual centered coordinate map is the actual manifold derivative. -/
theorem centeredCoordinateMap_fderiv (b : N → M)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N) :
    fderiv ℂ (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) b y) 0 =
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) b y := by
  let e := (complexChartAt (n := n) y).val
  let e' := (complexChartAt (n := n) (b y)).val
  let raw := fun u => e' (b (e.symm u))
  have hbd := (hb y).mdifferentiableAt (by simp)
  have hm : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) b y =
      fderiv ℂ raw (e y) := by
    rw [hbd.mfderiv]
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
      Function.comp_id, Set.range_id, fderivWithin_univ]
    rfl
  have hraw : DifferentiableAt ℂ raw (e y) := by
    have hc := (contMDiffAt_iff.mp (hb y)).2
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id] at hc
    change ContDiffWithinAt ℂ ∞ raw Set.univ (e y) at hc
    exact (hc.differentiableWithinAt (by simp)).differentiableAt (by simp)
  change fderiv ℂ (fun u => raw (u + e y) - e' (b y)) 0 = _
  rw [fderiv_sub_const, hm]
  have ha : HasFDerivAt (fun u : ComplexModel n => u + e y)
      (ContinuousLinearMap.id ℂ (ComplexModel n)) 0 :=
    (hasFDerivAt_id (0 : ComplexModel n)).add_const (e y)
  have hraw' : HasFDerivAt raw (fderiv ℂ raw (e y)) (0 + e y) := by
    simpa only [zero_add] using hraw.hasFDerivAt
  have he := hraw'.comp (0 : ComplexModel n) ha
  simpa only [zero_add, ContinuousLinearMap.comp_id, Function.comp_def] using he.fderiv

omit [IsComplexManifold n N] in
private theorem centeredPoint_tendsto (y : N) :
    Tendsto (fun z : ComplexModel n => (complexChartAt (n := n) y).val.symm
      (z + (complexChartAt (n := n) y).val y)) (𝓝 0) (𝓝 y) := by
  let e := (complexChartAt (n := n) y).val
  have hs := mem_complexChartAt_source (n := n) y
  have hAdd : Tendsto (fun z : ComplexModel n => z + e y) (𝓝 0) (𝓝 (e y)) := by
    simpa only [zero_add] using (continuous_add_const (e y)).tendsto (0 : ComplexModel n)
  have he := (e.continuousAt_symm (e.map_source hs)).tendsto.comp hAdd
  simpa only [e.left_inv hs, Function.comp_def] using he

omit [IsComplexManifold n M] [IsComplexManifold n N] [IsComplexManifold n L] in
/-- Actual centered coordinate maps compose as WHOLE germs in the SAME intermediate chart. -/
theorem centeredCoordinateMap_comp_eventually (b : N → M) (c : M → L)
    (hb : Continuous b) (y : N) :
    NativeHolGerm.centeredCoordinateMap (k := n) (n := n) (c ∘ b) y =ᶠ[𝓝 (0 : ComplexModel n)]
      (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) c (b y) ∘ NativeHolGerm.centeredCoordinateMap (k := n) (n := n) b y) := by
  let e := (complexChartAt (n := n) y).val
  let e' := (complexChartAt (n := n) (b y)).val
  have hNear : ∀ᶠ z : ComplexModel n in 𝓝 0, b (e.symm (z + e y)) ∈ e'.source :=
    (hb.continuousAt.tendsto.comp (centeredPoint_tendsto y)).eventually
      (e'.open_source.mem_nhds (mem_complexChartAt_source (n := n) (b y)))
  filter_upwards [hNear] with z hz
  simp only [NativeHolGerm.centeredCoordinateMap, coordinateMap, Function.comp_apply]
  rw [sub_add_cancel, e'.left_inv hz]

private theorem jacobianGerm_congr {F G : ComplexModel n → ComplexModel n}
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (h : F =ᶠ[𝓝 0] G) :
    jacobianGerm F hF = jacobianGerm G hG := by
  unfold jacobianGerm
  congr 1
  funext i j
  apply congrArg (HolomorphicGermCoordinateDerivation.coordinatePartial j)
  apply HolGerm.mk_eq_mk_iff.mpr
  exact h.mono fun z hz => congrArg (fun w : ComplexModel n => w i) hz

/-- The actual whole Jacobian chain rule uses precisely the original intermediate chart. -/
theorem centeredCoordinateMap_jacobianGerm_comp (b : N → M) (c : M → L)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    (hc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c) (y : N) :
    jacobianGerm (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) (c ∘ b) y)
      (NativeHolGerm.centeredCoordinateMap_holomorphic (k := n) (n := n) _ (hc.comp hb) y) =
    compAlgHom (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) b y)
      (NativeHolGerm.centeredCoordinateMap_holomorphic (k := n) (n := n) b hb y)
      (NativeHolGerm.centeredCoordinateMap_zero (k := n) (n := n) b y)
      (jacobianGerm (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) c (b y))
        (NativeHolGerm.centeredCoordinateMap_holomorphic (k := n) (n := n) c hc (b y))) *
    jacobianGerm (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) b y)
      (NativeHolGerm.centeredCoordinateMap_holomorphic (k := n) (n := n) b hb y) := by
  apply (jacobianGerm_congr _ _ (centeredCoordinateMap_comp_eventually b c hb.continuous y)).trans
  exact jacobianGerm_comp _ _ _ _ _

/-- A holomorphic actual left inverse forces the actual centered-chart Jacobian to be a unit. -/
theorem centeredCoordinateMap_jacobianGerm_isUnit_of_leftInverse (b : N → M)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    (s : M → N) (hleft : Function.LeftInverse s b) (y : N)
    (hs : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s (b y)) :
    IsUnit (jacobianGerm (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) b y)
      (NativeHolGerm.centeredCoordinateMap_holomorphic (k := n) (n := n) b hb y)) := by
  have hbd := (hb y).mdifferentiableAt (by simp)
  have hsd := hs.mdifferentiableAt (by simp)
  have he : s ∘ b = id := funext hleft
  have hd : (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s (b y)).comp
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) b y) =
        ContinuousLinearMap.id ℂ (ComplexModel n) := by
    rw [← mfderiv_comp y hsd hbd, he, mfderiv_id]
    rfl
  have hinj : Function.Injective (fderiv ℂ (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) b y) 0) := by
    rw [centeredCoordinateMap_fderiv b hb y]
    apply Function.LeftInverse.injective (g := mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s (b y))
    intro v
    exact congrArg (fun a : ComplexModel n →L[ℂ] ComplexModel n => a v) hd
  have hdet : (fderiv ℂ (NativeHolGerm.centeredCoordinateMap (k := n) (n := n) b y) 0).toLinearMap.det ≠ 0 := by
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hinj)
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  change Germ.valueRingHom ((jacobianGerm _ _ : HolGerm (ComplexModel n)) :
    Germ (𝓝 (0 : ComplexModel n)) ℂ) ≠ 0
  rw [jacobianGerm_source]
  exact hdet

end Manifold

section Scheme

variable {Y Z : Scheme} (fY : Y ⟶ Spec (.of ℂ)) (fZ : Z ⟶ Spec (.of ℂ))
  (j : Z ⟶ Y) (hj : j ≫ fY = fZ) (n : ℕ)
  [SmoothOfRelativeDimension n fY] [SmoothOfRelativeDimension n fZ]

local instance openJacobianTargetTopology : TopologicalSpace (SchemeComplexPoint fY) :=
  schemeAnalyticPointTopology fY
local instance openJacobianSourceTopology : TopologicalSpace (SchemeComplexPoint fZ) :=
  schemeAnalyticPointTopology fZ
local instance openJacobianTargetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fY) :=
  schemeAnalyticComplexChartedSpace fY n
local instance openJacobianSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fZ) :=
  schemeAnalyticComplexChartedSpace fZ n

/-- Literal structural compatibility preserves actual native holomorphy of the SAME map. -/
theorem schemeComplexPointMap_contMDiff_of_structure (k : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) k
      (schemeComplexPointMap fZ fY j hj) := by
  cases hj
  exact schemeComplexPointMap_contMDiff fY j n n k

variable [IsSeparated fY] [QuasiCompact fY] [IsSeparated fZ] [QuasiCompact fZ]

local instance openJacobianTargetManifold : IsComplexManifold n (SchemeComplexPoint fY) :=
  schemeAnalyticComplex_isComplexManifold fY n
local instance openJacobianSourceManifold : IsComplexManifold n (SchemeComplexPoint fZ) :=
  schemeAnalyticComplex_isComplexManifold fZ n

/-- The SAME original open immersion has a UNIT actual centered-chart Jacobian.
The actual holomorphic inverse is constructed from the original open immersion,
then its literal left identity makes the actual derivative injective. -/
theorem schemeOpenImmersion_jacobianGerm_isUnit [IsOpenImmersion j]
    (q : SchemeComplexPoint fZ) :
    IsUnit (jacobianGerm
      (NativeHolGerm.centeredCoordinateMap (k := n) (n := n)
        (schemeComplexPointMap fZ fY j hj) q)
      (NativeHolGerm.centeredCoordinateMap_holomorphic
        (schemeComplexPointMap fZ fY j hj)
        (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) q)) := by
  let b := schemeComplexPointMap fZ fY j hj
  have heq : (𝟙 Z) ≫ fZ = j ≫ fY := by rw [Category.id_comp, hj]
  let s := schemeNativeOpenInverseMap fY fZ j (𝟙 Z) heq q
  have hleft : Function.LeftInverse s b := by
    intro x
    exact schemeNativeOpenInverseMap_left_inv fY fZ j (𝟙 Z) heq q j hj
      (Category.id_comp j) x ⟨schemeComplexPointImage fZ x, rfl⟩
  have hO : IsOpen {p : SchemeComplexPoint fY | schemeComplexPointImage fY p ∈ Set.range j} :=
    (IsOpenImmersion.isOpen_range j).preimage (schemeComplexPointImage_continuous fY)
  have hbq : schemeComplexPointImage fY (b q) ∈ Set.range j :=
    ⟨schemeComplexPointImage fZ q, (Scheme.Hom.comp_apply q.val j default).symm⟩
  have hs := schemeNativeOpenInverseMap_contMDiffOn fY fZ n n j (𝟙 Z) heq q ∞
  exact centeredCoordinateMap_jacobianGerm_isUnit_of_leftInverse b
    (schemeComplexPointMap_contMDiff_of_structure fY fZ j hj n ∞) s hleft q
    (hs.contMDiffAt (hO.mem_nhds hbq))

end Scheme

end HolomorphicGerms.NativeOpenJacobian
