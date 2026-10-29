import EnvelopeProperty.AlgGeom.NativeLineFSPowerData

/-! # Actual original full FS and psh compare with EVERY genuine positive line power -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Scheme.Modules
open scoped Classical NNReal ENNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativeLineFubiniStudy
open Berkovich CanonicalGeometry SchemeGlobalSectionModelNormIsometries
open SchemeModuleIsoGlobalSections BundleTensorPowerPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
  (L : X.Modules) (hL : IsInvertible L)

/-- Actual original finite rational FS transports to ANY positive actual power line with its TRUE divided coefficient. -/
theorem IsFinFS.toPowerLine (r : ℕ) (hr : 0 < r) {a : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hφ : IsFinFS p L hL a φ) :
    IsFinFS p (bundleTensorPower L r) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r)
      (a/(r : ℚ)) φ := by
  obtain ⟨D,hD,hNZ,hφ⟩ := hφ
  refine ⟨D.toPowerLine L r hr,hD.toPowerLine L r hr,?_,?_⟩
  · intro y
    obtain ⟨q,hq,hq0⟩ := hNZ y
    refine ⟨_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_⟩
    exact (powerLineSection_norm p L hL D.deg r q.1 y).symm ▸ pow_ne_zero _ hq0
  · intro y
    exact (hφ y).trans (D.toPowerLine_eval p L hL r hr y).symm

/-- EVERY actual original finite rational power-line family realizes a genuine original FS function. -/
theorem IsFinFS.fromPowerLine (r : ℕ) {b : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hφ : IsFinFS p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) b φ) :
    IsFinFS p L hL ((r : ℚ)*b) φ := by
  obtain ⟨D,hD,hNZ,hφ⟩ := hφ
  refine ⟨D.fromPowerLine L r,hD.fromPowerLine L r,?_,?_⟩
  · intro y
    obtain ⟨q,hq,hq0⟩ := hNZ y
    refine ⟨_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_⟩
    have he := globalSectionNorm_moduleIso _root_.Valuation.one_apply_le_one y
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) D.deg)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (r*D.deg))
      (powerMulIso L r D.deg) q.1
    exact he.symm ▸ hq0
  · intro y
    exact (hφ y).trans (D.fromPowerLine_eval p L hL r y).symm

/-- Exact genuine finite rational original FS equivalence for EVERY actual positive line power. -/
theorem isFinFS_iff_powerLine (r : ℕ) (hr : 0 < r) (a : ℚ)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsFinFS p L hL a φ ↔ IsFinFS p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) (a/(r : ℚ)) φ := by
  constructor
  · exact fun h => h.toPowerLine p L hL r hr
  · intro h
    have hh := h.fromPowerLine p L hL r
    have hc : (r : ℚ)*(a/(r : ℚ)) = a := by field_simp [Nat.ne_of_gt hr]
    rwa [hc] at hh

/-- Actual original finite FS directed nets retain their TRUE divided real coefficient on power lines. -/
theorem IsFiniteFSNetLimit.toPowerLine (r : ℕ) (hr : 0 < r) {θ : ℝ}
    {u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hu : IsFiniteFSNetLimit p L hL θ u) :
    IsFiniteFSNetLimit p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) (θ/(r : ℝ)) u := by
  obtain ⟨hfin,husc,J,hJ,hdir,hn,a,v,hv,ha,hanti,hlim⟩ := hu
  let : Preorder J := hJ
  let : IsDirected J (· ≤ ·) := hdir
  let : Nonempty J := hn
  exact ⟨hfin,husc,J,hJ,hdir,hn,(fun j => a j/(r : ℚ)),v,
    (fun j => (hv j).toPowerLine p L hL r hr),
    by simpa only [Rat.cast_div,Rat.cast_natCast] using ha.div_const (r : ℝ),hanti,hlim⟩

/-- Actual original finite power-line FS nets realize original FS nets with coefficient multiplied by r. -/
theorem IsFiniteFSNetLimit.fromPowerLine (r : ℕ) {η : ℝ}
    {u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hu : IsFiniteFSNetLimit p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) η u) :
    IsFiniteFSNetLimit p L hL ((r : ℝ)*η) u := by
  obtain ⟨hfin,husc,J,hJ,hdir,hn,a,v,hv,ha,hanti,hlim⟩ := hu
  let : Preorder J := hJ
  let : IsDirected J (· ≤ ·) := hdir
  let : Nonempty J := hn
  exact ⟨hfin,husc,J,hJ,hdir,hn,(fun j => (r : ℚ)*a j),v,
    (fun j => (hv j).fromPowerLine p L hL r),
    by simpa only [Rat.cast_mul,Rat.cast_natCast] using (tendsto_const_nhds.mul ha),hanti,hlim⟩

/-- Exact original finite rational FS-net criterion for EVERY actual positive line power, all real coefficients. -/
theorem isFiniteFSNetLimit_iff_powerLine (r : ℕ) (hr : 0 < r) (θ : ℝ)
    (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsFiniteFSNetLimit p L hL θ u ↔ IsFiniteFSNetLimit p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) (θ/(r : ℝ)) u := by
  constructor
  · exact fun h => h.toPowerLine p L hL r hr
  · intro h
    have hh := h.fromPowerLine p L hL r
    have hc : (r : ℝ)*(θ/(r : ℝ)) = θ := by field_simp [Nat.ne_of_gt hr]
    rwa [hc] at hh

variable [IsIntegral X]

/-- FULL original FS transports by genuine positive powers, with nonzero original sections internally retained. -/
theorem IsFS.toPowerLine (r : ℕ) (hr : 0 < r) {a : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hφ : IsFS p L hL a φ) :
    IsFS p (bundleTensorPower L r) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r)
      (a/(r : ℚ)) φ := by
  obtain ⟨D,hD,hφ⟩ := hφ
  obtain ⟨y,hy⟩ := (D.nonzero_iff_exists_eval_ne_bot p L hL).mp hD
  refine ⟨D.toPowerLine L r hr,?_,fun z => (hφ z).trans (D.toPowerLine_eval p L hL r hr z).symm⟩
  apply ((D.toPowerLine L r hr).nonzero_iff_exists_eval_ne_bot p (bundleTensorPower L r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r)).mpr
  exact ⟨y,(D.toPowerLine_eval p L hL r hr y).symm ▸ hy⟩

/-- EVERY actual original full power-line FS family realizes an original full FS function. -/
theorem IsFS.fromPowerLine (r : ℕ) {b : ℚ}
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hφ : IsFS p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) b φ) :
    IsFS p L hL ((r : ℚ)*b) φ := by
  obtain ⟨D,hD,hφ⟩ := hφ
  obtain ⟨y,hy⟩ := (D.nonzero_iff_exists_eval_ne_bot p (bundleTensorPower L r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r)).mp hD
  refine ⟨D.fromPowerLine L r,?_,fun z => (hφ z).trans (D.fromPowerLine_eval p L hL r z).symm⟩
  apply ((D.fromPowerLine L r).nonzero_iff_exists_eval_ne_bot p L hL).mpr
  exact ⟨y,(D.fromPowerLine_eval p L hL r y).symm ▸ hy⟩

/-- Exact FULL independently defined original FS comparison for ANY positive actual original line power. -/
theorem isFS_iff_powerLine (r : ℕ) (hr : 0 < r) (a : ℚ)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsFS p L hL a φ ↔ IsFS p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) (a/(r : ℚ)) φ := by
  constructor
  · exact fun h => h.toPowerLine p L hL r hr
  · intro h
    have hh := h.fromPowerLine p L hL r
    have hc : (r : ℚ)*(a/(r : ℚ)) = a := by field_simp [Nat.ne_of_gt hr]
    rwa [hc] at hh

/-- Actual full original psh nets transport with their TRUE divided real coefficient to any positive original power line. -/
theorem IsPSH.toPowerLine (r : ℕ) (hr : 0 < r) {θ : ℝ}
    {u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hu : IsPSH p L hL θ u) :
    IsPSH p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) (θ/(r : ℝ)) u := by
  obtain ⟨hfin,husc,J,hJ,hdir,hn,a,v,hv,ha,hanti,hlim⟩ := hu
  let : Preorder J := hJ
  let : IsDirected J (· ≤ ·) := hdir
  let : Nonempty J := hn
  exact ⟨hfin,husc,J,hJ,hdir,hn,(fun j => a j/(r : ℚ)),v,
    (fun j => (hv j).toPowerLine p L hL r hr),
    by simpa only [Rat.cast_div,Rat.cast_natCast] using ha.div_const (r : ℝ),hanti,hlim⟩

/-- EVERY actual original full power-line psh net realizes true original psh with coefficient multiplied by r. -/
theorem IsPSH.fromPowerLine (r : ℕ) {η : ℝ}
    {u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hu : IsPSH p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) η u) :
    IsPSH p L hL ((r : ℝ)*η) u := by
  obtain ⟨hfin,husc,J,hJ,hdir,hn,a,v,hv,ha,hanti,hlim⟩ := hu
  let : Preorder J := hJ
  let : IsDirected J (· ≤ ·) := hdir
  let : Nonempty J := hn
  exact ⟨hfin,husc,J,hJ,hdir,hn,(fun j => (r : ℚ)*a j),v,
    (fun j => (hv j).fromPowerLine p L hL r),
    by simpa only [Rat.cast_mul,Rat.cast_natCast] using (tendsto_const_nhds.mul ha),hanti,hlim⟩

/-- Exact FULL original whole-section psh comparison for ANY positive actual original line power, all real coefficients. -/
theorem isPSH_iff_powerLine (r : ℕ) (hr : 0 < r) (θ : ℝ)
    (u : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsPSH p L hL θ u ↔ IsPSH p (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) (θ/(r : ℝ)) u := by
  constructor
  · exact fun h => h.toPowerLine p L hL r hr
  · intro h
    have hh := h.fromPowerLine p L hL r
    have hc : (r : ℝ)*(θ/(r : ℝ)) = θ := by field_simp [Nat.ne_of_gt hr]
    rwa [hc] at hh
end EnvelopeProperty.NativeLineFubiniStudy
