import SGPT.Okounkov.TailFlag
import TranscendentalNakamaye.Pending.SubmanifoldKahlerRestriction

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff
open TranscendentalNakamaye.FirstPass
open TranscendentalNakamaye.FirstPass.PositiveClasses
open TranscendentalNakamaye.FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending

/-- Actual original geometric input to dimension recursion: the original
compact connected Kähler manifold and its actual smooth flag. -/
structure OriginalFlagGeometry (n : ℕ) where
  carrier : Type u
  topology : TopologicalSpace carrier
  charts : letI := topology; ChartedSpace (ComplexModel n) carrier
  complex : letI := topology; letI := charts; IsComplexManifold n carrier
  compact : letI := topology; CompactSpace carrier
  connected : letI := topology; ConnectedSpace carrier
  omega : letI := topology; letI := charts; letI := complex;
    KahlerBackground n carrier
  flag : Fin (n + 1) → Set carrier
  smooth : letI := topology; letI := charts; letI := complex; IsSmoothFlag flag

namespace OriginalFlagGeometry

instance carrierTopology {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    TopologicalSpace F.carrier := F.topology
instance carrierCharts {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    ChartedSpace (ComplexModel n) F.carrier := F.charts
instance carrierComplex {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    IsComplexManifold n F.carrier := F.complex
instance carrierCompact {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    CompactSpace F.carrier := F.compact
instance carrierConnected {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    ConnectedSpace F.carrier := F.connected

/-- The bundle retains precisely the original given objects. -/
def ofOriginal {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [ConnectedSpace M] (omega : KahlerBackground n M)
    (Y : Fin (n + 1) → Set M) (hY : IsSmoothFlag Y) : OriginalFlagGeometry n where
  carrier := M
  topology := inferInstance
  charts := inferInstance
  complex := inferInstance
  compact := inferInstance
  connected := inferInstance
  omega := omega
  flag := Y
  smooth := hY

/-- The original first carrier has its actual codimension-one dimension. -/
theorem firstDivisor {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) :
    IsClosedConnectedSubmanifold (m + 1) (F.flag (1 : Fin (m + 2))) m := by
  simpa only [Fin.val_one, Nat.add_sub_cancel] using F.smooth.2.2 (1 : Fin (m + 2))

/-- The true source tail: original subtype topology, genuine inherited atlas,
restricted Kähler form and exactly the shifted original flag carriers. -/
def tail {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) : OriginalFlagGeometry m := by
  let W := F.flag (1 : Fin (m + 2))
  let hW : IsClosedConnectedSubmanifold (m + 1) W m := F.firstDivisor
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hW.2.2
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hW.2.2
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  letI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  exact {
    carrier := W
    topology := inferInstance
    charts := inferInstance
    complex := inferInstance
    compact := inferInstance
    connected := inferInstance
    omega := SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ m) hW.2.2 F.omega
    flag := tailFlag F.flag
    smooth := F.smooth.tail_isSmoothFlag }

end OriginalFlagGeometry

end SGPT.Okounkov
