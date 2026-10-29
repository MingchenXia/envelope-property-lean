import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeStalkFlatness
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Whole ideal-sheaf containment detected in the actual native complex stalks -/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.NativeIdealSheafDescent

open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms
open ComplexGeometry.Pluripotential

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- Every original closed point is the image of an actual complex point over the original base. -/
theorem exists_complexPoint_image_of_isClosed [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ p : SchemeComplexPoint f, schemeComplexPointImage f p = x := by
  refine ⟨⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩, ?_⟩
  exact pointOfClosedPoint_apply f x hx _

variable (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance descentPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance descentPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance descentPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- Faithful flatness at ALL actual complex points detects the WHOLE original ideal-sheaf inclusion. -/
theorem idealSheaf_le_iff_nativeStalkGerm (I J : X.IdealSheafData) :
    I ≤ J ↔ ∀ p : SchemeComplexPoint f,
      (I.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f n p) ≤
        (J.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f n p) := by
  constructor
  · intro h p
    exact Ideal.map_mono (Scheme.IdealSheafData.stalkIdeal_mono h _)
  · intro h
    let : Smooth f := SmoothOfRelativeDimension.smooth n f
    let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
    apply Scheme.IdealSheafData.le_of_forall_stalkIdeal_le_of_isClosed
    intro x hx
    obtain ⟨p, hp⟩ := exists_complexPoint_image_of_isClosed f x hx
    rw [← hp]
    exact (ideal_le_iff_schemeNativeStalkGerm f n p _ _).mpr (h p)

/-- Products are the actual WHOLE products in the original sheaf and native germ rings. -/
theorem idealSheaf_le_mul_iff_nativeStalkGerm (I J K : X.IdealSheafData) :
    I ≤ J * K ↔ ∀ p : SchemeComplexPoint f,
      (I.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f n p) ≤
        (J.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f n p) *
          (K.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f n p) := by
  simpa only [Scheme.IdealSheafData.stalkIdeal_mul, Ideal.map_mul] using
    idealSheaf_le_iff_nativeStalkGerm f n I (J * K)

end EnvelopeProperty.Char0.NativeIdealSheafDescent
