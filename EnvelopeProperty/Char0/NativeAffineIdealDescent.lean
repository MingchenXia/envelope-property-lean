import EnvelopeProperty.Char0.NativeIdealSheafDescent
import EnvelopeProperty.Char0.NativeAffineIdealWeight
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal

/-! # Whole original affine ideal products detected by the actual native maps -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeAffineIdealDescent

open CategoryTheory AlgebraicGeometry ComplexSchemes HolomorphicGerms
open ComplexGeometry.Pluripotential
open NativeAffineIdealWeight

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ Spec (.of ℂ))
    (n : ℕ) [SmoothOfRelativeDimension n f]

local instance affineStructure : IsAffineHom f := isAffineHom_of_isAffine _
local instance affineTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance affineCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance affineManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- The whole original ideal sheaf has exactly the extension through the SAME
original affine-to-stalk-to-native coefficient map, at EVERY actual point. -/
theorem map_specIdealSheaf_stalk_eq_nativeMap (I : Ideal R) (p : SchemeComplexPoint f) :
    ((specIdealSheaf I).stalkIdeal (schemeComplexPointImage f p)).map
        (schemeNativeStalkGerm f n p) =
      I.map (nativeMap f n p) := by
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ ⟨⊤, isAffineOpen_top _⟩ trivial,
    specIdealSheaf_ideal_top, Ideal.map_map, Ideal.map_map]
  rfl

/-- EVERY whole original affine ideal containment is detected in ALL actual
native complex germ rings, without a domain or nonzero hypothesis. -/
theorem ideal_le_iff_nativeMap (I J : Ideal R) :
    I ≤ J ↔ ∀ p : SchemeComplexPoint f,
      I.map (nativeMap f n p) ≤ J.map (nativeMap f n p) := by
  calc
    I ≤ J ↔ specIdealSheaf I ≤ specIdealSheaf J := (specIdealSheaf_le_iff I J).symm
    _ ↔ ∀ p : SchemeComplexPoint f,
        ((specIdealSheaf I).stalkIdeal (schemeComplexPointImage f p)).map
          (schemeNativeStalkGerm f n p) ≤
        ((specIdealSheaf J).stalkIdeal (schemeComplexPointImage f p)).map
          (schemeNativeStalkGerm f n p) :=
      NativeIdealSheafDescent.idealSheaf_le_iff_nativeStalkGerm f n _ _
    _ ↔ ∀ p : SchemeComplexPoint f,
        I.map (nativeMap f n p) ≤ J.map (nativeMap f n p) := by
      exact forall_congr' fun p => by
        rw [map_specIdealSheaf_stalk_eq_nativeMap f n I p,
          map_specIdealSheaf_stalk_eq_nativeMap f n J p]

/-- The SAME whole original affine product containment is reflected by ALL
actual native maps; zero ideals and dimension zero are included. -/
theorem ideal_le_mul_iff_nativeMap (K I J : Ideal R) :
    K ≤ I * J ↔ ∀ p : SchemeComplexPoint f,
      K.map (nativeMap f n p) ≤
        I.map (nativeMap f n p) * J.map (nativeMap f n p) := by
  simpa only [Ideal.map_mul] using ideal_le_iff_nativeMap f n K (I * J)

end EnvelopeProperty.Char0.NativeAffineIdealDescent
