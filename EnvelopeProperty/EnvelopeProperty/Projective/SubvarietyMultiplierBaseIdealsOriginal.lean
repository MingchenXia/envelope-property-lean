import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsActual
import EnvelopeProperty.Char0.MultiplierFamilySmoothness

/-! # Original algebraic smooth charts supply the SAME multiplier cone sequence -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
variable {k : Type u} [Field k] [CharZero k] {M : ℕ} (X : ProjSubvariety k M)

/-- The ACTUAL original multiplier cone sequence, with original smooth charts
as the sole smoothness datum. Every native family hypothesis is internally proved. -/
def originalMultiplierConeIdeal (hs : X.HasSmoothCharts) (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m : ℕ) : Ideal X.ConeRing := by
  let _ : Smooth (familyAbsoluteStructure X) :=
    Char0.MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  exact multiplierConeIdeal X d φ hC m

/-- The SAME original obstacle cone ideal is contained in the constructed
multiplier ideal with no native-model or comparison certificate input. -/
theorem coneObstacleIdeal_le_originalMultiplierConeIdeal
    (hs : X.HasSmoothCharts) (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) :
    X.coneObstacleIdeal d φ m ≤ originalMultiplierConeIdeal X hs d φ hC m := by
  let _ : Smooth (familyAbsoluteStructure X) :=
    Char0.MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  exact coneObstacleIdeal_le_multiplierConeIdeal X d φ hC hm

/-- Actual original multiplier subadditivity reaches the SAME original
cone saturation from only the ORIGINAL algebraic input data. -/
theorem originalMultiplierConeIdeal_mul_le_saturation
    (hs : X.HasSmoothCharts) (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m l : ℕ) :
    originalMultiplierConeIdeal X hs d φ hC (m * l) ≤
      X.saturation (originalMultiplierConeIdeal X hs d φ hC m ^ l) := by
  let _ : Smooth (familyAbsoluteStructure X) :=
    Char0.MultiplierFamilySmoothness.familyAbsoluteStructure_smooth X hs
  exact multiplierConeIdeal_mul_le_saturation X d φ hC m l

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
