import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingRatioEquiv

/-! # Literal original branch-product coefficients give the actual ratio identities

The whole coefficient equations are derived from the SAME original unit
factors and original branch/auxiliary generators. Unit roots remain whole.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.BranchRatios
variable {R : Type u} [CommRing R] {q : ℕ}
  (H : Fin q → Fin q) (d h : Fin q → R) (w : Fin q → Rˣ)
  (hH : ∀ i, H (H i) = H i) (hd : ∀ i, d (H i) = d i) (hh : ∀ i, h (H i) = 1)

/-- The literal SAME original coefficient, with its derived actual unit factor. -/
def rawCoefficient (i : Fin q) : R := (w i : R) * d i * h i

/-- The actual original unit factor for EVERY whole ratio-root equation. -/
def ratioUnit (i : Fin q) : Rˣ := if i = H i then w i else w i * (w (H i))⁻¹

/-- The SAME original generator in the actual ratio equation: original
branch at its head and original auxiliary member at EVERY other position. -/
def ratioGenerator (i : Fin q) : R := if i = H i then d i else h i

/-- Every actual whole ratio coefficient retains its ORIGINAL branch or
auxiliary generator and its actual original unit ratio. -/
def coefficient (i : Fin q) : R := (ratioUnit H w i : R) * ratioGenerator H d h i

include hH hh in
/-- Each distinguished ratio coefficient equals its SAME actual original
raw coefficient, proved from the absent original auxiliary generator. -/
theorem coefficient_head (i : Fin q) :
    coefficient H d h w (H i) = rawCoefficient d h w (H i) := by
  simp only [coefficient, ratioUnit, ratioGenerator, if_pos (hH i).symm,
    rawCoefficient, hh i, mul_one]

include hd hh in
/-- Every ORIGINAL raw coefficient is exactly the actual head coefficient
times its actual original ratio coefficient. This equality is proved. -/
theorem raw_mul_ratio (i : Fin q) (hi : i ≠ H i) :
    rawCoefficient d h w i = rawCoefficient d h w (H i) * coefficient H d h w i := by
  simp only [rawCoefficient, coefficient, ratioUnit, ratioGenerator, if_neg hi,
    Units.val_mul, hd i, hh i, mul_one]
  calc
    _ = (w i : R) * d i * h i *
        ((w (H i) : R) * (((w (H i))⁻¹ : Rˣ) : R)) := by rw [Units.mul_inv, mul_one]
    _ = _ := by ring

include hh in
/-- Nonzero SAME original branch generators give nonzero SAME original
head coefficients, without choosing a generic component. -/
theorem raw_head_ne_zero [IsDomain R] (hne : ∀ i, d i ≠ 0) (i : Fin q) :
    rawCoefficient d h w (H i) ≠ 0 := by
  rw [rawCoefficient, hh i, mul_one]
  exact mul_ne_zero (w (H i)).ne_zero (hne (H i))

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.BranchRatios
