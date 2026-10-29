import EnvelopeProperty.Vanishing.NadelCanonicalMixedRescale
import EnvelopeProperty.Vanishing.NadelCanonicalMixedUnitCover
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingTensor
import EnvelopeProperty.Vanishing.NadelMixedKummerResidue

/-! # Actual whole purification of original mixed coefficients after the whole tame unit cover -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed

open NadelMixedKummer NadelAdaptedChartMatching
open scoped TensorProduct

variable {R : Type u} [CommRing R] {q : ℕ} (N : Fin q → ℕ)
    (u : Fin q → Rˣ) (hN : ∀ i, 0 < N i) (h : Fin q → R)

/-- The SAME original unit-weighted mixed coefficients. -/
def weightedCoefficient (i : Fin q) : R := (u i : R) * h i

/-- Every actual original coefficient is purified by the original entire unit-root cover, with no chosen root. -/
theorem purifiedCoefficient (i : Fin q) :
    algebraMap R (UnitCover N u) (weightedCoefficient u h i) =
      (unitCover_rootUnit N u hN i : UnitCover N u) ^ N i *
        algebraMap R (UnitCover N u) (h i) := by
  rw [weightedCoefficient, map_mul, unitCover_rootUnit_coe, NadelMixedKummer.root_pow]

/-- The original WHOLE mixed algebra becomes the actual pure quotient on the entire faithful coefficient cover. -/
def purificationAlgEquiv :
    UnitCover N u ⊗[R] NadelMixedKummer.Ring N (weightedCoefficient u h) ≃ₐ[UnitCover N u]
      NadelMixedKummer.Ring N (fun i => algebraMap R (UnitCover N u) (h i)) :=
  (BaseChange.tensorAlgEquiv N (weightedCoefficient u h)).trans
    (rescaleAlgEquiv N
      (fun i => algebraMap R (UnitCover N u) (weightedCoefficient u h i))
      (fun i => algebraMap R (UnitCover N u) (h i)) (unitCover_rootUnit N u hN)
      (purifiedCoefficient N u hN h))

/-- The actual purification preserves every SAME original mixed root with its genuine full unit factor. -/
theorem purificationAlgEquiv_root (i : Fin q) :
    purificationAlgEquiv N u hN h
      (Algebra.TensorProduct.includeRight (NadelMixedKummer.root N (weightedCoefficient u h) i)) =
        algebraMap (UnitCover N u)
          (NadelMixedKummer.Ring N (fun j => algebraMap R (UnitCover N u) (h j)))
            (unitCover_rootUnit N u hN i : UnitCover N u) *
          NadelMixedKummer.root N (fun j => algebraMap R (UnitCover N u) (h j)) i := by
  rw [purificationAlgEquiv, AlgEquiv.trans_apply, BaseChange.tensorAlgEquiv_root]
  exact scaleHom_root N
    (fun j => algebraMap R (UnitCover N u) (weightedCoefficient u h j))
    (fun j => algebraMap R (UnitCover N u) (h j)) (unitCover_rootUnit N u hN)
    (purifiedCoefficient N u hN h) i

variable {n : ℕ} (x : Fin n → R) (active : Set (Fin q)) (σ : active ↪ Fin n)

/-- Original active coordinates and ALL inactive unit-one coefficients are retained. -/
def pureCoefficient (i : Fin q) : R := by
  classical
  exact if hi : i ∈ active then x (σ ⟨i, hi⟩) else 1

/-- The actual native mixed coefficients are the original units times exactly these pure original coordinates. -/
theorem mixedCoefficient_eq_weighted (i : Fin q) :
    mixedCoefficient x active σ u i = weightedCoefficient u (pureCoefficient x active σ) i := by
  classical
  by_cases hi : i ∈ active
  · simp only [mixedCoefficient, pureCoefficient, weightedCoefficient, dif_pos hi]
  · simp only [mixedCoefficient, pureCoefficient, weightedCoefficient, dif_neg hi, mul_one]

/-- Actual original mixed geometric data produce the WHOLE purification isomorphism internally. -/
def mixedPurificationAlgEquiv :
    UnitCover N u ⊗[R] NadelMixedKummer.Ring N (mixedCoefficient x active σ u) ≃ₐ[UnitCover N u]
      NadelMixedKummer.Ring N
        (fun i => algebraMap R (UnitCover N u) (pureCoefficient x active σ i)) := by
  rw [funext (mixedCoefficient_eq_weighted u x active σ)]
  exact purificationAlgEquiv N u hN (pureCoefficient x active σ)

end EnvelopeProperty.Vanishing.NadelCanonicalMixed
