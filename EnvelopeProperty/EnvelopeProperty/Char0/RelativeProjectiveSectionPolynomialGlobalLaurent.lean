import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialCharts
import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialSupport

/-! # An original whole O(e) section has one entire nonnegative Laurent expression -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual original chart coefficient multiplied by its OWN original coordinate power. -/
def sectionLaurent (i j : σ) (e : ℕ)
    (s : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤)) :
    originalLaurent (R := R) (σ := σ) :=
  chartToLaurent i (nativeCoefficient i j e s) * originalPolynomialToLaurent (X i) ^ e

/-- Native WHOLE frame transitions and native actual restriction naturality make all original shifted Laurent expressions equal. -/
theorem sectionLaurent_eq (i k j : σ) (e : ℕ)
    (s : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤)) :
    sectionLaurent i j e s = sectionLaurent k j e s := by
  have h := congrArg (overlapToLaurent (R := R) i k) (nativeCoefficient_overlap i k j e s)
  simp only [map_mul, map_pow, overlapToLaurent_restrict_left, overlapToLaurent_restrict_right] at h
  unfold sectionLaurent
  rw [h]
  calc
    _ = chartToLaurent k (nativeCoefficient k j e s) *
        (overlapToLaurent i k (coordinateOpenTransitionUnit (R := R) i k) *
          originalPolynomialToLaurent (X i)) ^ e := by rw [mul_pow]; ring
    _ = _ := by rw [overlapToLaurent_transition_clear]

/-- The original shifted expression has its actual allowed Laurent support on every original chart. -/
theorem sectionLaurent_mem_singleton [LinearOrder σ] [Fintype σ]
    (i j : σ) (e : ℕ) (s : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤)) :
    sectionLaurent i j e s ∈
      subsetHomogeneousLaurentModule (K := R) (I := ULift.{u} σ) (e : ℤ) {ULift.up i} :=
  originalAwayToLaurent_shift_mem i e ((chartAwayEquiv i).symm (nativeCoefficient i j e s))

/-- The SAME original whole expression belongs to the actual empty-coordinate polynomial piece, including a single projective coordinate. -/
theorem sectionLaurent_mem_empty [LinearOrder σ] [Fintype σ]
    (j : σ) (e : ℕ) (s : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤)) :
    sectionLaurent j j e s ∈
      subsetHomogeneousLaurentModule (K := R) (I := ULift.{u} σ) (e : ℤ) ∅ := by
  let : Nonempty (ULift.{u} σ) := ⟨ULift.up j⟩
  apply compatible_singleton_laurent_mem_empty e
  rintro ⟨i⟩
  rw [sectionLaurent_eq j i j e s]
  exact sectionLaurent_mem_singleton i j e s

end EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
