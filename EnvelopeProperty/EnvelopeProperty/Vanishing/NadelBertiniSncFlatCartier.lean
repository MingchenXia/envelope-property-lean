import EnvelopeProperty.Vanishing.NadelBertiniSncFlatSelected
import EnvelopeProperty.Vanishing.NadelBertiniSncFlatFrame
import EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartProjective
import EnvelopeProperty.Vanishing.NadelBertiniGenericIncidence
import Hironaka.Scheme.BlowUp.Invertible

/-! # The SAME original good-parameter hyperplane is an actual Cartier divisor -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatCartier
open NadelBertiniUniversal NadelBertiniProjectiveFrames NadelBertiniFibreSection
  NadelBertiniFibreSmooth NadelBertiniIncidenceChartProjective NadelBertiniRationalParameter
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual coordinate chart and original parameter triangle produce regularity
of the SAME original selected coefficient, with its actual scalar structure. -/
theorem projective_selected_coefficient_regular
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    (a : Fin (m + 1) → k)
    (ha : ∀ t, parameterMap a t ∈ NadelBertiniGenericIncidence.projectiveGoodOpen j)
    (i : Fin (m + 1)) :
    IsSMulRegular Γ((sourceOpen j i).toScheme, ⊤)
      (∑ b, ProperBirationalSections.coefficientMap
        ((sourceOpen j i).ι ≫ j ≫ DeJongAlterations.projectiveSpaceStructure k m) (a b) *
        coefficients j i b) := by
  let : Algebra k Γ((sourceOpen j i).toScheme, ⊤) :=
    (ProperBirationalSections.coefficientMap
      ((sourceOpen j i).ι ≫ j ≫ DeJongAlterations.projectiveSpaceStructure k m)).toAlgebra
  exact NadelBertiniSncFlatSelected.selectedEquation_regular_of_globalGoodOpen
    (projectiveToParameters j) (coefficients j i) i (pivot_coefficient j i) a
    (NadelBertiniIncidenceChartProjective.map j i) (map_parameter j i) (ha (⊥ : PrimeSpectrum k))

/-- Native invertible-ideal witnesses on the ORIGINAL coordinate affine cover,
internally produced from the actual good parameter and actual incidence quotient
charts. No desired Cartier or fibre-regularity certificate is supplied. -/
theorem projective_selected_isInvertible
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    (a : Fin (m + 1) → k)
    (ha : ∀ t, parameterMap a t ∈ NadelBertiniGenericIncidence.projectiveGoodOpen j) :
    (projectiveSelectedIdeal j a).IsInvertible := by
  classical
  intro x
  have hx : j x ∈ ⨆ i : Fin (m + 1), MvPolynomial.coordinateOpen (R := k) i := by
    rw [MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let W := sourceAffineOpen j i
  let r : Γ(W.1.toScheme, ⊤) := ∑ b, ProperBirationalSections.coefficientMap
    (W.1.ι ≫ j ≫ DeJongAlterations.projectiveSpaceStructure k m) (a b) * coefficients j i b
  have hr : IsSMulRegular Γ(W.1.toScheme, ⊤) r :=
    projective_selected_coefficient_regular j a ha i
  have hrn : r ∈ nonZeroDivisors Γ(W.1.toScheme, ⊤) := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro z hz
    exact hr (hz.trans (mul_zero r).symm)
  refine ⟨W, hi, W.1.topIso.hom r, ?_, ?_⟩
  · exact map_mem_nonZeroDivisors_of_ringEquiv
      W.1.topIso.commRingCatIsoToRingEquiv hrn
  · exact NadelBertiniSncFlatFrame.selectedIdeal_ideal_of_frame
      (j ≫ DeJongAlterations.projectiveSpaceStructure k m) a (projectiveLine j)
      ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) 1).pullback j)
      (projectiveSections j) W (coordinateFrame j i)

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatCartier
