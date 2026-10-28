import EnvelopeProperty.Vanishing.RelativeNadelBertiniIncidence
import EnvelopeProperty.Vanishing.RelativeNadelBertiniFlatSelected
import EnvelopeProperty.Vanishing.NadelBertiniIncidenceChartProjective
import EnvelopeProperty.Vanishing.NadelBertiniSncFlatFrame

/-! # Actual Cartier hyperplanes for relative projective coordinates

The original projective coordinate sections are over R, and their coefficient
parameters are over the original field k.  These two bases remain distinct.
No domain hypothesis on R or properness over k occurs.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelBertiniProjective
open NadelBertiniUniversal NadelBertiniProjectiveFrames NadelBertiniRestrictionCover
  NadelBertiniFibreSection NadelBertiniRationalParameter SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R : Type u} [Field k] [CommRing R] {m : ℕ} {X : Scheme.{u}}

abbrev lineInvertible (j : X ⟶ DeJongAlterations.projectiveSpace R m) :
    IsInvertible (projectiveLine j) :=
  (MvPolynomial.coordinateHyperplaneTwist_isInvertible
    (R := R) (0 : Fin (m + 1)) 1).pullback j

/-- Actual relative projective sections, with coefficient parameters over k. -/
def projection (p : X ⟶ Spec (.of k))
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) :
    incidence p (projectiveLine j) (lineInvertible j) (projectiveSections j) ⟶
      Spec (.of (parameterRing k m)) :=
  toParameters p (projectiveLine j) (lineInvertible j) (projectiveSections j)

instance projection_finiteType (p : X ⟶ Spec (.of k)) [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) : FiniteType (projection p j) :=
  RelativeNadelBertiniIncidence.toParameters_finiteType p _ _ _

/-- The actual entire selected zero ideal, using original k coefficients. -/
abbrev selectedIdeal (p : X ⟶ Spec (.of k))
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) (a : Fin (m + 1) → k) :
    X.IdealSheafData :=
  NadelBertiniFibreGeometry.selectedIdeal p a (projectiveLine j)
    (lineInvertible j) (projectiveSections j)

/-- The actual nonproper smooth parameter open for the relative system. -/
def goodOpen (p : X ⟶ Spec (.of k)) [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) :
    (Spec (.of (parameterRing k m))).Opens :=
  RelativeNadelBertiniGenericOpen.goodOpen (projection p j)

private theorem cover_pivot (j : X ⟶ DeJongAlterations.projectiveSpace R m)
    [IsClosedImmersion j] (i : Fin (m + 1)) :
    (show Γ((sourceOpen j i).toScheme, ⊤) from (coordinateFrame j i).hom.app ⊤
      (affinePullbackUnitTop (sourceOpen j i).ι (projectiveLine j) (projectiveSections j i))) = 1 := by
  change (coordinateFrame j i).hom.app ⊤
    (affinePullbackUnitTop (sourceOpen j i).ι (projectiveLine j)
      (sectionAtOne (sectionHom j i))) = _
  rw [pullback_sectionAtOne]
  exact congrArg sectionAtOne (coordinateFrame_section j i)

/-- Relative projective coordinates internally prove smoothness of the entire
coefficient incidence over the original field. -/
theorem total_smooth (p : X ⟶ Spec (.of k)) [Smooth p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) [IsClosedImmersion j] :
    Smooth (toSource p (projectiveLine j) (lineInvertible j) (projectiveSections j) ≫ p) := by
  let W : Fin (m + 1) → X.affineOpens := fun i => ⟨sourceOpen j i, sourceOpen_affine j i⟩
  have hW : ⨆ i, (W i).1 = ⊤ := by
    change ⨆ i, j ⁻¹ᵁ MvPolynomial.coordinateOpen (R := R) i = ⊤
    exact j.iSup_preimage_eq_top (MvPolynomial.iSup_coordinateOpen_eq_top (R := R))
  exact RelativeNadelBertiniIncidence.total_smooth_of_cover p _ _ _ W hW
    (coordinateFrame j) id (cover_pivot j)

/-- The actual nonproper good open contains the original generic parameter. -/
theorem genericPoint_mem_goodOpen [CharZero k] (p : X ⟶ Spec (.of k)) [Smooth p] [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) [IsClosedImmersion j] :
    genericPoint (Spec (.of (parameterRing k m))) ∈ goodOpen p j := by
  let := total_smooth p j
  exact (RelativeNadelBertiniGenericOpen.goodOpen_specification_of_smooth
    (Spec.map (CommRingCat.ofHom (algebraMap k (parameterRing k m))))
    (projection p j)
    (toSource p (projectiveLine j) (lineInvertible j) (projectiveSections j) ≫ p)).1

/-- The actual good parameter gives a smooth whole selected subscheme. -/
theorem selected_smooth (p : X ⟶ Spec (.of k)) [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) (a : Fin (m + 1) → k)
    (ha : ∀ t, parameterMap a t ∈ goodOpen p j) :
    Smooth ((selectedIdeal p j a).subschemeι ≫ p) := by
  let : FiniteType (toParameters p (projectiveLine j) (lineInvertible j) (projectiveSections j)) :=
    RelativeNadelBertiniIncidence.toParameters_finiteType p _ _ _
  exact RelativeNadelBertiniGenericOpen.selected_smooth p a _ _ _ ha

/-- The actual original selected coefficient in each original relative
projective affine chart is a nonzerodivisor. -/
theorem selected_coefficient_regular (p : X ⟶ Spec (.of k)) [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) [IsClosedImmersion j]
    (a : Fin (m + 1) → k) (ha : ∀ t, parameterMap a t ∈ goodOpen p j)
    (i : Fin (m + 1)) :
    IsSMulRegular Γ((sourceOpen j i).toScheme, ⊤)
      (∑ b, ProperBirationalSections.coefficientMap ((sourceOpen j i).ι ≫ p) (a b) *
        NadelBertiniIncidenceChartProjective.coefficients j i b) := by
  let W := NadelBertiniIncidenceChartProjective.sourceAffineOpen j i
  let : Algebra k Γ(W.1.toScheme, ⊤) :=
    (ProperBirationalSections.coefficientMap (W.1.ι ≫ p)).toAlgebra
  exact RelativeNadelBertiniFlatSelected.selectedEquation_regular_of_goodOpen
    (projection p j) (NadelBertiniIncidenceChartProjective.coefficients j i) i
    (NadelBertiniIncidenceChartProjective.pivot_coefficient j i) a
    (NadelBertiniIncidenceChartMap.map p (projectiveLine j) (lineInvertible j)
      W (coordinateFrame j i) (projectiveSections j))
    (NadelBertiniIncidenceChartMap.map_parameter p (projectiveLine j) (lineInvertible j)
      W (coordinateFrame j i) (projectiveSections j)) (ha (⊥ : PrimeSpectrum k))

/-- Actual good parameters internally make the SAME original whole selected
zero ideal an effective Cartier ideal, without a field-proper source. -/
theorem selected_isInvertible (p : X ⟶ Spec (.of k)) [FiniteType p]
    (j : X ⟶ DeJongAlterations.projectiveSpace R m) [IsClosedImmersion j]
    (a : Fin (m + 1) → k) (ha : ∀ t, parameterMap a t ∈ goodOpen p j) :
    (selectedIdeal p j a).IsInvertible := by
  classical
  intro x
  have hx : j x ∈ ⨆ i : Fin (m + 1), MvPolynomial.coordinateOpen (R := R) i := by
    rw [MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let W := NadelBertiniIncidenceChartProjective.sourceAffineOpen j i
  let r : Γ(W.1.toScheme, ⊤) := ∑ b,
    ProperBirationalSections.coefficientMap (W.1.ι ≫ p) (a b) *
      NadelBertiniIncidenceChartProjective.coefficients j i b
  have hr : IsSMulRegular Γ(W.1.toScheme, ⊤) r := selected_coefficient_regular p j a ha i
  have hrn : r ∈ nonZeroDivisors Γ(W.1.toScheme, ⊤) := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro z hz
    exact hr (hz.trans (mul_zero r).symm)
  refine ⟨W, hi, W.1.topIso.hom r, ?_, ?_⟩
  · exact map_mem_nonZeroDivisors_of_ringEquiv W.1.topIso.commRingCatIsoToRingEquiv hrn
  · exact NadelBertiniSncFlatFrame.selectedIdeal_ideal_of_frame p a
      (projectiveLine j) (lineInvertible j) (projectiveSections j) W (coordinateFrame j i)

end EnvelopeProperty.Vanishing.RelativeNadelBertiniProjective
