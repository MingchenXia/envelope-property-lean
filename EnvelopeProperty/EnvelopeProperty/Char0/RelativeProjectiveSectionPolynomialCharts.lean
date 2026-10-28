import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialMaps

/-! # Actual native projective chart restrictions have their same Laurent values -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial HomogeneousLocalization
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME native original projective chart ring is its original homogeneous Away ring. -/
def chartAwayEquiv (i : σ) : Away (homogeneousSubmodule σ R) (X i) ≃+*
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i) (isHomogeneous_X R i) one_pos).commRingCatIsoToRingEquiv

/-- The actual original overlap ring, with its original product denominator. -/
def overlapAwayEquiv (i k : σ) : Away (homogeneousSubmodule σ R) (X i * X k) ≃+*
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i * X k)
    (SetLike.mul_mem_graded (isHomogeneous_X R i) (isHomogeneous_X R k)) (by norm_num)).commRingCatIsoToRingEquiv

/-- Original whole chart sections are mapped to Laurent values by their actual native homogeneous fractions. -/
def chartToLaurent (i : σ) :
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) →+*
      originalLaurent (R := R) (σ := σ) :=
  (originalAwayToLaurent (X i) (originalPolynomialToLaurent_X_isUnit i)).comp
    (chartAwayEquiv i).symm.toRingHom

/-- The SAME actual whole overlap sections map to the original Laurent algebra. -/
def overlapToLaurent (i k : σ) :
    Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k) →+*
      originalLaurent (R := R) (σ := σ) :=
  (originalAwayToLaurent (X i * X k) (by
    rw [map_mul]; exact (originalPolynomialToLaurent_X_isUnit i).mul (originalPolynomialToLaurent_X_isUnit k))).comp
      (overlapAwayEquiv i k).symm.toRingHom

/-- The native LEFT whole restriction is the SAME original homogeneous-coordinate localization map. -/
theorem chartAway_restrict_left (i k : σ)
    (c : Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i)) :
    (overlapAwayEquiv (R := R) i k).symm
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op c) =
      awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl ((chartAwayEquiv i).symm c) := by
  apply (overlapAwayEquiv i k).injective
  rw [RingEquiv.apply_symm_apply]
  have h := Proj.awayMap_awayToSection (homogeneousSubmodule σ R) (isHomogeneous_X R k)
    (rfl : X i * X k = X i * X k)
  have h' := (congrArg (fun q => q.hom ((chartAwayEquiv i).symm c)) h).symm
  change (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
      ((chartAwayEquiv i) ((chartAwayEquiv i).symm c)) =
        (overlapAwayEquiv i k)
          (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl ((chartAwayEquiv i).symm c)) at h'
  simpa only [RingEquiv.apply_symm_apply] using h'

/-- The native RIGHT whole restriction retains the SAME original map, including the actual product-order equality. -/
theorem chartAway_restrict_right (i k : σ)
    (c : Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) k)) :
    (overlapAwayEquiv (R := R) i k).symm
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op c) =
      awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R i) (mul_comm (X i) (X k))
        ((chartAwayEquiv k).symm c) := by
  apply (overlapAwayEquiv i k).injective
  rw [RingEquiv.apply_symm_apply]
  have h := Proj.awayMap_awayToSection (homogeneousSubmodule σ R) (isHomogeneous_X R i)
    (mul_comm (X i) (X k))
  have h' := (congrArg (fun q => q.hom ((chartAwayEquiv k).symm c)) h).symm
  change (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op
      ((chartAwayEquiv k) ((chartAwayEquiv k).symm c)) =
        (overlapAwayEquiv i k)
          (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R i)
            (mul_comm (X i) (X k)) ((chartAwayEquiv k).symm c)) at h'
  simpa only [RingEquiv.apply_symm_apply] using h'

/-- Native LEFT restriction preserves each original whole Laurent value. -/
theorem overlapToLaurent_restrict_left (i k : σ)
    (c : Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i)) :
    overlapToLaurent i k ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op c) = chartToLaurent i c := by
  change originalAwayToLaurent (X i * X k)
    (by rw [map_mul]; exact (originalPolynomialToLaurent_X_isUnit i).mul (originalPolynomialToLaurent_X_isUnit k))
    ((overlapAwayEquiv i k).symm _) = _
  rw [chartAway_restrict_left]
  exact originalAwayToLaurent_awayMap (isHomogeneous_X R i) (isHomogeneous_X R k)
    (originalPolynomialToLaurent_X_isUnit i) (originalPolynomialToLaurent_X_isUnit k) rfl _

/-- Native RIGHT restriction preserves each original whole Laurent value. -/
theorem overlapToLaurent_restrict_right (i k : σ)
    (c : Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) k)) :
    overlapToLaurent i k ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (coordinateOpenOverlap_le_right (R := R) i k)).op c) = chartToLaurent k c := by
  change originalAwayToLaurent (X i * X k)
    (by rw [map_mul]; exact (originalPolynomialToLaurent_X_isUnit i).mul (originalPolynomialToLaurent_X_isUnit k))
    ((overlapAwayEquiv i k).symm _) = _
  rw [chartAway_restrict_right]
  exact originalAwayToLaurent_awayMap (isHomogeneous_X R k) (isHomogeneous_X R i)
    (originalPolynomialToLaurent_X_isUnit k) (originalPolynomialToLaurent_X_isUnit i) (mul_comm (X i) (X k)) _

/-- Every actual original homogeneous fraction retains its exact polynomial denominator-clearing identity. -/
theorem chartToLaurent_coefficient_clear (i : σ) (e : ℕ)
    (F : MvPolynomial σ R) (hF : F.IsHomogeneous e) :
    chartToLaurent i (ProjectiveHomogeneousSections.coefficient i e F hF) *
      originalPolynomialToLaurent (X i) ^ e = originalPolynomialToLaurent F := by
  change originalAwayToLaurent (X i) (originalPolynomialToLaurent_X_isUnit i) ((chartAwayEquiv i).symm
    ((chartAwayEquiv i) (ProjectiveHomogeneousSections.fraction i e F hF))) * _ = _
  rw [RingEquiv.symm_apply_apply]
  exact originalAwayToLaurent_mk_clear (X i) (originalPolynomialToLaurent_X_isUnit i)
    (isHomogeneous_X R i) e F (by simpa using hF)

/-- The original transition function clears by the SAME actual original coordinate in Laurent values. -/
theorem overlapToLaurent_transition_clear (i k : σ) :
    overlapToLaurent i k (coordinateOpenTransitionUnit (R := R) i k :
      Γ(Proj (homogeneousSubmodule σ R), coordinateOpenOverlap (R := R) i k)) *
      originalPolynomialToLaurent (X i) = originalPolynomialToLaurent (X k) := by
  change overlapToLaurent i k ((Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (coordinateOpenOverlap_le_left (R := R) i k)).op
      (coordinateHyperplaneLocalEquation (R := R) i k)) * _ = _
  rw [← ProjectiveHomogeneousSections.coefficient_X, overlapToLaurent_restrict_left]
  simpa only [pow_one] using chartToLaurent_coefficient_clear (R := R) i 1 (X k) (isHomogeneous_X R k)

end EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
