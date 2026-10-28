/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.SmoothFunctionFieldSubalgebras
import EnvelopeProperty.Algebra.RegularNormal
import EnvelopeProperty.Berkovich.SchemeNormalStalks
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular

/-! # Actual smooth integral schemes have normal original affine rings and stalks -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Hom
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [hf : Smooth f]
include f hf

/-- Every actual original affine section ring of an actual smooth scheme
is regular, without a perfect-field or integrality hypothesis. -/
theorem isRegularRing_sections_of_smooth {U : X.Opens} (hU : IsAffineOpen U) :
    IsRegularRing Γ(X, U) := by
  let _ := f.sectionsAlgebra U
  have : Algebra.Smooth k Γ(X, U) := f.smooth_sectionsAlgebra hU
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  exact isRegularRing_iff.mpr (fun P _ => Algebra.IsSmoothAt.isRegularLocalRing (k := k) P)

variable [IsIntegral X]

/-- Smoothness of the actual original integral scheme derives integral
closedness of its same original nonempty affine section ring. -/
theorem isIntegrallyClosed_sections_of_smooth {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsIntegrallyClosed Γ(X, U) := by
  let : IsRegularRing Γ(X, U) := f.isRegularRing_sections_of_smooth hU
  exact EnvelopeProperty.isIntegrallyClosed_of_isRegularRing Γ(X, U)

omit [IsIntegral X] in
/-- Every actual original local stalk of an actual smooth scheme
is a regular local ring, using its true affine localization comparison. -/
theorem isRegularLocalRing_stalk_of_smooth (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  have hm : x ∈ Set.range hU.fromSpec :=
    Eq.mpr (congrArg (fun S : Set X => x ∈ S) hU.range_fromSpec) hx
  obtain ⟨q, rfl⟩ := hm
  let : IsRegularRing Γ(X, U) := f.isRegularRing_sections_of_smooth hU
  exact IsRegularLocalRing.of_ringEquiv
    ((Spec.stalkIso Γ(X, U) q).commRingCatIsoToRingEquiv.symm.trans
      (asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.symm)

/-- Every actual original stalk of the actual smooth integral scheme
is integrally closed; no normality or local-normality certificate is supplied. -/
theorem isIntegrallyClosed_stalk_of_smooth (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  have hm : x ∈ Set.range hU.fromSpec :=
    Eq.mpr (congrArg (fun S : Set X => x ∈ S) hU.range_fromSpec) hx
  obtain ⟨q, rfl⟩ := hm
  let : IsIntegrallyClosed Γ(X, U) := f.isIntegrallyClosed_sections_of_smooth hU
  have : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv
    ((Spec.stalkIso Γ(X, U) q).commRingCatIsoToRingEquiv.symm.trans
      (asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.symm)

/-- Actual smooth integral schemes satisfy the standard geometric
unibranch class, derived from their actual original normal local rings. -/
theorem isGeometricallyUnibranch_of_smooth : EnvelopeProperty.IsGeometricallyUnibranchScheme X :=
  EnvelopeProperty.IsGeometricallyUnibranchScheme.of_normal_stalks X
    (fun _ => inferInstance) (f.isIntegrallyClosed_stalk_of_smooth)

end AlgebraicGeometry.Scheme.Hom
