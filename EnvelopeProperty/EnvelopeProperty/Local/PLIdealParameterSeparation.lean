/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierFlatModuleSeparation
import EnvelopeProperty.Local.PLIdealModelFlat
import EnvelopeProperty.Local.PLIdealNoncentralSheaves

/-! # Actual line-sheaf uniqueness on the same simultaneous model -/

open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- Actual whole original model flatness and genuine parameter regularity
prove detection by the ENTIRE noncentral open, without a flatness premise. -/
theorem simultaneousModel_hom_eq_of_parameter_pullback_eq
    (I L : X.NativeProductModel.IdealSheafData)
    {P Q : (X.simultaneousIdealBlowup I L).Modules}
    (hQ : Scheme.Modules.IsInvertible Q) (a b : P ⟶ Q)
    (h : (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).map a =
      (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).map b) :
    a = b := by
  have : Flat (X.simultaneousIdealBlowupStructure I L) :=
    X.simultaneousIdealBlowupStructure_isFlat I L
  exact CartierFlatParameter.hom_eq_of_parameter_pullback_eq
    (X.simultaneousIdealBlowupStructure I L) hQ a b Polynomial.X
    (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero) h

/-- The true whole original parameter open detects actual sheaf morphisms
into the actual same-model tensor-dual ratio. -/
theorem simultaneousRatioModel_hom_eq_of_parameter_pullback_eq
    (I L : X.NativeProductModel.IdealSheafData)
    {P : (X.simultaneousIdealBlowup I L).Modules}
    (a b : P ⟶ X.simultaneousRatioModelSheaf I L)
    (h : (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).map a =
      (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).map b) :
    a = b :=
  X.simultaneousModel_hom_eq_of_parameter_pullback_eq I L
    (X.simultaneousRatioModelSheaf_isInvertible I L) a b h

/-- Genuine whole noncentral pullback uniquely determines an actual
isomorphism to the same original ratio model line sheaf. -/
theorem simultaneousRatioModel_iso_eq_of_parameter_pullback_eq
    (I L : X.NativeProductModel.IdealSheafData)
    {P : (X.simultaneousIdealBlowup I L).Modules}
    (a b : P ≅ X.simultaneousRatioModelSheaf I L)
    (h : (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).mapIso a =
      (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).mapIso b) :
    a = b := by
  apply Iso.ext
  exact X.simultaneousRatioModel_hom_eq_of_parameter_pullback_eq I L a.hom b.hom
    (congrArg Iso.hom h)

end EnvelopeProperty.ProjSubvariety
