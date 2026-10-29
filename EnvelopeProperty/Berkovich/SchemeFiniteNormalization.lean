/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.SchemeIntegralNormalization
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints
import EnvelopeProperty.Alterations.Algebra.IntegralClosureFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Hironaka.Algebra.RegularSmooth.SmoothAt
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable {k : Type u} [Field k] {X : Scheme.{u}}

private theorem sectionAlgebra_finiteType (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (U : X.affineOpens) :
    letI := Berkovich.SchemeValuedPoint.sectionBaseAlgebra f U.1
    Algebra.FiniteType k Γ(X, U.1) := by
  exact f.finiteType_sectionsAlgebra U.2

/-- The SAME original generic-field normalization projection is finite for
any integral scheme locally of finite type over ANY field, without a
quasi-compactness, separatedness, dimension or perfectness assumption. -/
theorem projection_isFinite_of_locallyOfFiniteType [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    IsFinite (projection X) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _
    (iSup_nonemptyAffineOpen_eq_top X)]
  rintro ⟨⟨U, hU⟩, hne⟩
  let : Nonempty U := hne
  let : Algebra k Γ(X, U) := Berkovich.SchemeValuedPoint.sectionBaseAlgebra f U
  let : Algebra.FiniteType k Γ(X, U) := sectionAlgebra_finiteType f ⟨U, hU⟩
  let : Module.Finite Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U))) :=
    Alterations.Algebra.IntegralClosureFiniteType.finite_integralClosure
      k Γ(X, U) (FractionRing Γ(X, U))
  have hfinite : IsFinite (DomainNormalization.projection Γ(X, U)) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsOpenImmersion (chartMap X U hU) := chartMap_isOpenImmersion X U hU
  let e := IsOpenImmersion.isoOfRangeEq ((projection X) ⁻¹ᵁ U).ι (chartMap X U hU)
    (by simpa only [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange] using
      (congrArg (fun V : (normalization X).Opens => (V : Set (normalization X)))
        (chartMap_opensRange X U hU).symm))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ hU.isoSpec.hom]
  convert! hfinite
  rw [← cancel_mono hU.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, chartMap_comp_projection]

end EnvelopeProperty.IntegralSchemeNormalization
