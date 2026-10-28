import EnvelopeProperty.AlgGeom.AffineLocalizationStalks
import EnvelopeProperty.AffineGlobalSections
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.Localization.BaseChange

/-! # The SAME whole original localized inverse: native coefficients, points and stalks -/
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.LocalizedInverseStalks
open FlatGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec (.of A))
    (M : Submonoid A) [IsLocalization M S]
include M

/-- The SAME original whole inverse projection has its ACTUAL original
section map a genuine localization, derived from both native tensor triangles. -/
theorem projection_sections_isLocalization :
    letI := sectionsAlgebra f
    letI := (firstProjection (S := S) f).appTop.hom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, ⊤) M) Γ(baseChange (S := S) f, ⊤) := by
  let := sectionsAlgebra f
  let := sectionsAlgebra (structureMap (S := S) f)
  let := (firstProjection (S := S) f).appTop.hom.toAlgebra
  let e := AffineGlobalSections.tensorEquiv (S := S) f
  let eB : (S ⊗[A] Γ(Y, ⊤)) ≃ₐ[Γ(Y, ⊤)] Γ(baseChange (S := S) f, ⊤) :=
    { e.toRingEquiv with
      commutes' b := AffineGlobalSections.tensorEquiv_includeRight (S := S) f b }
  let : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, ⊤) M) (S ⊗[A] Γ(Y, ⊤)) :=
    IsLocalization.tensorRight (R := A) (S := Γ(Y, ⊤)) (A := S) M
  exact IsLocalization.isLocalization_of_algEquiv _ eB

/-- EVERY SAME original native stalk map of the actual whole localized
inverse projection is an isomorphism, with no localization/stalk certificate supplied. -/
theorem projection_stalkMap_isIso (y : baseChange (S := S) f) :
    IsIso ((firstProjection (S := S) f).stalkMap y) := by
  let := sectionsAlgebra f
  exact AffineLocalizationStalks.stalkMap_isIso (firstProjection (S := S) f)
    (Algebra.algebraMapSubmonoid Γ(Y, ⊤) M) (projection_sections_isLocalization f M) y

/-- EVERY SAME original native residue map of that actual whole projection
is an isomorphism, preserving the original point/coefficient action. -/
theorem projection_residueFieldMap_isIso (y : baseChange (S := S) f) :
    IsIso ((firstProjection (S := S) f).residueFieldMap y) := by
  let := sectionsAlgebra f
  exact AffineLocalizationStalks.residueFieldMap_isIso (firstProjection (S := S) f)
    (Algebra.algebraMapSubmonoid Γ(Y, ⊤) M) (projection_sections_isLocalization f M) y

omit [IsAffine Y] in
/-- The SAME original whole localized inverse has an injective actual point
projection, internally derived from the actual native localization map. -/
theorem projection_injective : Function.Injective (firstProjection (S := S) f) := by
  let : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
    IsPreimmersion.of_isLocalization M
  exact (firstProjection (S := S) f).isEmbedding.injective

end EnvelopeProperty.LocalizedInverseStalks
