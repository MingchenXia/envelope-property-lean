import EnvelopeProperty.AlgGeom.NativeProjectiveVariety
import EnvelopeProperty.Local.PLIdealSubvarietyModels

/-! # The SAME original closed variety and its whole native quotient Proj -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)

/-- The entire native homogeneous quotient Proj is the EXISTING original
closed-subscheme NativeScheme, via its actual scheme-theoretic image. -/
def quotientNativeIso : X.nativeScheme ≅ X.NativeScheme :=
  asIso X.nativeEmbedding.toImage

/-- The whole comparison preserves the literal ORIGINAL projective closed inclusion. -/
theorem quotientNativeIso_inclusion :
    X.quotientNativeIso.hom ≫ X.nativeInclusion = X.nativeEmbedding :=
  X.nativeEmbedding.toImage_imageι

/-- The whole comparison preserves the literal ORIGINAL coefficient morphism. -/
theorem quotientNativeIso_structure :
    X.quotientNativeIso.hom ≫ X.nativeStructure = X.quotientNativeStructure := by
  change X.quotientNativeIso.hom ≫ (X.nativeInclusion ≫ ProjBerk.nativeStructureMap) = _
  rw [← Category.assoc, quotientNativeIso_inclusion]
  rfl

/-- The inverse whole comparison retains the ORIGINAL coefficient morphism. -/
theorem quotientNativeIso_inv_structure :
    X.quotientNativeIso.inv ≫ X.quotientNativeStructure = X.nativeStructure := by
  rw [← quotientNativeIso_structure, Iso.inv_hom_id_assoc]

/-- The EXISTING original NativeScheme is integral; its integrality is derived
from the SAME original homogeneous prime quotient through the genuine whole isomorphism. -/
theorem originalNativeScheme_isIntegral : IsIntegral X.NativeScheme :=
  IsIntegral.of_isIso X.quotientNativeIso.hom

/-- The EXISTING original nativeStructure is polynomially projective over the
SAME literal original coefficient field, through its ORIGINAL projective inclusion. -/
theorem originalNativeStructure_isProjectiveFactorization :
    IsProjectiveFactorization X.nativeStructure := by
  have h := X.quotientNativeStructure_isProjectiveFactorization.comp_isClosedImmersion
    X.quotientNativeIso.inv inferInstance
  rwa [quotientNativeIso_inv_structure] at h

end EnvelopeProperty.ProjSubvariety
