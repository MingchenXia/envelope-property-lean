import EnvelopeProperty.Projective.Subvariety
import EnvelopeProperty.Projective.HomogeneousQuotient
import ModularCurves.ForMathlib.ProjectiveFactorization
import DeJongAlterations.Geometry.ProjIntegral
import Hironaka.Scheme.Resolution.Basic

/-! # The actual native scheme of an original projective subvariety -/

open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjSubvariety

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)

/-- The original homogeneous prime ideal, with its actual native grading. -/
def homogeneousIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin (n+1)) k) :=
  ⟨X.ideal, (isHomogeneousIdeal_iff_isHomogeneous X.ideal).mp X.isHomogeneousIdeal⟩

private local instance quotientGradedRing :
    GradedRing (GradedQuotient.grading (homogeneousSubmodule (Fin (n+1)) k) X.ideal) :=
  GradedQuotient.gradedRing _ X.ideal X.homogeneousIdeal.isHomogeneous

/-- The native projective scheme of the SAME original prime homogeneous quotient. -/
def nativeScheme : Scheme.{u} :=
  Proj (GradedQuotient.grading (homogeneousSubmodule (Fin (n+1)) k) X.ideal)

/-- The actual original homogeneous quotient gives the actual native projective embedding. -/
def nativeEmbedding : X.nativeScheme ⟶ Proj (homogeneousSubmodule (Fin (n+1)) k) :=
  GradedQuotient.quotientSchemeMap _ X.homogeneousIdeal

/-- The actual original embedding is closed, without radical replacement. -/
instance nativeEmbedding_isClosedImmersion : IsClosedImmersion X.nativeEmbedding :=
  GradedQuotient.instIsClosedImmersion_quotientSchemeMap _ X.homogeneousIdeal

/-- The original native structure morphism uses the SAME original coefficient field. -/
def quotientNativeStructure : X.nativeScheme ⟶ Spec (.of k) :=
  X.nativeEmbedding ≫ homogeneousProjπ

/-- The original quotient scheme is actually polynomially projective over its SAME field. -/
theorem quotientNativeStructure_isProjectiveFactorization :
    IsProjectiveFactorization X.quotientNativeStructure :=
  ⟨n, X.nativeEmbedding, inferInstance, rfl⟩

/-- The actual original quotient structure is proper over its original field. -/
instance quotientNativeStructure_isProper : IsProper X.quotientNativeStructure :=
  X.quotientNativeStructure_isProjectiveFactorization.isProper

/-- The actual original prime homogeneous quotient is an algebraic scheme over
the SAME original field, with finite type and separatedness derived internally. -/
def nativeAlgebraicScheme : AlgScheme k := by
  let : LocallyOfFiniteType X.quotientNativeStructure := inferInstance
  let : UniversallyClosed X.quotientNativeStructure := inferInstance
  let : QuasiCompact X.quotientNativeStructure := inferInstance
  exact AlgScheme.ofHom X.quotientNativeStructure ⟨⟩ inferInstance

/-- Relevance of the original prime ideal forces its actual quotient grading irrelevant ideal nonzero. -/
theorem native_irrelevant_ne_bot :
    HomogeneousIdeal.irrelevant
      (GradedQuotient.grading (homogeneousSubmodule (Fin (n+1)) k) X.ideal) ≠ ⊥ := by
  obtain ⟨i, hi⟩ := X.exists_X_notMem
  intro h
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem
    (GradedQuotient.grading (homogeneousSubmodule (Fin (n+1)) k) X.ideal)
    (by decide : 0 < (1 : ℕ))
    ((GradedQuotient.gradedMk (homogeneousSubmodule (Fin (n+1)) k) X.ideal).map_mem
      (isHomogeneous_X k i))
  rw [h] at hm
  exact hi (Ideal.Quotient.eq_zero_iff_mem.mp hm)

/-- The actual native quotient projective scheme of every original projective subvariety is integral. -/
instance nativeScheme_isIntegral : IsIntegral X.nativeScheme :=
  DeJongAlterations.Geometry.ProjIntegral.isIntegral_proj _ X.native_irrelevant_ne_bot

end EnvelopeProperty.ProjSubvariety
