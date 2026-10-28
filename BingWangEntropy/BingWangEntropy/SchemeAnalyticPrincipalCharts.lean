import BingWangEntropy.SchemeAnalyticOpenCharts
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Actual analytic principal chart embeddings

Actual localization morphisms carry the principal-open analytic homeomorphism.
They provide the neighborhoods needed to compare overlapping affine scheme
charts and prove the global chart open embedding.
-/

open CategoryTheory AlgebraicGeometry
open scoped Topology

namespace BingWangEntropy

noncomputable section

/-- The actual scheme morphism of a principal localization. -/
def complexPrincipalSchemeMap {A : CommRingCat} (r : A) :
    Spec (.of (Localization.Away r)) ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))

/-- A genuine principal localization is a native open immersion. -/
instance complexPrincipalSchemeMapOpen {A : CommRingCat} (r : A) :
    IsOpenImmersion (complexPrincipalSchemeMap r) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway r

/-- Its literal underlying image is the actual principal open. -/
theorem complexPrincipalSchemeMap_range {A : CommRingCat} (r : A) :
    Set.range (complexPrincipalSchemeMap r) = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum A)) := by
  exact congrArg TopologicalSpace.Opens.carrier (Scheme.Hom.opensRange_localizationAway r)

/-- The complex structures derived from an actual localization morphism form
an actual scalar tower with the native localization algebra. -/
theorem complexPrincipalSchemeScalarTower {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (r : A) :
    letI : Algebra ℂ A := affinePointFieldAlgebra f
    letI : Algebra ℂ (Localization.Away r) := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)
    letI : SMul A (Localization.Away r) := (inferInstance : Algebra A (Localization.Away r)).toSMul
    letI : SMul ℂ (Localization.Away r) :=
      (affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)).toSMul
    IsScalarTower ℂ A (Localization.Away r) := by
  let : Algebra ℂ A := affinePointFieldAlgebra f
  let : Algebra ℂ (Localization.Away r) := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)
  let : SMul A (Localization.Away r) := (inferInstance : Algebra A (Localization.Away r)).toSMul
  let : SMul ℂ (Localization.Away r) :=
    (affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)).toSMul
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change (Spec.preimage (complexPrincipalSchemeMap r ≫ f)).hom c =
    algebraMap A (Localization.Away r) ((Spec.preimage f).hom c)
  rw [Spec.preimage_comp]
  change (Spec.preimage (Spec.map (CommRingCat.ofHom
    (algebraMap A (Localization.Away r))))).hom ((Spec.preimage f).hom c) = _
  rw [Spec.preimage_map]
  rfl

/-- The genuine localization algebra map induces an open embedding of actual
algebra point spaces. -/
theorem localizationComplexPoint_isOpenEmbedding
    {A : Type} [CommRing A] [Algebra ℂ A]
    (S : Type) [CommRing S] [Algebra ℂ S] [Algebra A S] [IsScalarTower ℂ A S]
    (r : A) [IsLocalization.Away r S] :
    Topology.IsOpenEmbedding (fun p : ComplexAlgebraPoint S => p.comp (Algebra.algHom ℂ A S)) := by
  exact (complexPrincipalOpen_isOpen r).isOpenEmbedding_subtypeVal.comp
    (localizationComplexPointHomeomorph S r).isOpenEmbedding

/-- Actual scheme complex points of a genuine principal localization form an
open embedded chart in the inherited affine evaluation topology. -/
theorem complexPrincipalSchemePointMap_isOpenEmbedding {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (r : A) :
    letI := affineSchemePointTopologyOfStructure (complexPrincipalSchemeMap r ≫ f)
    letI := affineSchemePointTopologyOfStructure f
    Topology.IsOpenEmbedding
      (schemeComplexPointMap (complexPrincipalSchemeMap r ≫ f) f
        (complexPrincipalSchemeMap r) rfl) := by
  let : Algebra ℂ A := affinePointFieldAlgebra f
  let : Algebra ℂ (Localization.Away r) := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)
  let : SMul A (Localization.Away r) := (inferInstance : Algebra A (Localization.Away r)).toSMul
  let : SMul ℂ (Localization.Away r) :=
    (affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)).toSMul
  let : IsScalarTower ℂ A (Localization.Away r) := complexPrincipalSchemeScalarTower f r
  let := affineSchemePointTopologyOfStructure (complexPrincipalSchemeMap r ≫ f)
  let := affineSchemePointTopologyOfStructure f
  have hmap : affineSchemeMorphismAlgebraMap f (complexPrincipalSchemeMap r) =
      Algebra.algHom ℂ A (Localization.Away r) := by
    apply AlgHom.ext
    intro a
    change (Spec.preimage (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away r))))).hom a = _
    rw [Spec.preimage_map]
    rfl
  have heq : schemeComplexPointMap (complexPrincipalSchemeMap r ≫ f) f
        (complexPrincipalSchemeMap r) rfl =
      (affineSchemePointHomeomorphOfStructure f).symm ∘
        (fun p : ComplexAlgebraPoint (Localization.Away r) =>
          p.comp (Algebra.algHom ℂ A (Localization.Away r))) ∘
        affineSchemePointHomeomorphOfStructure (complexPrincipalSchemeMap r ≫ f) := by
    funext p
    apply (affineSchemePointHomeomorphOfStructure f).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact (affineSchemePointEquivOfStructure_naturality f (complexPrincipalSchemeMap r) p).trans
      (congrArg (fun h => (affineSchemePointEquivOfStructure
        (complexPrincipalSchemeMap r ≫ f) p).comp h) hmap)
  rw [heq]
  exact (affineSchemePointHomeomorphOfStructure f).symm.isOpenEmbedding.comp
    ((localizationComplexPoint_isOpenEmbedding (Localization.Away r) r).comp
      (affineSchemePointHomeomorphOfStructure (complexPrincipalSchemeMap r ≫ f)).isOpenEmbedding)

end

end BingWangEntropy
