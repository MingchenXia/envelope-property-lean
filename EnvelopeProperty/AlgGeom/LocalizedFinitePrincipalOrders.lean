import EnvelopeProperty.AlgGeom.AffinePrincipalLocalDegree
import EnvelopeProperty.AlgGeom.SchemeLocalizedFiniteAlgebras
import EnvelopeProperty.AlgGeom.SchemeRegularSectionOrders
import EnvelopeProperty.AlgGeom.IntegralSchemeDimension

/-! # True ALL-original-point native principal orders on the actual localized finite inverse -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.LocalizedFinitePrincipalOrders
open FlatGlobalSections AffineSchemeLocalDegrees FiniteClosedIdealLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coefficientMap_comp_SpecMap {R S : Type u} [CommRing R] [CommRing S]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of S)) (σ : R →+* S) :
    ProperBirationalSections.coefficientMap (q ≫ Spec.map (CommRingCat.ofHom σ)) =
      (ProperBirationalSections.coefficientMap q).comp σ := by
  unfold ProperBirationalSections.coefficientMap
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable {A S k : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [Field k] [Algebra k S] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))

/-- The SAME actual original local inverse has its literal original field
structure through the actual original local coefficient map. -/
def fieldStructure : baseChange (S := S) f ⟶ Spec (.of k) :=
  structureMap (S := S) f ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))

variable [IsDomain A] [IsIntegral Y] [IsFinite f] [IsDominant f]
    (M : Submonoid A) [IsLocalization M S] (hM : M ≤ nonZeroDivisors A)
    [IsLocalRing S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Module.Finite k (IsLocalRing.ResidueField S)]
include M hM

/-- The ACTUAL original principal quotient of the entire original local
inverse is internally finite over the SAME actual field structure. -/
theorem principalQuotient_finite (a : S) (ha : a ≠ 0) :
    letI := sectionsAlgebra (structureMap (S := S) f)
    letI := structureSectionsAlgebra (fieldStructure (S := S) (k := k) f)
    Module.Finite k (Γ(baseChange (S := S) f, ⊤) ⧸
      Ideal.span {algebraMap S Γ(baseChange (S := S) f, ⊤) a}) := by
  let T := baseChange (S := S) f
  let q := structureMap (S := S) f
  let := sectionsAlgebra q
  let := structureSectionsAlgebra (fieldStructure (S := S) (k := k) f)
  let : IsScalarTower k S Γ(T, ⊤) := IsScalarTower.of_algebraMap_eq (fun r => by
    exact RingHom.congr_fun (coefficientMap_comp_SpecMap q (algebraMap k S)) r)
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  let : IsIntegral T := SchemeLocalizedFiniteAlgebras.baseChange_isIntegral f M hM
  let : IsDomain Γ(T, ⊤) := SchemeLocalizedFiniteAlgebras.baseChange_sections_isDomain f M hM
  let : Module.Finite S Γ(T, ⊤) := SchemeLocalizedFiniteAlgebras.sections_module_finite q
  exact LocalPrincipalFieldDegrees.principalQuotient_finite (k := k) a ha

/-- The sum of TRUE native original Scheme.ord over ALL original points of
the SAME entire local finite inverse is actual original generic rank times
the ORIGINAL local base principal order and ORIGINAL residue degree.
No flatness/normality, quotient finiteness, point or degree certificate is supplied. -/
theorem finsum_principal_orders (hdim : topologicalKrullDim Y ≤ 1) (a : S) (ha : a ≠ 0) :
    letI := sectionsAlgebra f
    letI := sectionsAlgebra (structureMap (S := S) f)
    letI := structureSectionsAlgebra (fieldStructure (S := S) (k := k) f)
    letI : IsIntegral (baseChange (S := S) f) :=
      SchemeLocalizedFiniteAlgebras.baseChange_isIntegral f M hM
    letI : IsLocallyNoetherian (baseChange (S := S) f) :=
      LocallyOfFiniteType.isLocallyNoetherian (structureMap (S := S) f)
    (∑ᶠ z : baseChange (S := S) f,
      SchemeRegularSectionOrders.weightedOrder (fieldStructure (S := S) (k := k) f)
        (algebraMap S Γ(baseChange (S := S) f, ⊤) a) z) =
      (Module.finrank A Γ(Y, ⊤) : ℤ) * ((Ring.ord S a).toNat : ℤ) *
        (Module.finrank k (IsLocalRing.ResidueField S) : ℤ) := by
  let T := baseChange (S := S) f
  let q := structureMap (S := S) f
  let := sectionsAlgebra f
  let := sectionsAlgebra q
  let := structureSectionsAlgebra (fieldStructure (S := S) (k := k) f)
  let : IsScalarTower k S Γ(T, ⊤) := IsScalarTower.of_algebraMap_eq (fun r => by
    exact RingHom.congr_fun (coefficientMap_comp_SpecMap q (algebraMap k S)) r)
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  let : IsIntegral T := SchemeLocalizedFiniteAlgebras.baseChange_isIntegral f M hM
  let : IsAffine T := isAffine_of_isAffineHom q
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsDomain Γ(T, ⊤) := SchemeLocalizedFiniteAlgebras.baseChange_sections_isDomain f M hM
  let : Module.Finite S Γ(T, ⊤) := SchemeLocalizedFiniteAlgebras.sections_module_finite q
  let : Surjective f := inferInstance
  let : Surjective q := inferInstance
  have hi := SchemeLocalizedFiniteAlgebras.coefficientMap_injective q
  have haΓ : algebraMap S Γ(T, ⊤) a ≠ 0 := by
    change ProperBirationalSections.coefficientMap q a ≠ 0
    simpa only [map_zero] using hi.ne ha
  let : Module.Finite k (Γ(T, ⊤) ⧸ Ideal.span {algebraMap S Γ(T, ⊤) a}) :=
    principalQuotient_finite f M hM a ha
  have hdimT : topologicalKrullDim T ≤ 1 := by
    let : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
      IsPreimmersion.of_isLocalization M
    exact (firstProjection (S := S) f).isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hdegree := AffinePrincipalLocalDegree.finrank_quotient_eq_finsum_native_orders
    (fieldStructure (S := S) (k := k) f) hdimT (algebraMap S Γ(T, ⊤) a) haΓ
      (inferInstance : Module.Finite k (Γ(T, ⊤) ⧸ Ideal.span {algebraMap S Γ(T, ⊤) a}))
  change (Module.finrank k (Γ(T, ⊤) ⧸ Ideal.span {algebraMap S Γ(T, ⊤) a}) : ℤ) =
    ∑ᶠ z : T, SchemeRegularSectionOrders.weightedOrder (fieldStructure (S := S) (k := k) f)
      (algebraMap S Γ(T, ⊤) a) z at hdegree
  rw [LocalPrincipalFieldDegrees.finrank_principalQuotient (k := k) hi a ha,
    SchemeLocalizedFiniteAlgebras.baseChange_sections_finrank f M hM,
    Nat.cast_mul, Nat.cast_mul] at hdegree
  exact hdegree.symm

end EnvelopeProperty.LocalizedFinitePrincipalOrders
