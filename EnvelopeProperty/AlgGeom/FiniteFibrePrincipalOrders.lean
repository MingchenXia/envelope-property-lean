import EnvelopeProperty.AlgGeom.AtPrimeInverseRegularOrderSums
import EnvelopeProperty.AlgGeom.LocalizedFinitePrincipalOrders

/-! # Genuine ALL original finite-fibre principal orders without flatness -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.FiniteFibrePrincipalOrders
open FlatGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A k : Type u} [CommRing A] [Field k] [Algebra k A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (p : PrimeSpectrum A)

/-- The SAME original source field structure, with no chosen comparison map. -/
def sourceFieldStructure : Y ⟶ Spec (.of k) :=
  f ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))

/-- The whole actual original pullback square identifies the actual original
local-inverse field structure with the SAME original source structure. -/
theorem fieldStructure_eq :
    LocalizedFinitePrincipalOrders.fieldStructure (S := Localization.AtPrime p.asIdeal) (k := k) f =
      firstProjection (S := Localization.AtPrime p.asIdeal) f ≫ sourceFieldStructure (k := k) f := by
  unfold LocalizedFinitePrincipalOrders.fieldStructure sourceFieldStructure
  rw [IsScalarTower.algebraMap_eq k A (Localization.AtPrime p.asIdeal)]
  change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k A) ≫
    CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal))) = _
  rw [Spec.map_comp, ← Category.assoc, ← pullback.condition, Category.assoc]

variable [IsDomain A] [IsIntegral Y] [IsFinite f] [IsDominant f]

omit [IsDomain A] [IsIntegral Y] [IsDominant f] in
/-- The SAME actual original section projection retains EVERY original
coefficient, as an equality in the whole original inverse section ring. -/
theorem coefficient_pullback (a : A) :
    (firstProjection (S := Localization.AtPrime p.asIdeal) f).appTop
      (ProperBirationalSections.coefficientMap f a) =
    ProperBirationalSections.coefficientMap
      (structureMap (S := Localization.AtPrime p.asIdeal) f)
      (algebraMap A (Localization.AtPrime p.asIdeal) a) := by
  let : Module.Flat A (Localization.AtPrime p.asIdeal) :=
    IsLocalization.flat (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
  exact ConcreteCategory.congr_hom (originalSectionSquare (S := Localization.AtPrime p.asIdeal) f).w a

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Module.Finite k (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))]

omit [IsDomain A] [IsIntegral Y] [IsDominant f] [Ring.KrullDimLE 1 A] in
include f in
private theorem sourceNoetherian : IsLocallyNoetherian Y :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- Genuine weighted native original Scheme.ord over ALL points of the
SAME original finite fibre equals actual generic rank times the SAME original
local order and residue degree, without normality or flatness of the finite map. -/
theorem finsum_fibre_principal_orders (hdim : topologicalKrullDim Y ≤ 1)
    (hp : p ≠ ⊥) (a : A) (ha : a ≠ 0) :
    letI := sectionsAlgebra f
    letI : IsLocallyNoetherian Y := sourceNoetherian f
    (∑ᶠ y : {y : Y // f y = p}, SchemeRegularSectionOrders.weightedOrder
      (sourceFieldStructure (k := k) f) (ProperBirationalSections.coefficientMap f a) y.1) =
      (Module.finrank A Γ(Y, ⊤) : ℤ) *
        ((Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap A (Localization.AtPrime p.asIdeal) a)).toNat : ℤ) *
        (Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) : ℤ) := by
  let S := Localization.AtPrime p.asIdeal
  let := sectionsAlgebra f
  let : IsLocallyNoetherian Y := sourceNoetherian f
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing p.asIdeal.primeCompl S
    (inferInstance : IsNoetherianRing A)
  let : Ring.KrullDimLE 1 S := by
    rw [Ring.krullDimLE_iff]
    let : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
      IsPreimmersion.of_isLocalization p.asIdeal.primeCompl
    have h := (Spec.map (CommRingCat.ofHom (algebraMap A S))).isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum S) ≤ topologicalKrullDim (PrimeSpectrum A) at h
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
    exact h.trans (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A))
  have hi := SchemeLocalizedFiniteAlgebras.coefficientMap_injective f
  have hb : ProperBirationalSections.coefficientMap f a ≠ 0 := by
    simpa only [map_zero] using hi.ne ha
  have has : algebraMap A S a ≠ 0 := by
    simpa only [map_zero] using
      (IsLocalization.injective S p.asIdeal.primeCompl_le_nonZeroDivisors).ne ha
  rw [AtPrimeInverseRegularOrderSums.finsum_fibre_eq_localInverse f p
    (sourceFieldStructure (k := k) f) hdim hp _ hb, coefficient_pullback]
  rw [← fieldStructure_eq f p]
  exact LocalizedFinitePrincipalOrders.finsum_principal_orders (S := S) (k := k) f
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors hdim _ has

end EnvelopeProperty.FiniteFibrePrincipalOrders
