import EnvelopeProperty.AffineGlobalSections
import EnvelopeProperty.Algebra.LocalPrincipalFieldDegrees
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Flat.Localization

/-! # Actual whole finite inverse schemes at original coefficient localizations -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLocalizedFiniteAlgebras
open FlatGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] [IsDomain A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsIntegral Y] [IsFinite f] [IsDominant f]

omit [IsIntegral Y] in
/-- Actual original dominance makes the SAME whole original coefficient map injective. -/
theorem coefficientMap_injective : Function.Injective (ProperBirationalSections.coefficientMap f) := by
  let := IsSchemeTheoreticallyDominant.of_isDominant f
  exact (f.app_injective ⊤).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).injective

omit [IsDomain A] [IsIntegral Y] [IsDominant f] in
/-- Actual original finiteness gives the SAME whole original section algebra as a finite module. -/
theorem sections_module_finite :
    letI := sectionsAlgebra f
    Module.Finite A Γ(Y, ⊤) := by
  let := sectionsAlgebra f
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).surjective)

variable (M : Submonoid A) [IsLocalization M S] (hM : M ≤ nonZeroDivisors A)
include M hM

/-- The SAME whole finite inverse at an original coefficient localization
has an actual domain section ring, internally derived from original maps. -/
theorem baseChange_sections_isDomain : IsDomain Γ(baseChange (S := S) f, ⊤) := by
  let := sectionsAlgebra f
  let := sectionsAlgebra (structureMap (S := S) f)
  let : IsAffine Y := isAffine_of_isAffineHom f
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let : IsDomain Γ(Y, ⊤) := IsIntegral.component_integral ⊤
  let : FaithfulSMul A Γ(Y, ⊤) :=
    (faithfulSMul_iff_algebraMap_injective A Γ(Y, ⊤)).mpr (coefficientMap_injective f)
  let : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, ⊤) M) (S ⊗[A] Γ(Y, ⊤)) :=
    IsLocalization.tensorRight (R := A) (S := Γ(Y, ⊤)) (A := S) M
  have hN : Algebra.algebraMapSubmonoid Γ(Y, ⊤) M ≤ nonZeroDivisors Γ(Y, ⊤) :=
    map_le_nonZeroDivisors_of_injective (algebraMap A Γ(Y, ⊤)) (coefficientMap_injective f) hM
  let : IsDomain (S ⊗[A] Γ(Y, ⊤)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hN
  exact Function.Injective.isDomain (AffineGlobalSections.tensorEquiv (S := S) f).symm.toRingHom
    (AffineGlobalSections.tensorEquiv (S := S) f).symm.injective

/-- The ENTIRE actual localized finite inverse scheme is genuinely integral. -/
theorem baseChange_isIntegral : IsIntegral (baseChange (S := S) f) := by
  let : IsDomain Γ(baseChange (S := S) f, ⊤) := baseChange_sections_isDomain f M hM
  let : IsAffine (baseChange (S := S) f) := isAffine_of_isAffineHom (structureMap (S := S) f)
  let : Nonempty (baseChange (S := S) f) :=
    ⟨(baseChange (S := S) f).isoSpec.inv (⊥ : PrimeSpectrum Γ(baseChange (S := S) f, ⊤))⟩
  exact isIntegral_of_isAffine_of_isDomain (baseChange (S := S) f)

omit [IsDomain A] [IsIntegral Y] [IsDominant f] in
/-- Actual whole native section base change preserves the SAME original
generic rank, with every localization and tensor comparison internally derived. -/
theorem baseChange_sections_finrank :
    letI := sectionsAlgebra f
    letI := sectionsAlgebra (structureMap (S := S) f)
    Module.finrank S Γ(baseChange (S := S) f, ⊤) = Module.finrank A Γ(Y, ⊤) := by
  let := sectionsAlgebra f
  let := sectionsAlgebra (structureMap (S := S) f)
  let : IsAffine Y := isAffine_of_isAffineHom f
  let e := AffineGlobalSections.tensorEquiv (S := S) f
  rw [← e.toLinearEquiv.finrank_eq, IsLocalization.finrank_eq S M hM,
    IsLocalizedModule.finrank_eq M (TensorProduct.mk A S Γ(Y, ⊤) 1) hM]

/-- The SAME actual whole finite inverse over an original local coefficient
ring has true principal field degree with the SAME original generic-rank factor.
No flatness of the original finite morphism, normality, chosen inverse algebra,
finite quotient or rank/degree matching premise. -/
theorem baseChange_principal_fieldDegree {k : Type u} [Field k] [Algebra k S]
    [IsLocalRing S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Module.Finite k (IsLocalRing.ResidueField S)] (a : S) (ha : a ≠ 0) :
    letI := sectionsAlgebra f
    letI := sectionsAlgebra (structureMap (S := S) f)
    letI : Algebra k Γ(baseChange (S := S) f, ⊤) :=
      ((algebraMap S Γ(baseChange (S := S) f, ⊤)).comp (algebraMap k S)).toAlgebra
    Module.finrank k (Γ(baseChange (S := S) f, ⊤) ⧸
      Ideal.span {algebraMap S Γ(baseChange (S := S) f, ⊤) a}) =
        Module.finrank A Γ(Y, ⊤) * (Ring.ord S a).toNat *
          Module.finrank k (IsLocalRing.ResidueField S) := by
  let := sectionsAlgebra f
  let := sectionsAlgebra (structureMap (S := S) f)
  let : Algebra k Γ(baseChange (S := S) f, ⊤) :=
    ((algebraMap S Γ(baseChange (S := S) f, ⊤)).comp (algebraMap k S)).toAlgebra
  let : IsScalarTower k S Γ(baseChange (S := S) f, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  let : Module.Flat A S := IsLocalization.flat S M
  let : IsDomain Γ(baseChange (S := S) f, ⊤) := baseChange_sections_isDomain f M hM
  let : IsAffine Y := isAffine_of_isAffineHom f
  let : Module.Finite A Γ(Y, ⊤) := sections_module_finite f
  let e := AffineGlobalSections.tensorEquiv (S := S) f
  let : Module.Finite S Γ(baseChange (S := S) f, ⊤) := Module.Finite.equiv e.toLinearEquiv
  have hi : Function.Injective (algebraMap S Γ(baseChange (S := S) f, ⊤)) := by
    have hi₀ := Algebra.TensorProduct.includeLeft_injective (A := S) (S := S) (coefficientMap_injective f)
    intro x y hxy
    apply hi₀
    apply e.injective
    change e (algebraMap S (S ⊗[A] Γ(Y, ⊤)) x) = e (algebraMap S (S ⊗[A] Γ(Y, ⊤)) y)
    rw [e.commutes, e.commutes]
    exact hxy
  rw [LocalPrincipalFieldDegrees.finrank_principalQuotient (k := k) hi a ha,
    baseChange_sections_finrank f M hM]

end EnvelopeProperty.SchemeLocalizedFiniteAlgebras
