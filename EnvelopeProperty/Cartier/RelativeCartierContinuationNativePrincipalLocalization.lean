import EnvelopeProperty.Cartier.RelativeCartierContinuationPrincipalCotangentLocalization

/-! # Actual native twist localization along its original numerator map -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeNativePrincipalLocalization
open CategoryTheory
open scoped TensorProduct
universe u
variable {k B : Type u} [Field k] [CommRing B]
variable (α : k →+* B) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Tw" => RelativeFrobenius.twist α p
local notation "bP" z => CommRingCat.Hom.hom (SchemeRelativeFrobeniusAffineMap.ringMap α p) z
local notation "locB" z => Localization.Away (bP z)
local notation "αP" z => RingHom.comp (algebraMap B (locB z)) α
local notation "TwP" z => RelativeFrobenius.twist (αP z) p
local notation "cP" z => RelativeFrobenius.coefficientMap (αP z) p
local notation "eP" z => RelativeTwistPrincipalLocalization.principalIso α p z
local notation "τP" z => CommRingCat.Hom.hom
  (RelativeEtaleBaseChange.twistMap α (algebraMap B (locB z)) p)

/-- The actual native localized twist acts by EXACTLY the ORIGINAL numerator τ. -/
abbrev nativeAlgebra (t : Tw) : Algebra (Tw) (TwP t) := (τP t).toAlgebra

/-- The ENTIRE native algebra map is precisely the ORIGINAL twist numerator. -/
theorem nativeAlgebra_algebraMap (t : Tw) :
    letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
    algebraMap (Tw) (TwP t) = τP t := rfl

/-- The SAME original principal isomorphism is a genuine T-algebra equivalence,
from its INTERNALLY PROVED entire numerator equation. -/
def localizationEquiv (t : Tw) :
    letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
    (TwP t) ≃ₐ[Tw] Localization.Away t := by
  letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
  refine { (eP t).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro x
  exact congrArg (fun h : (Tw) ⟶ CommRingCat.of (Localization.Away t) => h.hom x)
    (RelativeTwistPrincipalLocalization.principalIso_twistMap α p t)

/-- EVERY actual element retains the SAME original principal-isomorphism value. -/
theorem localizationEquiv_apply (t : Tw) (x : TwP t) :
    localizationEquiv α p t x = (eP t).hom x := rfl

/-- The actual native localized twist genuinely IS the principal localization
along its SAME original τ. No localization or comparison certificate is supplied. -/
theorem native_isLocalization (t : Tw) :
    letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
    IsLocalization (Submonoid.powers t) (TwP t) := by
  let : Algebra (Tw) (TwP t) := nativeAlgebra α p t
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers t) (localizationEquiv α p t).symm

/-- The ORIGINAL two coefficient inclusions give the genuine native τ scalar tower. -/
theorem coefficientTower (t : Tw) :
    letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
    letI : Algebra k (TwP t) := (cP t).hom.toAlgebra
    letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
    IsScalarTower k (Tw) (TwP t) := by
  let : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
  let : Algebra k (TwP t) := (cP t).hom.toAlgebra
  let : Algebra (Tw) (TwP t) := nativeAlgebra α p t
  apply IsScalarTower.of_algebraMap_eq' (R := k) (S := Tw) (A := TwP t)
  exact (congrArg CommRingCat.Hom.hom
    (RelativeEtaleBaseChange.coefficientMap_twistMap α (algebraMap B (locB t)) p)).symm

/-- Genuine native cotangent scalar extension with actual target T', derived
from the actual localization and the ORIGINAL coefficient scalar tower. -/
def tensorCotangentEquiv (t : Tw) :
    letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
    letI : Algebra k (TwP t) := (cP t).hom.toAlgebra
    letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
    letI : IsScalarTower k (Tw) (TwP t) := coefficientTower α p t
    (TwP t) ⊗[Tw] KaehlerDifferential k (Tw) ≃ₗ[TwP t] KaehlerDifferential k (TwP t) := by
  letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
  letI : Algebra k (TwP t) := (cP t).hom.toAlgebra
  letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
  letI : IsScalarTower k (Tw) (TwP t) := coefficientTower α p t
  let : IsLocalization (Submonoid.powers t) (TwP t) := native_isLocalization α p t
  let : Algebra.FormallyEtale (Tw) (TwP t) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := TwP t) (Submonoid.powers t)
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (Tw) (TwP t)

/-- EVERY original scalar/differential tensor has its SAME native τ value. -/
theorem tensorCotangentEquiv_tmul_D (t : Tw) (a : TwP t) (x : Tw) :
    letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
    letI : Algebra k (TwP t) := (cP t).hom.toAlgebra
    letI : Algebra (Tw) (TwP t) := nativeAlgebra α p t
    letI : IsScalarTower k (Tw) (TwP t) := coefficientTower α p t
    tensorCotangentEquiv α p t (a ⊗ₜ[Tw] KaehlerDifferential.D k (Tw) x) =
      a • KaehlerDifferential.D k (TwP t) ((τP t) x) := by
  let : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
  let : Algebra k (TwP t) := (cP t).hom.toAlgebra
  let : Algebra (Tw) (TwP t) := nativeAlgebra α p t
  let : IsScalarTower k (Tw) (TwP t) := coefficientTower α p t
  change KaehlerDifferential.mapBaseChange k (Tw) (TwP t)
    (a ⊗ₜ[Tw] KaehlerDifferential.D k (Tw) x) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
    nativeAlgebra_algebraMap α p t]

end EnvelopeProperty.Cartier.RelativeNativePrincipalLocalization
