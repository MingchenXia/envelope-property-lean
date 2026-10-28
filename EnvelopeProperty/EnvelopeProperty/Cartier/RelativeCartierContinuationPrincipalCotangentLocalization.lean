import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistPrincipalLocalization
import EnvelopeProperty.Cartier.RelativeCartierContinuationGlobalExteriorExchange
import Mathlib.RingTheory.Etale.Kaehler

/-! # Actual cotangent/exterior transport along the SAME native principal comparison -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePrincipalCotangentLocalization
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
local notation "cA" z => RelativeFrobenius.coefficientMap α p ≫
  CommRingCat.ofHom (algebraMap (Tw) (Localization.Away z))
local notation "eP" z => RelativeTwistPrincipalLocalization.principalIso α p z
local notation "τP" z => RelativeEtaleBaseChange.twistMap α (algebraMap B (locB z)) p

/-- The actual universal cotangent comparison over the ORIGINAL coefficient square. -/
def cotangentIso (t : Tw) :=
  @RelativeGlobalCotangentExchange.cotangentIso.{u}
    (CommRingCat.of k) (TwP t) (CommRingCat.of (Localization.Away t)) (cP t) (cA t) (eP t)
    (RelativeTwistPrincipalLocalization.principalIso_coefficient α p t)

/-- EVERY original differential has its actual original principal-ring image. -/
theorem cotangentIso_D (t : Tw) (x : TwP t) :
    (cotangentIso α p t).hom (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d ((eP t).hom x) :=
  RelativeGlobalCotangentExchange.cotangentIso_D (cP t) (cA t) (eP t)
    (RelativeTwistPrincipalLocalization.principalIso_coefficient α p t) x

/-- The SAME actual twist numerator preserves every original universal differential. -/
theorem cotangentIso_twistMap_D (t : Tw) (x : Tw) :
    (cotangentIso α p t).hom (CommRingCat.KaehlerDifferential.d ((τP t) x)) =
      CommRingCat.KaehlerDifferential.d (algebraMap (Tw) (Localization.Away t) x) := by
  rw [cotangentIso_D]
  have h := congrArg (fun F : (Tw) ⟶ CommRingCat.of (Localization.Away t) => F.hom x)
    (RelativeTwistPrincipalLocalization.principalIso_twistMap α p t)
  exact congrArg CommRingCat.KaehlerDifferential.d h

/-- GENUINE all-degree native exterior equivalence, including zero and empty localizations. -/
def exteriorIso (t : Tw) (q : ℕ) :=
  @RelativeGlobalExteriorExchange.exteriorIso.{u}
    (CommRingCat.of k) (TwP t) (CommRingCat.of (Localization.Away t)) (cP t) (cA t) (eP t)
    (RelativeTwistPrincipalLocalization.principalIso_coefficient α p t) q

/-- EVERY original pure wedge retains its same ordered actual cotangent images. -/
theorem exteriorIso_wedge (t : Tw) (q : ℕ) (m : Fin q → CommRingCat.KaehlerDifferential (cP t)) :
    (exteriorIso α p t q).hom (exteriorPower.ιMulti (TwP t) q m) =
      exteriorPower.ιMulti (Localization.Away t) q (fun i => (cotangentIso α p t).hom (m i)) :=
  RelativeGlobalExteriorExchange.exteriorIso_wedge (cP t) (cA t) (eP t)
    (RelativeTwistPrincipalLocalization.principalIso_coefficient α p t) q m

/-- ALL original numerator differential wedges, including q0, retain their entire native values. -/
theorem exteriorIso_twistMap_wedge (t : Tw) (q : ℕ) (x : Fin q → Tw) :
    (exteriorIso α p t q).hom
        (exteriorPower.ιMulti (TwP t) q (fun i => CommRingCat.KaehlerDifferential.d ((τP t) (x i)))) =
      exteriorPower.ιMulti (Localization.Away t) q
        (fun i => CommRingCat.KaehlerDifferential.d
          (algebraMap (Tw) (Localization.Away t) (x i))) := by
  rw [exteriorIso_wedge]
  congr 1
  funext i
  exact cotangentIso_twistMap_D α p t (x i)

/-- The NATIVE induced localization algebra retains the ORIGINAL coefficient map. -/
theorem localization_algebraMap (t : Tw) :
    letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
    algebraMap k (Localization.Away t) = (cA t).hom := by
  let : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
  ext z
  rfl

/-- The actual original principal localization gives genuine cotangent scalar extension;
the k-actions are FIXED original coefficient maps, not free algebra inputs. -/
def tensorCotangentEquiv (t : Tw) :
    letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
    Localization.Away t ⊗[Tw] KaehlerDifferential k (Tw) ≃ₗ[Localization.Away t]
      KaehlerDifferential k (Localization.Away t) := by
  letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
  let : Algebra.FormallyEtale (Tw) (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.Away t) (Submonoid.powers t)
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (Tw) (Localization.Away t)

/-- EVERY actual pure tensor of an original differential retains its native localization value. -/
theorem tensorCotangentEquiv_tmul_D (t : Tw) (a : Localization.Away t) (x : Tw) :
    letI : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
    tensorCotangentEquiv α p t (a ⊗ₜ[Tw] KaehlerDifferential.D k (Tw) x) =
      a • KaehlerDifferential.D k (Localization.Away t)
        (algebraMap (Tw) (Localization.Away t) x) := by
  let : Algebra k (Tw) := (RelativeFrobenius.coefficientMap α p).hom.toAlgebra
  change KaehlerDifferential.mapBaseChange k (Tw) (Localization.Away t)
    (a ⊗ₜ[Tw] KaehlerDifferential.D k (Tw) x) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

end EnvelopeProperty.Cartier.RelativePrincipalCotangentLocalization
