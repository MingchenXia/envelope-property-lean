import EnvelopeProperty.Vanishing.NadelMixedKummerCotangentCriterion
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Algebra

/-! # Actual derivative and extension transport to the original prime localization

All maps are the native localization maps. Original derivatives are extended
through the genuine formally étale Kähler comparison, and the actual relation
kernel is transported using the actual localization kernel theorem.
-/

noncomputable section
universe u
open scoped TensorProduct
namespace EnvelopeProperty.Vanishing.NadelMixedKummer
namespace DerivativeLocalization
variable {k P T : Type u} [CommRing k] [CommRing P] [CommRing T]
  [Algebra k P] [Algebra k T] [Algebra P T] [IsScalarTower k P T]
  [Algebra.FormallyEtale P T]

/-- Extend the ACTUAL original derivation through the genuine formally étale
Kähler comparison; for prime localization this is the actual localized derivation. -/
def extend (δ : Derivation k P P) : Derivation k T T :=
  (((Algebra.linearMap P T).compDer δ).liftKaehlerDifferential.liftBaseChange T ∘ₗ
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k P T).symm.toLinearMap).compDer
      (KaehlerDifferential.D k T)

/-- The extended actual derivative retains its value on EVERY original element. -/
theorem extend_algebraMap (δ : Derivation k P P) (a : P) :
    extend δ (algebraMap P T a) = algebraMap P T (δ a) := by
  change (((Algebra.linearMap P T).compDer δ).liftKaehlerDifferential.liftBaseChange T)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k P T).symm
      (KaehlerDifferential.D k T (algebraMap P T a))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

end DerivativeLocalization
namespace ExtensionLocalization
variable {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
  (P : Algebra.Extension.{u} k S) (p : Ideal S) [p.IsPrime]

/-- The actual original extension localized at the SAME original target prime. -/
abbrev localExtension : Algebra.Extension k (Localization.AtPrime p) :=
  P.localization p.primeCompl

/-- The actual canonical original-ambient algebra on the native localization. -/
@[instance_reducible] def ambientAlgebra : Algebra P.Ring (localExtension P p).Ring :=
  show Algebra P.Ring (Localization (p.primeCompl.comap (algebraMap P.Ring S))) from inferInstance

attribute [local instance] ambientAlgebra

/-- The actual native localization property of the whole ambient ring. -/
theorem ambientLocalization : IsLocalization (p.primeCompl.comap (algebraMap P.Ring S))
    (localExtension P p).Ring :=
  show IsLocalization (p.primeCompl.comap (algebraMap P.Ring S))
    (Localization (p.primeCompl.comap (algebraMap P.Ring S))) from inferInstance

attribute [local instance] ambientLocalization

/-- The actual original coefficient tower on the whole ambient localization. -/
theorem ambientTower : IsScalarTower k P.Ring (localExtension P p).Ring :=
  show IsScalarTower k P.Ring (Localization (p.primeCompl.comap (algebraMap P.Ring S))) from inferInstance

attribute [local instance] ambientTower

/-- The whole ORIGINAL kernel localizes to the SAME native extension kernel. -/
theorem ker_eq_map : (localExtension P p).ker =
    P.ker.map (algebraMap P.Ring (localExtension P p).Ring) := by
  have ht : (p.primeCompl.comap (algebraMap P.Ring S)).map (algebraMap P.Ring S) =
      p.primeCompl := Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective p.primeCompl
  exact IsLocalization.ker_map (S := (localExtension P p).Ring)
    (Localization.AtPrime p) (algebraMap P.Ring S) ht

/-- Every original finite relation generator remains an actual generator of
the entire localized kernel, without a kernel presentation certificate. -/
theorem span_relation_eq_ker {q : ℕ} (r : Fin q → P.Ring)
    (hr : Ideal.span (Set.range r) = P.ker) :
    Ideal.span (Set.range (fun i => algebraMap P.Ring (localExtension P p).Ring (r i))) =
      (localExtension P p).ker := by
  rw [ker_eq_map, ← hr, Ideal.map_span]
  congr 1
  exact Set.range_comp _ _

/-- The actual localized ambient extension remains formally smooth by
native localization and composition, with no source smoothness input. -/
theorem ambient_formallySmooth [Algebra.FormallySmooth k P.Ring] :
    Algebra.FormallySmooth k (localExtension P p).Ring := by
  have : Algebra.FormallySmooth P.Ring (localExtension P p).Ring :=
    Algebra.FormallySmooth.of_isLocalization (p.primeCompl.comap (algebraMap P.Ring S))
  exact Algebra.FormallySmooth.comp k P.Ring (localExtension P p).Ring

end ExtensionLocalization
end EnvelopeProperty.Vanishing.NadelMixedKummer
