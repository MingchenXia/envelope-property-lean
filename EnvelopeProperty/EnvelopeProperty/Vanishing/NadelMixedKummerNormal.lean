import EnvelopeProperty.Vanishing.NadelMixedKummerSmooth
import EnvelopeProperty.Algebra.RegularNormal
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular

/-! # Actual regularity and local normality of the WHOLE mixed Kummer source

The entire source need not be a domain or connected. Every prime localization
is proved a regular domain and integrally closed, from actual smoothness.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer

/-- Prime localization of an actual regular ring is itself a regular ring,
by the native comparison of every further prime localization. -/
theorem regularRing_atPrime {B : Type u} [CommRing B] [IsRegularRing B]
    (p : Ideal B) [p.IsPrime] : IsRegularRing (Localization.AtPrime p) := by
  have : IsNoetherianRing (Localization.AtPrime p) := inferInstance
  apply isRegularRing_iff.mpr
  intro q hq
  let q₀ : Ideal B := q.comap (algebraMap B (Localization.AtPrime p))
  have : q₀.IsPrime := Ideal.comap_isPrime _ q
  have : IsLocalization.AtPrime (Localization.AtPrime q) q₀ :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization p.primeCompl _ q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q₀.primeCompl (Localization.AtPrime q)
      (Localization.AtPrime q₀)).symm.toRingEquiv

namespace SmoothSource
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (N : Fin q → ℕ) (c : Fin q → R)
  (A : Set (Fin q)) (σ : A ↪ Fin n) (u : Fin q → Rˣ)
  (hc : ∀ i, c i = mixedCoefficient x A σ u i)
  (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R))

include hx hc hN htame in
/-- The SAME WHOLE mixed quotient is a regular ring over the actual field,
without any domain, connectedness, normality or normalization input. -/
theorem regularRing : IsRegularRing (Ring N c) := by
  have : Algebra.Smooth k (Ring N c) := smooth x hx N c A σ u hc hN htame
  have : IsNoetherianRing (Ring N c) := Algebra.FiniteType.isNoetherianRing k (Ring N c)
  exact isRegularRing_iff.mpr (fun p _ => Algebra.IsSmoothAt.isRegularLocalRing (k := k) p)

include hx hc hN htame in
/-- Every ORIGINAL prime localization of the SAME whole source is genuinely
a domain, derived from its actual regular local ring. No component is selected. -/
theorem localization_isDomain (p : Ideal (Ring N c)) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) := by
  have : IsRegularRing (Ring N c) := regularRing x hx N c A σ u hc hN htame
  exact IsLocalRing.isDomain_of_isRegularLocalRing (Localization.AtPrime p)

include hx hc hN htame in
/-- Every ORIGINAL prime localization is integrally closed, derived from
actual regularity. This proves local normality of the WHOLE possibly
disconnected source without a global-domain premise. -/
theorem localization_isIntegrallyClosed (p : Ideal (Ring N c)) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  have : IsRegularRing (Ring N c) := regularRing x hx N c A σ u hc hN htame
  have : IsRegularRing (Localization.AtPrime p) := regularRing_atPrime p
  have : IsDomain (Localization.AtPrime p) := localization_isDomain x hx N c A σ u hc hN htame p
  exact EnvelopeProperty.isIntegrallyClosed_of_isRegularRing _

include hx hc hN htame in
/-- Every actual native scheme stalk of the SAME whole mixed source is
integrally closed; this is the genuine whole local normality endpoint. -/
theorem stalk_isIntegrallyClosed (z : Spec (.of (Ring N c))) :
    IsIntegrallyClosed ((Spec (.of (Ring N c))).presheaf.stalk z) := by
  let z' : PrimeSpectrum (Ring N c) := z
  have : z'.asIdeal.IsPrime := z'.isPrime
  have := localization_isIntegrallyClosed x hx N c A σ u hc hN htame z'.asIdeal
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of (Ring N c)) z').commRingCatIsoToRingEquiv.symm

end SmoothSource
end EnvelopeProperty.Vanishing.NadelMixedKummer
