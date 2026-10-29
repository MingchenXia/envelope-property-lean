import EnvelopeProperty.Vanishing.NadelMixedKummerDimensionStandard
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The SAME precise original relative dimension of the WHOLE mixed Kummer source

Actual original prime differential ranks determine genuine standard-smooth
principal neighbourhoods. These whole original neighbourhoods cover, giving
native scheme smoothness of exactly the original coordinate dimension n.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
namespace Neighbourhood
open Algebra Module
variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B] [Algebra.Smooth k B]
  (p : Ideal B) [p.IsPrime]

/-- The canonical native differential action at the SAME actual prime. -/
local instance primeDifferentialModule : Module (Localization.AtPrime p)
    (KaehlerDifferential k (Localization.AtPrime p)) :=
  instModuleKaehlerDifferentialOfSMulCommClass k (Localization.AtPrime p)
    (R' := Localization.AtPrime p)

/-- An actual original prime rank produces a native standard-smooth
principal neighbourhood of exactly that rank over the ORIGINAL base. -/
theorem exists_standardDimension (n : ℕ)
    (hn : Module.finrank (Localization.AtPrime p) (KaehlerDifferential k (Localization.AtPrime p)) = n) :
    ∃ g ∉ p, Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away g) := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (R := k) p
  let : Fact (g ∉ p) := ⟨hg⟩
  let : Algebra.IsStandardSmooth k (Localization.Away g) := hstd
  let : Algebra (Localization.Away g) (Localization.AtPrime p) := PrincipalPrime.algebra g p
  let : IsScalarTower B (Localization.Away g) (Localization.AtPrime p) := PrincipalPrime.tower g p
  let : IsLocalization (p.primeCompl.map (algebraMap B (Localization.Away g)))
      (Localization.AtPrime p) := PrincipalPrime.localization g p
  let : Algebra.FormallyEtale (Localization.Away g) (Localization.AtPrime p) :=
    PrincipalPrime.formallyEtale g p
  let : IsScalarTower k (Localization.Away g) (Localization.AtPrime p) := PrincipalPrime.baseTower g p
  exact ⟨g, hg, StandardDimension.of_formallyEtale_finrank (S := Localization.Away g)
    (T := Localization.AtPrime p) n hn⟩

end Neighbourhood
namespace SmoothSourceDimension
open Algebra Module
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (N : Fin q → ℕ) (c : Fin q → R) (A : Set (Fin q)) (σ : A ↪ Fin n) (u : Fin q → Rˣ)
  (hc : ∀ i, c i = mixedCoefficient x A σ u i)
  (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R))

include hx hc hN htame in
/-- Every original source prime has a genuine native standard-smooth
principal neighbourhood of SAME original coordinate dimension n. -/
theorem exists_standardDimension (p : Ideal (Ring N c)) [p.IsPrime] :
    ∃ g ∉ p, Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away g) := by
  have : Algebra.Smooth k (Ring N c) := SmoothSource.smooth x hx N c A σ u hc hN htame
  exact Neighbourhood.exists_standardDimension p n
    (finrank_local_kaehler x hx N c p A σ u hc hN htame)

include hx hc hN htame in
/-- The ACTUAL whole mixed quotient coefficient map is locally standard smooth
of precisely the ORIGINAL dimension, retaining all source components. -/
theorem locally_standardDimension :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap k (Ring N c)) := by
  classical
  choose f hf hstd using (fun p : PrimeSpectrum (Ring N c) =>
    exists_standardDimension x hx N c A σ u hc hN htame p.asIdeal)
  refine ⟨Set.range f, ?_, ?_⟩
  · simp [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, TopologicalSpace.Opens.ext_iff,
      Set.ext_iff]
    grind
  · rintro _ ⟨p, rfl⟩
    rw [← IsScalarTower.algebraMap_eq k (Ring N c) (Localization.Away (f p))]
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr (hstd p)

/-- The genuine native structure on the SAME entire mixed root scheme. -/
def structureMap : Spec (.of (Ring N c)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Ring N c)))

include hx hc hN htame in
/-- The SAME WHOLE original mixed Kummer source is ACTUALLY smooth of the
SAME original relative dimension n, without an n-smoothness or rank certificate. -/
theorem smoothOfRelativeDimension : SmoothOfRelativeDimension n (structureMap (k := k) N c) := by
  rw [structureMap, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  exact locally_standardDimension x hx N c A σ u hc hN htame

end SmoothSourceDimension
end EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
