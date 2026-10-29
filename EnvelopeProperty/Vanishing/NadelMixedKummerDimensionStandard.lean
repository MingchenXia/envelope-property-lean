import EnvelopeProperty.Vanishing.NadelMixedKummerDimensionLocal
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Precise standard-smooth dimension from an actual prime differential rank

Every ring map here is the native localization map. The prime differential
rank is compared through actual formally-etale Kahler base change with the
native standard-smooth neighbourhood, rather than assumed as a scheme dimension.
-/

noncomputable section
universe u
open scoped TensorProduct
namespace EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
namespace StandardDimension
open Algebra Module

variable {k S T : Type u} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
  [Algebra.FormallyEtale S T] [Nontrivial T] [Algebra.IsStandardSmooth k S]

/-- A native standard-smooth algebra's precise dimension is detected by
actual Kahler base change to any nonzero formally-etale target. -/
theorem of_formallyEtale_finrank (n : ℕ)
    (h : Module.finrank T (KaehlerDifferential k T) = n) :
    Algebra.IsStandardSmoothOfRelativeDimension n k S := by
  have : Nontrivial S := RingHom.domain_nontrivial (algebraMap S T)
  have hi := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S T).finrank_eq
  have hb : Module.finrank T (T ⊗[S] KaehlerDifferential k S) =
      Module.finrank S (KaehlerDifferential k S) := Module.finrank_baseChange
  have hn : Module.finrank S (KaehlerDifferential k S) = n := hb.symm.trans (hi.trans h)
  apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr
  rw [← Module.finrank_eq_rank, hn]

end StandardDimension
namespace PrincipalPrime
variable {B : Type u} [CommRing B] (g : B) (p : Ideal B) [p.IsPrime] [Fact (g ∉ p)]

/-- The actual original principal-open denominators lie in the SAME prime complement. -/
theorem powers_le : Submonoid.powers g ≤ p.primeCompl :=
  Submonoid.powers_le.mpr (Fact.out : g ∉ p)

/-- The genuine native principal-localization to prime-localization algebra. -/
@[instance_reducible] def algebra : Algebra (Localization.Away g) (Localization.AtPrime p) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers g) p.primeCompl (powers_le g p)
attribute [local instance] algebra

/-- The actual original coefficient structure triangle for these native localizations. -/
theorem tower : IsScalarTower B (Localization.Away g) (Localization.AtPrime p) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away g) (Localization.AtPrime p) (.powers g) p.primeCompl
    (powers_le g p)
attribute [local instance] tower

/-- The SAME prime localization is a genuine localization of the original principal open. -/
theorem localization : IsLocalization (p.primeCompl.map (algebraMap B (Localization.Away g)))
    (Localization.AtPrime p) :=
  IsLocalization.isLocalization_of_submonoid_le (Localization.Away g) (Localization.AtPrime p) (.powers g) p.primeCompl (powers_le g p)
attribute [local instance] localization

/-- The actual principal-open to original-prime map is formally etale. -/
theorem formallyEtale : Algebra.FormallyEtale (Localization.Away g) (Localization.AtPrime p) :=
  Algebra.FormallyEtale.of_isLocalization (p.primeCompl.map (algebraMap B (Localization.Away g)))
attribute [local instance] formallyEtale

variable {k : Type u} [CommRing k] [Algebra k B]

/-- The original k-algebra actions commute through the actual native localization maps. -/
theorem baseTower : IsScalarTower k (Localization.Away g) (Localization.AtPrime p) := by
  apply IsScalarTower.of_algebraMap_eq'
  rw [IsScalarTower.algebraMap_eq k B (Localization.Away g), ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq B (Localization.Away g) (Localization.AtPrime p),
    ← IsScalarTower.algebraMap_eq k B (Localization.AtPrime p)]

end PrincipalPrime
end EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
