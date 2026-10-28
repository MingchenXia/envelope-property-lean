import EnvelopeProperty.Vanishing.NadelMixedKummerDimensionAmbient
import Mathlib.LinearAlgebra.Dimension.Localization

/-! # Actual relation cotangent rank and quotient differential rank

The only determinant condition is the actual relation derivation Jacobian;
the mixed source supplies it internally. Every equivalence here is constructed
from the actual whole relation map and actual native cotangent complex.
-/

noncomputable section
universe u v
namespace EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
open Algebra Module
namespace CotangentRank
variable {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
  (P : Algebra.Extension.{u} k S) {q : ℕ} (r : Fin q → P.Ring)
  (hr : Ideal.span (Set.range r) = P.ker) (d : Fin q → Derivation k P.Ring S)
  (hJ : IsUnit (CotangentCriterion.jacobian P r d).det)

include hJ in
/-- The actual original finite relation map is bijective, by its actual
unit derivation Jacobian and whole kernel generation. -/
theorem relationMap_bijective : Function.Bijective (CotangentCriterion.relationMap P r hr) := by
  have hF : IsUnit (CotangentCriterion.derivativeMap P d ∘ₗ P.cotangentComplex ∘ₗ
      CotangentCriterion.relationMap P r hr) := by
    rw [CotangentCriterion.derivative_cotangent_relation]
    exact Matrix.isUnit_toLin'_iff.mpr
      ((CotangentCriterion.jacobian P r d).isUnit_iff_isUnit_det.mpr hJ)
  refine ⟨?_, CotangentCriterion.relationMap_surjective P r hr⟩
  intro a b hab
  apply ((Module.End.isUnit_iff _).mp hF).injective
  exact congrArg (fun v => CotangentCriterion.derivativeMap P d (P.cotangentComplex v)) hab

/-- A genuine q-dimensional whole original relation-cotangent equivalence. -/
def relationEquiv : (Fin q → S) ≃ₗ[S] P.Cotangent :=
  LinearEquiv.ofBijective (CotangentCriterion.relationMap P r hr)
    (relationMap_bijective P r hr d hJ)

/-- The actual original relation classes are a genuine basis of the WHOLE
kernel cotangent module, rather than an assumed regular-sequence certificate. -/
def relationBasis : Basis (Fin q) S P.Cotangent :=
  (Pi.basisFun S (Fin q)).map (relationEquiv P r hr d hJ)

include hr hJ in
/-- The ACTUAL native cotangent complex is injective, from the same genuine
unit minor and actual relation generators. -/
theorem cotangentComplex_injective : Function.Injective P.cotangentComplex := by
  have hF : IsUnit (CotangentCriterion.derivativeMap P d ∘ₗ P.cotangentComplex ∘ₗ
      CotangentCriterion.relationMap P r hr) := by
    rw [CotangentCriterion.derivative_cotangent_relation]
    exact Matrix.isUnit_toLin'_iff.mpr
      ((CotangentCriterion.jacobian P r d).isUnit_iff_isUnit_det.mpr hJ)
  intro a b hab
  obtain ⟨wa, rfl⟩ := CotangentCriterion.relationMap_surjective P r hr a
  obtain ⟨wb, rfl⟩ := CotangentCriterion.relationMap_surjective P r hr b
  apply congrArg (CotangentCriterion.relationMap P r hr)
  apply ((Module.End.isUnit_iff _).mp hF).injective
  exact congrArg (CotangentCriterion.derivativeMap P d) hab

variable [IsDomain S] {ι : Type v} [Fintype ι] (b : Basis ι S P.CotangentSpace)

include hr hJ b in
/-- The whole quotient differential rank is the ACTUAL ambient width minus
the actual number of original independent relations. -/
theorem finrank_kaehler : Module.finrank S (KaehlerDifferential k S) = Fintype.card ι - q := by
  have : Module.Finite S P.CotangentSpace := Module.Finite.of_basis b
  have : Module.Finite S P.Cotangent := Module.Finite.of_basis (relationBasis P r hr d hJ)
  have hker : LinearMap.ker P.toKaehler = LinearMap.range P.cotangentComplex :=
    LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler
  have hd := (LinearMap.ker P.toKaehler).finrank_quotient_add_finrank
  have hquot := (P.toKaehler.quotKerEquivOfSurjective P.toKaehler_surjective).finrank_eq
  rw [hquot, hker, LinearMap.finrank_range_of_inj (cotangentComplex_injective P r hr d hJ),
    Module.finrank_eq_card_basis (relationBasis P r hr d hJ),
    Module.finrank_eq_card_basis b, Fintype.card_fin] at hd
  omega

end CotangentRank
end EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
