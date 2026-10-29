import EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleChart
import EnvelopeProperty.Char0.BPGeometricMultiplierModule
import EnvelopeProperty.Vanishing.NadelPrincipalizationRestriction

/-! # Whole native affine BP formula on internally produced original charts

`Formula` names the complete geometric native conclusion so specialization
retains the original objects without repeatedly normalizing their large
module types. It is a proposition proved here, never a supplied certificate.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleMultiplier
open Char0

section Formula
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- The whole actual BP multiplier-module formula, for every exponent,
with its original rounded inclusion and pushed differential-section triangle. -/
def Formula (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ)
    (I : Ideal C) (hI : I ≠ ⊥) (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) : Prop :=
    letI := smoothOfRelativeDimension_of_etale_coordinates z hz
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      ∃ (hsm : SmoothOfRelativeDimension n (S.composite ≫ f))
        (hproper : IsProper S.composite)
        (hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor),
        ∀ q : ℚ,
          letI := hsm
          letI := hproper
          ∃ e : (multiplierIdealSheaf C I hI q).toModules ≅
              (Scheme.Modules.pushforward S.composite).obj
                (RoundedCanonicalModule.relativeRounded f S.composite n
                  ((specIdealSheaf I).comap S.composite) hJ q),
            e.hom ≫ (Scheme.Modules.pushforward S.composite).map
                (RoundedCanonicalModule.relativeRoundedInclusion f S.composite n
                  ((specIdealSheaf I).comap S.composite) hJ q) =
              (multiplierIdealSheaf C I hI q).toModulesInclusion ≫
                RoundedCanonicalModule.pushedDifferentialSection f S.composite n

/-- The existing native affine BP theorem proves the entire geometric formula. -/
theorem formula (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ)
    (I : Ideal C) (hI : I ≠ ⊥) (z : Fin n → C)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    Formula C n I hI z hz :=
  exists_BP_pushforwardRounded_iso_multiplierModule C n I hI z hz
end Formula

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Only original geometry supplies the selected actual chart, its literal
original generic-germ coefficient algebra, actual coefficient ideal and
etale tuple. The whole native BP formula is proved for those SAME data. -/
theorem originalFormula (I : X.IdealSheafData)
    (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (x : X) :
    let U := NadelPrincipalizationEtaleChart.chart f n x
    letI : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
    letI := f.stalkAlgebra (genericPoint X)
    letI := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
    Formula (NadelPrincipalizationAffineChart.algebra f U) n
      (NadelPrincipalizationAffineChart.ideal f I U)
      (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)
      (NadelPrincipalizationEtaleChart.fieldCoordinates f n x)
      (NadelPrincipalizationEtaleChart.fieldCoordinates_etale f n x) := by
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  exact formula (NadelPrincipalizationAffineChart.algebra f U) n
    (NadelPrincipalizationAffineChart.ideal f I U)
    (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)
    (NadelPrincipalizationEtaleChart.fieldCoordinates f n x)
    (NadelPrincipalizationEtaleChart.fieldCoordinates_etale f n x)

omit [CharZero k] in
/-- The native formula uses precisely the same actual affine triple as the
proved restriction of the original global BP. Only proof witnesses differ. -/
theorem selectedTriple_eq (I : X.IdealSheafData)
    (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) (x : X) :
    let U := NadelPrincipalizationEtaleChart.chart f n x
    letI : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
    letI := f.stalkAlgebra (genericPoint X)
    letI : SmoothOfRelativeDimension n (NadelPrincipalizationAffineChart.structureMap f U) :=
      smoothOfRelativeDimension_of_etale_coordinates
      (NadelPrincipalizationEtaleChart.fieldCoordinates f n x)
      (NadelPrincipalizationEtaleChart.fieldCoordinates_etale f n x)
    affinePrincipalizationTriple (NadelPrincipalizationAffineChart.structureMap f U) n
      (NadelPrincipalizationAffineChart.ideal f I U)
      (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U) =
      NadelPrincipalizationRestriction.affineTriple f n I hI U := rfl

end EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleMultiplier
