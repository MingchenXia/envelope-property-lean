import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyNative

/-!
# Bijectivity of the specified native relative inverse Cartier one-form map

The positive exterior-power construction agrees on every actual cotangent basis
vector with the already accepted one-form map. Its derived genuine bijectivity
therefore applies to that SAME native map, including over imperfect fields.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialCartier
open CategoryTheory MvPolynomial
open scoped Classical
universe u
variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
local notation "P" => MvPolynomial (Fin n) k
local notation "T" => RelativeFrobenius.twist (algebraMap k P) p
local notation "K" => RelativeEtaleDeRham.complex (X : Fin n → P) (polynomialEtale k n) p

private theorem original_oneEquiv_basis_singleton {R V I : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [LinearOrder I] (b : Module.Basis I R V) (i : I) :
    exteriorPower.oneEquiv R V
      (b.exteriorPower 1 (Set.powersetCard.ofCard (Finset.card_singleton i))) = b i := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.oneEquiv_ιMulti]
  dsimp only [Function.comp_apply]
  congr 1
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)

/-- The actual all-degree representative in degree one is the SAME accepted original
one-form representative under the genuine first exterior-power identification. -/
theorem oneRepresentative_exterior (w : KaehlerDifferential k T) :
    originalExteriorRepresentative k p n 1 ((exteriorPower.oneEquiv T
      (KaehlerDifferential k T)).symm w) = (oneRepresentative k p n w).val := by
  have h : (exteriorRepresentative k p n 1).comp
        (exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm.toLinearMap =
      (LinearMap.ker (oneShortComplex k p n).g.hom).subtype.comp
        (oneRepresentative k p n) := by
    apply (twistBasis k p n).ext
    intro i
    let s : Set.powersetCard (Fin n) 1 :=
      Set.powersetCard.ofCard (Finset.card_singleton i)
    have ht : (exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm
        (twistBasis k p n i) = (twistBasis k p n).exteriorPower 1 s := by
      apply (exteriorPower.oneEquiv T (KaehlerDifferential k T)).injective
      rw [LinearEquiv.apply_symm_apply, original_oneEquiv_basis_singleton]
    have hb : exteriorRepresentative k p n 1 ((twistBasis k p n).exteriorPower 1 s) =
        (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 1 from
          monomial (RelativePolynomialCoefficients.residueDigit p 1 s).toFinsupp (1 : k) •
            (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 1 s) := by
      exact Module.Basis.constr_basis _ _ _ _
    have hp : (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower 1 s =
        (exteriorPower.oneEquiv P (KaehlerDifferential k P)).symm
          (KaehlerDifferential.D k P (X i)) := by
      apply (exteriorPower.oneEquiv P (KaehlerDifferential k P)).injective
      rw [original_oneEquiv_basis_singleton, LinearEquiv.apply_symm_apply,
        KaehlerDifferential.mvPolynomialBasis_apply]
    have haexp : (RelativePolynomialCoefficients.residueDigit p 1 s).toFinsupp =
        Finsupp.single i (p-1) := by
      ext j
      have hs : j ∈ s ↔ j = i := by
        change j ∈ ({i} : Finset (Fin n)) ↔ j = i
        exact Finset.mem_singleton
      simp only [Box.toFinsupp_apply, RelativePolynomialCoefficients.residueDigit_apply,
        Finsupp.single_apply, hs, eq_comm]
    have ha : monomial (RelativePolynomialCoefficients.residueDigit p 1 s).toFinsupp (1 : k) =
        (X i : P)^(p-1) := by
      rw [haexp, X_pow_eq_monomial]
    have hr : oneRepresentative k p n (twistBasis k p n i) = oneCoordinateCycle k p n i := by
      rw [twistBasis_apply, oneRepresentative_D]
    change exteriorRepresentative k p n 1
      ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm (twistBasis k p n i)) =
        (oneRepresentative k p n (twistBasis k p n i)).val
    rw [ht, hb, hp, ha, hr, oneCoordinateCycle_val]
  exact congrArg (fun f => f w) h

/-- The positive-degree class construction at q=0 retains the SAME native one-cycle class. -/
theorem positiveCycleClass_zero : positiveCycleClass k p n 0 = oneCycleClass k p n := rfl

/-- The actual specified one-form map is the positive exterior Cartier map under the
genuine canonical cotangent/first-exterior-power identification. -/
theorem inverseCartierOne_eq_positive (w : KaehlerDifferential k T) :
    inverseCartierOne k p n w = inverseCartierPositive k p n 0
      ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm w) := by
  change oneCycleClass k p n (oneRepresentative k p n w) = positiveCycleClass k p n 0
    (positiveRepresentative k p n 0 ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm w))
  rw [positiveCycleClass_zero]
  congr 1
  apply Subtype.ext
  exact (oneRepresentative_exterior k p n w).symm

/-- Genuine bijectivity of the SAME native relative one-form inverse Cartier map, over
EVERY imperfect characteristic-p field as well as every perfect field. -/
theorem inverseCartierOne_bijective : Function.Bijective (inverseCartierOne k p n) := by
  have hb : Function.Bijective (fun w => inverseCartierPositive k p n 0
      ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm w)) :=
    (inverseCartierPositive_bijective k p n 0).comp
      (exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm.bijective
  have he : (inverseCartierOne k p n : KaehlerDifferential k T → (K).homology 1) =
      fun w => inverseCartierPositive k p n 0
        ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm w) :=
    funext (inverseCartierOne_eq_positive k p n)
  rw [he]
  exact hb

/-- The specified actual native relative one-form inverse Cartier isomorphism. -/
def inverseCartierOneEquiv : KaehlerDifferential k T ≃ₗ[T] (K).homology 1 :=
  LinearEquiv.ofBijective (inverseCartierOne k p n) (inverseCartierOne_bijective k p n)

end EnvelopeProperty.Cartier.RelativePolynomialCartier
