import EnvelopeProperty.Cartier.RelativeFrobeniusCoefficient
import Mathlib.Algebra.MvPolynomial.Expand

/-!
# The genuine finite polynomial Frobenius twist, independent coefficient universe

The accepted polynomial twist proof is repeated with a separate finite variable universe.
This keeps arbitrary base-ring universes while retaining the SAME native pushout, its
original coefficient inclusion, source inclusion, and actual relative Frobenius map.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialPresentation
open CategoryTheory Limits MvPolynomial
open scoped Classical
universe u
variable {R : Type u} {n : ℕ} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
local notation "P" => MvPolynomial (Fin n) R
local notation "T" => RelativeFrobenius.twist (algebraMap R P) p

/-- The original coefficient inclusion and original source variables give this actual
polynomial map into the SAME native relative Frobenius pushout. -/
def polynomialPresentation : P →+* T :=
  eval₂Hom (RelativeFrobenius.coefficientMap (algebraMap R P) p).hom
    (fun i => (RelativeFrobenius.sourceMap (algebraMap R P) p).hom (X i))

/-- Every original coefficient is retained by the actual presentation. -/
theorem polynomialPresentation_C (c : R) :
    polynomialPresentation (n := n) p (C c) =
      (RelativeFrobenius.coefficientMap (algebraMap R P) p).hom c :=
  eval₂Hom_C _ _ _

/-- Every variable is the SAME original variable under the native source inclusion. -/
theorem polynomialPresentation_X (i : Fin n) :
    polynomialPresentation (R := R) p (X i) =
      (RelativeFrobenius.sourceMap (algebraMap R P) p).hom (X i) :=
  eval₂Hom_X' _ _ _

/-- The whole genuine relative Frobenius after the original presentation is exactly
the coefficient-preserving expansion of exponents, including over imperfect bases. -/
theorem map_polynomialPresentation :
    (RelativeFrobenius.map (algebraMap R P) p).hom.comp (polynomialPresentation p) =
      (expand p (R := R) (σ := Fin n)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change (RelativeFrobenius.map (algebraMap R P) p).hom
      (polynomialPresentation p (C c)) = expand p (C c)
    rw [polynomialPresentation_C, expand_C]
    exact congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of P => h.hom c)
      (RelativeFrobenius.coefficientMap_map (algebraMap R P) p)
  · intro i
    change (RelativeFrobenius.map (algebraMap R P) p).hom
      (polynomialPresentation p (X i)) = expand p (X i)
    rw [polynomialPresentation_X, expand_X]
    exact congrArg (fun h : CommRingCat.of P ⟶ CommRingCat.of P => h.hom (X i))
      (RelativeFrobenius.sourceMap_map (algebraMap R P) p)

/-- Applying Frobenius to polynomial coefficients before the presentation recovers
the entire SAME original source inclusion, by its actual pushout square. -/
theorem polynomialPresentation_sourceMap :
    (polynomialPresentation (R := R) (n := n) p).comp (MvPolynomial.map (frobenius R p)) =
      (RelativeFrobenius.sourceMap (algebraMap R P) p).hom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change polynomialPresentation p (MvPolynomial.map (frobenius R p) (C c)) =
      (RelativeFrobenius.sourceMap (algebraMap R P) p).hom (C c)
    rw [MvPolynomial.map_C, polynomialPresentation_C]
    exact congrArg (fun h : CommRingCat.of R ⟶ T => h.hom c)
      (pushout.condition (f := CommRingCat.ofHom (frobenius R p))
        (g := CommRingCat.ofHom (algebraMap R P)))
  · intro i
    change polynomialPresentation p (MvPolynomial.map (frobenius R p) (X i)) =
      (RelativeFrobenius.sourceMap (algebraMap R P) p).hom (X i)
    rw [MvPolynomial.map_X, polynomialPresentation_X]

/-- Injectivity of exponent expansion proves injectivity of the actual presentation. -/
theorem polynomialPresentation_injective :
    Function.Injective (polynomialPresentation (R := R) (n := n) p) := by
  intro f g h
  apply MvPolynomial.expand_injective hp.out.pos
  have h' := congrArg (RelativeFrobenius.map (algebraMap R P) p).hom h
  change ((RelativeFrobenius.map (algebraMap R P) p).hom.comp
    (polynomialPresentation p)) f =
      ((RelativeFrobenius.map (algebraMap R P) p).hom.comp (polynomialPresentation p)) g at h'
  rw [map_polynomialPresentation] at h'
  exact h'

/-- Both entire native pushout inclusions lie in the original presentation range;
actual pushout ring generation therefore proves surjectivity. -/
theorem polynomialPresentation_surjective :
    Function.Surjective (polynomialPresentation (R := R) (n := n) p) := by
  have ht : Subring.closure
      (Set.range (RelativeFrobenius.coefficientMap (algebraMap R P) p) ∪
        Set.range (RelativeFrobenius.sourceMap (algebraMap R P) p)) = ⊤ :=
    CommRingCat.closure_range_union_range_eq_top_of_isPushout
      (IsPushout.of_hasPushout (CommRingCat.ofHom (frobenius R p))
        (CommRingCat.ofHom (algebraMap R P)))
  have hl : Subring.closure
      (Set.range (RelativeFrobenius.coefficientMap (algebraMap R P) p) ∪
        Set.range (RelativeFrobenius.sourceMap (algebraMap R P) p)) ≤
      (polynomialPresentation (R := R) (n := n) p).range := by
    apply Subring.closure_le.mpr
    rintro z (⟨c, rfl⟩ | ⟨f, rfl⟩)
    · exact ⟨C c, polynomialPresentation_C p c⟩
    · exact ⟨MvPolynomial.map (frobenius R p) f,
        DFunLike.congr_fun (polynomialPresentation_sourceMap (n := n) p) f⟩
  intro z
  apply hl
  rw [ht]
  trivial

/-- The genuine native polynomial Frobenius pushout has this actual polynomial ring
equivalence, retaining its specified original coefficient-and-variable map. -/
def polynomialTwistEquiv : P ≃+* T :=
  RingEquiv.ofBijective (polynomialPresentation p)
    ⟨polynomialPresentation_injective p, polynomialPresentation_surjective p⟩

end EnvelopeProperty.Cartier.RelativePolynomialPresentation
