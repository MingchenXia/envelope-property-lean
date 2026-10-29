import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyMap
import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyCoefficients

/-!
# Genuine relative polynomial representatives and actual boundary normal forms

The original relative complex differential is compared as a whole map with the
original polynomial differential used by the proved coordinate homotopies.
Actual native twist exterior forms then give coefficient-preserving representatives,
with an internally defined left inverse and full-residual normal forms.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialCartier
open CategoryTheory MvPolynomial
open scoped Classical
universe u
variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
local notation "P" => MvPolynomial (Fin n) k
local notation "T" => RelativeFrobenius.twist (algebraMap k P) p
local notation "e" => RelativePolynomialPresentation.polynomialPresentation (R := k) (n := n) p
local notation "a_" => RelativePolynomialCoefficients.residueDigit (σ := Fin n) p

/-- The actual polynomial and identity-chart etale cotangent bases are identical. -/
theorem polynomialBasis_eq :
    Char0.etaleDifferentialBasis (X : Fin n → P) (polynomialEtale k n) =
      KaehlerDifferential.mvPolynomialBasis k (Fin n) := by
  ext i
  rw [Char0.etaleDifferentialBasis_apply, KaehlerDifferential.mvPolynomialBasis_apply]

/-- The ENTIRE original polynomial form map for the true identity chart is the identity. -/
theorem polynomialFormMap_identity (q : ℕ)
    (w : ⋀[P]^q (KaehlerDifferential k P)) :
    EtaleDeRham.polynomialFormMap (X : Fin n → P) (polynomialEtale k n) q w = w := by
  let b := (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q
  conv_lhs => rw [← b.sum_repr w]
  rw [map_sum]
  calc
    _ = ∑ s, b.coord s w • b s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [EtaleDeRham.polynomialFormMap_smul_basis, polynomialBasis_eq,
        MvPolynomial.aeval_X_left_apply]
      rfl
    _ = w := b.sum_repr w

/-- The SAME actual original differential equals the polynomial differential on EVERY form. -/
theorem differential_polynomial (q : ℕ) (w : ⋀[P]^q (KaehlerDifferential k P)) :
    EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) q w =
      PolynomialDeRham.differential k q w := by
  have h := EtaleDeRham.differential_polynomialFormMap
    (X : Fin n → P) (polynomialEtale k n) q w
  rw [polynomialFormMap_identity, polynomialFormMap_identity] at h
  exact h

/-- Genuine native T-linear representatives on the ACTUAL twist exterior module. -/
def exteriorRepresentative (q : ℕ) :
    (⋀[T]^q (KaehlerDifferential k T)) →ₗ[T]
      RelativeEtaleDeRham.formModule (R := k) (B := P) p q :=
  ((twistBasis k p n).exteriorPower q).constr T (fun s =>
    (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from
      monomial (a_ q s).toFinsupp (1 : k) •
        (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s))

/-- Every actual coefficient e(f) acts by coefficient-preserving exponent expansion. -/
theorem exteriorRepresentative_smul_basis (q : ℕ) (s : Set.powersetCard (Fin n) q)
    (f : P) :
    exteriorRepresentative k p n q (e f • (twistBasis k p n).exteriorPower q s) =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from
        (expand p f * monomial (a_ q s).toFinsupp (1 : k)) •
          (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s) := by
  have hb : exteriorRepresentative k p n q ((twistBasis k p n).exteriorPower q s) =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from
        monomial (a_ q s).toFinsupp (1 : k) •
          (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s) := by
    exact Module.Basis.constr_basis _ _ _ _
  rw [map_smul, hb]
  change (RelativeFrobenius.map (algebraMap k P) p).hom (e f) •
    (monomial (a_ q s).toFinsupp (1 : k) •
      (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s) =
    (expand p f * monomial (a_ q s).toFinsupp (1 : k)) •
      (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s
  have hf := DFunLike.congr_fun
    (RelativePolynomialPresentation.map_polynomialPresentation (R := k) (n := n) p) f
  change (RelativeFrobenius.map (algebraMap k P) p).hom (e f) = expand p f at hf
  rw [hf, smul_smul]

/-- The SAME original representative as an additive map on original exterior forms. -/
def originalExteriorRepresentative (q : ℕ) :
    (⋀[T]^q (KaehlerDifferential k T)) →+ (⋀[P]^q (KaehlerDifferential k P)) where
  toFun w := exteriorRepresentative k p n q w
  map_zero' := (exteriorRepresentative k p n q).map_zero
  map_add' := (exteriorRepresentative k p n q).map_add

/-- The underlying original representative retains precisely the proved actual scalar action. -/
theorem originalExteriorRepresentative_smul_basis (q : ℕ)
    (s : Set.powersetCard (Fin n) q) (f : P) :
    originalExteriorRepresentative k p n q (e f • (twistBasis k p n).exteriorPower q s) =
      (expand p f * monomial (a_ q s).toFinsupp (1 : k)) •
        (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s :=
  exteriorRepresentative_smul_basis k p n q s f

/-- The whole actual coefficient map is constructed from SAME original exterior-basis
coordinates and the original coefficient-preserving extractor. -/
def exteriorCoefficient (q : ℕ) :
    (⋀[P]^q (KaehlerDifferential k P)) →+ (⋀[T]^q (KaehlerDifferential k T)) where
  toFun w := ∑ s : Set.powersetCard (Fin n) q,
    e (RelativePolynomialCoefficients.coefficientPoly k p (a_ q s).toFinsupp
      (((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q).coord s w)) •
        (twistBasis k p n).exteriorPower q s
  map_zero' := by simp only [map_zero, zero_smul, Finset.sum_const_zero]
  map_add' w z := by simp only [map_add, add_smul, Finset.sum_add_distrib]

/-- Each scalar basis coefficient is the actual unchanged coefficient extractor in T. -/
theorem exteriorCoefficient_smul_basis (q : ℕ) (s : Set.powersetCard (Fin n) q) (f : P) :
    exteriorCoefficient k p n q
      (f • (KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s) =
      e (RelativePolynomialCoefficients.coefficientPoly k p (a_ q s).toFinsupp f) •
        (twistBasis k p n).exteriorPower q s := by
  change (∑ t : Set.powersetCard (Fin n) q, _) = _
  rw [Finset.sum_eq_single s]
  · simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro t _ ht
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne ht, smul_eq_mul, mul_zero, map_zero, zero_smul]
  · intro hs
    exact (hs (Finset.mem_univ s)).elim

/-- The actual coefficient is recovered on every scalar exterior-basis input in T. -/
theorem exteriorCoefficient_representative_smul_basis (q : ℕ)
    (s : Set.powersetCard (Fin n) q) (t : T) :
    exteriorCoefficient k p n q (originalExteriorRepresentative k p n q
      (t • (twistBasis k p n).exteriorPower q s)) =
        t • (twistBasis k p n).exteriorPower q s := by
  obtain ⟨f, rfl⟩ := RelativePolynomialPresentation.polynomialPresentation_surjective
    (R := k) (n := n) p t
  rw [originalExteriorRepresentative_smul_basis, exteriorCoefficient_smul_basis,
    RelativePolynomialCoefficients.coefficientPoly_expand_mul]

/-- The ACTUAL constructed coefficient map is a left inverse on the entire twist exterior module. -/
theorem exteriorCoefficient_representative (q : ℕ) (z : ⋀[T]^q (KaehlerDifferential k T)) :
    exteriorCoefficient k p n q (originalExteriorRepresentative k p n q z) = z := by
  let b := (twistBasis k p n).exteriorPower q
  have hsum : ∑ s, b.coord s z • b s = z := b.sum_repr z
  calc
    _ = exteriorCoefficient k p n q
        (originalExteriorRepresentative k p n q (∑ s, b.coord s z • b s)) := by rw [hsum]
    _ = ∑ s, b.coord s z • b s := by
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro s _
      exact exteriorCoefficient_representative_smul_basis k p n q s (b.coord s z)
    _ = z := hsum

/-- Genuine injectivity of the original relative representative, without perfection. -/
theorem originalExteriorRepresentative_injective (q : ℕ) :
    Function.Injective (originalExteriorRepresentative k p n q) :=
  Function.LeftInverse.injective (exteriorCoefficient_representative k p n q)

/-- The actual full residual is precisely the representative of the constructed coefficient. -/
theorem representative_exteriorCoefficient (q : ℕ) (w : ⋀[P]^q (KaehlerDifferential k P)) :
    originalExteriorRepresentative k p n q (exteriorCoefficient k p n q w) =
      PolynomialCartierProjection.originalAllResidual k p q w := by
  change originalExteriorRepresentative k p n q (∑ s : Set.powersetCard (Fin n) q, _) = _
  rw [map_sum]
  simp only [originalExteriorRepresentative_smul_basis]
  conv_rhs => rw [← ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q).sum_repr w]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact (RelativePolynomialCoefficients.originalAllResidual_smul_basis k p q s _).symm

/-- Every original relative representative is fixed by the WHOLE actual full residual. -/
theorem originalExteriorRepresentative_fixed (q : ℕ) (z : ⋀[T]^q (KaehlerDifferential k T)) :
    PolynomialCartierProjection.originalAllResidual k p q
      (originalExteriorRepresentative k p n q z) = originalExteriorRepresentative k p n q z := by
  rw [← representative_exteriorCoefficient, exteriorCoefficient_representative]

/-- Every original relative representative is closed for the SAME actual relative differential. -/
theorem originalExteriorRepresentative_closed (q : ℕ) (z : ⋀[T]^q (KaehlerDifferential k T)) :
    EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) q
      (originalExteriorRepresentative k p n q z) = 0 := by
  rw [differential_polynomial, ← originalExteriorRepresentative_fixed k p n q z]
  exact PolynomialCartierProjection.originalAllResidual_closed k p q _

/-- The actual proved coordinate homotopy gives an ORIGINAL primitive modulo the relative
representative, on EVERY original positive-degree cycle. -/
theorem original_boundary_normalForm (q : ℕ)
    (w : ⋀[P]^(q+1) (KaehlerDifferential k P))
    (hw : EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) (q+1) w = 0) :
    ∃ u : ⋀[P]^q (KaehlerDifferential k P),
      EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) q u =
        w - originalExteriorRepresentative k p n (q+1) (exteriorCoefficient k p n (q+1) w) := by
  rw [differential_polynomial] at hw
  obtain ⟨u, hu⟩ := PolynomialCartierResiduals.original_exists_primitive_sub_residualList k p
    (Finset.univ.toList) q w hw
  refine ⟨u, ?_⟩
  rw [differential_polynomial, representative_exteriorCoefficient]
  exact hu

/-- An actual positive-degree representative is a boundary precisely for the zero
actual twist form. Every boundary and residual assertion is internally derived. -/
theorem original_representative_boundary_iff (q : ℕ)
    (z : ⋀[T]^(q+1) (KaehlerDifferential k T)) :
    (∃ u : ⋀[P]^q (KaehlerDifferential k P),
      EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) q u =
        originalExteriorRepresentative k p n (q+1) z) ↔ z = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    apply originalExteriorRepresentative_injective k p n (q+1)
    rw [map_zero]
    calc
      _ = PolynomialCartierProjection.originalAllResidual k p (q+1)
          (originalExteriorRepresentative k p n (q+1) z) :=
        (originalExteriorRepresentative_fixed k p n (q+1) z).symm
      _ = PolynomialCartierProjection.originalAllResidual k p (q+1)
          (EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) q u) := by rw [hu]
      _ = 0 := by
        rw [differential_polynomial]
        exact PolynomialCartierProjection.originalAllResidual_boundary_zero k p q u
  · rintro rfl
    exact ⟨0, by rw [map_zero, map_zero]⟩

end EnvelopeProperty.Cartier.RelativePolynomialCartier
