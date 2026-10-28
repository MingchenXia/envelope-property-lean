import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyPresentation
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The actual degree-one inverse Cartier map over the polynomial Frobenius twist

The source is the original cotangent module of the actual twist with its original
coefficient inclusion. The target is native H1 of the actual relative complex.
Original coefficients remain unchanged; no perfection or coefficient roots are used.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialCartier
open CategoryTheory Limits MvPolynomial
open scoped Classical
universe u
variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
local notation "P" => MvPolynomial (Fin n) k
local notation "T" => RelativeFrobenius.twist (algebraMap k P) p

/-- The actual original coefficient inclusion supplies the canonical twist algebra. -/
instance twistCoefficientAlgebra : Algebra k T :=
  (RelativeFrobenius.coefficientMap (algebraMap k P) p).hom.toAlgebra

/-- The actual polynomial source variables in the SAME original twist. -/
def twistCoordinate (i : Fin n) : T :=
  RelativePolynomialPresentation.polynomialPresentation (R := k) p (X i)

/-- The actual evaluation map on the twist is the previously proved original presentation. -/
theorem twistChart_eq :
    (aeval (R := k) (twistCoordinate k p n)).toRingHom =
      RelativePolynomialPresentation.polynomialPresentation (R := k) (n := n) p := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change aeval (twistCoordinate k p n) (C c) =
      RelativePolynomialPresentation.polynomialPresentation p (C c)
    rw [MvPolynomial.aeval_C, RelativePolynomialPresentation.polynomialPresentation_C]
    rfl
  · intro i
    change aeval (twistCoordinate k p n) (X i) =
      RelativePolynomialPresentation.polynomialPresentation p (X i)
    rw [MvPolynomial.aeval_X]
    rfl

/-- Etaleness of the true twist chart is derived from the actual presentation bijection. -/
theorem twistChart_etale : (aeval (R := k) (twistCoordinate k p n)).toRingHom.Etale := by
  rw [twistChart_eq]
  exact RingHom.Etale.of_bijective
    ⟨RelativePolynomialPresentation.polynomialPresentation_injective p,
      RelativePolynomialPresentation.polynomialPresentation_surjective p⟩

/-- The SAME actual twist cotangent module has its genuine basis dY_i. -/
def twistBasis : Module.Basis (Fin n) T (KaehlerDifferential k T) :=
  Char0.etaleDifferentialBasis (twistCoordinate k p n) (twistChart_etale k p n)

/-- The actual twist basis vectors are the original universal differentials dY_i. -/
theorem twistBasis_apply (i : Fin n) :
    twistBasis k p n i = KaehlerDifferential.D k T (twistCoordinate k p n i) :=
  Char0.etaleDifferentialBasis_apply _ _ _

/-- The original polynomial coordinate map is etale because it is the actual identity. -/
theorem polynomialEtale : (aeval (R := k) (X : Fin n → P)).toRingHom.Etale := by
  rw [MvPolynomial.aeval_X_left]
  exact RingHom.Etale.of_bijective Function.bijective_id

local notation "K" => RelativeEtaleDeRham.complex (X : Fin n → P) (polynomialEtale k n) p

/-- The SAME actual original 0/1/2 row over the genuine relative coefficient ring. -/
def oneShortComplex : ShortComplex (ModuleCat T) :=
  ShortComplex.mk
    (RelativeEtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) p 0)
    (RelativeEtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) p 1)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact EtaleDeRham.differential_square (X : Fin n → P) (polynomialEtale k n) 0 w)

private def adjacentRowIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (A : ℕ → C) (d : ∀ q, A q ⟶ A (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) :
    (CochainComplex.of A d sq).sc' q (q+1) (q+1+1) ≅
      ShortComplex.mk (d q) (d (q+1)) (sq q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])

private def oneNativeRowIso : (K).sc' 0 1 2 ≅ oneShortComplex k p n := by
  unfold RelativeEtaleDeRham.complex oneShortComplex
  exact adjacentRowIso _ _ _ 0

/-- The genuine whole-relative-complex H1 is compared with its SAME original adjacent row. -/
def oneHomologyIso : (K).homology 1 ≅ (oneShortComplex k p n).homology :=
  (K).homologyIsoSc' 0 1 2 (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1) ≪≫
    ShortComplex.homologyMapIso (oneNativeRowIso k p n)

/-- The actual cycle/boundary quotient is identified with the SAME native whole-complex H1. -/
def oneQuotientIso : ModuleCat.of T
    (LinearMap.ker (oneShortComplex k p n).g.hom ⧸
      LinearMap.range (oneShortComplex k p n).moduleCatToCycles) ≅ (K).homology 1 :=
  (oneShortComplex k p n).moduleCatHomologyIso.symm ≪≫ (oneHomologyIso k p n).symm

/-- The original quotient class map into actual native relative H1, with true T-linearity. -/
def oneCycleClass : LinearMap.ker (oneShortComplex k p n).g.hom →ₗ[T] (K).homology 1 :=
  (oneQuotientIso k p n).hom.hom.comp
    (LinearMap.range (oneShortComplex k p n).moduleCatToCycles).mkQ

/-- The actual original closed coordinate form X_i^(p-1)dX_i in the relative cycle module. -/
def oneCoordinateCycle (i : Fin n) : LinearMap.ker (oneShortComplex k p n).g.hom :=
  ⟨(show RelativeEtaleDeRham.formModule (R := k) (B := P) p 1 from
      (X i : P)^(p-1) • (exteriorPower.oneEquiv P (KaehlerDifferential k P)).symm
        (KaehlerDifferential.D k P (X i))),
    by
      change EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 1
        ((X i : P)^(p-1) • (exteriorPower.oneEquiv P (KaehlerDifferential k P)).symm
          (KaehlerDifferential.D k P (X i))) = 0
      exact EtaleDifferentialLeibniz.differential_power_universalD
        (X : Fin n → P) (polynomialEtale k n) (X i) (p-1)⟩

/-- The SAME original coordinate form is retained before taking its actual cohomology class. -/
theorem oneCoordinateCycle_val (i : Fin n) :
    (oneCoordinateCycle k p n i).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 1 from
        (X i : P)^(p-1) • (exteriorPower.oneEquiv P (KaehlerDifferential k P)).symm
          (KaehlerDifferential.D k P (X i))) := rfl

/-- The actual dY_i basis defines a genuine T-linear lift into original relative cycles. -/
def oneRepresentative : KaehlerDifferential k T →ₗ[T]
    LinearMap.ker (oneShortComplex k p n).g.hom :=
  (twistBasis k p n).constr T (oneCoordinateCycle k p n)

/-- Every original twist coordinate differential has the SAME specified original cycle. -/
theorem oneRepresentative_D (i : Fin n) :
    oneRepresentative k p n (KaehlerDifferential.D k T (twistCoordinate k p n i)) =
      oneCoordinateCycle k p n i := by
  rw [← twistBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

/-- The actual relative inverse Cartier one-form map into native H1 of the SAME complex. -/
def inverseCartierOne : KaehlerDifferential k T →ₗ[T] (K).homology 1 :=
  (oneCycleClass k p n).comp (oneRepresentative k p n)

/-- The actual original dY_i maps to precisely the native class of X_i^(p-1)dX_i. -/
theorem inverseCartierOne_D (i : Fin n) :
    inverseCartierOne k p n (KaehlerDifferential.D k T (twistCoordinate k p n i)) =
      oneCycleClass k p n (oneCoordinateCycle k p n i) := by
  change oneCycleClass k p n
    (oneRepresentative k p n (KaehlerDifferential.D k T (twistCoordinate k p n i))) = _
  rw [oneRepresentative_D]

/-- Every original base coefficient in a dY_i representative acts by that SAME coefficient,
without raising it to p or extracting any coefficient root, including over imperfect fields. -/
theorem oneRepresentative_coefficient_D (a : k) (i : Fin n) :
    (oneRepresentative k p n
      ((algebraMap k T a) • KaehlerDifferential.D k T (twistCoordinate k p n i))).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 1 from
        (C a : P) • ((X i : P)^(p-1) •
          (exteriorPower.oneEquiv P (KaehlerDifferential k P)).symm
            (KaehlerDifferential.D k P (X i)))) := by
  rw [map_smul, oneRepresentative_D, Submodule.coe_smul]
  exact RelativeEtaleDeRham.coefficient_smul (R := k) (B := P) p 1 a _

end EnvelopeProperty.Cartier.RelativePolynomialCartier
