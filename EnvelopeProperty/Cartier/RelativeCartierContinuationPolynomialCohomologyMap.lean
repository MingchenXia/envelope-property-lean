import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyPresentation
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The degree-one inverse Cartier map over the relative Frobenius twist of a polynomial ring

Let `P = k[X₁, …, Xₙ]` over a field `k` of characteristic `p`, and `T` the relative Frobenius twist
of `k → P`. The inverse Cartier map in degree one goes from the Kähler differentials of `T` over
`k` to the first cohomology of the relative de Rham complex of `P`, and sends `dYᵢ` to the class of
`Xᵢ^(p-1) dXᵢ`. The coefficients in `k` act without change; `k` need not be perfect.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialCartier
open CategoryTheory Limits MvPolynomial
open scoped Classical
universe u
variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
local notation "P" => MvPolynomial (Fin n) k
local notation "T" => RelativeFrobenius.twist (algebraMap k P) p

/-- The `k`-algebra structure of the twist, from its coefficient map. -/
instance twistCoefficientAlgebra : Algebra k T :=
  (RelativeFrobenius.coefficientMap (algebraMap k P) p).hom.toAlgebra

/-- The coordinates `Yᵢ` of the twist: the images of the variables `Xᵢ`. -/
def twistCoordinate (i : Fin n) : T :=
  RelativePolynomialPresentation.polynomialPresentation (R := k) p (X i)

/-- Evaluation at the coordinates `Yᵢ` is the polynomial presentation of the twist. -/
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

/-- The coordinates `Yᵢ` of the twist are étale, the presentation being bijective. -/
theorem twistChart_etale : (aeval (R := k) (twistCoordinate k p n)).toRingHom.Etale := by
  rw [twistChart_eq]
  exact RingHom.Etale.of_bijective
    ⟨RelativePolynomialPresentation.polynomialPresentation_injective p,
      RelativePolynomialPresentation.polynomialPresentation_surjective p⟩

/-- The basis `(dYᵢ)` of the Kähler differentials of the twist. -/
def twistBasis : Module.Basis (Fin n) T (KaehlerDifferential k T) :=
  Char0.etaleDifferentialBasis (twistCoordinate k p n) (twistChart_etale k p n)

/-- The basis vectors of `twistBasis` are the differentials `dYᵢ`. -/
theorem twistBasis_apply (i : Fin n) :
    twistBasis k p n i = KaehlerDifferential.D k T (twistCoordinate k p n i) :=
  Char0.etaleDifferentialBasis_apply _ _ _

/-- The variables of `P` are étale coordinates (the evaluation map is the identity). -/
theorem polynomialEtale : (aeval (R := k) (X : Fin n → P)).toRingHom.Etale := by
  rw [MvPolynomial.aeval_X_left]
  exact RingHom.Etale.of_bijective Function.bijective_id

local notation "K" => RelativeEtaleDeRham.complex (X : Fin n → P) (polynomialEtale k n) p

/-- The short complex of the relative de Rham complex in degrees `0, 1, 2`, over `T`. -/
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

/-- The first cohomology of the relative de Rham complex is the homology of
`oneShortComplex`. -/
def oneHomologyIso : (K).homology 1 ≅ (oneShortComplex k p n).homology :=
  (K).homologyIsoSc' 0 1 2 (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1) ≪≫
    ShortComplex.homologyMapIso (oneNativeRowIso k p n)

/-- The quotient of cycles by boundaries is the first cohomology of the relative complex. -/
def oneQuotientIso : ModuleCat.of T
    (LinearMap.ker (oneShortComplex k p n).g.hom ⧸
      LinearMap.range (oneShortComplex k p n).moduleCatToCycles) ≅ (K).homology 1 :=
  (oneShortComplex k p n).moduleCatHomologyIso.symm ≪≫ (oneHomologyIso k p n).symm

/-- The `T`-linear class map from degree-one cycles to the first cohomology. -/
def oneCycleClass : LinearMap.ker (oneShortComplex k p n).g.hom →ₗ[T] (K).homology 1 :=
  (oneQuotientIso k p n).hom.hom.comp
    (LinearMap.range (oneShortComplex k p n).moduleCatToCycles).mkQ

/-- The closed form `Xᵢ^(p-1) dXᵢ`, as a degree-one cycle. -/
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

/-- The underlying form of `oneCoordinateCycle i` is `Xᵢ^(p-1) dXᵢ`. -/
theorem oneCoordinateCycle_val (i : Fin n) :
    (oneCoordinateCycle k p n i).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 1 from
        (X i : P)^(p-1) • (exteriorPower.oneEquiv P (KaehlerDifferential k P)).symm
          (KaehlerDifferential.D k P (X i))) := rfl

/-- The `T`-linear map to degree-one cycles sending `dYᵢ` to `Xᵢ^(p-1) dXᵢ`, defined on the
basis `(dYᵢ)`. -/
def oneRepresentative : KaehlerDifferential k T →ₗ[T]
    LinearMap.ker (oneShortComplex k p n).g.hom :=
  (twistBasis k p n).constr T (oneCoordinateCycle k p n)

/-- `oneRepresentative` sends `dYᵢ` to `Xᵢ^(p-1) dXᵢ`. -/
theorem oneRepresentative_D (i : Fin n) :
    oneRepresentative k p n (KaehlerDifferential.D k T (twistCoordinate k p n i)) =
      oneCoordinateCycle k p n i := by
  rw [← twistBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

/-- The inverse Cartier map in degree one, to the first cohomology of the relative complex. -/
def inverseCartierOne : KaehlerDifferential k T →ₗ[T] (K).homology 1 :=
  (oneCycleClass k p n).comp (oneRepresentative k p n)

/-- The inverse Cartier map sends `dYᵢ` to the class of `Xᵢ^(p-1) dXᵢ`. -/
theorem inverseCartierOne_D (i : Fin n) :
    inverseCartierOne k p n (KaehlerDifferential.D k T (twistCoordinate k p n i)) =
      oneCycleClass k p n (oneCoordinateCycle k p n i) := by
  change oneCycleClass k p n
    (oneRepresentative k p n (KaehlerDifferential.D k T (twistCoordinate k p n i))) = _
  rw [oneRepresentative_D]

/-- `oneRepresentative (a • dYᵢ) = a • Xᵢ^(p-1) dXᵢ` for `a ∈ k`: the coefficient is neither
raised to the `p`-th power nor replaced by a `p`-th root, so `k` need not be perfect. -/
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
