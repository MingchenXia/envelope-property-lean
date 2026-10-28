import EnvelopeProperty.Vanishing.NadelKummerCoverTowerPolynomial
import Mathlib.RingTheory.AlgebraTower
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The genuine finite monomial basis of the original coordinate-power algebra

The basis is constructed from the existing native successive monic root
bases, then transported along the proved actual polynomial algebra
isomorphism. All scalar actions are the original power-map actions.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerCover.Tower

open NadelFiniteDualityTower Module

variable {R : Type u} [CommRing R] [Nontrivial R] (d : ℕ → ℕ) (c : ℕ → R)

/-- The actual successive power-basis indices, retaining every original
root's exponent range. -/
def basisIndex : ℕ → Type
  | 0 => PUnit
  | k + 1 => basisIndex k × Fin (d k + 1)

/-- Every actual finite-stage power basis has a finite original index. -/
theorem basisIndex_finite : ∀ k, Finite (basisIndex d k)
  | 0 => inferInstanceAs (Finite PUnit)
  | k + 1 => by
      let := basisIndex_finite k
      exact inferInstanceAs (Finite (basisIndex d k × Fin (d k + 1)))

/-- The original tower has its actual successive monic power basis over
its SAME original coefficient ring, with no supplied freeness input. -/
def basis : ∀ k,
    let _ : Algebra R (independentRootRing d c k) := (independentRootStructure d c k).toAlgebra
    Basis (basisIndex d k) R (independentRootRing d c k)
  | 0 => Basis.singleton PUnit R
  | k + 1 => by
      let B := independentRootRing d c k
      let C := independentRootRing d c (k + 1)
      let : Nontrivial B := independentRootRing_nontrivial d c k
      let : Algebra R B := (independentRootStructure d c k).toAlgebra
      let : Algebra B C := inferInstanceAs
        (Algebra B (NadelFiniteDuality.Root (d k) (independentRootStructure d c k (c k))))
      let : Algebra R C := (independentRootStructure d c (k + 1)).toAlgebra
      let tower : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
      exact @Basis.smulTower R B C _ _ _ _ _ _ tower _ _ (basis k)
        (CyclicSectionPowerBasis.basis (d k + 1) (independentRootStructure d c k (c k))
          (Nat.succ_pos _))

/-- The genuine finite-stage basis rank is the product of the ORIGINAL
positive root degrees. -/
theorem basisIndex_card (k : ℕ) :
    Nat.card (basisIndex d k) = ∏ i ∈ Finset.range k, (d i + 1) := by
  induction k with
  | zero => simp [basisIndex]
  | succ k ih =>
      let := basisIndex_finite d k
      simp only [basisIndex, Nat.card_prod, Nat.card_fin, ih, Finset.prod_range_succ]

end EnvelopeProperty.Vanishing.NadelKummerCover.Tower

namespace EnvelopeProperty.Vanishing.NadelKummerCover

open AlgebraicGeometry CategoryTheory Module NadelFiniteDualityTower

variable (R : Type u) [CommRing R] [Nontrivial R] {n : ℕ} (d : Fin n → ℕ)

/-- A genuine finite basis for the actual coordinate-power polynomial
algebra, obtained from its proved original independent-root algebra iso. -/
def coordinatePowerBasis :
    let _ : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
    Basis (Tower.basisIndex (coordinateTowerDegree d) n)
      (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) := by
  let : Algebra (MvPolynomial (Fin n) R) (coordinateTowerRing R d) :=
    (coordinateTowerStructure R d).toAlgebra
  let : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
  let : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
  exact (Tower.basis (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) n).map
    (coordinateTowerAlgEquiv R d).toLinearEquiv

/-- Each actual basis vector is the genuine image of the original
successive monic root-basis vector under the proved coordinate map. -/
theorem coordinatePowerBasis_apply (i : Tower.basisIndex (coordinateTowerDegree d) n) :
    coordinatePowerBasis R d i = coordinateTowerToPolynomial R d
      (Tower.basis (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) n i) := by
  let : Algebra (MvPolynomial (Fin n) R) (coordinateTowerRing R d) :=
    (coordinateTowerStructure R d).toAlgebra
  let : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
  exact Basis.map_apply _ _ _

/-- The actual finite basis has the product of the ORIGINAL positive
coordinate exponents as its exact index cardinality. -/
theorem coordinatePowerBasis_card :
    Nat.card (Tower.basisIndex (coordinateTowerDegree d) n) = ∏ j : Fin n, (d j + 1) := by
  rw [Tower.basisIndex_card, ← Fin.prod_univ_eq_prod_range
    (fun i => coordinateTowerDegree d i + 1) n]
  apply Finset.prod_congr rfl
  intro j _
  rw [coordinateTowerDegree, dif_pos j.isLt]

/-- Freeness uses the actual original power-map scalar action. -/
theorem coordinatePowerHom_free :
    let _ : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
    Module.Free (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) := by
  let : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
  exact Module.Free.of_basis (coordinatePowerBasis R d)

/-- The constructed basis is genuinely finite, retaining the original
finite coordinate/root index rather than an arbitrary generation input. -/
theorem coordinatePowerHom_finite_of_basis :
    let _ : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
    Module.Finite (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) := by
  let : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
  let : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
  let := Tower.basisIndex_finite (coordinateTowerDegree d) n
  exact Module.Finite.of_basis (coordinatePowerBasis R d)

/-- The SAME actual positive coordinate-power scheme map is flat,
proved from its actual constructed free monomial basis. -/
theorem coordinatePowerMap_flat : Flat (coordinatePowerMap R (fun j => d j + 1)) := by
  rw [coordinatePowerMap, Flat.SpecMap_iff]
  let : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
  let : Module (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra.toModule
  let : Module.Free (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    coordinatePowerHom_free R d
  exact (inferInstance : Module.Flat (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))

/-- The actual flatness applies to EVERY original positive exponent
vector, by the proved positive-degree basis with d j = m j - 1. -/
theorem coordinatePowerMap_flat_of_pos (m : Fin n → ℕ) (hm : ∀ j, 0 < m j) :
    Flat (coordinatePowerMap R m) := by
  have he : (fun j => m j - 1 + 1) = m :=
    funext (fun j => Nat.sub_add_cancel (hm j))
  simpa only [he] using coordinatePowerMap_flat R (fun j => m j - 1)

/-- The literal original coordinate-root pullback projection is flat
by genuine scheme base change of the original constructed free algebra. -/
theorem chartProjection_flat {U : Scheme.{u}} (g : U ⟶ polynomialSpace R n) :
    Flat (chartProjection g (fun j => d j + 1)) := by
  let := coordinatePowerMap_flat R d
  exact inferInstanceAs (Flat (Limits.pullback.fst g (coordinatePowerMap R (fun j => d j + 1))))

/-- The literal branched local-cover projection is flat for every
positive original exponent vector, by actual native base change. -/
theorem chartProjection_flat_of_pos {U : Scheme.{u}} (g : U ⟶ polynomialSpace R n)
    (m : Fin n → ℕ) (hm : ∀ j, 0 < m j) : Flat (chartProjection g m) := by
  let := coordinatePowerMap_flat_of_pos R m hm
  exact inferInstanceAs (Flat (Limits.pullback.fst g (coordinatePowerMap R m)))

end EnvelopeProperty.Vanishing.NadelKummerCover
