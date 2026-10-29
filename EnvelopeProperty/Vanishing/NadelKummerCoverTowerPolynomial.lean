import EnvelopeProperty.Vanishing.NadelKummerCoverTowerCore
import EnvelopeProperty.Vanishing.NadelKummerCover

/-! # The actual independent-root tower and the original coordinate-power algebra

The root tower, the maps in both directions and both inverse identities
are constructed from the original polynomial coordinates and positive
exponents. The desired algebra isomorphism is never an input.
-/

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerCover

open NadelFiniteDualityTower

variable (R : Type u) [CommRing R] {n : ℕ} (d : Fin n → ℕ)

/-- Extend the actual finite coordinate root degrees minus one to the
native natural-number-indexed tower. Values after n are unused. -/
def coordinateTowerDegree (i : ℕ) : ℕ := if hi : i < n then d ⟨i, hi⟩ else 0

/-- The actual original polynomial coordinate as the tower coefficient.
Values after the final coordinate are unused. -/
def coordinateTowerCoefficient (i : ℕ) : MvPolynomial (Fin n) R :=
  if hi : i < n then MvPolynomial.X ⟨i, hi⟩ else 0

/-- The exact original finite tower extracting roots of every original
coordinate, with positive exponent d j + 1. -/
abbrev coordinateTowerRing : Type u :=
  independentRootRing (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) n

/-- The same original coefficient homomorphism into this literal tower. -/
abbrev coordinateTowerStructure : MvPolynomial (Fin n) R →+* coordinateTowerRing R d :=
  independentRootStructure (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) n

/-- Each original adjoined coordinate root carried to the actual final stage. -/
def coordinateTowerRoot (j : Fin n) : coordinateTowerRing R d :=
  Tower.rootInStage (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n))
    (Nat.succ_le_of_lt j.isLt)

/-- Its actual original coordinate power relation in the final tower. -/
theorem coordinateTowerRoot_pow (j : Fin n) :
    coordinateTowerRoot R d j ^ (d j + 1) =
      coordinateTowerStructure R d (MvPolynomial.X j) := by
  simpa only [coordinateTowerRoot, coordinateTowerDegree, coordinateTowerCoefficient,
    dif_pos j.isLt] using
    Tower.rootInStage_pow (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n))
      (Nat.succ_le_of_lt j.isLt)

private theorem coordinateTower_actual_roots (i : ℕ) :
    coordinateTowerCoefficient R (n := n) i ^ (coordinateTowerDegree d i + 1) =
      coordinatePowerHom R (fun j => d j + 1) (coordinateTowerCoefficient R (n := n) i) := by
  by_cases hi : i < n
  · simp only [coordinateTowerCoefficient, coordinateTowerDegree, dif_pos hi,
      coordinatePowerHom_X]
  · simp only [coordinateTowerCoefficient, coordinateTowerDegree, dif_neg hi,
      zero_add, pow_one, map_zero]

/-- The actual universal tower evaluation to the original target polynomial
ring sends every new root to its coordinate and every old coordinate to
its original positive power. -/
def coordinateTowerToPolynomial : coordinateTowerRing R d →+* MvPolynomial (Fin n) R :=
  Tower.evaluation (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n))
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom
    (coordinateTowerCoefficient R (n := n)) (coordinateTower_actual_roots R d) n

/-- Its WHOLE coefficient composite is the same original power homomorphism. -/
theorem coordinateTowerToPolynomial_structure :
    (coordinateTowerToPolynomial R d).comp (coordinateTowerStructure R d) =
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom :=
  Tower.evaluation_structure _ _ _ _ _ _

/-- Each actual original root in the final stage maps to the original
polynomial coordinate, not merely an abstract isomorphic generator. -/
theorem coordinateTowerToPolynomial_root (j : Fin n) :
    coordinateTowerToPolynomial R d (coordinateTowerRoot R d j) = MvPolynomial.X j := by
  simpa only [coordinateTowerToPolynomial, coordinateTowerRoot, coordinateTowerCoefficient,
    dif_pos j.isLt] using
    Tower.evaluation_rootInStage (coordinateTowerDegree d)
      (coordinateTowerCoefficient R (n := n))
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom
      (coordinateTowerCoefficient R (n := n)) (coordinateTower_actual_roots R d)
      (Nat.succ_le_of_lt j.isLt)

/-- The genuine reverse polynomial homomorphism sends each original
coordinate to the actual corresponding adjoined root in the final stage. -/
def polynomialToCoordinateTower : MvPolynomial (Fin n) R →+* coordinateTowerRing R d :=
  MvPolynomial.eval₂Hom ((coordinateTowerStructure R d).comp MvPolynomial.C)
    (coordinateTowerRoot R d)

@[simp] theorem polynomialToCoordinateTower_X (j : Fin n) :
    polynomialToCoordinateTower R d (MvPolynomial.X j) = coordinateTowerRoot R d j :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[simp] theorem polynomialToCoordinateTower_C (r : R) :
    polynomialToCoordinateTower R d (MvPolynomial.C r) =
      coordinateTowerStructure R d (MvPolynomial.C r) :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- The original coordinate-root equations identify the entire composite
on the SAME original coefficient polynomial algebra. -/
theorem polynomialToCoordinateTower_structure :
    (polynomialToCoordinateTower R d).comp
        (coordinatePowerHom R (fun j => d j + 1)).toRingHom =
      coordinateTowerStructure R d := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change polynomialToCoordinateTower R d
      (coordinatePowerHom R (fun j => d j + 1) (MvPolynomial.C r)) = _
    rw [coordinatePowerHom_C, polynomialToCoordinateTower_C]
  · intro j
    change polynomialToCoordinateTower R d
      (coordinatePowerHom R (fun j => d j + 1) (MvPolynomial.X j)) = _
    rw [coordinatePowerHom_X, map_pow, polynomialToCoordinateTower_X, coordinateTowerRoot_pow]

/-- The whole original polynomial ring is fixed by the forward-reverse
composite, by actual coefficient and coordinate identities. -/
theorem coordinateTowerToPolynomial_comp :
    (coordinateTowerToPolynomial R d).comp (polynomialToCoordinateTower R d) =
      RingHom.id (MvPolynomial (Fin n) R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polynomialToCoordinateTower_C, RingHom.id_apply]
    have h := congrArg (fun f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R =>
      f (MvPolynomial.C r)) (coordinateTowerToPolynomial_structure R d)
    exact h.trans (coordinatePowerHom_C R _ r)
  · intro j
    simp only [RingHom.comp_apply, polynomialToCoordinateTower_X,
      coordinateTowerToPolynomial_root, RingHom.id_apply]

/-- The reverse-after-evaluation composite on EVERY actual earlier
stage is the genuine transition to the final original tower stage. -/
theorem polynomialToCoordinateTower_evaluation (k : ℕ) (hk : k ≤ n) :
    (polynomialToCoordinateTower R d).comp
        (Tower.evaluation (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n))
          (coordinatePowerHom R (fun j => d j + 1)).toRingHom
          (coordinateTowerCoefficient R (n := n)) (coordinateTower_actual_roots R d) k) =
      Tower.transition (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) hk := by
  induction k with
  | zero =>
      change (polynomialToCoordinateTower R d).comp
        (coordinatePowerHom R (fun j => d j + 1)).toRingHom = _
      rw [polynomialToCoordinateTower_structure]
      exact (Tower.transition_structure (coordinateTowerDegree d)
        (coordinateTowerCoefficient R (n := n)) hk).symm
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl k)) hk
      apply AdjoinRoot.ringHom_ext
      · change ((polynomialToCoordinateTower R d).comp
          (Tower.evaluation (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n))
            (coordinatePowerHom R (fun j => d j + 1)).toRingHom
            (coordinateTowerCoefficient R (n := n)) (coordinateTower_actual_roots R d) (k + 1))).comp
          (independentRootStep (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n)) k) = _
        rw [RingHom.comp_assoc, Tower.evaluation_step, ih hk']
        exact (Tower.transition_comp_step (coordinateTowerDegree d)
          (coordinateTowerCoefficient R (n := n)) hk).symm
      · change polynomialToCoordinateTower R d
          (Tower.evaluation (coordinateTowerDegree d) (coordinateTowerCoefficient R (n := n))
            (coordinatePowerHom R (fun j => d j + 1)).toRingHom
            (coordinateTowerCoefficient R (n := n)) (coordinateTower_actual_roots R d) (k + 1)
              (CyclicSectionAlgebra.root (coordinateTowerDegree d k + 1)
                (independentRootStructure (coordinateTowerDegree d)
                  (coordinateTowerCoefficient R (n := n)) k (coordinateTowerCoefficient R k)))) = _
        rw [Tower.evaluation_root]
        have hkn : k < n := Nat.lt_of_succ_le hk
        have hcoord : coordinateTowerCoefficient R (n := n) k = MvPolynomial.X ⟨k, hkn⟩ :=
          dif_pos hkn
        exact (congrArg (polynomialToCoordinateTower R d) hcoord).trans
          (polynomialToCoordinateTower_X R d ⟨k, hkn⟩)

/-- The WHOLE actual original tower is fixed by the reverse-forward
composite, using its actual successive quotient generators. -/
theorem polynomialToCoordinateTower_comp :
    (polynomialToCoordinateTower R d).comp (coordinateTowerToPolynomial R d) =
      RingHom.id (coordinateTowerRing R d) := by
  exact (polynomialToCoordinateTower_evaluation R d n (Nat.le_refl n)).trans
    (Tower.transition_self _ _ n)

/-- The genuine original independent-root tower is isomorphic to the
target polynomial ring by the actual coordinate maps in both directions. -/
def coordinateTowerEquiv : coordinateTowerRing R d ≃+* MvPolynomial (Fin n) R :=
  RingEquiv.ofRingHom (coordinateTowerToPolynomial R d) (polynomialToCoordinateTower R d)
    (coordinateTowerToPolynomial_comp R d) (polynomialToCoordinateTower_comp R d)

/-- This is an actual algebra comparison for the ORIGINAL power-map
algebra structure, rather than the identity algebra on the same type. -/
def coordinateTowerAlgEquiv :
    let _ : Algebra (MvPolynomial (Fin n) R) (coordinateTowerRing R d) :=
      (coordinateTowerStructure R d).toAlgebra
    let _ : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
      (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
    coordinateTowerRing R d ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) R := by
  let : Algebra (MvPolynomial (Fin n) R) (coordinateTowerRing R d) :=
    (coordinateTowerStructure R d).toAlgebra
  let : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
    (coordinatePowerHom R (fun j => d j + 1)).toRingHom.toAlgebra
  exact {
    toRingEquiv := coordinateTowerEquiv R d
    commutes' := fun z => congrArg
      (fun f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R => f z)
      (coordinateTowerToPolynomial_structure R d) }

end EnvelopeProperty.Vanishing.NadelKummerCover
