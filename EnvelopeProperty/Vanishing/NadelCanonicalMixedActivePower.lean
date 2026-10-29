import EnvelopeProperty.Vanishing.NadelCanonicalMixedActivePowerFormulas

/-! # The actual whole active quotient is the literal coordinate-power base change -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open NadelMixedKummer NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange NadelKummerCover
attribute [local instance] Classical.propDecidable
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R)
local notation "d" => coordinateExponent N I σ
local notation "x" => originalCoordinates a
local notation "A₀" => ActiveRing N I (pureCoefficient x I σ)
local notation "C₀" => powerBaseChangeRing k d R a.toRingHom

/-- Both actual polynomial inclusions agree on the SAME original small coefficient ring. -/
theorem powerRight_constant (c : k) :
    powerBaseChangeRight k d R a.toRingHom (MvPolynomial.C c) =
      powerBaseChangeLeft k d R a.toRingHom (algebraMap k R c) := by
  have h := congrArg (fun z : MvPolynomial (Fin n) k →+* C₀ => z (MvPolynomial.C c))
    (powerBaseChange_square k d R a.toRingHom)
  have hC : powerMap k d (MvPolynomial.C c) = MvPolynomial.C c :=
    coordinatePowerHom_C k (fun j => d j + 1) c
  have ha : a (MvPolynomial.C c) = algebraMap k R c := a.commutes c
  change powerBaseChangeLeft k d R a.toRingHom (a (MvPolynomial.C c)) =
    powerBaseChangeRight k d R a.toRingHom (powerMap k d (MvPolynomial.C c)) at h
  rw [ha, hC] at h
  exact h.symm

/-- The original active quotient is recovered on the WHOLE ring, not only its fraction field or points. -/
theorem powerToActive_comp_activeToPower :
    (powerToActive N I σ hN a).comp (activeToPower N I σ hN a) = RingHom.id A₀ := by
  apply hom_ext
  · rw [RingHom.comp_assoc, activeToPower_structure, powerToActive_left]
    rfl
  · intro i
    change powerToActive N I σ hN a (activeToPower N I σ hN a _) = _
    rw [activeToPower_root]
    by_cases hh : i ∈ I
    · rw [dif_pos hh]
      have hr := congrArg (fun f : MvPolynomial (Fin n) k →+* A₀ => f (MvPolynomial.X (σ ⟨i, hh⟩)))
        (powerToActive_right N I σ hN a)
      change powerToActive N I σ hN a (powerBaseChangeRight k d R a.toRingHom _) = _ at hr
      rw [hr]
      have he : (coordinateEvaluation N I σ a).toRingHom (MvPolynomial.X (σ ⟨i, hh⟩)) =
          coordinateRoot N I σ x (σ ⟨i, hh⟩) := by
        change coordinateEvaluation N I σ a (MvPolynomial.X (σ ⟨i, hh⟩)) = _
        simp only [coordinateEvaluation, MvPolynomial.aeval_X]
      exact he.trans (coordinateRoot_active N I σ x ⟨i, hh⟩)
    · rw [dif_neg hh, map_one, activeRoot_absent N I (pureCoefficient x I σ)
        (fun j hj => by simp only [pureCoefficient, dif_neg hj]) i hh]
      rfl

/-- The whole original target polynomial and coefficient algebra are recovered by the actual reverse composite. -/
theorem activeToPower_comp_powerToActive :
    (activeToPower N I σ hN a).comp (powerToActive N I σ hN a) = RingHom.id C₀ := by
  let P := MvPolynomial (Fin n) k
  let : Algebra P R := a.toRingHom.toAlgebra
  let : Algebra P P := (powerMap k d).toAlgebra
  let : Module P P := (powerMap k d).toAlgebra.toModule
  apply Algebra.TensorProduct.ringHom_ext
  · change ((activeToPower N I σ hN a).comp (powerToActive N I σ hN a)).comp
      (powerBaseChangeLeft k d R a.toRingHom) = _
    rw [RingHom.comp_assoc, powerToActive_left, activeToPower_structure]
    rfl
  · change ((activeToPower N I σ hN a).comp (powerToActive N I σ hN a)).comp
      (powerBaseChangeRight k d R a.toRingHom) = _
    rw [RingHom.comp_assoc, powerToActive_right]
    apply MvPolynomial.ringHom_ext
    · intro c
      change activeToPower N I σ hN a (coordinateEvaluation N I σ a (MvPolynomial.C c)) =
        powerBaseChangeRight k d R a.toRingHom (MvPolynomial.C c)
      have hc : coordinateEvaluation N I σ a (MvPolynomial.C c) = algebraMap k A₀ c :=
        (coordinateEvaluation N I σ a).commutes c
      rw [hc, IsScalarTower.algebraMap_apply k R A₀]
      have hs := congrArg (fun f : R →+* C₀ => f (algebraMap k R c))
        (activeToPower_structure N I σ hN a)
      exact hs.trans (powerRight_constant N I σ a c).symm
    · intro j
      change activeToPower N I σ hN a (coordinateEvaluation N I σ a (MvPolynomial.X j)) =
        powerBaseChangeRight k d R a.toRingHom (MvPolynomial.X j)
      have he : coordinateEvaluation N I σ a (MvPolynomial.X j) = coordinateRoot N I σ x j := by
        simp only [coordinateEvaluation, MvPolynomial.aeval_X]
      rw [he]
      by_cases hj : ∃ i : I, σ i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [coordinateRoot_active, activeToPower_root, dif_pos i.2]
      · rw [coordinateRoot_absent N I σ x j hj]
        have hs := congrArg (fun f : R →+* C₀ => f (x j)) (activeToPower_structure N I σ hN a)
        change activeToPower N I σ hN a (algebraMap R A₀ (x j)) = _ at hs
        rw [hs]
        have hp := powerRight_coordinate_pow N I σ hN a j
        rw [coordinateDegree_absent N I σ j hj, pow_one] at hp
        exact hp.symm

/-- The actual WHOLE active quotient and literal original coordinate-power base change are isomorphic. -/
def activePowerRingEquiv : A₀ ≃+* C₀ :=
  RingEquiv.ofRingHom (activeToPower N I σ hN a) (powerToActive N I σ hN a)
    (activeToPower_comp_powerToActive N I σ hN a) (powerToActive_comp_activeToPower N I σ hN a)

/-- The genuine whole power comparison preserves the SAME original coefficient algebra action. -/
def activePowerAlgEquiv :
    letI : Algebra R C₀ := (powerBaseChangeLeft k d R a.toRingHom).toAlgebra
    A₀ ≃ₐ[R] C₀ := by
  let : Algebra R C₀ := (powerBaseChangeLeft k d R a.toRingHom).toAlgebra
  exact { toRingEquiv := activePowerRingEquiv N I σ hN a
          commutes' r := congrArg (fun f : R →+* C₀ => f r) (activeToPower_structure N I σ hN a) }

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
