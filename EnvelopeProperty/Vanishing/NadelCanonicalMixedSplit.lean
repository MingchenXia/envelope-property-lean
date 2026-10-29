import EnvelopeProperty.Vanishing.NadelCanonicalMixedSplitCore

/-! # Whole original pure mixed algebra as its active quotient and complete inactive unit layer -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open NadelMixedKummer
attribute [local instance] Classical.propDecidable
variable {R : Type u} [CommRing R] {q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q))
    (h : Fin q → R) (hi : ∀ i, i ∉ I → h i = 1)

/-- Every actual first-layer root has its full original whole-source value. -/
theorem activeToWhole_root (i : Fin q) :
    activeToWhole N I h hi (root (activeDegree N I) h i) =
      if i ∈ I then root N h i else 1 := by
  classical
  exact evaluate_root _ _ _ _ _ i

/-- Every actual second-layer root retains its complete original inactive factor. -/
theorem splitToWhole_root (i : Fin q) :
    splitToWhole N I h hi (root (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h)) i) =
      if i ∈ I then 1 else root N h i := by
  classical
  exact evaluate_root _ _ _ _ _ i

/-- Each original root has the actual same first- or second-layer root in the inverse candidate. -/
theorem wholeToSplit_root (i : Fin q) :
    wholeToSplit N I h hi (root N h i) =
      if i ∈ I then algebraMap (ActiveRing N I h) (SplitRing N I h) (root (activeDegree N I) h i)
        else root (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h)) i := by
  classical
  exact evaluate_root _ _ _ _ _ i

include hi in
/-- The first-layer degree-one inactive root is actually one, on the WHOLE quotient. -/
theorem activeRoot_absent (i : Fin q) (hh : i ∉ I) : root (activeDegree N I) h i = 1 := by
  classical
  simpa only [activeDegree, if_neg hh, pow_one, hi i hh, map_one] using
    root_pow (activeDegree N I) h i

/-- The second-layer active degree-one root is actually one, without a component projection. -/
theorem inactiveRoot_active (i : Fin q) (hh : i ∈ I) :
    root (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h)) i = 1 := by
  classical
  simpa only [inactiveDegree, if_pos hh, pow_one, map_one] using
    root_pow (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h)) i

/-- The true inverse candidate preserves the entire original active coefficient algebra. -/
theorem wholeToSplit_active : (wholeToSplit N I h hi).comp (activeToWhole N I h hi) =
    algebraMap (ActiveRing N I h) (SplitRing N I h) := by
  classical
  apply hom_ext
  · rw [RingHom.comp_assoc, activeToWhole_structure, wholeToSplit_structure]
    rfl
  · intro i
    change wholeToSplit N I h hi (activeToWhole N I h hi _) = _
    rw [activeToWhole_root]
    by_cases hh : i ∈ I
    · rw [if_pos hh, wholeToSplit_root, if_pos hh]
    · rw [if_neg hh, map_one, activeRoot_absent N I h hi i hh, map_one]

/-- Both original whole universal properties give the actual pure active/inactive splitting equivalence. -/
def wholeRingEquiv : Ring N h ≃+* SplitRing N I h := by
  classical
  have hf : (splitToWhole N I h hi).comp (wholeToSplit N I h hi) = RingHom.id _ := by
    apply hom_ext
    · rw [RingHom.comp_assoc, wholeToSplit_structure]
      dsimp only [coefficientHom]
      rw [← RingHom.comp_assoc, splitToWhole_active, activeToWhole_structure]
      rfl
    · intro i
      change splitToWhole N I h hi (wholeToSplit N I h hi _) = _
      rw [wholeToSplit_root]
      by_cases hh : i ∈ I
      · rw [if_pos hh]
        exact (congrArg (fun f : ActiveRing N I h →+* Ring N h => f (root (activeDegree N I) h i))
          (splitToWhole_active N I h hi)).trans
            ((activeToWhole_root N I h hi i).trans (if_pos hh))
      · rw [if_neg hh, splitToWhole_root, if_neg hh]
        rfl
  have hg : (wholeToSplit N I h hi).comp (splitToWhole N I h hi) = RingHom.id _ := by
    apply hom_ext
    · rw [RingHom.comp_assoc, splitToWhole_active, wholeToSplit_active]
      rfl
    · intro i
      change wholeToSplit N I h hi (splitToWhole N I h hi _) = _
      rw [splitToWhole_root]
      by_cases hh : i ∈ I
      · rw [if_pos hh, map_one, inactiveRoot_active N I h i hh]
        rfl
      · rw [if_neg hh, wholeToSplit_root, if_neg hh]
        rfl
  exact RingEquiv.ofRingHom (wholeToSplit N I h hi) (splitToWhole N I h hi) hg hf

/-- The actual original R-coefficient action is the literal two-step coefficient map. -/
theorem coefficientHom_eq : coefficientHom N I h = algebraMap R (SplitRing N I h) := by
  exact IsScalarTower.algebraMap_eq R (ActiveRing N I h) (SplitRing N I h)

/-- The WHOLE original pure mixed quotient is the actual full unit-root layer over its active quotient. -/
def wholeAlgEquiv : Ring N h ≃ₐ[R] SplitRing N I h :=
  { toRingEquiv := wholeRingEquiv N I h hi
    commutes' := fun r => (congrArg (fun f : R →+* SplitRing N I h => f r)
      (wholeToSplit_structure N I h hi)).trans
        (congrArg (fun f : R →+* SplitRing N I h => f r) (coefficientHom_eq N I h)) }

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
