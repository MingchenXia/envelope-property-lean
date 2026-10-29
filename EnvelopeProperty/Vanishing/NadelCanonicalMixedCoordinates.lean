import EnvelopeProperty.Vanishing.NadelCanonicalMixedSplit

/-! # The actual coordinate exponents and roots of the original active quotient -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open NadelMixedKummer
attribute [local instance] Classical.propDecidable
variable {R : Type u} [CommRing R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (x : Fin n → R)

/-- The actual original positive coordinate exponent; original unused coordinates have degree one. -/
def coordinateDegree (j : Fin n) : ℕ :=
  if hj : ∃ i : I, σ i = j then N (Classical.choose hj).1 else 1

/-- The genuine original active root, or original unchanged base coordinate when it is unused. -/
def coordinateRoot (j : Fin n) : ActiveRing N I (pureCoefficient x I σ) :=
  if hj : ∃ i : I, σ i = j then root (activeDegree N I) (pureCoefficient x I σ) (Classical.choose hj).1
    else algebraMap R (ActiveRing N I (pureCoefficient x I σ)) (x j)

/-- Original coordinate injection gives exactly the SAME original root degree. -/
theorem coordinateDegree_active (i : I) : coordinateDegree N I σ (σ i) = N i.1 := by
  have h : ∃ i' : I, σ i' = σ i := ⟨i, rfl⟩
  rw [coordinateDegree, dif_pos h]
  exact congrArg (fun z : I => N z.1) (σ.injective (Classical.choose_spec h))

/-- Original coordinate injection retains the SAME actual original root. -/
theorem coordinateRoot_active (i : I) :
    coordinateRoot N I σ x (σ i) = root (activeDegree N I) (pureCoefficient x I σ) i.1 := by
  have h : ∃ i' : I, σ i' = σ i := ⟨i, rfl⟩
  rw [coordinateRoot, dif_pos h]
  exact congrArg (fun z : I => root (activeDegree N I) (pureCoefficient x I σ) z.1)
    (σ.injective (Classical.choose_spec h))

/-- No extra root is extracted from any original unused coordinate. -/
theorem coordinateDegree_absent (j : Fin n) (hj : ¬ ∃ i : I, σ i = j) :
    coordinateDegree N I σ j = 1 := by rw [coordinateDegree, dif_neg hj]

/-- Every unused coordinate remains its original true coefficient image. -/
theorem coordinateRoot_absent (j : Fin n) (hj : ¬ ∃ i : I, σ i = j) :
    coordinateRoot N I σ x j = algebraMap R (ActiveRing N I (pureCoefficient x I σ)) (x j) := by
  rw [coordinateRoot, dif_neg hj]

/-- The actual coordinate roots satisfy every SAME original coordinate-power equation. -/
theorem coordinateRoot_pow (j : Fin n) :
    coordinateRoot N I σ x j ^ coordinateDegree N I σ j =
      algebraMap R (ActiveRing N I (pureCoefficient x I σ)) (x j) := by
  by_cases hj : ∃ i : I, σ i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [coordinateRoot_active, coordinateDegree_active]
    have hp := root_pow (activeDegree N I) (pureCoefficient x I σ) i.1
    simpa only [activeDegree, if_pos i.2, pureCoefficient, dif_pos i.2] using hp
  · rw [coordinateRoot_absent N I σ x j hj, coordinateDegree_absent N I σ j hj, pow_one]

/-- Positivity of every true original root degree gives positivity of every constructed coordinate exponent. -/
theorem coordinateDegree_pos (hN : ∀ i, 0 < N i) (j : Fin n) : 0 < coordinateDegree N I σ j := by
  unfold coordinateDegree
  split_ifs with hj
  · exact hN (Classical.choose hj).1
  · exact Nat.zero_lt_one

/-- The original coordinate exponent minus one, for the native positive-power API. -/
def coordinateExponent (j : Fin n) : ℕ := coordinateDegree N I σ j - 1

/-- The native power exponent retains the SAME positive original coordinate degree. -/
theorem coordinateExponent_succ (hN : ∀ i, 0 < N i) (j : Fin n) :
    coordinateExponent N I σ j + 1 = coordinateDegree N I σ j :=
  Nat.sub_add_cancel (coordinateDegree_pos N I σ hN j)

/-- Every original active exponent retains its original root degree. -/
theorem coordinateExponent_active (hN : ∀ i, 0 < N i) (i : I) :
    coordinateExponent N I σ (σ i) + 1 = N i.1 := by
  rw [coordinateExponent_succ N I σ hN, coordinateDegree_active]

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
