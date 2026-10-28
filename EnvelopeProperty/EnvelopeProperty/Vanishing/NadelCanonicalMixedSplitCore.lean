import EnvelopeProperty.Vanishing.NadelCanonicalMixedPurification

/-! # Actual active and entire inactive factors of the original pure simultaneous quotient -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open NadelMixedKummer
variable {R : Type u} [CommRing R] {q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q))
    (h : Fin q → R) (hi : ∀ i, i ∉ I → h i = 1)

/-- The original active degrees; inactive degree-one equations retain their actual unit-one root. -/
def activeDegree (i : Fin q) : ℕ := by classical exact if i ∈ I then N i else 1

/-- The original entire inactive degrees; active degree-one factors are actual trivial unit layers. -/
def inactiveDegree (i : Fin q) : ℕ := by classical exact if i ∈ I then 1 else N i

/-- The actual active quotient, without removing any original coefficient map. -/
abbrev ActiveRing := Ring (activeDegree N I) h

/-- The WHOLE original inactive unit-root layer above the actual active quotient. -/
abbrev SplitRing := Ring (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h))

/-- The literal composite of the original two coefficient inclusions. -/
def coefficientHom : R →+* SplitRing N I h :=
  (algebraMap (ActiveRing N I h) (SplitRing N I h)).comp (algebraMap R (ActiveRing N I h))

/-- The actual active quotient maps to the original pure quotient, fixing all original active roots. -/
def activeToWhole : ActiveRing N I h →+* Ring N h := by
  classical
  exact evaluate (activeDegree N I) h (algebraMap R (Ring N h))
    (fun i => if i ∈ I then root N h i else 1) (by
      intro i
      by_cases hh : i ∈ I
      · simp only [activeDegree, if_pos hh]
        exact root_pow N h i
      · simp only [activeDegree, if_neg hh, one_pow, hi i hh, map_one])

/-- Every original coefficient is preserved by the genuine active inclusion. -/
theorem activeToWhole_structure : (activeToWhole N I h hi).comp (algebraMap R (ActiveRing N I h)) =
    algebraMap R (Ring N h) := by
  classical
  exact evaluate_structure _ _ _ _ _

/-- The actual whole second-layer quotient maps to all original inactive roots, with no component choice. -/
def splitToWhole : SplitRing N I h →+* Ring N h := by
  classical
  exact evaluate (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h)) (activeToWhole N I h hi)
    (fun i => if i ∈ I then 1 else root N h i) (by
      intro i
      by_cases hh : i ∈ I
      · simp only [inactiveDegree, if_pos hh, one_pow, map_one]
      · simp only [inactiveDegree, if_neg hh, root_pow, hi i hh, map_one])

/-- The whole split map retains the actual original active coefficient ring. -/
theorem splitToWhole_active : (splitToWhole N I h hi).comp
    (algebraMap (ActiveRing N I h) (SplitRing N I h)) = activeToWhole N I h hi := by
  classical
  exact evaluate_structure _ _ _ _ _

/-- The inverse candidate sends each original active root to the actual first layer and each inactive root to its complete second layer. -/
def wholeToSplit : Ring N h →+* SplitRing N I h := by
  classical
  exact evaluate N h (coefficientHom N I h)
    (fun i => if i ∈ I then
      algebraMap (ActiveRing N I h) (SplitRing N I h) (root (activeDegree N I) h i)
      else root (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h)) i) (by
      intro i
      by_cases hh : i ∈ I
      · simp only [if_pos hh]
        rw [← map_pow]
        have hp := root_pow (activeDegree N I) h i
        simp only [activeDegree, if_pos hh] at hp
        rw [hp]
        rfl
      · simp only [if_neg hh]
        have hp := root_pow (inactiveDegree N I) (fun _ => (1 : ActiveRing N I h)) i
        simp only [inactiveDegree, if_neg hh, map_one] at hp
        rw [hp, hi i hh, map_one])

/-- The original coefficient triangle is retained on the entire inverse candidate. -/
theorem wholeToSplit_structure : (wholeToSplit N I h hi).comp (algebraMap R (Ring N h)) =
    coefficientHom N I h := by
  classical
  exact evaluate_structure _ _ _ _ _

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
