import EnvelopeProperty.Cartier.FrobeniusLiftDifference

/-! # Genuine naturality of canonical divided ring differences under actual lift diagrams -/
noncomputable section
namespace EnvelopeProperty.Cartier.FrobeniusLiftDifferenceNaturality
open FrobeniusLiftDifference
universe u
variable {p : ℕ} {R S A B R' S' A' B' : Type u}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [CommRing R'] [CommRing S'] [CommRing A'] [CommRing B']
  (a : Reduction p R A) (b : FlatReduction p S B)
  (a' : Reduction p R' A') (b' : FlatReduction p S' B')
  (φ : A →+* B) (φ' : A' →+* B')
  (f g : R →+* S) (f' g' : R' →+* S')
  (hf : ∀ r, b.map (f r) = φ (a.map r))
  (hg : ∀ r, b.map (g r) = φ (a.map r))
  (hf' : ∀ r, b'.map (f' r) = φ' (a'.map r))
  (hg' : ∀ r, b'.map (g' r) = φ' (a'.map r))
  (α : R →+* R') (β : S →+* S') (α₀ : A →+* A') (β₀ : B →+* B')
  (ha : ∀ r, a'.map (α r) = α₀ (a.map r))
  (hb : ∀ s, b'.map (β s) = β₀ (b.map s))
  (hff : ∀ r, β (f r) = f' (α r))
  (hgg : ∀ r, β (g r) = g' (α r))

include hf hf' ha hb hff in
/-- The ACTUAL coefficient-action square is DERIVED from the genuine reduction/lift ring diagram. -/
theorem residueMapSquare : β₀.comp φ = φ'.comp α₀ := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := a.surjective x
  change β₀ (φ (a.map r)) = φ' (α₀ (a.map r))
  rw [← hf r, ← hb (f r), hff r, hf', ha]

include ha hb hff hgg in
/-- The ENTIRE canonical divided difference is natural under the ACTUAL ring-lift diagram. -/
theorem difference_naturality :
    β₀ ∘ difference a b φ f g hf hg =
      difference a' b' φ' f' g' hf' hg' ∘ α₀ := by
  funext x
  obtain ⟨r, rfl⟩ := a.surjective x
  obtain ⟨u, hu⟩ : ∃ u : S, (p : S)*u = f r-g r :=
    (b.kernel_iff (f r-g r)).mp (by rw [map_sub, hf, hg, sub_self])
  have hu' : (p : S') * β u = f' (α r)-g' (α r) := by
    calc
      (p : S') * β u = β ((p : S)*u) := by rw [map_mul, map_natCast]
      _ = β (f r-g r) := congrArg β hu
      _ = f' (α r)-g' (α r) := by rw [map_sub, hff, hgg]
  change β₀ (difference a b φ f g hf hg (a.map r)) =
    difference a' b' φ' f' g' hf' hg' (α₀ (a.map r))
  rw [difference_eq_of_lift a b φ f g hf hg r u hu, ← ha r,
    difference_eq_of_lift a' b' φ' f' g' hf' hg' (α r) (β u) hu']
  exact (hb u).symm

end EnvelopeProperty.Cartier.FrobeniusLiftDifferenceNaturality
