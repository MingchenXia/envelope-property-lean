import ModularCurves.ForMathlib.SheafCohomologyExact

/-! # Actual sheaf cohomology vanishing along a finite resolution -/

open CategoryTheory
noncomputable section
universe u v w w'

namespace EnvelopeProperty.SheafFiniteResolutionVanishing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

private theorem right_cohomology_subsingleton
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (q : ℕ)
    (hE : Subsingleton (Sheaf.H S.X₂ q))
    (hZ : Subsingleton (Sheaf.H S.X₁ (q + 1))) :
    Subsingleton (Sheaf.H S.X₃ q) := by
  let := hE
  let := hZ
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₃ hS x rfl (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- Vanishing of the diagonal cohomology of a finite exact resolution,
including its final kernel, annihilates the actual cohomology of its target. -/
theorem subsingleton_H_of_finite_resolution
    (Z E : ℕ → Sheaf J AddCommGrpCat.{w})
    (ι : ∀ i, Z (i + 1) ⟶ E i) (π : ∀ i, E i ⟶ Z i)
    (hzero : ∀ i, ι i ≫ π i = 0) (r q : ℕ)
    (hS : ∀ i, i < r → (ShortComplex.mk (ι i) (π i) (hzero i)).ShortExact)
    (hE : ∀ i, i < r → Subsingleton (Sheaf.H (E i) (q + i)))
    (hZ : Subsingleton (Sheaf.H (Z r) (q + r))) :
    Subsingleton (Sheaf.H (Z 0) q) := by
  have hback : ∀ k, k ≤ r →
      Subsingleton (Sheaf.H (Z (r - k)) (q + (r - k))) := by
    intro k
    induction k with
    | zero => simpa using hZ
    | succ k ih =>
      intro hk
      have hi : r - (k + 1) < r := by omega
      have hnext : r - k = r - (k + 1) + 1 := by omega
      exact right_cohomology_subsingleton (hS _ hi) _ (hE _ hi)
        (by simpa only [hnext, Nat.add_assoc] using ih (by omega))
  simpa using hback r le_rfl

end EnvelopeProperty.SheafFiniteResolutionVanishing
