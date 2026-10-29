import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The entire proper central fibre in a separated compactification

The map is the actual original fibre-product projection followed by the
given morphism. Relative properness and the whole structure triangles
close its entire image; no absolute properness or image certificate is
assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace EnvelopeProperty.ProperCentralFiberCompactification

variable {B S R T : Scheme.{u}}

/-- The actual original fibre-product map retains its whole structure triangle. -/
theorem pullback_comp_structure
    (ε : S ⟶ B) (γ : B ⟶ S) (hε : ε ≫ γ = 𝟙 S)
    (b : R ⟶ B) (e : R ⟶ T) (p : T ⟶ S) (he : e ≫ p = b ≫ γ) :
    (pullback.fst b ε ≫ e) ≫ p = pullback.snd b ε := by
  calc
    _ = (pullback.fst b ε ≫ b) ≫ γ := by
      rw [Category.assoc, he, ← Category.assoc]
    _ = (pullback.snd b ε ≫ ε) ≫ γ := by rw [pullback.condition]
    _ = pullback.snd b ε := by rw [Category.assoc, hε, Category.comp_id]

/-- Proper base change and separated cancellation make the SAME original map proper. -/
theorem isProper_pullback_comp
    (ε : S ⟶ B) (γ : B ⟶ S) (hε : ε ≫ γ = 𝟙 S)
    (b : R ⟶ B) [IsProper b] (e : R ⟶ T)
    (p : T ⟶ S) [IsSeparated p] (he : e ≫ p = b ≫ γ) :
    IsProper (pullback.fst b ε ≫ e) := by
  let : IsProper ((pullback.fst b ε ≫ e) ≫ p) := by
    rw [pullback_comp_structure ε γ hε b e p he]
    infer_instance
  exact IsProper.of_comp (pullback.fst b ε ≫ e) p

/-- Its entire actual range retains every original compatible fibre-product point. -/
theorem range_pullback_comp (b : R ⟶ B) (ε : S ⟶ B) (e : R ⟶ T) :
    Set.range (pullback.fst b ε ≫ e) = e '' (b ⁻¹' Set.range ε) := by
  change Set.range (e ∘ pullback.fst b ε) = _
  rw [Set.range_comp, Scheme.Pullback.range_fst]

/-- Relative properness closes the SAME entire original central image. -/
theorem isClosed_image_preimage_range
    (ε : S ⟶ B) (γ : B ⟶ S) (hε : ε ≫ γ = 𝟙 S)
    (b : R ⟶ B) [IsProper b] (e : R ⟶ T)
    (p : T ⟶ S) [IsSeparated p] (he : e ≫ p = b ≫ γ) :
    IsClosed (e '' (b ⁻¹' Set.range ε)) := by
  let : IsProper (pullback.fst b ε ≫ e) :=
    isProper_pullback_comp ε γ hε b e p he
  rw [← range_pullback_comp b ε e]
  exact (pullback.fst b ε ≫ e).isClosedMap.isClosed_range

end EnvelopeProperty.ProperCentralFiberCompactification
