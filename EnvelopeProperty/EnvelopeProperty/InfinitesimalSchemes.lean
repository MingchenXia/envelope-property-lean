/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.SchemeNilBaseChange
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Literal original infinitesimal pullbacks and all whole transition maps -/
open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
namespace EnvelopeProperty.InfinitesimalSchemes
variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The original quotient ring at EVERY natural order, including zero and whole ideals. -/
abbrev ring (n : ℕ) := R ⧸ I^n

/-- The literal original coefficient morphism into the same base scheme. -/
abbrev coefficientScheme (n : ℕ) : Spec (.of (ring I n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)))

/-- The LITERAL original infinitesimal pullback, with every nilpotent retained. -/
abbrev model (n : ℕ) := pullback f (coefficientScheme I n)

/-- The original whole scheme projection to X. -/
abbrev projection (n : ℕ) : model I f n ⟶ X := pullback.fst _ _

/-- The original coefficient projection to Spec(R/I^n). -/
abbrev structureMap (n : ℕ) : model I f n ⟶ Spec (.of (ring I n)) := pullback.snd _ _

/-- The genuine original quotient factor retains the WHOLE R coefficient morphism. -/
theorem coefficientScheme_factor {n m : ℕ} (h : n≤m) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)) ≫ coefficientScheme I m =
      coefficientScheme I n := by
  dsimp only [coefficientScheme]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.factorPow I h).comp (Ideal.Quotient.mk (I^m)))) = _
  rw [Ideal.Quotient.factor_comp_mk]

/-- The actual original whole map between original-order infinitesimal pullbacks. -/
def transition {n m : ℕ} (h : n≤m) : model I f n ⟶ model I f m :=
  pullback.lift (projection I f n)
    (structureMap I f n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h))) (by
      rw [Category.assoc,coefficientScheme_factor I h]
      exact pullback.condition)

/-- Every transition preserves the ENTIRE original projection to X. -/
@[reassoc] theorem transition_projection {n m : ℕ} (h : n≤m) :
    transition I f h ≫ projection I f m = projection I f n := pullback.lift_fst _ _ _

/-- Every transition preserves the WHOLE original quotient coefficient map. -/
@[reassoc] theorem transition_structureMap {n m : ℕ} (h : n≤m) :
    transition I f h ≫ structureMap I f m =
      structureMap I f n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)) :=
  pullback.lift_snd _ _ _

/-- The literal same-order transition is the ENTIRE scheme identity. -/
theorem transition_self (n : ℕ) : transition I f (le_refl n) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [transition,projection]
  · simp [transition,structureMap,Ideal.Quotient.factorPow]

/-- All original-order transitions obey actual WHOLE scheme composition. -/
theorem transition_comp {l n m : ℕ} (hln : l≤n) (hnm : n≤m) :
    transition I f hln ≫ transition I f hnm = transition I f (hln.trans hnm) := by
  apply pullback.hom_ext
  · change (transition I f hln ≫ transition I f hnm) ≫ projection I f m =
      transition I f (hln.trans hnm) ≫ projection I f m
    simp only [Category.assoc,transition_projection]
  · change (transition I f hln ≫ transition I f hnm) ≫ structureMap I f m =
      transition I f (hln.trans hnm) ≫ structureMap I f m
    rw [Category.assoc,transition_structureMap,transition_structureMap_assoc,
      transition_structureMap]
    rw [← Spec.map_comp]
    change _ ≫ Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.factorPow I hln).comp (Ideal.Quotient.factorPow I hnm))) = _
    rw [Ideal.Quotient.factor_comp]

/-- Every actual quotient-factor kernel element is genuinely nilpotent when the target order is positive. -/
theorem nilpotent_mem_ker_factorPow {n m : ℕ} (hn : 0<n) (h : n≤m)
    (z : ring I m) (hz : z ∈ RingHom.ker (Ideal.Quotient.factorPow I h)) : IsNilpotent z := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective z
  have ha : a ∈ I^n := by
    simpa only [RingHom.mem_ker,Ideal.Quotient.factorPow,Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem] using hz
  refine ⟨m,?_⟩
  rw [← map_pow,Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (Ideal.pow_le_self hn.ne' ha) m

/-- Genuine pullback pasting derives the ACTUAL base-change square of every original transition. -/
theorem isPullback_transition {n m : ℕ} (h : n≤m) :
    IsPullback (transition I f h) (structureMap I f n) (structureMap I f m)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h))) := by
  apply IsPullback.of_right (h₁₂ := projection I f m) (h₂₂ := coefficientScheme I m) ?_
    (transition_structureMap I f h) (IsPullback.of_hasPullback f (coefficientScheme I m))
  rw [transition_projection,coefficientScheme_factor]
  exact IsPullback.of_hasPullback f (coefficientScheme I n)

/-- The literal original transition is a true closed immersion, at every order. -/
theorem isClosedImmersion_transition {n m : ℕ} (h : n≤m) : IsClosedImmersion (transition I f h) := by
  have hα := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I h))
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right h))
  exact MorphismProperty.of_isPullback (isPullback_transition I f h).flip hα

/-- Genuine nil-kernel prime correspondence and actual pasting DERIVE scheme surjectivity for positive orders. -/
theorem surjective_transition {n m : ℕ} (hn : 0<n) (h : n≤m) : Surjective (transition I f h) := by
  have hα := SchemeNilBaseChange.surjective_specMap (Ideal.Quotient.factorPow I h)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right h))
    (nilpotent_mem_ker_factorPow I hn h)
  exact MorphismProperty.of_isPullback (isPullback_transition I f h).flip hα

/-- The ORIGINAL whole transition section map bijects true idempotents, without a whole-section surjectivity claim. -/
def idempotentRestrictionEquiv {n m : ℕ} (hn : 0<n) (h : n≤m) :
    {e : Γ(model I f m,⊤) // IsIdempotentElem e} ≃
      {e : Γ(model I f n,⊤) // IsIdempotentElem e} := by
  let : IsClosedImmersion (transition I f h) := isClosedImmersion_transition I f h
  let : Surjective (transition I f h) := surjective_transition I f hn h
  exact Equiv.ofBijective (SchemeIdempotentRestriction.map (transition I f h))
    (SchemeIdempotentRestriction.map_bijective_of_closed_surjective (transition I f h))

end EnvelopeProperty.InfinitesimalSchemes
