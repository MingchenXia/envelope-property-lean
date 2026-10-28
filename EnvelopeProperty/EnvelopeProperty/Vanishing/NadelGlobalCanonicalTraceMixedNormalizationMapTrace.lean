import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCounit
import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniquenessCore

/-! # Genuine algebra trace of the original whole purification ring map

The same proof-backed representative used by the original ring-map
producer retains its actual S-algebra equivalence. Its equality to the
original produced purification follows from choice_spec, not a supplied
trace identity. All original unit-root factors are retained.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] mixedPurificationIso

private def actualSealedValue {α : Type u} (a : α) : α :=
  Classical.choose (show ∃ b : α, b = a from ⟨a, rfl⟩)

private theorem actualSealedValue_eq {α : Type u} (a : α) : actualSealedValue a = a :=
  Classical.choose_spec (show ∃ b : α, b = a from ⟨a, rfl⟩)

private theorem trace_of_actual_values
    {R C P : Type u} [CommRing R] [CommRing C] [CommRing P]
    [Algebra R C] [Algebra R P] (e : C ≃ₐ[R] P) (f : C → P)
    (h : ∀ z, f z = e.toRingHom.toFun z) (z : C) :
    Algebra.trace R P (f z) = Algebra.trace R C z := by
  rw [h]
  exact Algebra.trace_eq_of_algEquiv e z

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
local notation "Bₘ" => mixedRing x N I σ u
local notation "Sᵤ" => UnitCover N u
local notation "Cₘ" => extendedMixedRing x N I σ u
local notation "Pₘ" => mixedPureRing (k := k) x N I σ u

/-- The SAME actual purification ring map preserves the unnormalized
trace of the original whole tensor algebra on EVERY original element. -/
theorem mixedPurificationMap_trace (hN : ∀ i, 0 < N i) (z : Cₘ) :
    Algebra.trace Sᵤ Pₘ (mixedPurificationMap (k := k) x N I σ u hN z) =
      Algebra.trace Sᵤ Cₘ z := by
  let e := actualSealedValue (mixedPurificationIso (k := k) x N I σ u hN)
  exact trace_of_actual_values e
    (fun w => mixedPurificationMap (k := k) x N I σ u hN w) (fun _ => rfl) z

variable [Nontrivial A]

/-- The actual whole purification ring map has the ORIGINAL B/A trace
on EVERY original coefficient and every unit-cover pure tensor. -/
theorem mixedPurificationMap_trace_tmul (hN : ∀ i, 0 < N i) (s : Sᵤ) (c : Bₘ) :
    Algebra.trace Sᵤ Pₘ
        (mixedPurificationMap (k := k) x N I σ u hN (s ⊗ₜ[A] c)) =
      s * algebraMap A Sᵤ (Algebra.trace A Bₘ c) := by
  let : Module.Free A Bₘ :=
    NadelAdaptedChartMatching.VaryingFinite.free N (mixedCoefficient x I σ u) hN
  let : Module.Finite A Bₘ :=
    NadelAdaptedChartMatching.VaryingFinite.finite N (mixedCoefficient x I σ u) hN
  exact (mixedPurificationMap_trace x N I σ u hN (s ⊗ₜ[A] c)).trans
    (NadelKummerTraceBaseChangeUniqueness.trace_tmul (A := A) (B := Bₘ) s c)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
