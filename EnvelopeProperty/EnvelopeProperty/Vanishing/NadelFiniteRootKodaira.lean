import EnvelopeProperty.Vanishing.NadelFiniteCoverKodaira
import EnvelopeProperty.AlgGeom.AmpleLinePositivePowers

/-! # Actual integral root lines on the whole original finite cover

An actual positive-power isomorphism gives ampleness internally. For the
original rounded line that isomorphism must still be constructed from the
whole root ideals; it is not a new DI input or a vanishing premise.
-/

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules

namespace EnvelopeProperty.Vanishing.NadelFiniteRootKodaira

open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

/-- The whole actual integral root line is ample, from the actual positive
power comparison to the original finite pullback, including disconnected W. -/
theorem isAmple_of_finite_power {R : Type u} [CommRing R] [IsDomain R]
    {X W : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L)
    (π : W ⟶ X) [IsFinite π] (N : W.Modules) (hN : IsInvertible N)
    (d : ℕ) (hd : 0 < d)
    (e : bundleTensorPower N d ≅ (Scheme.Modules.pullback π).obj L) :
    SchemeLineAmpleness.IsAmple (π ≫ p) N :=
  AmpleLinePositivePowers.isAmple_of_tensorPower (π ≫ p) N hN d hd
    (AmpleTensorLines.ample_of_iso (NadelFiniteAmplePullback.isAmple_pullback p L hL π) e.symm)

/-- Actual positive Kodaira cohomology of that same whole integral root line,
using the proved global Witt decomposition. -/
theorem cover {k : Type u} [Field k] [CharZero k] {X W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L)
    (π : W ⟶ X) [IsFinite π] (N : W.Modules) (hN : IsInvertible N)
    (d : ℕ) (hd : 0 < d)
    (e : bundleTensorPower N d ≅ (Scheme.Modules.pullback π).obj L)
    (n : ℕ) [SmoothOfRelativeDimension n (π ≫ p)] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf (π ≫ p) n ⊗ N : W.Modules).sheaf (q + 1)) :=
  KodairaCharacteristicZero.kodaira (π ≫ p) n N
    (isAmple_of_finite_power p L hL π N hN d hd e) q

end EnvelopeProperty.Vanishing.NadelFiniteRootKodaira
