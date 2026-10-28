import EnvelopeProperty.Vanishing.KodairaCharacteristicZero
import EnvelopeProperty.Vanishing.NadelFiniteAmplePullback
import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology
import EnvelopeProperty.Vanishing.SmoothExteriorFiniteType
import ModularCurves.ForMathlib.FiniteAffineOpenCover

/-! # Actual Kodaira groups and canonical pushforwards on the whole finite cover

Global normalization geometry and canonical duality are not assumed under
new certificate names.  These theorems apply to any actual finite morphism
whose original source structure is smooth of the stated dimension.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelFiniteCoverKodaira

open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Positive Kodaira cohomology of the whole actual finite covering scheme,
with ampleness of the original pulled-back line proved internally. -/
theorem cover {k : Type u} [Field k] [CharZero k] {X W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L)
    (π : W ⟶ X) [IsFinite π] (n : ℕ) [SmoothOfRelativeDimension n (π ≫ p)] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf (π ≫ p) n ⊗ (Scheme.Modules.pullback π).obj L : W.Modules).sheaf (q + 1)) :=
  KodairaCharacteristicZero.kodaira (π ≫ p) n ((Scheme.Modules.pullback π).obj L)
    (NadelFiniteAmplePullback.isAmple_pullback p L hL π) q

/-- The actual canonical finite pushforward has zero positive cohomology
after the original ample twist.  The genuine affine comparison, original
finite affine cover and line projection formula are all supplied internally. -/
theorem pushforward {k : Type u} [Field k] [CharZero k] {X W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L)
    (π : W ⟶ X) [IsFinite π] (n : ℕ) [SmoothOfRelativeDimension n (π ≫ p)] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pushforward π).obj (canonicalLineSheaf (π ≫ p) n) ⊗ L :
        X.Modules).sheaf (q + 1)) := by
  let : IsProper p := hL.isProjectiveFactorization.isProper
  let : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let M := canonicalLineSheaf (π ≫ p) n
  let : M.IsQuasicoherent := SmoothExteriorFiniteType.isQuasicoherent (π ≫ p) n n
  obtain ⟨ι, hι, U, hU, hUa⟩ := X.exists_finite_affine_openCover
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact (AffinePushforwardCohomology.subsingleton_H_twist_iff_pushforward π p M L
    hL.isInvertible U hU hUa q).mp (cover p L hL π n q)

end EnvelopeProperty.Vanishing.NadelFiniteCoverKodaira
