import EnvelopeProperty.AlgGeom.SchemeGeneratedLineCoefficients
import EnvelopeProperty.Alterations.Algebra.SegreGluing

/-! # Actual polynomial sections of the mixed coordinate chart maps -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Alterations.Geometry.ProjectiveIdeal
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateAlgebra
open SchemeGeneratedLineCoefficients
variable {R : Type u} [CommRing R] {m : ℕ}

/-- The literal actual padded coordinate associated to the original pair. -/
def pairCoordinate (a b : Fin (m + 1)) :
    Fin (Fintype.card (ULift.{u} (Fin (m + 1) × Fin (m + 1))) + 1) :=
  ((Fintype.equivFin (ULift.{u} (Fin (m + 1) × Fin (m + 1)))) (ULift.up (a, b))).succ

private def rowVariable (i : Fin (m + 1)) (a : ChartIndex i) :
    ChartIndex (pairCoordinate i i) := by
  refine ⟨pairCoordinate i a.1, ?_⟩
  intro h
  have he := Fin.succ_injective _ h
  have hp := (Fintype.equivFin (ULift.{u} (Fin (m + 1) × Fin (m + 1)))).injective he
  have ha : a.1 = i := congrArg (fun q : ULift.{u} (Fin (m + 1) × Fin (m + 1)) =>
    q.down.2) hp
  exact a.2 ha

private def mixedTuple (i : Fin (m + 1)) (d : ℕ) :
    Fin (Fintype.card (ULift.{u} (Fin (m + 1) × Fin (m + 1))) + 1) → CoordinateRing R i :=
  paddedCoefficients (fun a : ULift.{u} (Fin (m + 1) × Fin (m + 1)) =>
    coordinateDehomCoord i a.down.1 ^ d * coordinateDehomCoord i a.down.2)

private theorem mixedTuple_pair (i a b : Fin (m + 1)) (d : ℕ) :
    mixedTuple (R := R) i d (pairCoordinate a b) =
      coordinateDehomCoord i a ^ d * coordinateDehomCoord i b := by
  simp only [mixedTuple, pairCoordinate, paddedCoefficients, Fin.cases_succ,
    Equiv.symm_apply_apply]

/-- The genuine normalized mixed chart map is surjective because its actual
row variables have an internally constructed polynomial section. No chart
surjectivity certificate, domain or reducedness assumption is supplied. -/
theorem mixedChartMap_surjective (i : Fin (m + 1)) (d : ℕ) :
    Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R (CoordinateRing R i))
      (fun a : ChartIndex (pairCoordinate i i) => mixedTuple i d a.1)) := by
  classical
  let φ : CoordinateRing R (pairCoordinate i i) →+* CoordinateRing R i :=
    MvPolynomial.eval₂Hom (algebraMap R (CoordinateRing R i))
      (fun a : ChartIndex (pairCoordinate i i) => mixedTuple i d a.1)
  let ψ : CoordinateRing R i →+* CoordinateRing R (pairCoordinate i i) :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun a => MvPolynomial.X (rowVariable i a))
  have hφψ : φ.comp ψ = RingHom.id (CoordinateRing R i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, ψ, φ,
        MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      rfl
    · intro a
      simp only [RingHom.comp_apply, ψ, φ,
        MvPolynomial.eval₂Hom_X', RingHom.id_apply]
      change mixedTuple i d (pairCoordinate i a.1) = MvPolynomial.X a
      rw [mixedTuple_pair, coordinateDehomCoord_self, one_pow, one_mul]
      exact coordinateDehomCoord_ne i a
  intro z
  exact ⟨ψ z, congrArg (fun f : CoordinateRing R i →+* CoordinateRing R i => f z) hφψ⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateAlgebra
