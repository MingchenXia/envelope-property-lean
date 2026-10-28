/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SmoothFamilyDVRChart
import Mathlib.FieldTheory.FinTrdeg

/-!
# All divisorial coordinate inputs are produced from the actual DVR

Essential finite type supplies finite residue-transcendence degree. Actual
residue lifts and an actual uniformizer therefore remove every coordinate
premise from the smooth-family divisorial chart producer.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k : Type u} [Field k]

/-- Every actual essentially finite-type DVR produces its own actual uniformizer and
finite lifted residue-transcendence coordinates. -/
theorem exists_finite_dvr_coordinates (V : Type u) [CommRing V] [IsDomain V]
    [Algebra k V] [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V] :
    ∃ (m : ℕ) (π : V) (u : Fin m → V),
      Irreducible π ∧ IsTranscendenceBasis k (residue V ∘ u) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : Algebra.EssFiniteType k (ResidueField V) :=
    inferInstanceAs (Algebra.EssFiniteType k (V ⧸ IsLocalRing.maximalIdeal V))
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k (ResidueField V)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  choose u hu using fun x : s => residue_surjective (R := V) (x : ResidueField V)
  refine ⟨Fintype.card s, π, u ∘ e, hπ, ?_⟩
  have hres : residue V ∘ (u ∘ e) = ((↑) : s → ResidueField V) ∘ e := by
    funext i
    exact hu (e i)
  rw [hres]
  exact hs.comp_equiv e

variable {K : Type u} [Field K] [Algebra k K] [CharZero k]

/-- Actual smoothness, actual function field and an actual divisorial DVR suffice to
produce the entire simultaneous monomial leaf and original-source DVR Jacobian data.
There are no source-coordinate, DVR-coordinate or dimension premises. -/
theorem exists_smooth_family_divisorial_chart
    (C V : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
    (hCV : C ≤ V) {κ : Type*} [Fintype κ] (I : κ → Ideal C) (hI : ∀ j, I j ≠ ⊥) :
    ∃ (m : ℕ) (π : V) (u : ULift.{u} (Fin m) → V) (hπ : Irreducible π)
      (hu : IsTranscendenceBasis k (residue V ∘ u))
      (n : ℕ) (T : ReesChartTree k K C) (i : T.LeafIndex)
      (hEV : T.leafAlgebra i ≤ V)
      (v : Fin n → T.leafAlgebra i)
      (_hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
      (τ : Type u) (_ : Fintype τ) (c : τ → Fin n), Function.Injective c ∧
      ∃ (d : κ → τ → ℕ) (a : τ → ℕ),
        (∀ j, (I j).map (Subalgebra.inclusion hCV).toRingHom =
          span {∏ l, Subalgebra.inclusion hEV (v (c l)) ^ d j l}) ∧
        ∃ e : Fin n ≃ Option (ULift.{u} (Fin m)),
          dvrOriginalSourceJacobianIdeal C V hCV hπ hu e =
            span {(Matrix.of fun l j => dvrLeafPartials (T.leafAlgebra i) V hEV hπ hu e j
              (v l)).det * ∏ l, Subalgebra.inclusion hEV (v (c l)) ^ a l} := by
  obtain ⟨m, π, u, hπ, hu⟩ := exists_finite_dvr_coordinates (k := k) V
  let u' : ULift.{u} (Fin m) → V := fun i => u i.down
  have hu' : IsTranscendenceBasis k (residue V ∘ u') := hu.comp_equiv Equiv.ulift
  exact ⟨m, π, u', hπ, hu', exists_smooth_family_dvr_chart C V hCV I hI hπ hu'⟩

end EnvelopeProperty.Char0
