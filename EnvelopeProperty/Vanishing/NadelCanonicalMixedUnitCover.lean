import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingFinite
import EnvelopeProperty.AlgGeom.KummerUnitRootCover
import Mathlib.RingTheory.RingHom.Etale

/-! # The actual entire finite free faithfully flat tame unit-root cover -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed

open NadelMixedKummer NadelAdaptedChartMatching NadelFiniteDualityTower

variable {R : Type u} [CommRing R] {q : ℕ} (N : Fin q → ℕ) (u : Fin q → Rˣ)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : R))

/-- The coefficient cover is the WHOLE original simultaneous quotient, retaining every unit-root factor. -/
abbrev UnitCover := NadelMixedKummer.Ring N (fun i => (u i : R))

include hN

/-- Every original coefficient-cover root is a unit, without any component choice. -/
theorem unitCover_root_isUnit (i : Fin q) :
    IsUnit (NadelMixedKummer.root N (fun j => (u j : R)) i) := by
  apply (isUnit_pow_iff (hN i).ne').mp
  rw [NadelMixedKummer.root_pow]
  exact (u i).isUnit.map (algebraMap R (UnitCover N u))

/-- The original root as a genuine unit of the WHOLE coefficient cover. -/
def unitCover_rootUnit (i : Fin q) : (UnitCover N u)ˣ := (unitCover_root_isUnit N u hN i).unit

/-- The actual produced unit retains the same literal original root. -/
theorem unitCover_rootUnit_coe (i : Fin q) :
    (unitCover_rootUnit N u hN i : UnitCover N u) =
      NadelMixedKummer.root N (fun j => (u j : R)) i :=
  (unitCover_root_isUnit N u hN i).unit_spec

include htame in
private theorem step_etale (k : ℕ) (hk : k < q) :
    (independentRootStep (VaryingFamily.degree N)
      (VaryingFamily.coefficient (fun i => (u i : R))) k).Etale := by
  let B := independentRootRing (VaryingFamily.degree N)
    (VaryingFamily.coefficient (fun i => (u i : R))) k
  let f : R →+* B := independentRootStructure (VaryingFamily.degree N)
    (VaryingFamily.coefficient (fun i => (u i : R))) k
  let v : Bˣ := Units.map f.toMonoidHom (u ⟨k, hk⟩)
  have hc : f (VaryingFamily.coefficient (fun i => (u i : R)) k) = (v : B) := by
    change f (VaryingFamily.coefficient (fun i => (u i : R)) k) = f (u ⟨k, hk⟩ : R)
    rw [VaryingFamily.coefficient, dif_pos hk]
  have hd : VaryingFamily.degree N k + 1 = N ⟨k, hk⟩ :=
    VaryingFamily.degree_eq N hN ⟨k, hk⟩
  change (algebraMap B (NadelFiniteDuality.Root (VaryingFamily.degree N k)
    (f (VaryingFamily.coefficient (fun i => (u i : R)) k)))).Etale
  rw [hc]
  change (algebraMap B (CyclicSectionAlgebra.RootRing (VaryingFamily.degree N k + 1) (v : B))).Etale
  rw [hd, RingHom.etale_algebraMap]
  exact KummerUnitRootCover.etale (N ⟨k, hk⟩) v (hN ⟨k, hk⟩)
    (by simpa only [map_natCast] using (htame ⟨k, hk⟩).map f)

include htame in
private theorem stage_etale : ∀ (k : ℕ) (_ : k ≤ q),
    (independentRootStructure (VaryingFamily.degree N)
      (VaryingFamily.coefficient (fun i => (u i : R))) k).Etale := by
  intro k
  induction k with
  | zero =>
      intro _
      exact RingHom.Etale.of_bijective Function.bijective_id
  | succ k ih =>
      intro hk
      rw [independentRootStructure_succ]
      exact RingHom.Etale.stableUnderComposition _ _
        (ih (Nat.le_of_succ_le hk)) (step_etale N u hN htame k (Nat.lt_of_succ_le hk))

include htame in
/-- The WHOLE simultaneous coefficient cover is actually étale over its SAME original ring. -/
theorem unitCover_etale : Algebra.Etale R (UnitCover N u) := by
  let : Algebra R (VaryingFamily.Ring N (fun i => (u i : R))) :=
    (VaryingFamily.structureMap N (fun i => (u i : R))).toAlgebra
  let : Algebra.Etale R (VaryingFamily.Ring N (fun i => (u i : R))) :=
    stage_etale N u hN htame q (Nat.le_refl q)
  exact Algebra.Etale.of_equiv (VaryingFinite.algEquiv N (fun i => (u i : R)) hN).symm

variable [Nontrivial R]

/-- The entire coefficient cover is nonzero, by the actual original finite monic tower. -/
theorem unitCover_nontrivial : Nontrivial (UnitCover N u) := by
  let : Nontrivial (VaryingFamily.Ring N (fun i => (u i : R))) :=
    independentRootRing_nontrivial (VaryingFamily.degree N)
      (VaryingFamily.coefficient (fun i => (u i : R))) q
  exact (VaryingFinite.ringEquiv N (fun i => (u i : R)) hN).toEquiv.nontrivial

/-- The whole original variable-degree monic basis gives actual finite freeness of the cover. -/
theorem unitCover_free : Module.Free R (UnitCover N u) :=
  VaryingFinite.free N (fun i => (u i : R)) hN

/-- Every original root factor is retained in the genuine finite coefficient cover. -/
theorem unitCover_finite : Module.Finite R (UnitCover N u) :=
  VaryingFinite.finite N (fun i => (u i : R)) hN

/-- Actual faithful flatness follows from the whole nonzero monic basis, with no domain condition on the cover. -/
theorem unitCover_faithfullyFlat : Module.FaithfullyFlat R (UnitCover N u) := by
  let := unitCover_nontrivial N u hN
  let := unitCover_free N u hN
  infer_instance

end EnvelopeProperty.Vanishing.NadelCanonicalMixed
