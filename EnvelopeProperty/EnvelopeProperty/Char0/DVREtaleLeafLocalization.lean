/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DerivationSourceLocalization
import EnvelopeProperty.Char0.DVRCoordinatePresentations
import EnvelopeProperty.Char0.DVRLeafLogBound

/-!
# Actual divisorial localizations of etale leaves

The genuine all-source derivative ideal of a DVR localization is the unit
ideal. Actual etale factorization then proves its leaf-coordinate determinant
is a unit and bounds the sum of every leaf coordinate order by one.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  (V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
  [Algebra.EssFiniteType k V] {ι : Type u} [Fintype ι]
  {π : V} {u : ι → V} {n : ℕ}

/-- The actual original-source Jacobian ideal for the DVR itself contains one from
its genuine uniformizer and residue-coordinate tuple. -/
theorem dvrOriginalSourceJacobianIdeal_self_eq_top
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u))
    (e : Fin n ≃ Option ι) :
    dvrOriginalSourceJacobianIdeal V V le_rfl hπ hu e = ⊤ := by
  let w : Fin n → V := fun i => (e i).elim π u
  have hw (i : Fin n) : (w i : K) = dvrCoordinates π u (e i) := by
    cases h : e i <;> simp [w, h, dvrCoordinates]
  let M : Matrix (Fin n) (Fin n) V :=
    Matrix.of fun i j => dvrLeafPartials V V le_rfl hπ hu e j (w i)
  have hM : M = 1 := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change partialDeriv (isTranscendenceBasis_dvrCoordinates hπ hu) (e j) (w i : K) =
      ((if i = j then 1 else 0 : V) : K)
    rw [hw i, partialDeriv_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, e.injective.ne hij]
  have hgen : M.det ∈ dvrOriginalSourceJacobianIdeal V V le_rfl hπ hu e :=
    Ideal.subset_span ⟨w, rfl⟩
  apply (Ideal.eq_top_iff_one _).mpr
  simpa only [hM, Matrix.det_one] using hgen

/-- Localization of the actual source makes its genuine all-original-functions DVR
Jacobian ideal the unit ideal, with no invertibility premise. -/
theorem dvrOriginalSourceJacobianIdeal_localization_eq_top
    (E : Subalgebra k K) (hEV : E ≤ V) (M : Submonoid E)
    (hlocal : letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
      IsLocalization M V)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u))
    (e : Fin n ≃ Option ι) :
    dvrOriginalSourceJacobianIdeal E V hEV hπ hu e = ⊤ := by
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsLocalization M V := hlocal
  have h := derivationSourceJacobianIdeal_source_localization
    (k := k) (A := V) M (dvrLeafPartials V V le_rfl hπ hu e)
  change dvrOriginalSourceJacobianIdeal E V hEV hπ hu e =
    dvrOriginalSourceJacobianIdeal V V le_rfl hπ hu e at h
  exact h.trans (dvrOriginalSourceJacobianIdeal_self_eq_top V hπ hu e)

/-- The actual determinant of the leaf coordinates in the genuine DVR partials is a
unit whenever the actual DVR is a localization of the actual etale leaf. -/
theorem isUnit_dvrLeafDet_of_localization
    (E : Subalgebra k K) (hEV : E ≤ V) (M : Submonoid E)
    (hlocal : letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
      IsLocalization M V)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u))
    (e : Fin n ≃ Option ι) (v : Fin n → E)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
    letI : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
    IsUnit (Matrix.of fun i j => dvrLeafPartials E V hEV hπ hu e j (v i)).det := by
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hself : affineRelativeJacobianIdeal (R := E) (etaleDifferentialBasis v hv) = ⊤ :=
    affineRelativeJacobianIdeal_self_eq_top_of_coordinate_basis
      (etaleDifferentialBasis v hv) v (etaleDifferentialBasis_apply v hv)
  have h := derivationSourceJacobianIdeal_eq (R := E) v hv (dvrLeafPartials E V hEV hπ hu e)
  rw [hself, Ideal.map_top, Ideal.mul_top] at h
  apply Ideal.span_singleton_eq_top.mp
  exact h.symm.trans (dvrOriginalSourceJacobianIdeal_localization_eq_top V E hEV M hlocal hπ hu e)

/-- At a genuine divisorial localization of an actual etale leaf, the sum of all
actual normalized coordinate orders is at most one. -/
theorem sum_addVal_leaf_le_one_of_localization
    (E : Subalgebra k K) (hEV : E ≤ V) (M : Submonoid E)
    (hlocal : letI : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
      IsLocalization M V)
    (hπ : Irreducible π) (hu : IsTranscendenceBasis k (residue V ∘ u))
    (e : Fin n ≃ Option ι) (v : Fin n → E)
    (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    (∑ i, addVal V (Subalgebra.inclusion hEV (v i))) ≤ 1 := by
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := sum_addVal_leaf_le_one_add_dvrLeafDet E V hEV hπ hu e v
  rw [addVal_eq_zero_iff.mpr (isUnit_dvrLeafDet_of_localization V E hEV M hlocal hπ hu e v hv),
    add_zero] at h
  exact h

end EnvelopeProperty.Char0
