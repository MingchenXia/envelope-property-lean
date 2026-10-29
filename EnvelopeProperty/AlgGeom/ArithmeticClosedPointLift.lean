import EnvelopeProperty.AlgGeom.ArithmeticClosedPoints
import EnvelopeProperty.DeligneIllusie.WittTwo
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # The original arithmetic closed point lifts to the original length-two Witt ring

The only Witt base imported here is the already-published literal truncated
Witt ring. Native formal smoothness constructs an actual lift of the original
quotient map, and its image of the original principal-open element is a unit.
No family descent, global Cartier/DI, or vanishing endpoint is asserted.
-/

noncomputable section
namespace EnvelopeProperty.ArithmeticClosedPointLift
open DeligneIllusie

private theorem reduction_kernel_square_zero (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [CharP k p] [PerfectRing k p] :
    RingHom.ker (WittTwo.reduction p k) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, ha⟩ := (WittTwo.exists_mul_prime_iff p k x).mpr hx
  obtain ⟨b, hb⟩ := (WittTwo.exists_mul_prime_iff p k y).mpr hy
  change x * y = 0
  rw [ha, hb]
  calc
    (a * p) * (b * p) = (a * b) * (p : WittTwo.Ring p k) ^ 2 := by ring
    _ = 0 := by rw [WittTwo.prime_square_zero, mul_zero]

private theorem isUnit_of_reduction_ne_zero (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
    (x : WittTwo.Ring p k) (hx : WittTwo.reduction p k x ≠ 0) : IsUnit x := by
  let e := (WittTwo.reduction p k).quotientKerEquivOfSurjective
    (WittTwo.reduction_surjective p k)
  have hu : IsUnit (WittTwo.reduction p k x) := isUnit_iff_ne_zero.mpr hx
  have hq : IsUnit (Ideal.Quotient.mk (RingHom.ker (WittTwo.reduction p k)) x) := by
    have h := hu.map e.symm.toRingHom
    change IsUnit (e.symm (WittTwo.reduction p k x)) at h
    simpa only [e, RingHom.quotientKerEquivOfSurjective_symm_apply] using h
  exact (IsNilpotent.isUnit_quotient_mk_iff
    ⟨2, reduction_kernel_square_zero p k⟩).mp hq

/-- The original integer-smooth domain internally produces an arbitrarily large-characteristic
closed point, its literal residue field, and an actual W2 point with the original reduction square
and an invertible image of the original principal-open element. -/
theorem exists_large_characteristic_witt_lift
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℤ R] [Algebra.FiniteType ℤ R] [Algebra.Smooth ℤ R]
    (r : R) (hr : r ≠ 0) (N : ℕ) :
    ∃ (m : MaximalSpectrum R) (p : ℕ) (hp : Fact p.Prime),
      N < p ∧ r ∉ m.asIdeal ∧
        ∃ (_hc : CharP (R ⧸ m.asIdeal) p) (_hf : Finite (R ⧸ m.asIdeal)),
          letI : Fact p.Prime := hp
          letI : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
          ∃ lifted : R →+* WittTwo.Ring p (R ⧸ m.asIdeal),
            (WittTwo.reduction p (R ⧸ m.asIdeal)).comp lifted = Ideal.Quotient.mk m.asIdeal ∧
              IsUnit (lifted r) := by
  obtain ⟨m, p, hp, hNp, hrm, hc, hf⟩ :=
    ArithmeticClosedPoints.exists_large_characteristic_closed_point r hr N
  refine ⟨m, p, ⟨hp⟩, hNp, hrm, hc, hf, ?_⟩
  let k := R ⧸ m.asIdeal
  let : Field k := Ideal.Quotient.field m.asIdeal
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := hc
  have : Finite k := hf
  let φ : R →ₐ[ℤ] k :=
    { Ideal.Quotient.mk m.asIdeal with commutes' := fun z => by simp }
  let ρ : WittTwo.Ring p k →ₐ[ℤ] k :=
    { WittTwo.reduction p k with commutes' := fun z => by simp }
  let lifted : R →ₐ[ℤ] WittTwo.Ring p k :=
    Algebra.FormallySmooth.liftOfSurjective φ ρ (WittTwo.reduction_surjective p k)
      ⟨2, reduction_kernel_square_zero p k⟩
  have hsquare : (WittTwo.reduction p k).comp lifted.toRingHom = Ideal.Quotient.mk m.asIdeal :=
    congrArg AlgHom.toRingHom (Algebra.FormallySmooth.comp_liftOfSurjective φ ρ
      (WittTwo.reduction_surjective p k) ⟨2, reduction_kernel_square_zero p k⟩)
  refine ⟨lifted.toRingHom, hsquare, ?_⟩
  apply isUnit_of_reduction_ne_zero p k
  have heval := RingHom.congr_fun hsquare r
  change WittTwo.reduction p k (lifted.toRingHom r) = Ideal.Quotient.mk m.asIdeal r at heval
  rw [heval]
  exact fun h => hrm (Ideal.Quotient.eq_zero_iff_mem.mp h)

end EnvelopeProperty.ArithmeticClosedPointLift
