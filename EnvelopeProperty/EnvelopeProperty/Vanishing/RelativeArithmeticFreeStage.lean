import EnvelopeProperty.AlgGeom.ArithmeticClosedPointLift
import TauCeti.RingTheory.Spectrum.Prime.GenericFreeness

/-! # A produced Witt point in finitely many actual relative free loci

The finite modules are finite over a separate finite-type algebra.  No
finiteness over the arithmetic coefficient domain, domain hypothesis on
that separate algebra, or finite-rank freeness is required.
-/

noncomputable section
open Topology TopologicalSpace
universe u v w z

namespace EnvelopeProperty.Vanishing.RelativeArithmeticFreeStage

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {ι : Type w} [Finite ι]
    (M : ι → Type z) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, Module B (M i)]
    [∀ i, IsScalarTower A B (M i)] [∀ i, Module.Finite B (M i)]

include B

/-- Actual generic freeness produces one principal open on which all the
specified relative finite modules are free over the local coefficient rings. -/
theorem exists_simultaneous_free_principal_open :
    ∃ a : A, a ≠ 0 ∧ ∀ P : PrimeSpectrum A, a ∉ P.asIdeal →
      ∀ i, Module.Free (Localization.AtPrime P.asIdeal)
        (LocalizedModule P.asIdeal.primeCompl (M i)) := by
  let η : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  have hηmin : (⊥ : Ideal A) ∈ minimalPrimes A := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  let U : Set (PrimeSpectrum A) := ⋂ i, interior (Module.freeLocus A (M i))
  have hU : IsOpen U := isOpen_iInter_of_finite fun _ => isOpen_interior
  have hηU : η ∈ U := Set.mem_iInter.mpr fun i =>
    mem_interior_iff_mem_nhds.mpr
      (Module.freeLocus_mem_nhds_of_mem_minimalPrimes (B := B) (M i) hηmin)
  obtain ⟨S, hS⟩ := (PrimeSpectrum.isOpen_iff U).mp hU
  have hSnot : ¬ S ⊆ (⊥ : Ideal A) := by
    intro hs
    have hηc : η ∈ Uᶜ := by
      rw [hS]
      exact hs
    exact hηc hηU
  obtain ⟨a, haS, ha⟩ := Set.not_subset.mp hSnot
  have ha0 : a ≠ 0 := by
    intro hzero
    apply ha
    change a ∈ (⊥ : Ideal A)
    simpa only [hzero] using (⊥ : Ideal A).zero_mem
  refine ⟨a, ha0, ?_⟩
  intro P haP i
  have hPU : P ∈ U := by
    by_contra hP
    have hPZ : P ∈ PrimeSpectrum.zeroLocus S := by
      rw [← hS]
      exact hP
    exact haP (hPZ haS)
  have hmem : P ∈ Module.freeLocus A (M i) :=
    interior_subset (Set.mem_iInter.mp hPU i)
  exact hmem

variable [CharZero A] [Algebra ℤ A] [Algebra.FiniteType ℤ A] [Algebra.Smooth ℤ A]

/-- The same actual coefficient domain supplies a large-characteristic closed
point and Witt lift inside every prescribed principal open, with simultaneous
arbitrary-rank local freeness of the relative finite modules at that point. -/
theorem exists_simultaneous_free_witt_point (s : A) (hs : s ≠ 0) (N : ℕ) :
    ∃ (P : MaximalSpectrum A) (p : ℕ) (hp : Fact p.Prime),
      N < p ∧ s ∉ P.asIdeal ∧
        (∀ i, Module.Free (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl (M i))) ∧
        ∃ (_hc : CharP (A ⧸ P.asIdeal) p) (_hf : Finite (A ⧸ P.asIdeal)),
          letI : Fact p.Prime := hp
          letI : Field (A ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
          ∃ lifted : A →+* DeligneIllusie.WittTwo.Ring p (A ⧸ P.asIdeal),
            (DeligneIllusie.WittTwo.reduction p (A ⧸ P.asIdeal)).comp lifted =
              Ideal.Quotient.mk P.asIdeal := by
  obtain ⟨a, ha, hfree⟩ := exists_simultaneous_free_principal_open (A := A) (B := B) M
  obtain ⟨P, p, hp, hNp, hsaP, hc, hf, lifted, hred, _⟩ :=
    ArithmeticClosedPointLift.exists_large_characteristic_witt_lift
      (s * a) (mul_ne_zero hs ha) N
  have hsP : s ∉ P.asIdeal := fun h => hsaP (P.asIdeal.mul_mem_right a h)
  have haP : a ∉ P.asIdeal := fun h => hsaP (P.asIdeal.mul_mem_left s h)
  exact ⟨P, p, hp, hNp, hsP, hfree ⟨P.asIdeal, inferInstance⟩ haP,
    hc, hf, lifted, hred⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticFreeStage
