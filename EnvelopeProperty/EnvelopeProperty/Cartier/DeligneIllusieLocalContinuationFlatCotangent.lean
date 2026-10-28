import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDifferential
import Mathlib.RingTheory.Smooth.Basic

/-! # Actual cotangent annihilators derived from projectivity and smoothness

The projective splitting is produced by projectivity. The cotangent reduction is
the original Kaehler map. No cotangent flatness or differential comparison is an input.
-/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationFlatCotangent

open FrobeniusLiftDifference

universe u v w z
variable {p : ℕ} {S : Type u} {B : Type v} [CommRing S] [CommRing B]
  {M : Type w} {N : Type z} [AddCommMonoid M] [AddCommMonoid N]
  [Module S M] [Module B N]

/-- A genuine projective splitting transfers the SCALAR annihilator condition to every
actual semilinear reduction. No splitting, module annihilator or comparison is an input. -/
theorem semilinear_eq_zero_of_projective [Module.Projective S M]
    (q : S →+* B) (hAnn : ∀ s, (p : S)*s = 0 → q s = 0)
    (ρ : M →ₛₗ[q] N) (m : M) (hm : (p : S) • m = 0) : ρ m = 0 := by
  classical
  obtain ⟨j, hj⟩ := Module.Projective.out (R := S) (P := M)
  have hjzero : (p : S) • j m = 0 := by
    rw [← map_smul, hm, map_zero]
  have hcoef (i : M) : q ((j m) i) = 0 := by
    apply hAnn
    have h := congrArg (fun v : M →₀ S => v i) hjzero
    simpa only [Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] using h
  calc
    ρ m = ρ (Finsupp.linearCombination S (id : M → M) (j m)) :=
      congrArg ρ (hj m).symm
    _ = (j m).sum (fun i c => q c • ρ i) := by
      simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smulₛₗ, id_eq]
    _ = 0 := by
      change (j m).support.sum (fun i => q ((j m) i) • ρ i) = 0
      apply Finset.sum_eq_zero
      intro i hi
      rw [hcoef i, zero_smul]

/-- The same result for a native linear map into the ORIGINAL compatible algebra-module action. -/
theorem linearMap_eq_zero_of_projective [Module.Projective S M] [Algebra S B]
    [Module S N] [IsScalarTower S B N]
    (hAnn : ∀ s, (p : S)*s = 0 → algebraMap S B s = 0)
    (L : M →ₗ[S] N) (m : M) (hm : (p : S) • m = 0) : L m = 0 := by
  let ρ : M →ₛₗ[algebraMap S B] N :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun s m => by
        rw [map_smul]
        exact (IsScalarTower.algebraMap_smul B s (L m)).symm }
  exact semilinear_eq_zero_of_projective (algebraMap S B) hAnn ρ m hm

section Cotangent

variable (C K : Type*) [CommRing C] [CommRing K]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra K B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]

/-- Projectivity of the actual lifted cotangent module DERIVES the missing annihilator
condition for the SAME actual native cotangent reduction and coefficient actions. -/
theorem cotangent_annihilator_of_projective
    [Module.Projective S (KaehlerDifferential C S)]
    (b : FlatReduction p S B) (hq : algebraMap S B = b.map)
    (ω : KaehlerDifferential C S) (hω : (p : S) • ω = 0) :
    DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K ω = 0 := by
  apply linearMap_eq_zero_of_projective (B := B) (M := KaehlerDifferential C S)
    (N := KaehlerDifferential K B) _
    (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) ω hω
  intro s hs
  rw [hq]
  exact b.flat s hs

/-- Actual formal smoothness supplies projectivity of Ω[S/C] through Mathlib's native theorem. -/
theorem cotangent_annihilator_of_formallySmooth [Algebra.FormallySmooth C S]
    (b : FlatReduction p S B) (hq : algebraMap S B = b.map)
    (ω : KaehlerDifferential C S) (hω : (p : S) • ω = 0) :
    DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K ω = 0 :=
  cotangent_annihilator_of_projective C K b hq ω hω

/-- In particular, the ORIGINAL smooth lifted algebra derives the entire cotangent condition. -/
theorem cotangent_annihilator_of_smooth [Algebra.Smooth C S]
    (b : FlatReduction p S B) (hq : algebraMap S B = b.map)
    (ω : KaehlerDifferential C S) (hω : (p : S) • ω = 0) :
    DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K ω = 0 :=
  cotangent_annihilator_of_formallySmooth C K b hq ω hω

variable {R : Type w} {A : Type z} [CommRing R] [CommRing A]
  (a : Reduction p R A) (b : FlatReduction p S B) (φ : A →+* B) (f g : R →+* S)
  (hf : ∀ x, b.map (f x) = φ (a.map x))
  (hg : ∀ x, b.map (g x) = φ (a.map x)) (hq : algebraMap S B = b.map)

include hq

/-- The original all-function differential comparison now consumes honest smooth lifting data,
with NO cotangent-annihilator or differential-comparison certificate. -/
theorem differentialDifference_comparison_of_formallySmooth [Algebra.FormallySmooth C S]
    (x : A) :
    DeligneIllusieLocalContinuationDifferential.differentialDifference C K a b φ f g hf hg x =
      KaehlerDifferential.D K B (difference a b φ f g hf hg x) := by
  exact DeligneIllusieLocalContinuationDifferential.differentialDifference_comparison
    C K a b φ f g hf hg hq (cotangent_annihilator_of_formallySmooth C K b hq) x

/-- Difference of TWO ACTUAL divided differentials follows from actual smooth lifting data. -/
theorem two_dividedDifferentials_comparison_of_formallySmooth [Algebra.FormallySmooth C S]
    (x : R) (ηf ηg : KaehlerDifferential C S)
    (hηf : (p : S) • ηf = KaehlerDifferential.D C S (f x))
    (hηg : (p : S) • ηg = KaehlerDifferential.D C S (g x)) :
    DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K ηf -
        DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K ηg =
      KaehlerDifferential.D K B (difference a b φ f g hf hg (a.map x)) := by
  exact DeligneIllusieLocalContinuationDifferential.two_dividedDifferentials_comparison
    C K a b φ f g hf hg hq (cotangent_annihilator_of_formallySmooth C K b hq)
      x ηf ηg hηf hηg

end Cotangent
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationFlatCotangent
