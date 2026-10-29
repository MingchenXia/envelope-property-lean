import Mathlib.RingTheory.Kaehler.Basic

/-!
# Kaehler Base Ring Equivalence

Actual original Kähler modules under an actual coefficient-ring equivalence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.KaehlerBaseRingEquivalence

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R A] [Algebra S A]
variable (e : R ≃+* S) (h : ∀ r : R, algebraMap S A (e r) = algebraMap R A r)

/-- The original universal map from the first base to the equivalent second base. -/
def map : KaehlerDifferential R A →ₗ[A] KaehlerDifferential S A := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq (fun r => (h r).symm)
  exact ((KaehlerDifferential.D S A).restrictScalars R).liftKaehlerDifferential

/-- Every original universal differential has its SAME original value under base equivalence. -/
theorem map_D (a : A) : map e h (KaehlerDifferential.D R A a) =
    KaehlerDifferential.D S A a := by
  unfold map
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl

include h in
private theorem inverse_compat (s : S) :
    algebraMap R A (e.symm s) = algebraMap S A s := by
  rw [← h, e.apply_symm_apply]

private theorem left_inverse :
    (map e.symm (inverse_compat e h)).comp (map e h) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro a
  change map e.symm (inverse_compat e h) (map e h (KaehlerDifferential.D R A a)) =
    KaehlerDifferential.D R A a
  rw [map_D, map_D]

private theorem right_inverse :
    (map e h).comp (map e.symm (inverse_compat e h)) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro a
  change map e h (map e.symm (inverse_compat e h) (KaehlerDifferential.D S A a)) =
    KaehlerDifferential.D S A a
  rw [map_D, map_D]

/-- The SAME actual universal maps form an original A-linear equivalence. -/
def equiv : KaehlerDifferential R A ≃ₗ[A] KaehlerDifferential S A where
  __ := map e h
  invFun := map e.symm (inverse_compat e h)
  left_inv a := LinearMap.congr_fun (left_inverse e h) a
  right_inv a := LinearMap.congr_fun (right_inverse e h) a

/-- The genuine equivalence retains every original universal differential. -/
theorem equiv_D (a : A) : equiv e h (KaehlerDifferential.D R A a) =
    KaehlerDifferential.D S A a := map_D e h a

/-- The actual inverse retains every original universal differential as well. -/
theorem equiv_symm_D (a : A) : (equiv e h).symm (KaehlerDifferential.D S A a) =
    KaehlerDifferential.D R A a := map_D e.symm (inverse_compat e h) a

end EnvelopeProperty.KaehlerBaseRingEquivalence
