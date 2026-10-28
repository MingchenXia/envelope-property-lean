import Mathlib.RingTheory.Kaehler.Basic

/-! Actual native Kähler module transport under genuine original algebra equivalences. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.KaehlerAlgebraEquivalence
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- The genuine native Kähler map with its actual original coefficient semilinearity. -/
def map (e : A ≃ₐ[R] B) : KaehlerDifferential R A →ₛₗ[e.toRingHom] KaehlerDifferential R B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
  let f := KaehlerDifferential.map R R A B
  exact { f.toAddMonoidHom with
    map_smul' := fun a w => by
      change f (a • w) = e a • f w
      rw [f.map_smul]
      exact (IsScalarTower.algebraMap_smul B a (f w)).symm }

/-- EVERY original universal differential has its actual mapped original value. -/
theorem map_D (e : A ≃ₐ[R] B) (a : A) :
    map e (KaehlerDifferential.D R A a) = KaehlerDifferential.D R B (e a) := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
  change KaehlerDifferential.map R R A B (KaehlerDifferential.D R A a) = _
  rw [KaehlerDifferential.map_D]
  rfl

private theorem left_inverse (e : A ≃ₐ[R] B) (w : KaehlerDifferential R A) :
    map e.symm (map e w) = w := by
  have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    rw [map_D, map_D, e.symm_apply_apply]
  | zero => rw [map_zero, map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, hz, hw]
  | smul a z _ hz =>
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hz]
    change e.symm (e a) • z = a • z
    rw [e.symm_apply_apply]

local instance inversePair (e : A ≃ₐ[R] B) : RingHomInvPair e.toRingHom e.symm.toRingHom where
  comp_eq := by ext a; exact e.symm_apply_apply a
  comp_eq₂ := by ext b; exact e.apply_symm_apply b

/-- The SAME actual native maps form a genuine original semilinear equivalence. -/
def equiv (e : A ≃ₐ[R] B) : KaehlerDifferential R A ≃ₛₗ[e.toRingHom] KaehlerDifferential R B where
  __ := map e
  invFun := map e.symm
  left_inv := left_inverse e
  right_inv := left_inverse e.symm

/-- The actual equivalence retains the genuine universal differential formula. -/
theorem equiv_D (e : A ≃ₐ[R] B) (a : A) :
    equiv e (KaehlerDifferential.D R A a) = KaehlerDifferential.D R B (e a) := map_D e a

/-- The actual inverse retains its genuine universal differential formula. -/
theorem equiv_symm_D (e : A ≃ₐ[R] B) (b : B) :
    (equiv e).symm (KaehlerDifferential.D R B b) = KaehlerDifferential.D R A (e.symm b) :=
  map_D e.symm b
end EnvelopeProperty.KaehlerAlgebraEquivalence
