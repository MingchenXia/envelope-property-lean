/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumResidueField
import EnvelopeProperty.Berkovich.SpectrumSupport

/-!
# Affine points as genuinely valued residue fields

Over any commutative ring, a prime together with a real ultrametric valuation on
its actual residue field gives a seminorm with exactly that support. This is a
homeomorphic description of the general spectrum for the canonical evaluation
topology. Ring homomorphisms act through actual induced residue-field maps.

An arbitrary prescribed base seminorm gives an exact closed relative subspace,
and algebra homomorphisms preserve it. These are affine point-space results;
no global scheme analytification or analytic structure sheaf is identified here.
-/

open scoped NNReal Topology
open Topology

noncomputable section

namespace EnvelopeProperty.Berkovich

/-- An actual affine prime together with a real valuation on its residue field. -/
structure ValuedPoint (A : Type*) [CommRing A] where
  prime : PrimeSpectrum A
  residueVal : Valuation prime.asIdeal.ResidueField ℝ≥0

namespace ValuedPoint

variable {A : Type*} [CommRing A]

/-- The value of an original-ring element in the valued residue field. -/
def eval (y : ValuedPoint A) (a : A) : ℝ≥0 :=
  y.residueVal (algebraMap A y.prime.asIdeal.ResidueField a)

/-- Evaluation in a valued residue field is a genuine original-ring seminorm. -/
def toSpectrum (y : ValuedPoint A) : Spectrum A :=
  Spectrum.ofValuation (y.residueVal.comap (algebraMap A y.prime.asIdeal.ResidueField))

@[simp]
theorem toSpectrum_val_apply (y : ValuedPoint A) (a : A) : (toSpectrum y).val a = eval y a := rfl

@[simp]
theorem eval_eq_zero_iff (y : ValuedPoint A) (a : A) : eval y a = 0 ↔ a ∈ y.prime.asIdeal := by
  rw [eval, Valuation.zero_iff, Ideal.algebraMap_residueField_eq_zero]

/-- The evaluation seminorm has exactly the stated prime, not merely a contained support. -/
@[simp]
theorem support_toSpectrum (y : ValuedPoint A) : Spectrum.support (toSpectrum y) = y.prime := by
  apply PrimeSpectrum.ext
  exact Ideal.ext fun a => eval_eq_zero_iff y a

/-- The actual support and induced residue-field valuation of a seminorm point. -/
def ofSpectrum (x : Spectrum A) : ValuedPoint A :=
  ⟨Spectrum.support x, x.residueValuation⟩

@[simp]
theorem ofSpectrum_prime (x : Spectrum A) : (ofSpectrum x).prime = Spectrum.support x := rfl

@[simp]
theorem eval_ofSpectrum (x : Spectrum A) (a : A) : eval (ofSpectrum x) a = x.val a :=
  Spectrum.residueValuation_algebraMap x a

@[simp]
theorem toSpectrum_ofSpectrum (x : Spectrum A) : toSpectrum (ofSpectrum x) = x :=
  Spectrum.ext_val (eval_ofSpectrum x)

/-- Values on the original ring determine the actual prime and entire residue-field valuation. -/
theorem toSpectrum_injective : Function.Injective (toSpectrum : ValuedPoint A → Spectrum A) := by
  rintro ⟨p, v⟩ ⟨q, w⟩ h
  have hp : p = q := (support_toSpectrum ⟨p, v⟩).symm.trans
    ((congrArg Spectrum.support h).trans (support_toSpectrum ⟨q, w⟩))
  subst q
  have hv : v = w := EnvelopeProperty.Valuation.ext_of_residueField p.asIdeal
    (fun a => congrArg (fun x : Spectrum A => x.val a) h)
  subst w
  rfl

@[simp]
theorem ofSpectrum_toSpectrum (y : ValuedPoint A) : ofSpectrum (toSpectrum y) = y :=
  toSpectrum_injective (toSpectrum_ofSpectrum (toSpectrum y))

/-- A genuine equivalence between valued residue-field points and real seminorm points. -/
def spectrumEquiv : ValuedPoint A ≃ Spectrum A where
  toFun := toSpectrum
  invFun := ofSpectrum
  left_inv := ofSpectrum_toSpectrum
  right_inv := toSpectrum_ofSpectrum

/-- The complete family of original-ring evaluation coordinates. -/
def toFun (y : ValuedPoint A) : A → ℝ≥0 := eval y

theorem toFun_injective : Function.Injective (toFun : ValuedPoint A → A → ℝ≥0) := by
  intro y z h
  exact toSpectrum_injective (Spectrum.ext_val fun a => congrFun h a)

/-- The canonical topology is the coarsest topology making every evaluation continuous. -/
instance : TopologicalSpace (ValuedPoint A) := TopologicalSpace.induced toFun inferInstance

theorem isInducing_toFun : IsInducing (toFun : ValuedPoint A → A → ℝ≥0) := ⟨rfl⟩

theorem isEmbedding_toFun : IsEmbedding (toFun : ValuedPoint A → A → ℝ≥0) :=
  ⟨isInducing_toFun, toFun_injective⟩

instance : T2Space (ValuedPoint A) := isEmbedding_toFun.t2Space

@[fun_prop]
theorem continuous_toFun : Continuous (toFun : ValuedPoint A → A → ℝ≥0) :=
  isInducing_toFun.continuous

@[fun_prop]
theorem continuous_eval (a : A) : Continuous (fun y : ValuedPoint A => eval y a) :=
  (continuous_apply a).comp continuous_toFun

/-- Continuity into valued points is exactly continuity of every original-ring evaluation. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → ValuedPoint A} :
    Continuous f ↔ ∀ a : A, Continuous (fun x => eval (f x) a) := by
  rw [isInducing_toFun.continuous_iff, continuous_pi_iff]
  rfl

@[fun_prop]
theorem continuous_toSpectrum : Continuous (toSpectrum : ValuedPoint A → Spectrum A) := by
  rw [Spectrum.continuous_iff]
  exact continuous_eval

@[fun_prop]
theorem continuous_ofSpectrum : Continuous (ofSpectrum : Spectrum A → ValuedPoint A) := by
  rw [continuous_iff]
  intro a
  simpa only [eval_ofSpectrum] using Spectrum.continuous_abs a

/-- The valued residue-field description is an actual homeomorphism for the evaluation topology. -/
def spectrumHomeomorph : ValuedPoint A ≃ₜ Spectrum A where
  __ := spectrumEquiv
  continuous_toFun := continuous_toSpectrum
  continuous_invFun := continuous_ofSpectrum

@[simp]
theorem spectrumHomeomorph_apply (y : ValuedPoint A) : spectrumHomeomorph y = toSpectrum y := rfl

@[simp]
theorem spectrumHomeomorph_symm_apply (x : Spectrum A) :
    spectrumHomeomorph.symm x = ofSpectrum x := rfl

@[fun_prop]
theorem continuous_prime : Continuous (fun y : ValuedPoint A => y.prime) := by
  have h := (Spectrum.continuous_support (A := A)).comp continuous_toSpectrum
  simpa only [Function.comp_def, support_toSpectrum] using h

section Pullback

variable {B : Type*} [CommRing B]

/-- Pull back the actual residue-field valuation along the induced residue-field homomorphism. -/
def comap (φ : A →+* B) (y : ValuedPoint B) : ValuedPoint A :=
  ⟨PrimeSpectrum.comap φ y.prime,
    y.residueVal.comap (Ideal.ResidueField.map
      (PrimeSpectrum.comap φ y.prime).asIdeal y.prime.asIdeal φ rfl)⟩

@[simp]
theorem comap_prime (φ : A →+* B) (y : ValuedPoint B) :
    (comap φ y).prime = PrimeSpectrum.comap φ y.prime := rfl

@[simp]
theorem eval_comap (φ : A →+* B) (y : ValuedPoint B) (a : A) :
    eval (comap φ y) a = eval y (φ a) := by
  change y.residueVal (Ideal.ResidueField.map _ _ φ _
    (algebraMap A (PrimeSpectrum.comap φ y.prime).asIdeal.ResidueField a)) = _
  exact congrArg y.residueVal (Ideal.ResidueField.map_algebraMap _ _ _ _ a)

@[simp]
theorem toSpectrum_comap (φ : A →+* B) (y : ValuedPoint B) :
    toSpectrum (comap φ y) = Spectrum.comap φ (toSpectrum y) :=
  Spectrum.ext_val (eval_comap φ y)

@[fun_prop]
theorem continuous_comap (φ : A →+* B) : Continuous (comap φ) := by
  rw [continuous_iff]
  intro a
  simpa only [eval_comap] using continuous_eval (φ a)

@[simp]
theorem comap_id (y : ValuedPoint A) : comap (RingHom.id A) y = y := by
  apply toSpectrum_injective
  rw [toSpectrum_comap, Spectrum.comap_id]

theorem comap_comp {C : Type*} [CommRing C] (φ : A →+* B) (ψ : B →+* C) (z : ValuedPoint C) :
    comap (ψ.comp φ) z = comap φ (comap ψ z) := by
  apply toSpectrum_injective
  rw [toSpectrum_comap, toSpectrum_comap, toSpectrum_comap, Spectrum.comap_comp]

end Pullback

section Relative

variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0)
variable (A : Type*) [CommRing A] [Algebra R A]

/-- Valued residue-field points whose original-ring evaluations restrict to the prescribed base. -/
def relativeLocus : Set (ValuedPoint A) :=
  {y | ∀ r : R, eval y (algebraMap R A r) = v r}

@[simp]
theorem mem_relativeLocus (y : ValuedPoint A) :
    y ∈ relativeLocus v A ↔ ∀ r : R, eval y (algebraMap R A r) = v r := Iff.rfl

theorem isClosed_relativeLocus : IsClosed (relativeLocus v A) := by
  change IsClosed (toSpectrum ⁻¹' EnvelopeProperty.Berkovich.relativeLocus v A)
  exact (EnvelopeProperty.Berkovich.isClosed_relativeLocus v A).preimage continuous_toSpectrum

end Relative

end ValuedPoint

/-- Actual valued residue-field points extending a prescribed base seminorm. -/
abbrev RelativeValuedPoint {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) (A : Type*)
    [CommRing A] [Algebra R A] : Type _ := ValuedPoint.relativeLocus v A

namespace RelativeValuedPoint

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
variable {A : Type*} [CommRing A] [Algebra R A]

/-- Restrict the genuine valued-point homeomorphism to the exact coefficient locus. -/
def spectrumHomeomorph : RelativeValuedPoint v A ≃ₜ RelativeSpectrum v A :=
  ValuedPoint.spectrumHomeomorph.subtype (fun _ => Iff.rfl)

@[simp]
theorem spectrumHomeomorph_apply_coe (y : RelativeValuedPoint v A) :
    (spectrumHomeomorph y : Spectrum A) = ValuedPoint.toSpectrum y.1 := rfl

@[simp]
theorem spectrumHomeomorph_symm_apply_coe (x : RelativeSpectrum v A) :
    (spectrumHomeomorph.symm x : ValuedPoint A) = ValuedPoint.ofSpectrum x.1 := rfl

/-- Prescribed valued points form a closed subspace of all valued residue-field points. -/
theorem isClosedEmbedding_subtypeVal :
    IsClosedEmbedding ((↑) : RelativeValuedPoint v A → ValuedPoint A) :=
  (ValuedPoint.isClosed_relativeLocus v A).isClosedEmbedding_subtypeVal

/-- Original-ring evaluation at a relative valued point. -/
abbrev eval (y : RelativeValuedPoint v A) (a : A) : ℝ≥0 := ValuedPoint.eval y.1 a

@[simp]
theorem eval_algebraMap (y : RelativeValuedPoint v A) (r : R) :
    eval y (algebraMap R A r) = v r := y.2 r

@[fun_prop]
theorem continuous_eval (a : A) : Continuous (fun y : RelativeValuedPoint v A => eval y a) :=
  (ValuedPoint.continuous_eval a).comp continuous_subtype_val

/-- All relative supports contract to the prime support of the prescribed base seminorm. -/
theorem prime_base (y : RelativeValuedPoint v A) :
    PrimeSpectrum.comap (algebraMap R A) y.1.prime =
      Spectrum.support (Spectrum.ofValuation v) := by
  have h := RelativeSpectrum.support_base (spectrumHomeomorph y)
  simpa only [RelativeSpectrum.support, spectrumHomeomorph_apply_coe,
    ValuedPoint.support_toSpectrum] using h

section Pullback

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- The actual residue-field pullback preserves the prescribed base along algebra maps. -/
def comap (φ : A →ₐ[R] B) (y : RelativeValuedPoint v B) : RelativeValuedPoint v A :=
  ⟨ValuedPoint.comap φ.toRingHom y.1, fun r => by
    rw [ValuedPoint.eval_comap]
    change ValuedPoint.eval y.1 (φ (algebraMap R A r)) = v r
    rw [φ.commutes]
    exact y.2 r⟩

@[simp]
theorem comap_coe (φ : A →ₐ[R] B) (y : RelativeValuedPoint v B) :
    (comap φ y : ValuedPoint A) = ValuedPoint.comap φ.toRingHom y.1 := rfl

@[simp]
theorem eval_comap (φ : A →ₐ[R] B) (y : RelativeValuedPoint v B) (a : A) :
    eval (comap φ y) a = eval y (φ a) := ValuedPoint.eval_comap φ.toRingHom y.1 a

@[simp]
theorem spectrumHomeomorph_comap (φ : A →ₐ[R] B) (y : RelativeValuedPoint v B) :
    spectrumHomeomorph (comap φ y) = RelativeSpectrum.comap φ (spectrumHomeomorph y) :=
  RelativeSpectrum.ext_val (eval_comap φ y)

@[fun_prop]
theorem continuous_comap (φ : A →ₐ[R] B) : Continuous (comap (v := v) φ) := by
  apply Continuous.subtype_mk
  exact (ValuedPoint.continuous_comap φ.toRingHom).comp continuous_subtype_val

@[simp]
theorem comap_id (y : RelativeValuedPoint v A) : comap (AlgHom.id R A) y = y :=
  Subtype.ext (ValuedPoint.comap_id y.1)

theorem comap_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (z : RelativeValuedPoint v C) :
    comap (ψ.comp φ) z = comap φ (comap ψ z) :=
  Subtype.ext (ValuedPoint.comap_comp φ.toRingHom ψ.toRingHom z.1)

end Pullback

end RelativeValuedPoint

end EnvelopeProperty.Berkovich
