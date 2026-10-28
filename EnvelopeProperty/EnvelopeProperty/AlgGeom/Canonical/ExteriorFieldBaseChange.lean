import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Actual whole exterior forms and morphism differentials under change of fields

The coefficient square is the actual algebra pushout. Every arbitrary
original form and wedge is retained by the literal Kähler comparison;
no fixed-base differential comparison is substituted for change of field.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.CanonicalGeometry

open scoped TensorProduct

universe u v

section Pushout

variable {k L A A' : Type u} [Field k] [Field L] [CommRing A] [CommRing A']
  [Algebra k L] [Algebra k A] [Algebra k A'] [Algebra L A'] [Algebra A A']
  [IsScalarTower k L A'] [IsScalarTower k A A'] [Algebra.IsPushout k L A A']

/-- The actual change-of-field Kähler comparison retains EVERY original whole differential form. -/
theorem kaehlerFieldBaseChange_one_tmul (ω : KaehlerDifferential k A) :
    KaehlerDifferential.tensorKaehlerEquiv k L A A' (1 ⊗ₜ[A] ω) =
      KaehlerDifferential.map k L A A' ω := by
  let F : KaehlerDifferential k A →ₗ[A] KaehlerDifferential L A' :=
    ((KaehlerDifferential.tensorKaehlerEquiv k L A A').toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A A' (KaehlerDifferential k A) 1)
  have hF : F = KaehlerDifferential.map k L A A' := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation k A)
    rintro _ ⟨a, rfl⟩
    change KaehlerDifferential.tensorKaehlerEquiv k L A A'
      (1 ⊗ₜ[A] KaehlerDifferential.D k A a) = _
    rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul, KaehlerDifferential.map_D]
  exact LinearMap.congr_fun hF ω

/-- The original differential basis is transported through the actual field pushout. -/
def fieldDifferentialBasis {I : Type v} (b : Module.Basis I A (KaehlerDifferential k A)) :
    Module.Basis I A' (KaehlerDifferential L A') :=
  (b.baseChange A').map (KaehlerDifferential.tensorKaehlerEquiv k L A A')

/-- Every actual new basis vector is exactly the image of the SAME original whole form. -/
theorem fieldDifferentialBasis_apply {I : Type v}
    (b : Module.Basis I A (KaehlerDifferential k A)) (i : I) :
    fieldDifferentialBasis (L := L) (A' := A') b i = KaehlerDifferential.map k L A A' (b i) := by
  rw [fieldDifferentialBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  exact kaehlerFieldBaseChange_one_tmul _

/-- Actual full scalar extension of the original exterior module under the SAME changed field. -/
def exteriorKaehlerFieldBaseChangeEquiv {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential k A)) (n : ℕ) :
    A' ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) ≃ₗ[A']
      (⋀[A']^n (KaehlerDifferential L A')) :=
  (exteriorBasisBaseChangeEquiv b n).trans
    (exteriorLinearEquiv (KaehlerDifferential.tensorKaehlerEquiv k L A A') n)

/-- Every wedge of arbitrary WHOLE original forms retains its literal actual change-of-field images. -/
theorem exteriorKaehlerFieldBaseChangeEquiv_wedge {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential k A)) (n : ℕ)
    (ω : Fin n → KaehlerDifferential k A) :
    exteriorKaehlerFieldBaseChangeEquiv (L := L) (A' := A') b n
      (1 ⊗ₜ[A] exteriorPower.ιMulti A n ω) =
      exteriorPower.ιMulti A' n (fun i => KaehlerDifferential.map k L A A' (ω i)) := by
  rw [exteriorKaehlerFieldBaseChangeEquiv, LinearEquiv.trans_apply,
    exteriorBasisBaseChangeEquiv_wedge, exteriorLinearEquiv_ιMulti]
  congr 1
  funext i
  exact kaehlerFieldBaseChange_one_tmul _

/-- The SAME original functions have their exact actual universal differential wedge after field change. -/
theorem exteriorKaehlerFieldBaseChangeEquiv_wedge_D {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential k A)) (n : ℕ) (a : Fin n → A) :
    exteriorKaehlerFieldBaseChangeEquiv (L := L) (A' := A') b n
      (1 ⊗ₜ[A] exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (a i))) =
      exteriorPower.ιMulti A' n (fun i => KaehlerDifferential.D L A' (algebraMap A A' (a i))) := by
  rw [exteriorKaehlerFieldBaseChangeEquiv_wedge]
  simp only [KaehlerDifferential.map_D]

end Pushout

section Naturality

variable {k L R A R' A' : Type u} [Field k] [Field L]
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra k L] [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
  [Algebra k R'] [Algebra L R'] [Algebra R R'] [IsScalarTower k L R'] [IsScalarTower k R R']
  [Algebra k A'] [Algebra L A'] [Algebra A A'] [IsScalarTower k L A'] [IsScalarTower k A A']
  [Algebra R' A'] [IsScalarTower L R' A'] [Algebra R A']
  [IsScalarTower R R' A'] [IsScalarTower R A A']

/-- The ENTIRE original morphism differential square commutes under the actual coefficient field change. -/
theorem kaehlerFieldBaseChange_naturality (ω : KaehlerDifferential k R) :
    KaehlerDifferential.map L L R' A' (KaehlerDifferential.map k L R R' ω) =
      KaehlerDifferential.map k L A A' (KaehlerDifferential.map k k R A ω) := by
  have h : ((KaehlerDifferential.map L L R' A').restrictScalars R).comp
      (KaehlerDifferential.map k L R R') =
        ((KaehlerDifferential.map k L A A').restrictScalars R).comp
          (KaehlerDifferential.map k k R A) := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation k R)
    rintro _ ⟨r, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, KaehlerDifferential.map_D]
    rw [← IsScalarTower.algebraMap_apply R R' A', ← IsScalarTower.algebraMap_apply R A A']
  exact LinearMap.congr_fun h ω

end Naturality

end EnvelopeProperty.CanonicalGeometry
