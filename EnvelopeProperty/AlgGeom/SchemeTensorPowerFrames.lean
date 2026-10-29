import EnvelopeProperty.Berkovich.SchemeResidueFrameTransition
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms

/-! # Actual entire original tensor-power frames and their transition units -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.SchemeTensorPowerFrames
open SchemeModuleFrameCoefficients CanonicalGeometry
open Berkovich.SchemeResidueFrameComparison Berkovich.SchemeResidueFrameTransition
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The actual original whole frame of the native tensor, using true structure multiplication. -/
def tensorFrame {X : Scheme.{u}} {P Q : X.Modules}
    (e : P ≅ unitObj X) (d : Q ≅ unitObj X) : P ⊗ Q ≅ unitObj X :=
  (e ⊗ᵢ d) ≪≫ ModularCurves.unitObjTensorIso X

/-- Actual inverse-frame unit sections transport through any true preceding module iso. -/
theorem unitSection_precompIso {X : Scheme.{u}} {P Q : X.Modules}
    (a : P ≅ Q) (e : Q ≅ unitObj X) : unitSection (a ≪≫ e) = a.inv.app ⊤ (unitSection e) := rfl

/-- Genuine pure tensor coefficients in the actual tensor frame multiply. -/
theorem tensorFrame_coefficient {X : Scheme.{u}} {P Q : X.Modules}
    (e : P ≅ unitObj X) (d : Q ≅ unitObj X) (s : Γ(P, ⊤)) (t : Γ(Q, ⊤)) :
    coefficient (tensorFrame e d) (ModularCurves.tensorSection P Q ⊤ s t) =
      coefficient e s * coefficient d t := by
  have hn := ModularCurves.tensorSection_map e.hom d.hom ⊤ s t
  have hs := congrArg (fun z => (ModularCurves.unitObjTensorIso X).hom.app ⊤ z) hn
  exact hs.trans (ModularCurves.unitObjTensorIso_hom_tensorSection X ⊤ _ _)

/-- The genuine entire tensor-frame unit is the actual pure tensor of the original frame units. -/
theorem tensorFrame_unitSection {X : Scheme.{u}} {P Q : X.Modules}
    (e : P ≅ unitObj X) (d : Q ≅ unitObj X) :
    unitSection (tensorFrame e d) = ModularCurves.tensorSection P Q ⊤ (unitSection e) (unitSection d) := by
  have hi : Function.Injective ((tensorFrame e d).hom.app ⊤) :=
    (ConcreteCategory.bijective_of_isIso ((tensorFrame e d).hom.app ⊤)).injective
  apply hi
  exact (coefficient_unitSection (tensorFrame e d)).trans
    ((tensorFrame_coefficient e d (unitSection e) (unitSection d)).trans
      (by rw [coefficient_unitSection, coefficient_unitSection, one_mul])).symm

/-- The genuine original explicit tensor powers carry actual entire recursively constructed frames. -/
def powerFrame {X : Scheme.{u}} {P : X.Modules} (e : P ≅ unitObj X) :
    (n : ℕ) → bundleTensorPower P n ≅ unitObj X
  | 0 => Iso.refl _
  | n + 1 => (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).symm ≪≫
      tensorFrame (powerFrame e n) e

/-- The true inverse power-frame unit is the original explicit pure tensor of the previous units. -/
theorem powerFrame_unitSection_succ {X : Scheme.{u}} {P : X.Modules}
    (e : P ≅ unitObj X) (n : ℕ) :
    unitSection (powerFrame e (n + 1)) =
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).hom.app ⊤
        (ModularCurves.tensorSection (bundleTensorPower P n) P ⊤
          (unitSection (powerFrame e n)) (unitSection e)) := by
  exact (unitSection_precompIso _ _).trans
    (congrArg (fun z => (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).hom.app ⊤ z)
      (tensorFrame_unitSection (powerFrame e n) e))

section Spec
variable {A : Type u} [CommRing A] {P Q : (Spec (.of A)).Modules}

/-- The same genuine preceding original iso cancels in actual frame transition units. -/
theorem transitionUnit_precompIso (a : P ≅ Q) (e₀ e₁ : Q ≅ unitObj (Spec (.of A))) :
    transitionUnit (a ≪≫ e₀) (a ≪≫ e₁) = transitionUnit e₀ e₁ := by
  apply Units.ext
  have hc := congrArg (fun f : Q ⟶ Q =>
    (Scheme.ΓSpecIso (.of A)).hom (e₁.hom.app ⊤ (f.app ⊤ (unitSection e₀)))) a.inv_hom_id
  exact (transitionUnit_val (a ≪≫ e₀) (a ≪≫ e₁)).trans
    (hc.trans (transitionUnit_val e₀ e₁).symm)

/-- Genuine actual entire tensor frames multiply their genuinely derived original transition units. -/
theorem transitionUnit_tensorFrame (e₀ e₁ : P ≅ unitObj (Spec (.of A)))
    (d₀ d₁ : Q ≅ unitObj (Spec (.of A))) :
    transitionUnit (tensorFrame e₀ d₀) (tensorFrame e₁ d₁) =
      transitionUnit e₀ e₁ * transitionUnit d₀ d₁ := by
  apply Units.ext
  have hu := congrArg (fun s : Γ(P ⊗ Q, ⊤) =>
    (Scheme.ΓSpecIso (.of A)).hom ((tensorFrame e₁ d₁).hom.app ⊤ s)) (tensorFrame_unitSection e₀ d₀)
  have hc := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom
    (tensorFrame_coefficient e₁ d₁ (unitSection e₀) (unitSection d₀))
  have hm := (Scheme.ΓSpecIso (.of A)).hom.hom.map_mul
    (coefficient e₁ (unitSection e₀)) (coefficient d₁ (unitSection d₀))
  have ht := congrArg₂ (fun a b : A => a * b)
    (transitionUnit_val e₀ e₁).symm (transitionUnit_val d₀ d₁).symm
  exact (transitionUnit_val (tensorFrame e₀ d₀) (tensorFrame e₁ d₁)).trans
    (hu.trans (hc.trans (hm.trans ht)))

/-- ACTUAL entire original power frames have exactly the degree-one genuine transition unit to that power. -/
theorem transitionUnit_powerFrame (e₀ e₁ : P ≅ unitObj (Spec (.of A))) (n : ℕ) :
    transitionUnit (powerFrame e₀ n) (powerFrame e₁ n) = transitionUnit e₀ e₁ ^ n := by
  induction n with
  | zero =>
    change transitionUnit (Iso.refl (unitObj (Spec (.of A)))) (Iso.refl (unitObj (Spec (.of A)))) = _
    exact (transitionUnit_self _).trans (pow_zero _).symm
  | succ n ih =>
    have ht := transitionUnit_precompIso
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower P n) P).symm
      (tensorFrame (powerFrame e₀ n) e₀) (tensorFrame (powerFrame e₁ n) e₁)
    have hm := transitionUnit_tensorFrame (powerFrame e₀ n) (powerFrame e₁ n) e₀ e₁
    have hp := congrArg (fun u : Aˣ => u * transitionUnit e₀ e₁) ih
    exact ht.trans (hm.trans (hp.trans (pow_succ _ _).symm))

/-- EVERY actual valuation derives true power coherence for the actual power-frame transition factors. -/
theorem transitionUnit_powerFrame_value (e₀ e₁ : P ≅ unitObj (Spec (.of A)))
    (ν : Valuation A ℝ≥0) (n : ℕ) :
    ν (transitionUnit (powerFrame e₀ n) (powerFrame e₁ n) : A) = ν (transitionUnit e₀ e₁ : A) ^ n := by
  have h := congrArg (fun u : Aˣ => ν (u : A)) (transitionUnit_powerFrame e₀ e₁ n)
  exact h.trans (ν.map_pow _ n)
end Spec

end EnvelopeProperty.SchemeTensorPowerFrames
