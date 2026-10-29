import EnvelopeProperty.Vanishing.FrobeniusLineComparison
import EnvelopeProperty.Vanishing.FrobeniusLineCore

/-! # Equality of actual pulled and tensor-power line-frame transitions

The local comparison is independent of the original rank-one frame.  This
is the common-transition calculation required before geometric gluing.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.FrobeniusLineComparison

open CanonicalGeometry FrobeniusLineCore Cartier
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Tensoring two actual frame changes multiplies their actual original
structure-ring scalars. -/
theorem tensorFrame_hom_eq_comp_scalars {X : Scheme.{u}} {L M : X.Modules}
    (e e' : L ≅ unitObj X) (g g' : M ≅ unitObj X) (a b : Γ(X, ⊤))
    (he : e.hom = e'.hom ≫ ModularCurves.unitEndomorphismOfTopSection a)
    (hg : g.hom = g'.hom ≫ ModularCurves.unitEndomorphismOfTopSection b) :
    (tensorFrame e g).hom =
      (tensorFrame e' g').hom ≫ ModularCurves.unitEndomorphismOfTopSection (a * b) := by
  have ht : e.hom ⊗ₘ g.hom = (e'.hom ⊗ₘ g'.hom) ≫
      (ModularCurves.unitEndomorphismOfTopSection a ⊗ₘ
        ModularCurves.unitEndomorphismOfTopSection b) := by
    rw [he, hg, ← tensorHom_comp_tensorHom]
  simp only [tensorFrame, Iso.trans_hom, tensorIso_hom, Category.assoc]
  rw [ht]
  simp only [Category.assoc]
  rw [ModularCurves.unitObjTensorIso_hom_comp_scalars]

/-- Actual tensor-power frames raise a genuine frame transition scalar to
the literal power, including the zero power. -/
theorem powerFrame_hom_eq_comp_scalar {X : Scheme.{u}} {L : X.Modules}
    (e e' : L ≅ unitObj X) (a : Γ(X, ⊤))
    (he : e.hom = e'.hom ≫ ModularCurves.unitEndomorphismOfTopSection a) (m : ℕ) :
    (powerFrame e m).hom =
      (powerFrame e' m).hom ≫ ModularCurves.unitEndomorphismOfTopSection (a ^ m) := by
  induction m with
  | zero =>
    change 𝟙 (unitObj X) =
      𝟙 (unitObj X) ≫ ModularCurves.unitEndomorphismOfTopSection (a ^ 0)
    rw [pow_zero, ModularCurves.unitEndomorphismOfTopSection_one, Category.comp_id]
  | succ m ih =>
    have ht := tensorFrame_hom_eq_comp_scalars (powerFrame e m) (powerFrame e' m)
      e e' (a ^ m) a ih he
    change (ModularCurves.monoidalTensorObjIso (bundleTensorPower L m) L).inv ≫
      (tensorFrame (powerFrame e m) e).hom =
        ((ModularCurves.monoidalTensorObjIso (bundleTensorPower L m) L).inv ≫
          (tensorFrame (powerFrame e' m) e').hom) ≫ _
    rw [ht, pow_succ, Category.assoc]

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The exact original relative-to-absolute comparison on every tensor
power, including the actual structure-module comparison in degree zero. -/
def relativePullbackPowerIso (L : X.Modules) (m : ℕ) :
    (pullback (SchemeRelativeFrobenius.map p f)).obj
        (bundleTensorPower (twistedLine f p L) m) ≅
      bundleTensorPower ((pullback (SchemeFrobenius.map f p)).obj L) m :=
  BundleTensorPowerPullback.pullbackIso (SchemeRelativeFrobenius.map p f)
    (twistedLine f p L) m ≪≫
      BundleTensorPowerPullback.powerIso (relativePullbackIso f p L) m

/-- The actual coefficient-preserving comparison on a whole framed open. -/
def frameComparison {L : X.Modules} (e : L ≅ unitObj X) :
    (pullback (SchemeFrobenius.map f p)).obj L ≅ bundleTensorPower L p :=
  pulledFrame f p e ≪≫ (powerFrame e p).symm

/-- The local Frobenius/power comparison is independent of the chosen
actual frame. Both transition functions are proved to be the same pth
power; no transition equality certificate is an input. -/
theorem frameComparison_eq {L : X.Modules} (e e' : L ≅ unitObj X) :
    frameComparison f p e = frameComparison f p e' := by
  obtain ⟨a, ha⟩ := unitIso_eq_globalUnit (e'.symm ≪≫ e)
  have he : e.hom = e'.hom ≫ ModularCurves.unitEndomorphismOfTopSection
      (a : Γ(X, ⊤)) := by
    have h := congrArg Iso.hom ha
    change e'.inv ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection (a : Γ(X, ⊤)) at h
    have hc := congrArg (fun q => e'.hom ≫ q) h
    simpa only [Iso.hom_inv_id_assoc] using hc
  have hF := pulledFrame_hom_eq_comp_scalar f p e e' (a : Γ(X, ⊤)) he
  have hP := powerFrame_hom_eq_comp_scalar e e' (a : Γ(X, ⊤)) he p
  apply Iso.ext
  apply (cancel_mono (powerFrame e p).hom).mp
  change (pulledFrame f p e).hom ≫ (powerFrame e p).inv ≫ (powerFrame e p).hom =
    (pulledFrame f p e').hom ≫ (powerFrame e' p).inv ≫ (powerFrame e p).hom
  rw [Iso.inv_hom_id, Category.comp_id, hP]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hF

end EnvelopeProperty.Vanishing.FrobeniusLineComparison
