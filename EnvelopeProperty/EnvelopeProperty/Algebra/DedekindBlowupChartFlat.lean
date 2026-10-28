/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Scheme.BlowUp.AffineBlowUpAlgebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Actual blowup charts are flat over an original Dedekind base

The chart is the true subalgebra of the original localization, so its
inherited base torsion-freeness proves flatness without a domain/reduction
assumption on the original algebra or any generator assumption.
-/

open AlgebraicGeometry
noncomputable section
universe u v
namespace EnvelopeProperty
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {A : Type v} [CommRing A] [Algebra R A] [Module.Flat R A]

/-- Every genuine affine blowup chart of an actual flat algebra over a
Dedekind domain is flat over that original base. -/
theorem affineBlowUpAlgebra_flat_over_dedekind (I : Ideal A) (a : A) :
    Module.Flat R (affineBlowUpAlgebra I a) := by
  have : Module.Flat A (Localization.Away a) := IsLocalization.flat _ (Submonoid.powers a)
  have : Module.Flat R (Localization.Away a) := Module.Flat.trans R A (Localization.Away a)
  have : Module.IsTorsionFree R (Localization.Away a) := inferInstance
  have : Module.IsTorsionFree R (affineBlowUpAlgebra I a) :=
    Function.Injective.moduleIsTorsionFree (R := R)
      (fun x : affineBlowUpAlgebra I a => (x : Localization.Away a))
      Subtype.val_injective (fun _ _ => rfl)
  infer_instance

end EnvelopeProperty
