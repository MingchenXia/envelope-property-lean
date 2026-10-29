import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration
import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility
import EnvelopeProperty.AlgGeom.SchemeGeneratedTensorSections

/-! # Removing one fixed canonical buffer from actual finite generators -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.Char0.MultiplierUniformGenerationBuffer
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem tensorInvertible {X : Scheme.{u}} {A B : X.Modules}
    (hA : IsInvertible A) (hB : IsInvertible B) : IsInvertible (A ⊗ B) :=
  (hA.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso A B)

private theorem finiteGenerators_of_iso {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf}
    (G : M.GeneratingSections) [G.IsFiniteType] (e : M ≅ N) :
    ∃ H : N.GeneratingSections, H.IsFiniteType :=
  ⟨G.ofEpi e.hom, inferInstance⟩

/-- The actual tensor product of the two original finite families generates
this original tensor module, with a Cartesian-product index type. -/
theorem exists_tensor_generatingSections {X : Scheme.{u}} (M N : X.Modules)
    (hN : IsInvertible N)
    (hM : ∃ G : M.GeneratingSections, G.IsFiniteType)
    (hNG : ∃ G : N.GeneratingSections, G.IsFiniteType) :
    ∃ G : (M ⊗ N).GeneratingSections, G.IsFiniteType := by
  obtain ⟨G, hG⟩ := hM
  obtain ⟨H, hH⟩ := hNG
  let : G.IsFiniteType := hG
  let : H.IsFiniteType := hH
  exact ⟨SchemeGeneratedTensorSections.generatingSections hN G H,
    SchemeGeneratedTensorSections.generatingSections_isFiniteType hN G H⟩

/-- A whole module isomorphism, using the native invertible evaluation,
that cancels the original canonical line and its actual dual. -/
def bufferCancellationIso {X : Scheme.{u}} (W : X.Modules) (hW : IsInvertible W)
    (P Q L J : X.Modules) :
    (((W ⊗ (P ⊗ L)) ⊗ J) ⊗ (Q ⊗ dualObj W)) ≅
      (((P ⊗ Q) ⊗ L) ⊗ J) := by
  let D := dualObj W
  let e : (W ⊗ (P ⊗ L)) ⊗ (Q ⊗ D) ≅ (P ⊗ Q) ⊗ L :=
    ((β_ W (P ⊗ L)) ⊗ᵢ Iso.refl (Q ⊗ D)) ≪≫
      (α_ (P ⊗ L) W (Q ⊗ D)) ≪≫
      (Iso.refl (P ⊗ L) ⊗ᵢ (α_ W Q D).symm) ≪≫
      (Iso.refl (P ⊗ L) ⊗ᵢ ((β_ W Q) ⊗ᵢ Iso.refl D)) ≪≫
      (Iso.refl (P ⊗ L) ⊗ᵢ (α_ Q W D)) ≪≫
      (α_ (P ⊗ L) Q (W ⊗ D)).symm ≪≫
      (Iso.refl ((P ⊗ L) ⊗ Q) ⊗ᵢ hW.monoidalEvaluationIso) ≪≫
      (ρ_ ((P ⊗ L) ⊗ Q)) ≪≫
      (α_ P L Q) ≪≫
      (Iso.refl P ⊗ᵢ (β_ L Q)) ≪≫
      (α_ P Q L).symm
  exact (α_ (W ⊗ (P ⊗ L)) J (Q ⊗ D)) ≪≫
    (Iso.refl (W ⊗ (P ⊗ L)) ⊗ᵢ (β_ J (Q ⊗ D))) ≪≫
    (α_ (W ⊗ (P ⊗ L)) (Q ⊗ D) J).symm ≪≫
    (e ⊗ᵢ Iso.refl J)

/-- Finite actual generators for a canonical twist and a fixed inverse
canonical buffer produce generators for the same original pure twist. -/
theorem exists_generatingSections_remove_canonical {X : Scheme.{u}}
    (W H L J : X.Modules) (hW : IsInvertible W) (hH : IsInvertible H)
    (b s m : ℕ)
    (hM : ∃ G : (((W ⊗ (bundleTensorPower H b ⊗ bundleTensorPower L m)) ⊗ J)).GeneratingSections,
      G.IsFiniteType)
    (hB : ∃ G : (bundleTensorPower H s ⊗ dualObj W).GeneratingSections, G.IsFiniteType) :
    ∃ G : ((bundleTensorPower H (b + s) ⊗ bundleTensorPower L m) ⊗ J).GeneratingSections,
      G.IsFiniteType := by
  let B := bundleTensorPower H s ⊗ dualObj W
  have hBI : IsInvertible B := tensorInvertible
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hH s) hW.dual
  obtain ⟨G, hG⟩ := exists_tensor_generatingSections
    ((W ⊗ (bundleTensorPower H b ⊗ bundleTensorPower L m)) ⊗ J) B hBI hM hB
  let : G.IsFiniteType := hG
  let e : (((W ⊗ (bundleTensorPower H b ⊗ bundleTensorPower L m)) ⊗ J) ⊗ B) ≅
      ((bundleTensorPower H (b + s) ⊗ bundleTensorPower L m) ⊗ J) :=
    bufferCancellationIso W hW
    (bundleTensorPower H b) (bundleTensorPower H s) (bundleTensorPower L m) J ≪≫
    ((TensorPowerBaseIdealGrading.tensorPowerAddIso H b s ⊗ᵢ
      Iso.refl (bundleTensorPower L m)) ⊗ᵢ Iso.refl J)
  exact finiteGenerators_of_iso G e

/-- One fixed inverse-canonical Serre buffer is selected before any varying
ideal, multiplier exponent, or tensor power of another line is supplied. -/
theorem exists_fixed_inverse_canonical_buffer {R k : Type u} [CommRing R] [Field k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (p : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple π H) :
    ∃ s : ℕ, ∃ G : (bundleTensorPower H s ⊗ dualObj (canonicalLineSheaf p n)).GeneratingSections,
      G.IsFiniteType := by
  obtain ⟨s, hs⟩ := AmpleLineTwistGeneration.exists_eventual_generatingSections π H hH
    (dualObj (canonicalLineSheaf p n)) (canonicalLineSheaf_isInvertible p n).dual
  exact ⟨s, hs s le_rfl⟩

end EnvelopeProperty.Char0.MultiplierUniformGenerationBuffer
