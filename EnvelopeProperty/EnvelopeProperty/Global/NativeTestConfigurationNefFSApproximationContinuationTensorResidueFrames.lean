import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorCoherence
import EnvelopeProperty.Berkovich.SchemeInducedPowerFrames

/-! # Tensor coherence of induced residue frames and reference support frames

Residue-field frames of lines are transported along module isomorphisms and scheme maps
(`inducedResidueFrame`, `SchemeLineSectionEvaluation.localPullbackFrame`,
`SchemeSupportLineFrames.supportGenericFrame`).  This file proves that these constructions
commute with tensor products of lines, up to the inverse pullback tensorators:

* `inducedResidueFrame_tensor`;
* `supportGenericFrame_localPullbackTensor`.

These are the frame-level inputs of the tensor law for native norm factors in
`…ContinuationTensorPotential`.
-/
open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfigurationNefFSTensorResidueFrames
open SchemeTensorPowerFrames SchemePulledPowerFrames
open Berkovich Berkovich.SchemeFramedSectionPullback
noncomputable local instance nfTensorResidueFramesModulesMonoidal (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y
noncomputable local instance nfTensorResidueFramesPullbackMonoidal {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (pullback f).Monoidal := pullbackMonoidal f

private theorem inverse_tensorator_naturality
    {D E : Type*} [Category D] [MonoidalCategory D]
    [Category E] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] {A B P Q : D} (a : A ≅ B) (b : P ≅ Q) :
    F.mapIso (a ⊗ᵢ b) ≪≫ (Functor.Monoidal.μIso F B Q).symm =
      (Functor.Monoidal.μIso F A P).symm ≪≫ (F.mapIso a ⊗ᵢ F.mapIso b) := by
  apply Iso.ext
  exact (Functor.OplaxMonoidal.δ_natural F a.hom b.hom).symm

/-- The tensor frame induced through the SAME original map and genuine
tensor module comparison is exactly the tensor of the two induced frames.
The original residue-field map and all whole comparisons are preserved. -/
theorem inducedResidueFrame_tensor {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {M H : Z.Modules} {N K : Y.Modules}
    (alpha : (pullback g).obj M ≅ N) (beta : (pullback g).obj H ≅ K)
    (y : SchemeValuedPoint Y)
    (e : (pullback (Z.fromSpecResidueField (g y.point))).obj M ≅
      unitObj (Spec (.of (Z.residueField (g y.point)))))
    (d : (pullback (Z.fromSpecResidueField (g y.point))).obj H ≅
      unitObj (Spec (.of (Z.residueField (g y.point))))) :
    inducedResidueFrame g
        ((Functor.Monoidal.μIso (pullback g) M H).symm ≪≫ (alpha ⊗ᵢ beta)) y
        ((Functor.Monoidal.μIso (pullback (Z.fromSpecResidueField (g y.point))) M H).symm ≪≫
          tensorFrame e d) =
      (Functor.Monoidal.μIso (pullback (Y.fromSpecResidueField y.point)) N K).symm ≪≫
        tensorFrame (inducedResidueFrame g alpha y e) (inducedResidueFrame g beta y d) := by
  let t := Y.fromSpecResidueField y.point
  let b := Z.fromSpecResidueField (g y.point)
  let q := Spec.map (g.residueFieldMap y.point)
  let h := g.SpecMap_residueFieldMap_fromSpecResidueField y.point
  let deltaG := (Functor.Monoidal.μIso (pullback g) M H).symm
  let deltaB := (Functor.Monoidal.μIso (pullback b) M H).symm
  let deltaTG := (Functor.Monoidal.μIso (pullback (t ≫ g)) M H).symm
  let deltaT := (Functor.Monoidal.μIso (pullback t) ((pullback g).obj M) ((pullback g).obj H)).symm
  let deltaN := (Functor.Monoidal.μIso (pullback t) N K).symm
  let em := frameViaFactor q b (t ≫ g) h e
  let eh := frameViaFactor q b (t ≫ g) h d
  let EM := (pullbackComp t g).app M ≪≫ em
  let EH := (pullbackComp t g).app H ≪≫ eh
  have hc : (pullbackComp t g).app (M ⊗ H) ≪≫ deltaTG =
      (pullback t).mapIso deltaG ≪≫ deltaT ≪≫
        ((pullbackComp t g).app M ⊗ᵢ (pullbackComp t g).app H) := by
    apply Iso.ext
    exact (pullbackComp_inverse_tensorator t g M H).symm
  have hf : frameViaFactor q b (t ≫ g) h (deltaB ≪≫ tensorFrame e d) =
      deltaTG ≪≫ tensorFrame em eh := frameViaFactor_tensor q b (t ≫ g) h e d
  have hbody : (pullbackComp t g).app (M ⊗ H) ≪≫
      frameViaFactor q b (t ≫ g) h (deltaB ≪≫ tensorFrame e d) =
      (pullback t).mapIso deltaG ≪≫ deltaT ≪≫ tensorFrame EM EH := by
    rw [hf, ← Iso.trans_assoc, hc]
    simp only [Iso.trans_assoc]
    rw [tensorFrame_naturality]
  have hm : inducedResidueFrame g alpha y e = (pullback t).mapIso alpha.symm ≪≫ EM := by
    simpa only [Functor.mapIso_symm] using inducedResidueFrame_eq g alpha y e
  have hh : inducedResidueFrame g beta y d = (pullback t).mapIso beta.symm ≪≫ EH := by
    simpa only [Functor.mapIso_symm] using inducedResidueFrame_eq g beta y d
  have hn : (pullback t).mapIso (alpha ⊗ᵢ beta).symm ≪≫ deltaT =
      deltaN ≪≫ ((pullback t).mapIso alpha.symm ⊗ᵢ (pullback t).mapIso beta.symm) :=
    inverse_tensorator_naturality (pullback t) alpha.symm beta.symm
  have hi := inducedResidueFrame_eq g (deltaG ≪≫ (alpha ⊗ᵢ beta)) y
    (deltaB ≪≫ tensorFrame e d)
  calc
    _ = ((pullback t).mapIso (deltaG ≪≫ (alpha ⊗ᵢ beta))).symm ≪≫
        ((pullbackComp t g).app (M ⊗ H) ≪≫
          frameViaFactor q b (t ≫ g) h (deltaB ≪≫ tensorFrame e d)) := hi
    _ = (pullback t).mapIso (alpha ⊗ᵢ beta).symm ≪≫
        deltaT ≪≫ tensorFrame EM EH := by
      rw [hbody]
      simp only [Functor.mapIso_trans, Iso.trans_symm, Functor.mapIso_symm,
        Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = deltaN ≪≫ tensorFrame ((pullback t).mapIso alpha.symm ≪≫ EM)
        ((pullback t).mapIso beta.symm ≪≫ EH) := by
      rw [← Iso.trans_assoc, hn, Iso.trans_assoc, tensorFrame_naturality]
    _ = _ := by rw [hm, hh]

private theorem localPullbackFrame_tensor {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (U : Z.Opens) {M H : Z.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (d : (pullback U.ι).obj H ≅ unitObj U.toScheme) :
    SchemeLineSectionEvaluation.localPullbackFrame g U
        ((Functor.Monoidal.μIso (pullback U.ι) M H).symm ≪≫ tensorFrame e d) =
      (pullback (g ⁻¹ᵁ U).ι).mapIso (Functor.Monoidal.μIso (pullback g) M H).symm ≪≫
        (Functor.Monoidal.μIso (pullback (g ⁻¹ᵁ U).ι) ((pullback g).obj M)
            ((pullback g).obj H)).symm ≪≫
          tensorFrame (SchemeLineSectionEvaluation.localPullbackFrame g U e)
            (SchemeLineSectionEvaluation.localPullbackFrame g U d) := by
  let a := (g ⁻¹ᵁ U).ι
  let em := frameViaFactor (g ∣_ U) U.ι (a ≫ g) (morphismRestrict_ι g U) e
  let eh := frameViaFactor (g ∣_ U) U.ι (a ≫ g) (morphismRestrict_ι g U) d
  have hf := frameViaFactor_tensor (g ∣_ U) U.ι (a ≫ g) (morphismRestrict_ι g U) e d
  have hc : (pullbackComp a g).app (M ⊗ H) ≪≫
      (Functor.Monoidal.μIso (pullback (a ≫ g)) M H).symm =
      (pullback a).mapIso (Functor.Monoidal.μIso (pullback g) M H).symm ≪≫
        (Functor.Monoidal.μIso (pullback a) ((pullback g).obj M) ((pullback g).obj H)).symm ≪≫
          ((pullbackComp a g).app M ⊗ᵢ (pullbackComp a g).app H) := by
    apply Iso.ext
    exact (pullbackComp_inverse_tensorator a g M H).symm
  dsimp only [SchemeLineSectionEvaluation.localPullbackFrame]
  rw [hf, ← Iso.trans_assoc, hc]
  simp only [Iso.trans_assoc]
  rw [tensorFrame_naturality]

private theorem supportGenericFrame_tensor {Y : Scheme.{u}} (y : Y)
    (U : Y.Opens) (hy : y ∈ U) {M H : Y.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (d : (pullback U.ι).obj H ≅ unitObj U.toScheme) :
    SchemeSupportLineFrames.supportGenericFrame y U hy
        ((Functor.Monoidal.μIso (pullback U.ι) M H).symm ≪≫ tensorFrame e d) =
      (Functor.Monoidal.μIso (pullback (Y.fromSpecResidueField y)) M H).symm ≪≫
        tensorFrame (SchemeSupportLineFrames.supportGenericFrame y U hy e)
          (SchemeSupportLineFrames.supportGenericFrame y U hy d) :=
  frameViaFactor_tensor (SchemeSupportLineFrames.supportGenericFactor y U hy) U.ι
    (Y.fromSpecResidueField y) (SchemeSupportLineFrames.supportGenericFactor_comp y U hy) e d

/-- Actual original support/local frames of a tensor have the common
preceding tensorator followed by the tensor of the two original frames. -/
theorem supportGenericFrame_localPullbackTensor {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (y : Y) (U : Z.Opens) (hy : y ∈ g ⁻¹ᵁ U) {M H : Z.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (d : (pullback U.ι).obj H ≅ unitObj U.toScheme) :
    SchemeSupportLineFrames.supportGenericFrame y (g ⁻¹ᵁ U) hy
        (SchemeLineSectionEvaluation.localPullbackFrame g U
          ((Functor.Monoidal.μIso (pullback U.ι) M H).symm ≪≫ tensorFrame e d)) =
      (pullback (Y.fromSpecResidueField y)).mapIso (Functor.Monoidal.μIso (pullback g) M H).symm ≪≫
        (Functor.Monoidal.μIso (pullback (Y.fromSpecResidueField y)) ((pullback g).obj M)
            ((pullback g).obj H)).symm ≪≫
          tensorFrame
            (SchemeSupportLineFrames.supportGenericFrame y (g ⁻¹ᵁ U) hy
              (SchemeLineSectionEvaluation.localPullbackFrame g U e))
            (SchemeSupportLineFrames.supportGenericFrame y (g ⁻¹ᵁ U) hy
              (SchemeLineSectionEvaluation.localPullbackFrame g U d)) := by
  rw [localPullbackFrame_tensor]
  have hn := frameViaFactor_naturality (SchemeSupportLineFrames.supportGenericFactor y (g ⁻¹ᵁ U) hy)
    (g ⁻¹ᵁ U).ι (Y.fromSpecResidueField y)
    (SchemeSupportLineFrames.supportGenericFactor_comp y (g ⁻¹ᵁ U) hy)
    (Functor.Monoidal.μIso (pullback g) M H).symm
    ((Functor.Monoidal.μIso (pullback (g ⁻¹ᵁ U).ι) ((pullback g).obj M)
        ((pullback g).obj H)).symm ≪≫
      tensorFrame (SchemeLineSectionEvaluation.localPullbackFrame g U e)
        (SchemeLineSectionEvaluation.localPullbackFrame g U d))
  exact hn.trans (congrArg (fun E =>
    (pullback (Y.fromSpecResidueField y)).mapIso (Functor.Monoidal.μIso (pullback g) M H).symm ≪≫ E)
    (supportGenericFrame_tensor y (g ⁻¹ᵁ U) hy
        (SchemeLineSectionEvaluation.localPullbackFrame g U e)
      (SchemeLineSectionEvaluation.localPullbackFrame g U d)))

end EnvelopeProperty.NativeTestConfigurationNefFSTensorResidueFrames
