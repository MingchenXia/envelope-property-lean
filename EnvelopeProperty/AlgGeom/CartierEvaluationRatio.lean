/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierDualTransportBaseChange
import EnvelopeProperty.AlgGeom.CartierTensorPullbackNaturality

/-! # Actual ratio comparisons from the canonical original evaluation -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y Z : Scheme.{u}} {M N : Y.Modules}

/-- The true whole original tensor-dual ratio comparison uses actual
original evaluation-preserving dual transport, with no coherence premise. -/
def evaluationRatioComparison (hN : IsInvertible N) (f g : X ⟶ Y)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M)
    (d : (Modules.pullback f).obj N ≅ (Modules.pullback g).obj N) :
    (Modules.pullback f).obj (tensorObj M (dualObj N)) ≅
      (Modules.pullback g).obj (tensorObj M (dualObj N)) :=
  canonicalTensorPullbackIso f M (dualObj N) ≪≫
    tensorObjCongr e (hN.evaluationDualTransportIso f g d) ≪≫
    (canonicalTensorPullbackIso g M (dualObj N)).symm

/-- True identity on both factors gives actual identity on the whole
original pulled tensor-dual ratio module sheaf. -/
theorem evaluationRatioComparison_refl (hN : IsInvertible N) (f : X ⟶ Y) :
    evaluationRatioComparison (M := M) hN f f (Iso.refl _) (Iso.refl _) = Iso.refl _ := by
  simp only [evaluationRatioComparison, hN.evaluationDualTransportIso_refl,
    tensorObjCongr_refl, Iso.refl_trans, Iso.self_symm_id]

/-- Actual tensor-dual ratio comparisons respect original simultaneous
factor composition on all original scheme modules. -/
theorem evaluationRatioComparison_trans (hN : IsInvertible N) (f g h : X ⟶ Y)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M)
    (e' : (Modules.pullback g).obj M ≅ (Modules.pullback h).obj M)
    (d : (Modules.pullback f).obj N ≅ (Modules.pullback g).obj N)
    (d' : (Modules.pullback g).obj N ≅ (Modules.pullback h).obj N) :
    evaluationRatioComparison hN f g e d ≪≫ evaluationRatioComparison hN g h e' d' =
      evaluationRatioComparison hN f h (e ≪≫ e') (d ≪≫ d') := by
  unfold evaluationRatioComparison
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [← Iso.trans_assoc (tensorObjCongr e _), ← tensorObjCongr_trans,
    hN.evaluationDualTransportIso_trans]

/-- Actual equality of original scheme morphisms gives its actual native
whole equality comparison on the original ratio module sheaf. -/
theorem evaluationRatioComparison_congr (hN : IsInvertible N)
    (f g : X ⟶ Y) (h : f = g) :
    evaluationRatioComparison hN f g ((pullbackCongr h).app M)
        ((pullbackCongr h).app N) =
      (pullbackCongr h).app (tensorObj M (dualObj N)) := by
  subst g
  change evaluationRatioComparison hN f f (Iso.refl _) (Iso.refl _) = Iso.refl _
  exact evaluationRatioComparison_refl hN f

private theorem tensorObjCongr_symm_actual {M₁ M₂ N₁ N₂ : X.Modules}
    (e : M₁ ≅ M₂) (d : N₁ ≅ N₂) :
    tensorObjCongr e.symm d.symm = (tensorObjCongr e d).symm := by
  apply Iso.ext
  rfl

private theorem tensorComparison_baseChange {M N : Z.Modules}
    (f g : Y ⟶ Z)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M)
    (d : (Modules.pullback f).obj N ≅ (Modules.pullback g).obj N) (h : X ⟶ Y) :
    pullbackIsoAlong f g
        (canonicalTensorPullbackIso f M N ≪≫ tensorObjCongr e d ≪≫
          (canonicalTensorPullbackIso g M N).symm) h =
      canonicalTensorPullbackIso (h ≫ f) M N ≪≫
        tensorObjCongr (pullbackIsoAlong f g e h) (pullbackIsoAlong f g d h) ≪≫
        (canonicalTensorPullbackIso (h ≫ g) M N).symm := by
  let Kf := canonicalTensorPullbackIso f M N
  let Kg := canonicalTensorPullbackIso g M N
  let Khf := canonicalTensorPullbackIso (h ≫ f) M N
  let Khg := canonicalTensorPullbackIso (h ≫ g) M N
  let Hf := canonicalTensorPullbackIso h ((Modules.pullback f).obj M) ((Modules.pullback f).obj N)
  let Hg := canonicalTensorPullbackIso h ((Modules.pullback g).obj M) ((Modules.pullback g).obj N)
  let cf := (pullbackComp h f).app (tensorObj M N)
  let cg := (pullbackComp h g).app (tensorObj M N)
  let Tf := tensorObjCongr ((pullbackComp h f).app M) ((pullbackComp h f).app N)
  let Tg := tensorObjCongr ((pullbackComp h g).app M) ((pullbackComp h g).app N)
  let E := tensorObjCongr e d
  let Eh := tensorObjCongr ((Modules.pullback h).mapIso e) ((Modules.pullback h).mapIso d)
  let E' := tensorObjCongr (pullbackIsoAlong f g e h) (pullbackIsoAlong f g d h)
  have hf : (Modules.pullback h).mapIso Kf ≪≫ Hf ≪≫ Tf = cf ≪≫ Khf :=
    canonicalTensorPullbackIso_comp h f M N
  have hg : (Modules.pullback h).mapIso Kg ≪≫ Hg ≪≫ Tg = cg ≪≫ Khg :=
    canonicalTensorPullbackIso_comp h g M N
  have hn : (Modules.pullback h).mapIso E ≪≫ Hg = Hf ≪≫ Eh :=
    canonicalTensorPullbackIso_natural h e d
  have he : E' = Tf.symm ≪≫ Eh ≪≫ Tg := by
    dsimp only [E', pullbackIsoAlong]
    rw [tensorObjCongr_trans, tensorObjCongr_trans]
    rw [tensorObjCongr_symm_actual]
  have hl : cf.symm ≪≫ (Modules.pullback h).mapIso Kf = Khf ≪≫ Tf.symm ≪≫ Hf.symm := by
    have h' := congrArg (fun q => cf.symm ≪≫ q ≪≫ Tf.symm ≪≫ Hf.symm) hf
    simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
      Iso.self_symm_id, Iso.trans_refl] using h'
  have hr : (Modules.pullback h).mapIso Kg.symm ≪≫ cg = Hg ≪≫ Tg ≪≫ Khg.symm := by
    have h' := congrArg (fun q => ((Modules.pullback h).mapIso Kg).symm ≪≫ q ≪≫ Khg.symm) hg
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
      Iso.symm_self_id_assoc, Functor.mapIso_symm] using h'.symm
  change cf.symm ≪≫ (Modules.pullback h).mapIso (Kf ≪≫ E ≪≫ Kg.symm) ≪≫ cg =
    Khf ≪≫ E' ≪≫ Khg.symm
  simp only [Functor.mapIso_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc cf.symm, hl, hr]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc ((Modules.pullback h).mapIso E), hn]
  rw [he]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- The genuine original ratio comparison commutes with ARBITRARY
original base change, with the true native whole pullback compositions. -/
theorem evaluationRatioComparison_baseChange {M N : Z.Modules}
    (hN : IsInvertible N) (f g : Y ⟶ Z)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M)
    (d : (Modules.pullback f).obj N ≅ (Modules.pullback g).obj N) (h : X ⟶ Y) :
    pullbackIsoAlong f g (evaluationRatioComparison hN f g e d) h =
      evaluationRatioComparison hN (h ≫ f) (h ≫ g)
        (pullbackIsoAlong f g e h) (pullbackIsoAlong f g d h) := by
  unfold evaluationRatioComparison
  rw [tensorComparison_baseChange, hN.evaluationDualTransportIso_baseChange]

end AlgebraicGeometry.Scheme.Modules
