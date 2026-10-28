import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionRecovery
import EnvelopeProperty.AlgGeom.CartierEvaluationTransport

/-! # Actual evaluation-preserving dual pullback for original Hom-sections -/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace EnvelopeProperty.SchemeInvertibleHomSection

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)

private def homSectionPulledTensorLeftFullyFaithful :
    (tensorLeft ((Scheme.Modules.pullback f).obj A)).FullyFaithful :=
  (hA.pullback f).tensorRightFullyFaithful.ofIso
    (BraidedCategory.tensorLeftIsoTensorRight ((Scheme.Modules.pullback f).obj A)).symm

/-- The actual pullback of the ORIGINAL dual is identified with the SAME
original dual of the actual pullback, by the genuine ORIGINAL evaluations.
Both the isomorphism and its evaluation compatibility are derived. -/
def dualPullbackEvaluationIso :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.dualObj A) ≅
      Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A) :=
  (homSectionPulledTensorLeftFullyFaithful f A hA).preimageIso
    (hA.pulledEvaluationIso f ≪≫ (hA.pullback f).monoidalEvaluationIso.symm)

/-- The ENTIRE actual evaluation is retained by the actual constructed
dual-pullback isomorphism, with the true original tensor and unit maps. -/
theorem dualPullbackEvaluationIso_pairing :
    (Scheme.Modules.pullback f).obj A ◁ (dualPullbackEvaluationIso f A hA).hom ≫
      (hA.pullback f).monoidalEvaluationIso.hom = (hA.pulledEvaluationIso f).hom := by
  have he := (homSectionPulledTensorLeftFullyFaithful f A hA).map_preimage
    (hA.pulledEvaluationIso f ≪≫ (hA.pullback f).monoidalEvaluationIso.symm).hom
  change (Scheme.Modules.pullback f).obj A ◁ (dualPullbackEvaluationIso f A hA).hom = _ at he
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The SAME original whole evaluation characterizes this comparison
among ALL original pulled-dual morphisms, without a matching premise. -/
theorem dualPullbackEvaluationIso_unique
    (b : (Scheme.Modules.pullback f).obj (Scheme.Modules.dualObj A) ⟶
      Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A))
    (hb : (Scheme.Modules.pullback f).obj A ◁ b ≫
      (hA.pullback f).monoidalEvaluationIso.hom = (hA.pulledEvaluationIso f).hom) :
    b = (dualPullbackEvaluationIso f A hA).hom := by
  apply (homSectionPulledTensorLeftFullyFaithful f A hA).map_injective
  apply (cancel_mono (hA.pullback f).monoidalEvaluationIso.hom).mp
  exact hb.trans (dualPullbackEvaluationIso_pairing f A hA).symm

end
end EnvelopeProperty.SchemeInvertibleHomSection
