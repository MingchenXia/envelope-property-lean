/-
Copyright (c) 2026. All rights reserved.
-/
import ModularCurves.Picard.PicComparison
import ModularCurves.EllipticCurve.PoleSheaf

/-! # Actual canonical dual evaluation and invertible tensor cancellation -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {M : X.Modules}

/-- Genuine cover-local invertibility makes the ORIGINAL canonical sheaf
EVALUATION morphism itself an isomorphism, with no chosen pairing premise. -/
theorem IsInvertible.ev_isIso (hM : IsInvertible M) : IsIso (ev M) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  have hw : PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj) (evPre M) := by
    refine sheafificationW_of_bijective_on_cover (evPre M) U hU (fun i W hW => ?_)
    obtain ⟨e⟩ := htriv i
    exact bijective_evPre_app_of_triv (restrictTrivialization hW e)
  rw [PresheafOfModules.sheafificationW_iff] at hw
  have : IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (evPre M)) := hw
  let eSheaf := asIso ((PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).map (evPre M))
  let eFinal := eSheaf ≪≫ sheafifyValIso (unitObj X)
  change IsIso eFinal.hom
  exact eFinal.isIso_hom

/-- The true actual canonical evaluation isomorphism against the original dual. -/
def IsInvertible.evaluationIso (hM : IsInvertible M) :
    AlgebraicGeometry.Scheme.Modules.tensorObj M (dualObj M) ≅ unitObj X := by
  have := hM.ev_isIso
  exact asIso (ev M)

/-- The homomorphism of this genuine pairing is the ORIGINAL evaluation. -/
theorem IsInvertible.evaluationIso_hom (hM : IsInvertible M) :
    hM.evaluationIso.hom = ev M := rfl

/-- The actual original canonical evaluation also inverts the genuine
coherent tensor, with the TRUE original monoidal unit comparison. -/
def IsInvertible.monoidalEvaluationIso (hM : IsInvertible M) :
    letI : MonoidalCategory X.Modules := monoidalCategory X
    M ⊗ dualObj M ≅ 𝟙_ X.Modules := by
  let : MonoidalCategory X.Modules := monoidalCategory X
  exact ModularCurves.monoidalTensorObjIso M (dualObj M) ≪≫
    hM.evaluationIso ≪≫ (ModularCurves.monoidalUnitObjIso X).symm

private def tensorRightDualInverseIso (hM : IsInvertible M) :
    letI : MonoidalCategory X.Modules := monoidalCategory X
    𝟭 X.Modules ≅ tensorRight M ⋙ tensorRight (dualObj M) := by
  let : MonoidalCategory X.Modules := monoidalCategory X
  let e := hM.monoidalEvaluationIso
  let hcongr : tensorRight (𝟙_ X.Modules) ≅ tensorRight (M ⊗ dualObj M) :=
    NatIso.ofComponents (fun P => whiskerLeftIso P e.symm) (by
      intro P Q f
      exact (whisker_exchange f e.inv).symm)
  exact (rightUnitorNatIso X.Modules).symm ≪≫ hcongr ≪≫ tensorRightTensor M (dualObj M)

private theorem tensorRight_faithful_of_invertible (hM : IsInvertible M) :
    letI : MonoidalCategory X.Modules := monoidalCategory X
    (tensorRight M).Faithful := by
  let : MonoidalCategory X.Modules := monoidalCategory X
  have : (tensorRight M ⋙ tensorRight (dualObj M)).Faithful :=
    Functor.Faithful.of_iso (tensorRightDualInverseIso hM)
  exact Functor.Faithful.of_comp (tensorRight M) (tensorRight (dualObj M))

/-- Tensor by the SAME original invertible module is genuinely fully faithful,
constructing actual unique morphism/isomorphism lifts with no cancellation premise. -/
def IsInvertible.tensorRightFullyFaithful (hM : IsInvertible M) :
    letI : MonoidalCategory X.Modules := monoidalCategory X
    (tensorRight M).FullyFaithful := by
  let : MonoidalCategory X.Modules := monoidalCategory X
  have : (tensorRight M).Faithful := tensorRight_faithful_of_invertible hM
  have : (tensorRight (dualObj M)).Faithful := tensorRight_faithful_of_invertible hM.dual
  have : (tensorRight M).Full :=
    Functor.Full.of_comp_faithful_iso (tensorRightDualInverseIso hM).symm
  exact Functor.FullyFaithful.ofFullyFaithful (tensorRight M)

end AlgebraicGeometry.Scheme.Modules
