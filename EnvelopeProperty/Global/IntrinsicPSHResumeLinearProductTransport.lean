import EnvelopeProperty.Global.IntrinsicPSHResumeLinearPowers
import ModularCurves.EllipticCurve.PullbackTensorSection
import ModularCurves.Picard.DualPullback.LocalSection

/-! # Actual whole-section pullback and the same original tensor comparisons -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
open EnvelopeProperty.CanonicalGeometry
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
open Scheme.Modules SchemeLineSectionEvaluation

/-- The actual adjunction-unit image on the whole open, for the original
pullback functor and original section spaces. -/
def wholePullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules)
    (s : Γ(A, ⊤)) : Γ((pullback f).obj A, ⊤) :=
  (((pullbackPushforwardAdjunction f).unit.app A).val.app (op ⊤)).hom.toFun s

/-- The SAME whole pullback value is the actual unit-normalized pullback
of the original structure-module morphism at one. -/
theorem wholePullbackSection_eq_sectionAtOne {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Y.Modules) (s : Γ(A, ⊤)) :
    wholePullbackSection f A s = sectionAtOne (pullbackSectionHom f (topSectionHom A s)) := by
  have h := pullback_unit_app_top_applyT f A s
  exact h.trans (congrArg
    (fun z => (((pullbackUnitIso f).inv ≫ (pullback f).map (topSectionHom A s)).val.app
      (op (f ⁻¹ᵁ (⊤ : Y.Opens)))) z)
    (map_one (f.app ⊤).hom))

/-- The old original whole-section isomorphism has this same actual
adjunction-unit pullback as its inverse on every original section. -/
theorem isoPullbackTopSections_inv_wholePullbackSection {X Y : Scheme.{u}}
    (e : X ≅ Y) (A : Y.Modules) (s : Γ(A, ⊤)) :
    (isoPullbackTopSections e A).inv s = wholePullbackSection e.hom A s := by
  have hs : sectionAtOne (topSectionHom A s) = s := topSectionHom_app_top_apply_one A s
  exact (congrArg (fun t => (isoPullbackTopSections e A).inv t) hs).symm.trans
    ((isoPullbackTopSections_inv_sectionAtOne e A (topSectionHom A s)).trans
      (wholePullbackSection_eq_sectionAtOne e.hom A s).symm)

/-- Actual whole pullback commutes with the SAME original module morphism. -/
theorem wholePullbackSection_map {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules}
    (a : A ⟶ B) (s : Γ(A, ⊤)) :
    ((pullback f).map a).val.app (op ⊤) (wholePullbackSection f A s) =
      wholePullbackSection f B (a.val.app (op ⊤) s) :=
  pullbackUnit_map_appT f a ⊤ s

/-- The SAME actual canonical explicit tensor pullback preserves actual
whole pure-section tensors, without a supplied matching square. -/
theorem canonicalTensorPullbackIso_wholePullbackSection {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A B : Y.Modules) (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    (canonicalTensorPullbackIso f A B).hom.val.app (op ⊤)
        (wholePullbackSection f (bundleTensor A B) (tensorSection A B ⊤ s t)) =
      tensorSection ((pullback f).obj A) ((pullback f).obj B) ⊤
        (wholePullbackSection f A s) (wholePullbackSection f B t) := by
  let : MonoidalCategory X.Modules := monoidalCategory X
  let : MonoidalCategory Y.Modules := monoidalCategory Y
  let : (pullback f).Monoidal := pullbackMonoidal f
  let k := ModularCurves.monoidalTensorObjIso A B
  let kx := ModularCurves.monoidalTensorObjIso ((pullback f).obj A) ((pullback f).obj B)
  let μ := Functor.Monoidal.μIso (pullback f) A B
  have hc : (pullback f).map k.hom ≫ (canonicalTensorPullbackIso f A B).hom =
      μ.inv ≫ kx.hom := by
    change (pullback f).map k.hom ≫
      ((pullback f).map k.inv ≫ μ.inv ≫ kx.hom) = μ.inv ≫ kx.hom
    exact Iso.hom_inv_id_assoc ((pullback f).mapIso k) _
  have hY : k.hom.val.app (op ⊤) (ModularCurves.tensorSection A B ⊤ s t) =
      tensorSection A B ⊤ s t :=
    congrArg (fun q : bundleTensor A B ⟶ bundleTensor A B =>
      q.val.app (op ⊤) (tensorSection A B ⊤ s t)) k.inv_hom_id
  have hX : kx.hom.val.app (op ⊤)
      (ModularCurves.tensorSection ((pullback f).obj A) ((pullback f).obj B) ⊤
        (wholePullbackSection f A s) (wholePullbackSection f B t)) =
      tensorSection ((pullback f).obj A) ((pullback f).obj B) ⊤
        (wholePullbackSection f A s) (wholePullbackSection f B t) :=
    congrArg (fun q : bundleTensor ((pullback f).obj A) ((pullback f).obj B) ⟶
        bundleTensor ((pullback f).obj A) ((pullback f).obj B) =>
      q.val.app (op ⊤) (tensorSection ((pullback f).obj A) ((pullback f).obj B) ⊤
        (wholePullbackSection f A s) (wholePullbackSection f B t))) kx.inv_hom_id
  let z := wholePullbackSection f (A ⊗ B) (ModularCurves.tensorSection A B ⊤ s t)
  have hδ : μ.inv.val.app (op ⊤) z =
      ModularCurves.tensorSection ((pullback f).obj A) ((pullback f).obj B) ⊤
        (wholePullbackSection f A s) (wholePullbackSection f B t) :=
    ModularCurves.pullback_δ_unit_tensorSection f A B ⊤ s t
  have hn := (wholePullbackSection_map f k.hom (ModularCurves.tensorSection A B ⊤ s t)).trans
    (congrArg (wholePullbackSection f (bundleTensor A B)) hY)
  have hv := congrArg (fun q : (pullback f).obj (A ⊗ B) ⟶
      bundleTensor ((pullback f).obj A) ((pullback f).obj B) =>
    q.val.app (op ⊤) z) hc
  change (canonicalTensorPullbackIso f A B).hom.val.app (op ⊤)
      (((pullback f).map k.hom).val.app (op ⊤) z) =
    kx.hom.val.app (op ⊤) (μ.inv.val.app (op ⊤) z) at hv
  exact (congrArg (fun q => (canonicalTensorPullbackIso f A B).hom.val.app (op ⊤) q) hn).symm.trans
    (hv.trans ((congrArg (fun q => kx.hom.val.app (op ⊤) q) hδ).trans hX))

end EnvelopeProperty.ClosedProjectiveGlobalSections
