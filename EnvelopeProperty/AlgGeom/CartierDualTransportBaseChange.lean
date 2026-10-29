/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierEvaluationBaseChange

/-! # Actual canonical dual transport and genuine base change -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  symmetricCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Modules.pullback f).Monoidal := pullbackMonoidal f
variable {X Y Z : Scheme.{u}}

/-- Actual balanced evaluation uniquely specifies the genuine transport
among ALL original pulled-dual module morphisms. -/
theorem IsInvertible.evaluationDualTransportIso_unique_balanced {M : Y.Modules}
    (hM : IsInvertible M) (f g : X ⟶ Y)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M)
    (q : (Modules.pullback f).obj (dualObj M) ⟶ (Modules.pullback g).obj (dualObj M))
    (hq : (e.hom ⊗ₘ q) ≫ (hM.pulledEvaluationIso g).hom =
      (hM.pulledEvaluationIso f).hom) :
    q = (hM.evaluationDualTransportIso f g e).hom := by
  apply hM.evaluationDualTransportIso_unique f g e
  apply (cancel_epi (e.hom ▷ (Modules.pullback f).obj (dualObj M))).mp
  simpa only [tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc,
    Iso.hom_inv_id, id_whiskerRight, Category.id_comp] using hq

/-- Actual whole pullback of an isomorphism expressed on the literal
original composite scheme maps through the genuine native comparisons. -/
def pullbackIsoAlong {M : Z.Modules} (f g : Y ⟶ Z)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M) (h : X ⟶ Y) :
    (Modules.pullback (h ≫ f)).obj M ≅ (Modules.pullback (h ≫ g)).obj M :=
  ((pullbackComp h f).app M).symm ≪≫ (Modules.pullback h).mapIso e ≪≫
    (pullbackComp h g).app M

/-- Actual canonical dual transport commutes with arbitrary original
base change using the TRUE native composition comparisons on both factors. -/
theorem IsInvertible.evaluationDualTransportIso_baseChange {M : Z.Modules}
    (hM : IsInvertible M) (f g : Y ⟶ Z)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M) (h : X ⟶ Y) :
    hM.evaluationDualTransportIso (h ≫ f) (h ≫ g) (pullbackIsoAlong f g e h) =
      pullbackIsoAlong f g (hM.evaluationDualTransportIso f g e) h := by
  let τ := hM.evaluationDualTransportIso f g e
  let cf := (pullbackComp h f).app M
  let cfd := (pullbackComp h f).app (dualObj M)
  let cg := (pullbackComp h g).app M
  let cgd := (pullbackComp h g).app (dualObj M)
  let e' := pullbackIsoAlong f g e h
  let τ' := pullbackIsoAlong f g τ h
  have hp : (e ⊗ᵢ τ) ≪≫ hM.pulledEvaluationIso g = hM.pulledEvaluationIso f := by
    apply Iso.ext
    exact hM.evaluationDualTransportIso_balanced f g e
  have hc : (cf ⊗ᵢ cfd) ≪≫ (e' ⊗ᵢ τ') =
      ((Modules.pullback h).mapIso e ⊗ᵢ (Modules.pullback h).mapIso τ) ≪≫
        (cg ⊗ᵢ cgd) := by
    apply Iso.ext
    simp only [Iso.trans_hom, tensorIso_hom, e', τ', pullbackIsoAlong,
      Iso.symm_hom, Functor.mapIso_hom]
    simp only [← tensorHom_comp_tensorHom, cf, cfd, cg, cgd]
    exact (cf ⊗ᵢ cfd).hom_inv_id_assoc _
  have hn : ((Modules.pullback h).mapIso e ⊗ᵢ (Modules.pullback h).mapIso τ) ≪≫
      Functor.Monoidal.μIso (Modules.pullback h)
        ((Modules.pullback g).obj M) ((Modules.pullback g).obj (dualObj M)) =
      Functor.Monoidal.μIso (Modules.pullback h)
        ((Modules.pullback f).obj M) ((Modules.pullback f).obj (dualObj M)) ≪≫
        (Modules.pullback h).mapIso (e ⊗ᵢ τ) := by
    apply Iso.ext
    exact Functor.LaxMonoidal.μ_natural (Modules.pullback h) e.hom τ.hom
  have heq : (cf ⊗ᵢ cfd) ≪≫ (e' ⊗ᵢ τ') ≪≫ hM.pulledEvaluationIso (h ≫ g) =
      (cf ⊗ᵢ cfd) ≪≫ hM.pulledEvaluationIso (h ≫ f) := by
    rw [← Iso.trans_assoc, hc, Iso.trans_assoc]
    rw [show (cg ⊗ᵢ cgd) ≪≫ hM.pulledEvaluationIso (h ≫ g) = _ from
      hM.pulledEvaluationIso_comp h g]
    rw [← Iso.trans_assoc, hn]
    simp only [Iso.trans_assoc]
    rw [← Iso.trans_assoc ((Modules.pullback h).mapIso (e ⊗ᵢ τ)),
      ← Functor.mapIso_trans, hp]
    exact (hM.pulledEvaluationIso_comp h f).symm
  apply Iso.ext
  symm
  apply hM.evaluationDualTransportIso_unique_balanced (h ≫ f) (h ≫ g) e'
  apply (cancel_epi (cf ⊗ᵢ cfd).hom).mp
  exact congrArg Iso.hom heq

/-- Native equality comparison gives the ORIGINAL native equality
comparison on the actual original pulled dual. -/
theorem IsInvertible.evaluationDualTransportIso_congr {M : Y.Modules}
    (hM : IsInvertible M) (f g : X ⟶ Y) (h : f = g) :
    hM.evaluationDualTransportIso f g ((pullbackCongr h).app M) =
      (pullbackCongr h).app (dualObj M) := by
  subst g
  change hM.evaluationDualTransportIso f f (Iso.refl _) = Iso.refl _
  exact hM.evaluationDualTransportIso_refl f

end AlgebraicGeometry.Scheme.Modules
