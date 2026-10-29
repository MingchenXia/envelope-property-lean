/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierEvaluationTransport
import EnvelopeProperty.AlgGeom.CartierPullbackTensorCoherence

/-! # Genuine canonical evaluation and actual pullback composition -/

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
variable {X Y Z : Scheme.{u}} {M : Z.Modules}

/-- The actual native composition isomorphisms preserve the ORIGINAL
pulled evaluation using the genuine tensor and unit comparisons. -/
theorem IsInvertible.pulledEvaluationIso_comp (hM : IsInvertible M)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (((pullbackComp f g).app M) ⊗ᵢ ((pullbackComp f g).app (dualObj M))) ≪≫
        hM.pulledEvaluationIso (f ≫ g) =
      Functor.Monoidal.μIso (Modules.pullback f)
          ((Modules.pullback g).obj M) ((Modules.pullback g).obj (dualObj M)) ≪≫
        (Modules.pullback f).mapIso (hM.pulledEvaluationIso g) ≪≫
        (Functor.Monoidal.εIso (Modules.pullback f)).symm := by
  have : (pullbackComp f g).hom.IsMonoidal := pullbackComp_hom_isMonoidal f g
  have ht := NatTrans.IsMonoidal.tensor (τ := (pullbackComp f g).hom) M (dualObj M)
  have hu := NatTrans.IsMonoidal.unit (τ := (pullbackComp f g).hom)
  have hn := (pullbackComp f g).hom.naturality hM.monoidalEvaluationIso.hom
  apply Iso.ext
  simp only [Iso.trans_hom, tensorIso_hom, IsInvertible.pulledEvaluationIso,
    Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_inv, Functor.mapIso_hom,
    Iso.symm_hom] at *
  change ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app (dualObj M)) ≫
      Functor.LaxMonoidal.μ (Modules.pullback (f ≫ g)) M (dualObj M) ≫
      (Modules.pullback (f ≫ g)).map hM.monoidalEvaluationIso.hom ≫
      Functor.OplaxMonoidal.η (Modules.pullback (f ≫ g)) = _
  rw [← Category.assoc, ← ht]
  rw [Category.assoc, ← Category.assoc _ _ (Functor.OplaxMonoidal.η
    (Modules.pullback (f ≫ g))), ← hn]
  have hu' : (pullbackComp f g).hom.app (𝟙_ Z.Modules) ≫
      Functor.OplaxMonoidal.η (Modules.pullback (f ≫ g)) =
      Functor.OplaxMonoidal.η (Modules.pullback g ⋙ Modules.pullback f) := by
    apply (cancel_epi (Functor.LaxMonoidal.ε
      (Modules.pullback g ⋙ Modules.pullback f))).mp
    rw [← Category.assoc, hu]
    simp only [Functor.Monoidal.ε_η]
  simp only [Category.assoc]
  rw [hu']
  simp only [Functor.LaxMonoidal.comp_μ, Functor.OplaxMonoidal.comp_η,
    Functor.map_comp, Functor.comp_map, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
