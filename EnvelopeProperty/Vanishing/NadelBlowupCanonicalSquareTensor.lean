import EnvelopeProperty.Vanishing.NadelBlowupCanonicalBaseChangeTensor
import EnvelopeProperty.AlgGeom.CartierCanonicalTensorPullback

/-! # Whole tensor-ideal inclusions under the actual original line comparisons -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareTensor
open NadelBlowupCanonicalBaseChangeTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

/-- A whole equality of ORIGINAL geometric ideals retains their SAME
entire tensor-ideal inclusion under the actual equality transport. -/
theorem tensorIdeal_eq_transport {X : Scheme.{u}} (B : X.Modules)
    {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg (fun K : X.IdealSheafData => Scheme.Modules.tensorObj B K.toModules) h)).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap B J.toModules J.toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion := by
  subst J
  exact Category.id_comp _

/-- The original entire tensor-ideal inclusion is natural for the SAME
actual original whole module isomorphism. -/
theorem tensorLeftIso_inclusion {X : Scheme.{u}} {B N : X.Modules}
    (e : B ≅ N) (I : X.IdealSheafData) :
    (tensorObjCongr e (Iso.refl I.toModules)).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap N I.toModules I.toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion ≫ e.hom := by
  apply (cancel_epi (ModularCurves.monoidalTensorObjIso B I.toModules).hom).mp
  rw [← Category.assoc, ModularCurves.cartierMonoidalTensorObjIso_hom_natural]
  simp only [Iso.refl_hom, tensorHom_id, Category.assoc]
  rw [SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  rw [← Category.assoc (ModularCurves.monoidalTensorObjIso B I.toModules).hom,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]
  exact (Category.assoc _ _ _).symm

/-- Actual flat Cartier transport and the SAME whole source and target
comparisons preserve the ENTIRE original factor/inclusion equation. -/
theorem transport_iso_inclusion {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q]
    (J : X.IdealSheafData) (hJ : J.IsInvertible) {C B : X.Modules} {A N : Y.Modules}
    (a : A ≅ (pullback q).obj C) (b : (pullback q).obj B ≅ N)
    (c : C ≅ Scheme.Modules.tensorObj B J.toModules) (δ : C ⟶ B)
    (hc : c.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap B _ J.toModulesInclusion = δ) :
    (a ≪≫ (pullback q).mapIso c ≪≫ flatCartierTensorIso q B J hJ ≪≫
        tensorObjCongr b (Iso.refl _)).hom ≫
          SchemeTensorObjMorphisms.tensorObjIdealMap N _ (J.comap q).toModulesInclusion =
      a.hom ≫ (pullback q).map δ ≫ b.hom := by
  let F := pullback q
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [tensorLeftIso_inclusion b (J.comap q)]
  calc
    _ = a.hom ≫ F.map c.hom ≫ F.map
        (SchemeTensorObjMorphisms.tensorObjIdealMap B _ J.toModulesInclusion) ≫ b.hom := by
      simpa only [Category.assoc] using congrArg (fun z => a.hom ≫ F.map c.hom ≫ z ≫ b.hom)
        (flatCartierTensorIso_inclusion q B J hJ)
    _ = _ := by
      rw [← Category.assoc (F.map c.hom), ← F.map_comp, hc]

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareTensor
