import EnvelopeProperty.AlgGeom.QuasicoherentImageFactorization
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import EnvelopeProperty.AlgGeom.InvertibleSheafBaseIdeal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Whole image of an actual original family of invertible-sheaf sections -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
noncomputable section
universe u v w
namespace EnvelopeProperty.InvertibleSectionFamilyImage
open Scheme.Modules InvertibleSheafBaseIdeal QuasicoherentImageFactorization
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem summand_factor {C : Type u} [Category.{v} C] {ι : Type w}
    (f : ι → C) [HasCoproduct f] {M N P : C} (e : M ≅ ∐ f)
    (q : ∀ i, f i ⟶ P) (p : M ⟶ N) (j : N ⟶ P)
    (h : p ≫ j = e.hom ≫ Sigma.desc q) (i : ι) :
    (Sigma.ι f i ≫ e.inv ≫ p) ≫ j = q i := by
  rw [Category.assoc, Category.assoc, h, Iso.inv_hom_id_assoc, Sigma.ι_desc]

/-- The actual native unit tensor comparison with the original dual line. -/
def unitTensorDualIso {X : Scheme.{u}} (L : X.Modules) :
    unitObj X ⊗ dualObj L ≅ dualObj L :=
  ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl (dualObj L)) ≪≫
    λ_ (dualObj L)

/-- The actual free-module tensor is the coproduct of the SAME original dual. -/
def freeTensorDualIso {X : Scheme.{u}} {L : X.Modules} (hL : IsInvertible L)
    (ι : Type u) :
    (tensorRight (C := X.Modules) (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) ι) ≅
      ∐ (fun _ : ι => dualObj L) := by
  let : (tensorRight (dualObj L)).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence (dualObj L) hL.dual
  exact PreservesCoproduct.iso (tensorRight (dualObj L)) (fun _ : ι => unitObj X) ≪≫
    Sigma.mapIso (fun _ : ι => unitTensorDualIso L)

/-- The true original free-module tensor source is quasicoherent. -/
theorem freeTensorDual_isQuasicoherent {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (ι : Type u) :
    ((tensorRight (C := X.Modules) (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) ι)).IsQuasicoherent :=
  SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight _ _ hL.dual

/-- Transport the coproduct of the original evaluations through the canonical
free tensor comparison; no chosen frame or comparison premise is used. -/
def familyEvaluation {X : Scheme.{u}} {L : X.Modules} (hL : IsInvertible L)
    {ι : Type u} (s : ι → Γ(L, ⊤)) :
    (tensorRight (C := X.Modules) (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) ι) ⟶ unitObj X :=
  (freeTensorDualIso hL ι).hom ≫ Sigma.desc (fun i => sectionEvaluation L (s i))

private theorem image_coproduct_transport {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {ι : Type u}
    (e : M ≅ ∐ (fun _ : ι => N)) (q : ι → (N ⟶ unitObj X)) :
    QuasicoherentImageIdeal.imageIdeal M (e.hom ≫ Sigma.desc q) =
      ⨆ i, QuasicoherentImageIdeal.imageIdeal N (q i) := by
  let α : M ⟶ unitObj X := e.hom ≫ Sigma.desc q
  let J : X.IdealSheafData := ⨆ i, QuasicoherentImageIdeal.imageIdeal N (q i)
  apply le_antisymm
  · apply (imageIdeal_le_iff_factor α J).mpr
    let b (i : ι) : N ⟶ J.toModules :=
      factorOfImageLE (q i) J
        (le_iSup (fun i => QuasicoherentImageIdeal.imageIdeal N (q i)) i)
    refine ⟨e.hom ≫ Sigma.desc b, ?_⟩
    change e.hom ≫ Sigma.desc b ≫ J.toModulesInclusion = e.hom ≫ Sigma.desc q
    congr 1
    apply Sigma.hom_ext
    intro i
    have hb : b i ≫ J.toModulesInclusion = q i := factorOfImageLE_inclusion _ _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ J.toModulesInclusion) (Sigma.ι_desc b i)).trans
        (hb.trans (Sigma.ι_desc q i).symm))
  · apply iSup_le
    intro i
    apply (imageIdeal_le_iff_factor (q i) _).mpr
    refine ⟨Sigma.ι (fun _ : ι => N) i ≫ e.inv ≫
      QuasicoherentImageModule.imageFactor α, ?_⟩
    exact summand_factor (C := X.Modules) _ e q _ _
      (QuasicoherentImageModule.imageFactor_inclusion α) i

/-- The whole actual image is precisely the sum of all the original section ideals. -/
theorem familyEvaluation_imageIdeal {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) {ι : Type u} (s : ι → Γ(L, ⊤)) :
    let : ((tensorRight (C := X.Modules) (dualObj L)).obj
      (SheafOfModules.free (R := X.ringCatSheaf) ι)).IsQuasicoherent :=
      freeTensorDual_isQuasicoherent hL ι
    QuasicoherentImageIdeal.imageIdeal _ (familyEvaluation hL s) =
      ⨆ i, sectionIdeal hL (s i) := by
  let : ((tensorRight (C := X.Modules) (dualObj L)).obj
    (SheafOfModules.free (R := X.ringCatSheaf) ι)).IsQuasicoherent :=
    freeTensorDual_isQuasicoherent hL ι
  let : (dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  exact image_coproduct_transport (freeTensorDualIso hL ι)
    (fun i => sectionEvaluation L (s i))

end EnvelopeProperty.InvertibleSectionFamilyImage
