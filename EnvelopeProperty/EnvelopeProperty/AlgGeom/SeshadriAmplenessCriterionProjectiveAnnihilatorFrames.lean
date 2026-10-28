import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import ModularCurves.EllipticCurve.PullbackTensorSection

/-! # Original section tensor frames for the actual coherent annihilator

The construction uses actual restriction-unit maps, actual native tensor
comparisons and original line frames. It supplies section tensor values for
untwisting the same finite-kernel annihilator, without an incoming annihilation
or tensor-comparison certificate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem restrictUnit_sections_bijective {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) :
    Function.Bijective
      (((restrictAdjunction U.ι).unit.app M).val.app (.op U)) := by
  have hpre : U.ι ⁻¹ᵁ U = ⊤ := by
    ext y
    exact iff_true_intro y.property
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U :=
    (congrArg (fun V => U.ι ''ᵁ V) hpre).trans U.ι_image_top
  have heq : homOfLE (U.ι.image_preimage_le U) = eqToHom himg :=
    Subsingleton.elim _ _
  let : IsIso (homOfLE (U.ι.image_preimage_le U)) := by
    rw [heq]
    infer_instance
  change Function.Bijective
    (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op)
  exact ConcreteCategory.bijective_of_isIso _

private def originalRightUnitTensorIso {X : Scheme.{u}}
    (M : X.Modules) : M ⊗ unitObj X ≅ M :=
  ModularCurves.monoidalTensorObjIso M (unitObj X) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
      Scheme.Modules.sheafifyValIso M

private theorem originalRightUnitTensorIso_tensorSection {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) (a : Γ(X, U)) :
    (originalRightUnitTensorIso M).hom.val.app (.op U)
      (ModularCurves.tensorSection M (unitObj X) U m a) = a • m := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let q : (M.val ⊗ (unitObj X).val).obj (.op U) := m ⊗ₜ a
  let uq := (adj.unit.app (M.val ⊗ (unitObj X).val)).app (.op U) q
  let e := ModularCurves.monoidalTensorObjIso M (unitObj X)
  let f := (ρ_ M.val).hom
  let c := Scheme.Modules.sheafifyValIso M
  have hcancel := Scheme.Modules.iso_inv_hom_app_applyT e (.op U) uq
  change c.hom.val.app (.op U) ((L.map f).val.app (.op U)
    (e.hom.val.app (.op U) (e.inv.val.app (.op U) uq))) = a • m
  have hnat := adj.unit_naturality f
  have htri := adj.right_triangle_components M
  change adj.unit.app (M.val ⊗ (unitObj X).val) ≫ (L.map f).val =
    f ≫ adj.unit.app M.val at hnat
  change adj.unit.app M.val ≫ c.hom.val = 𝟙 M.val at htri
  have hpre : adj.unit.app (M.val ⊗ (unitObj X).val) ≫
      (L.map f).val ≫ c.hom.val = f := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ c.hom.val) hnat).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => f ≫ k) htri).trans (Category.comp_id f))))
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (.op U)) hpre) q
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hp
  have h := ConcreteCategory.congr_hom
    (PresheafOfModules.rightUnitor_hom_app M.val (.op U)) q
  exact (congrArg (fun z => c.hom.val.app (.op U)
      ((L.map f).val.app (.op U) z)) hcancel).trans
    (hp.trans (h.trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply
      (R := X.sheaf.obj.obj (.op U))
      (M := M.val.obj (.op U)) m a)))

private def originalFrameTensorIso {X : Scheme.{u}} (M T : X.Modules)
    (U : X.Opens) (e : T.restrict U.ι ≅ unitObj U.toScheme) :
    (M ⊗ T).restrict U.ι ≅ M.restrict U.ι :=
  ModularCurves.restrictMonoidalTensorIso U.ι M T ≪≫
    (Iso.refl (M.restrict U.ι) ⊗ᵢ e) ≪≫
      originalRightUnitTensorIso (M.restrict U.ι)

private theorem originalFrameTensorIso_tensorSection {X : Scheme.{u}}
    (M T : X.Modules) (U : X.Opens)
    (e : T.restrict U.ι ≅ unitObj U.toScheme) (t : Γ(T, U))
    (ht : e.hom.val.app (.op (U.ι ⁻¹ᵁ U))
      (((restrictAdjunction U.ι).unit.app T).val.app (.op U) t) =
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)))
    (m : Γ(M, U)) :
    (originalFrameTensorIso M T U e).hom.val.app (.op (U.ι ⁻¹ᵁ U))
      (((restrictAdjunction U.ι).unit.app (M ⊗ T)).val.app (.op U)
        (ModularCurves.tensorSection M T U m t)) =
      ((restrictAdjunction U.ι).unit.app M).val.app (.op U) m := by
  let Z := U.ι ⁻¹ᵁ U
  let A := M.restrict U.ι
  let B := T.restrict U.ι
  let m' : Γ(A, Z) := ((restrictAdjunction U.ι).unit.app M).val.app (.op U) m
  let t' : Γ(B, Z) := ((restrictAdjunction U.ι).unit.app T).val.app (.op U) t
  have hrestrict :
      (ModularCurves.restrictMonoidalTensorIso U.ι M T).hom.val.app (.op Z)
        (((restrictAdjunction U.ι).unit.app (M ⊗ T)).val.app (.op U)
          (ModularCurves.tensorSection M T U m t)) =
        ModularCurves.tensorSection A B Z m' t' := by
    have hnative := ModularCurves.restrictMonoidalTensorIso_localModuleSection M T U m t
    have hP := Scheme.Modules.overFunctorEquiv_hom_localModuleSection_preimageT
      (M ⊗ T) U (ModularCurves.tensorSection M T U m t)
    have hM := Scheme.Modules.overFunctorEquiv_hom_localModuleSection_preimageT M U m
    have hT := Scheme.Modules.overFunctorEquiv_hom_localModuleSection_preimageT T U t
    exact (congrArg
      (fun z => (ModularCurves.restrictMonoidalTensorIso U.ι M T).hom.val.app
        (.op Z) z) hP.symm).trans
      (hnative.trans (congrArg₂ (ModularCurves.tensorSection A B Z) hM hT))
  have hmap : (𝟙 A ⊗ₘ e.hom).val.app (.op Z)
      (ModularCurves.tensorSection A B Z m' t') =
      ModularCurves.tensorSection A (unitObj U.toScheme) Z m'
        (e.hom.val.app (.op Z) t') :=
    ModularCurves.tensorSection_map (𝟙 A) e.hom Z m' t'
  change (originalRightUnitTensorIso A).hom.val.app (.op Z)
    ((𝟙 A ⊗ₘ e.hom).val.app (.op Z)
      ((ModularCurves.restrictMonoidalTensorIso U.ι M T).hom.val.app (.op Z)
        (((restrictAdjunction U.ι).unit.app (M ⊗ T)).val.app (.op U)
          (ModularCurves.tensorSection M T U m t)))) = m'
  exact (congrArg (fun z => (originalRightUnitTensorIso A).hom.val.app (.op Z)
      ((𝟙 A ⊗ₘ e.hom).val.app (.op Z) z)) hrestrict).trans
    ((congrArg (fun z => (originalRightUnitTensorIso A).hom.val.app (.op Z) z)
      hmap).trans
      ((originalRightUnitTensorIso_tensorSection A Z m' _).trans
        ((congrArg (fun a : Γ(U.toScheme, Z) => a • m') ht).trans (one_smul _ _))))

/-- A genuine local line frame supplies one original coefficient-one section
whose original pure-tensor maps are bijective for every original module. -/
theorem exists_tensorSection_bijective_of_frame {X : Scheme.{u}}
    (T : X.Modules) (U : X.Opens) (e : T.restrict U.ι ≅ unitObj U.toScheme) :
    ∃ t : Γ(T, U), ∀ M : X.Modules,
      Function.Bijective (fun m : Γ(M, U) => ModularCurves.tensorSection M T U m t) := by
  let Z := U.ι ⁻¹ᵁ U
  obtain ⟨t, ht⟩ := (restrictUnit_sections_bijective T U).2
    (e.inv.val.app (.op Z) (1 : Γ(U.toScheme, Z)))
  have htone : e.hom.val.app (.op Z)
      (((restrictAdjunction U.ι).unit.app T).val.app (.op U) t) =
        (1 : Γ(U.toScheme, Z)) :=
    (congrArg (fun z => e.hom.val.app (.op Z) z) ht).trans
      (Scheme.Modules.iso_inv_hom_app_applyT e (.op Z) (1 : Γ(U.toScheme, Z)))
  refine ⟨t, fun M => ?_⟩
  let j := ((restrictAdjunction U.ι).unit.app M).val.app (.op U)
  let k := ((restrictAdjunction U.ι).unit.app (M ⊗ T)).val.app (.op U)
  let c := originalFrameTensorIso M T U e
  let cZ := (SheafOfModules.evaluation U.toScheme.ringCatSheaf (.op Z)).mapIso c
  have hj := restrictUnit_sections_bijective M U
  have hk := restrictUnit_sections_bijective (M ⊗ T) U
  have hc : Function.Bijective cZ.hom := ConcreteCategory.bijective_of_isIso _
  have hvalue (m : Γ(M, U)) :
      cZ.hom (k (ModularCurves.tensorSection M T U m t)) = j m :=
    originalFrameTensorIso_tensorSection M T U e t htone m
  constructor
  · intro m n h
    exact hj.1 ((hvalue m).symm.trans
      ((congrArg (fun z => cZ.hom (k z)) h).trans (hvalue n)))
  · intro w
    obtain ⟨m, hm⟩ := hj.2 (cZ.hom (k w))
    exact ⟨m, hk.1 (hc.1 ((hvalue m).trans hm))⟩

end EnvelopeProperty.SeshadriAmplenessCriterion
