import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorFiniteType
import EnvelopeProperty.AlgGeom.GeometricIdealKernelModuleComparison
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCoherentDevissage
import EnvelopeProperty.AlgGeom.SchemeModuleStalkLinearity
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionProjectiveAnnihilatorFrames
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.RingTheory.Ideal.Colon
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso

/-! # Actual finite-kernel projective coherent annihilators

The actual ideal-twist generators and their original multiplication arrows
will construct a finite coherent kernel. Original stalk annihilation is to be
proved from those same generators, with no incoming annihilator certificate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules Opposite
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

open CategoryTheory.MonoidalCategory
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

noncomputable local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

private def idealTwistMap {X : Scheme.{u}} (J T : X.Modules)
    (inc : J ⟶ unitObj X) : J ⊗ T ⟶ T :=
  (inc ⊗ₘ 𝟙 T) ≫ (SchemeTensorUnitSections.leftUnitIso T).hom

private theorem idealTwistMap_tensorSection {X : Scheme.{u}}
    (J T : X.Modules) (inc : J ⟶ unitObj X) (U : X.Opens)
    (b : Γ(J, U)) (t : Γ(T, U)) :
    (idealTwistMap J T inc).val.app (op U)
      (ModularCurves.tensorSection J T U b t) =
      (show Γ(X, U) from inc.val.app (op U) b) • t := by
  have hmap : (inc ⊗ₘ 𝟙 T).val.app (op U)
      (ModularCurves.tensorSection J T U b t) =
      ModularCurves.tensorSection (unitObj X) T U (inc.val.app (op U) b) t :=
    ModularCurves.tensorSection_map inc (𝟙 T) U b t
  change (SchemeTensorUnitSections.leftUnitIso T).hom.val.app (op U)
    ((inc ⊗ₘ 𝟙 T).val.app (op U)
      (ModularCurves.tensorSection J T U b t)) = _
  exact (congrArg
    (fun z => (SchemeTensorUnitSections.leftUnitIso T).hom.val.app (op U) z)
    hmap).trans (SchemeTensorUnitSections.leftUnitIso_hom_tensorSection T U _ t)

private def idealTwistGenerator {X : Scheme.{u}} (J T : X.Modules)
    (inc : J ⟶ unitObj X) (G : (J ⊗ T).GeneratingSections) (i : G.I) :
    unitObj X ⟶ T :=
  SchemeGeneratingSectionsUnit.generatorHom G i ≫ idealTwistMap J T inc

private def sectionMultiplication {X : Scheme.{u}} (F T : X.Modules)
    (s : unitObj X ⟶ T) : F ⟶ F ⊗ T where
  val :=
    { app U := by
        let R : RingCat.{u} := X.ringCatSheaf.obj.obj U
        let A : ModuleCat R := F.val.obj U
        let B : ModuleCat R := (Scheme.Modules.tensorObj F T).val.obj U
        let C : ModuleCat R := (F ⊗ T).val.obj U
        let t : Γ(T, U.unop) := s.val.app U (1 : Γ(X, U.unop))
        let b : A →ₗ[R] B :=
          { toFun := fun m => CanonicalGeometry.tensorSection F T U.unop m t
            map_add' := fun m n => CanonicalGeometry.tensorSection_add_left F T U.unop m n t
            map_smul' := fun r m => CanonicalGeometry.tensorSection_smul_left F T U.unop r m t }
        let e : B ⟶ C := (ModularCurves.monoidalTensorObjIso F T).inv.val.app U
        exact ModuleCat.ofHom (e.hom.comp b)
      naturality := fun {U V} f => by
        apply ModuleCat.hom_ext
        ext m
        let v := (Scheme.Modules.toPresheaf X).map s
        have hn := ConcreteCategory.congr_hom (v.naturality f)
          (1 : Γ(X, U.unop))
        have hunit : (unitObj X).presheaf.map f (1 : Γ(X, U.unop)) =
            (1 : Γ(X, V.unop)) := (X.presheaf.map f).hom.map_one
        have hs : T.presheaf.map f (s.val.app U (1 : Γ(X, U.unop))) =
            s.val.app V (1 : Γ(X, V.unop)) :=
          hn.symm.trans (congrArg (fun z => s.val.app V z) hunit)
        have hres := ModularCurves.tensorSection_restrict F T f.unop.le m
          (s.val.app U (1 : Γ(X, U.unop)))
        have hthin : (homOfLE f.unop.le).op = f := Subsingleton.elim _ _
        cases hthin
        exact (congrArg (ModularCurves.tensorSection F T V.unop
          (F.presheaf.map _ m)) hs).symm.trans hres.symm }


private theorem sectionMultiplication_apply {X : Scheme.{u}} (F T : X.Modules)
    (s : unitObj X ⟶ T) (U : X.Opens) (m : Γ(F, U)) :
    (sectionMultiplication F T s).val.app (op U) m =
      ModularCurves.tensorSection F T U m (s.val.app (op U) (1 : Γ(X, U))) := rfl


private def sectionTuple {X : Scheme.{u}} (F T : X.Modules) {r : ℕ}
    (s : Fin r → (unitObj X ⟶ T)) : F ⟶ biproduct (fun _ : Fin r => F ⊗ T) :=
  biproduct.lift (fun i => sectionMultiplication F T (s i))

private def sectionKernel {X : Scheme.{u}} (F T : X.Modules) {r : ℕ}
    (s : Fin r → (unitObj X ⟶ T)) : X.Modules :=
  kernel (sectionTuple F T s)

private theorem sectionTupleTarget_quasicoherent {X : Scheme.{u}}
    (F T : X.Modules) [F.IsQuasicoherent] (hT : IsInvertible T) (r : ℕ) :
    (biproduct (fun _ : Fin r => F ⊗ T)).IsQuasicoherent := by
  let P : Fin r → X.Modules := fun _ => F ⊗ T
  have hFT : (F ⊗ T).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight F T hT
  have hP : (∐ P).IsQuasicoherent :=
    isQuasicoherent_coproduct P (fun _ => hFT)
  exact (isQuasicoherent X).prop_of_iso (biproduct.isoCoproduct P).symm hP

private theorem sectionKernel_quasicoherent {X : Scheme.{u}}
    (F T : X.Modules) [F.IsQuasicoherent] (hT : IsInvertible T) {r : ℕ}
    (s : Fin r → (unitObj X ⟶ T)) : (sectionKernel F T s).IsQuasicoherent := by
  let : (biproduct (fun _ : Fin r => F ⊗ T)).IsQuasicoherent :=
    sectionTupleTarget_quasicoherent F T hT r
  exact isQuasicoherent_kernel (sectionTuple F T s)

private theorem sectionKernel_finiteType {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F T : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hT : IsInvertible T) {r : ℕ}
    (s : Fin r → (unitObj X ⟶ T)) : (sectionKernel F T s).IsFiniteType := by
  let : (biproduct (fun _ : Fin r => F ⊗ T)).IsQuasicoherent :=
    sectionTupleTarget_quasicoherent F T hT r
  exact isFiniteType_kernel (sectionTuple F T s)


private theorem exists_kernel_section {X : Scheme.{u}} {F G : X.Modules}
    (q : F ⟶ G) (U : X.Opens) (s : Γ(F, U))
    (hs : q.val.app (op U) s = 0) :
    ∃ t : Γ(kernel q, U), (kernel.ι q).val.app (op U) t = s := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let v : E.obj F ⟶ E.obj G := E.map q
  let a : ModuleCat.of (X.ringCatSheaf.obj.obj (op U)) v.hom.ker ≅
      E.obj (kernel q) :=
    (ModuleCat.kernelIsoKer v).symm ≪≫ (PreservesKernel.iso E q).symm
  have ha : a.hom ≫ E.map (kernel.ι q) = ModuleCat.ofHom v.hom.ker.subtype := by
    change ((ModuleCat.kernelIsoKer v).inv ≫ (PreservesKernel.iso E q).inv) ≫
      E.map (kernel.ι q) = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => (ModuleCat.kernelIsoKer v).inv ≫ h)
        (PreservesKernel.iso_inv_ι E q)).trans
        (ModuleCat.kernelIsoKer_inv_kernel_ι v))
  let z : v.hom.ker := ⟨s, hs⟩
  exact ⟨a.hom z, ConcreteCategory.congr_hom ha z⟩

private theorem kernel_stalk_lift {X : Scheme.{u}} {F G : X.Modules}
    (q : F ⟶ G) (x : X) (m : F.presheaf.stalk x)
    (hm : ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map q) m = 0) :
    ∃ t : (kernel q).presheaf.stalk x,
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (kernel.ι q)) t = m := by
  obtain ⟨U, hxU, s, hs⟩ := F.presheaf.exists_germ_eq m
  let v := (Scheme.Modules.toPresheaf X).map q
  have hg : G.presheaf.germ U x hxU (q.val.app (op U) s) =
      G.presheaf.germ U x hxU 0 := by
    have hn := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU v s
    exact hn.symm.trans ((congrArg
      (fun a => (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map v a) hs).trans
        (hm.trans (map_zero (G.presheaf.germ U x hxU).hom).symm))
  obtain ⟨V, hxV, i, j, he⟩ := G.presheaf.germ_eq x hxU hxU _ _ hg
  have hzero : q.val.app (op V) (F.presheaf.map i.op s) = 0 := by
    have hn := ConcreteCategory.congr_hom (v.naturality i.op) s
    change q.val.app (op V) (F.presheaf.map i.op s) =
      G.presheaf.map i.op (q.val.app (op U) s) at hn
    exact hn.trans (he.trans (map_zero _))
  obtain ⟨t, ht⟩ := exists_kernel_section q V (F.presheaf.map i.op s) hzero
  refine ⟨(kernel q).presheaf.germ V x hxV t, ?_⟩
  have hn := TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
    ((Scheme.Modules.toPresheaf X).map (kernel.ι q)) t
  exact hn.trans ((congrArg (F.presheaf.germ V x hxV) ht).trans
    ((F.presheaf.germ_res_apply i x hxV s).trans hs))

private theorem kernel_stalk_injective {X : Scheme.{u}} {F G : X.Modules}
    (q : F ⟶ G) (x : X) :
    Function.Injective ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (kernel.ι q)) := by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (f := (Scheme.Modules.toPresheaf X).map (kernel.ι q))
  intro U
  let a : kernel q ⟶ F := kernel.ι q
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  change Function.Injective (E.map a)
  let e : E.obj (kernel q) ≅ kernel (E.map q) := PreservesKernel.iso E q
  have he : e.inv ≫ E.map a = kernel.ι (E.map q) :=
    PreservesKernel.iso_inv_ι E q
  have hi : Function.Injective e.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom).1
  have hk : Function.Injective (kernel.ι (E.map q)) :=
    (ModuleCat.mono_iff_injective (kernel.ι (E.map q))).mp inferInstance
  intro b c hbc
  apply hi
  apply hk
  have hb : kernel.ι (E.map q) (e.hom b) = (E.map a) b :=
    (ConcreteCategory.congr_hom he (e.hom b)).symm.trans
      (congrArg (fun z => (E.map a) z) (ConcreteCategory.congr_hom e.hom_inv_id b))
  have hc : kernel.ι (E.map q) (e.hom c) = (E.map a) c :=
    (ConcreteCategory.congr_hom he (e.hom c)).symm.trans
      (congrArg (fun z => (E.map a) z) (ConcreteCategory.congr_hom e.hom_inv_id c))
  exact hb.trans (hbc.trans hc.symm)

#check @AlgebraicGeometry.Scheme.IdealSheafData.isFinitePresentation_toModules
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.isFinitePresentation_toModules

private theorem additive_biproduct_total {C : Type*} [Category C] [Preadditive C]
    {R : Type u} [Ring R] (E : C ⥤ ModuleCat R) [E.Additive]
    {n : ℕ} (P : Fin n → C) [HasBiproduct P] (t : E.obj (biproduct P)) :
    ∑ i, (E.map (biproduct.π P i ≫ biproduct.ι P i)).hom t = t := by
  have h := congrArg (fun a => (E.map a).hom t) (biproduct.total (f := P))
  have hs : (∑ i, (E.map (biproduct.π P i ≫ biproduct.ι P i)).hom t) =
      (E.map (𝟙 (biproduct P))).hom t := by
    simpa only [Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply] using h
  exact hs.trans (ConcreteCategory.congr_hom (E.map_id (biproduct P)) t)

private theorem finiteGeneratorDesc_epi {X : Scheme.{u}} {M : X.Modules}
    (G : M.GeneratingSections) (n : ℕ) (e : G.I ≃ Fin n) :
    Epi (biproduct.desc (fun i : Fin n =>
      SchemeGeneratingSectionsUnit.generatorHom G (e.symm i))) := by
  let P : Fin n → X.Modules := fun _ => unitObj X
  let : HasBiproduct P := inferInstanceAs (HasBiproduct (fun _ : Fin n => unitObj X))
  let q : biproduct P ⟶ M := biproduct.desc (fun i =>
    SchemeGeneratingSectionsUnit.generatorHom G (e.symm i))
  let A : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) G.I
  let H := SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) G.I
  let K : Cofan (fun _ : G.I => unitObj X) :=
    Cofan.mk (biproduct P) (fun i => biproduct.ι P (e i))
  let h : A ⟶ biproduct P := H.desc K
  have hf : h ≫ q = G.π := by
    apply H.hom_ext
    intro j
    obtain ⟨i⟩ := j
    change SheafOfModules.ιFree i ≫ (h ≫ q) =
      SchemeGeneratingSectionsUnit.generatorHom G i
    have h1 : SheafOfModules.ιFree i ≫ h = biproduct.ι P (e i) := H.fac K ⟨i⟩
    have h2 : biproduct.ι P (e i) ≫ q =
        SchemeGeneratingSectionsUnit.generatorHom G i :=
      (biproduct.ι_desc _ _).trans
        (congrArg (SchemeGeneratingSectionsUnit.generatorHom G) (e.symm_apply_apply i))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ q) h1).trans h2)
  let : Epi (h ≫ q) := hf.symm ▸ G.epi
  exact epi_of_epi h q

/-- The same actual finite global generating family spans every original affine section module. -/
theorem finiteGenerator_span {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (G : M.GeneratingSections) [G.IsFiniteType]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Submodule.span Γ(X, U) (Set.range fun i : G.I =>
      (SchemeGeneratingSectionsUnit.generatorHom G i).val.app (op U)
        (1 : Γ(X, U))) = ⊤ := by
  classical
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  let : Fintype G.I := Fintype.ofFinite G.I
  let n := Fintype.card G.I
  let e : G.I ≃ Fin n := Fintype.equivFin G.I
  let P : Fin n → X.Modules := fun _ => unitObj X
  let hB : HasBiproduct P := inferInstanceAs (HasBiproduct (fun _ : Fin n => unitObj X))
  let q : biproduct P ⟶ M := biproduct.desc (fun i =>
    SchemeGeneratingSectionsUnit.generatorHom G (e.symm i))
  let : Epi q := finiteGeneratorDesc_epi G n e
  let : (unitObj X).IsQuasicoherent := by
    let c : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ unitObj X :=
      coproductUniqueIso (fun _ : PUnit => unitObj X)
    exact (isQuasicoherent X).prop_of_iso c inferInstance
  let : (biproduct P).IsQuasicoherent :=
    (isQuasicoherent X).prop_of_iso (biproduct.isoCoproduct P).symm
      (isQuasicoherent_coproduct P (fun _ => inferInstance))
  let E : X.Modules ⥤ ModuleCat Γ(X, U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let hE : E.Additive := by
    constructor
    intro A B f g
    rfl
  apply top_unique
  intro z _
  obtain ⟨t, ht⟩ := isQuasicoherent_app_surjective_of_epi U hU q z
  have htotal : ∑ i, (E.map (biproduct.π P i ≫ biproduct.ι P i)).hom t = t :=
    @additive_biproduct_total X.Modules inferInstance inferInstance Γ(X, U)
      inferInstance E hE n P hB t
  have htspan : ∀ i : Fin n,
      (q.val.app (op U)).hom
        ((E.map (biproduct.π P i ≫ biproduct.ι P i)).hom t) ∈
      Submodule.span Γ(X, U) (Set.range fun j : G.I =>
        (SchemeGeneratingSectionsUnit.generatorHom G j).val.app (op U)
          (1 : Γ(X, U))) := by
    intro i
    have hq : biproduct.ι P i ≫ q =
        SchemeGeneratingSectionsUnit.generatorHom G (e.symm i) := biproduct.ι_desc _ _
    let r : Γ(X, U) := (E.map (biproduct.π P i)).hom t
    have hi := congrArg (fun a : unitObj X ⟶ M => (E.map a).hom r) hq
    have hc : (q.val.app (op U)).hom
        ((E.map (biproduct.π P i ≫ biproduct.ι P i)).hom t) =
      (E.map (SchemeGeneratingSectionsUnit.generatorHom G (e.symm i))).hom r :=
      (congrArg (fun w => (q.val.app (op U)).hom w)
        (ConcreteCategory.congr_hom
          (E.map_comp (biproduct.π P i) (biproduct.ι P i)) t)).trans
        ((ConcreteCategory.congr_hom
          (E.map_comp (biproduct.ι P i) q) r).symm.trans hi)
    have hs : (E.map (SchemeGeneratingSectionsUnit.generatorHom G (e.symm i))).hom
        (r * 1) = r •
        ((SchemeGeneratingSectionsUnit.generatorHom G (e.symm i)).val.app (op U)
          (1 : Γ(X, U))) :=
      (E.map (SchemeGeneratingSectionsUnit.generatorHom G (e.symm i))).hom.map_smul r
        (1 : Γ(X, U))
    have hs' := (congrArg
      (E.map (SchemeGeneratingSectionsUnit.generatorHom G (e.symm i))).hom
      (mul_one r)).symm.trans hs
    have hmem : r •
        ((SchemeGeneratingSectionsUnit.generatorHom G (e.symm i)).val.app (op U)
          (1 : Γ(X, U))) ∈
        Submodule.span Γ(X, U) (Set.range fun j : G.I =>
          (SchemeGeneratingSectionsUnit.generatorHom G j).val.app (op U)
            (1 : Γ(X, U))) :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm i, rfl⟩)
    exact (hc.trans hs').symm ▸ hmem
  let S : Submodule Γ(X, U) Γ(M, U) := Submodule.span Γ(X, U)
    (Set.range fun i : G.I => (SchemeGeneratingSectionsUnit.generatorHom G i).val.app (op U)
      (1 : Γ(X, U)))
  have hmem : (∑ i : Fin n, (q.val.app (op U)).hom
      ((E.map (biproduct.π P i ≫ biproduct.ι P i)).hom t)) ∈ S :=
    Submodule.sum_mem _ (fun i _ => htspan i)
  have hsum := map_sum (q.val.app (op U)).hom
    (fun i => (E.map (biproduct.π P i ≫ biproduct.ι P i)).hom t) Finset.univ
  have heq := hsum.symm.trans ((congrArg (q.val.app (op U)).hom htotal).trans ht)
  exact Eq.mp (congrArg (fun w : Γ(M, U) => w ∈ S) heq) hmem


private theorem native_tensorSection_add_right {X : Scheme.{u}}
    (F T : X.Modules) (U : X.Opens) (m : Γ(F, U)) (a b : Γ(T, U)) :
    ModularCurves.tensorSection F T U m (a + b) =
      ModularCurves.tensorSection F T U m a + ModularCurves.tensorSection F T U m b := by
  let e := ((ModularCurves.monoidalTensorObjIso F T).inv.val.app (op U)).hom
  exact (congrArg (fun z => e z)
    (CanonicalGeometry.tensorSection_add_right F T U m a b)).trans (e.map_add _ _)

private theorem native_tensorSection_smul_right {X : Scheme.{u}}
    (F T : X.Modules) (U : X.Opens) (r : Γ(X, U)) (m : Γ(F, U)) (t : Γ(T, U)) :
    ModularCurves.tensorSection F T U m (r • t) =
      r • ModularCurves.tensorSection F T U m t := by
  let e := ((ModularCurves.monoidalTensorObjIso F T).inv.val.app (op U)).hom
  exact (congrArg (fun z => e z)
    (CanonicalGeometry.tensorSection_smul_right F T U r m t)).trans (e.map_smul r _)

private theorem kernel_lift_component {C : Type*} [Category C] [HasZeroMorphisms C]
    {n : ℕ} (B : Fin n → C) [HasBiproduct B] {A : C}
    (s : ∀ i, A ⟶ B i) [HasKernel (biproduct.lift s)] (i : Fin n) :
    kernel.ι (biproduct.lift s) ≫ s i = 0 := by
  let q := biproduct.lift s
  have hq : q ≫ biproduct.π B i = s i := biproduct.lift_π s i
  exact (congrArg (fun f => kernel.ι q ≫ f) hq).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ biproduct.π B i) (kernel.condition q)).trans
        zero_comp))

#check fun {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) =>
  ∀ (x : X) (r : X.presheaf.stalk x), r ∈ I.stalkIdeal x →
    ∀ m : M.presheaf.stalk x, r • m = 0
#check @AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_map_germ
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_map_germ

private theorem kernel_twistedIdeal_tensor_zero {X : Scheme.{u}}
    (F J T : X.Modules) [J.IsQuasicoherent] (inc : J ⟶ unitObj X)
    (hT : IsInvertible T) (G : (J ⊗ T).GeneratingSections) [G.IsFiniteType]
    (r : ℕ) (e : G.I ≃ Fin r) (U : X.Opens) (hU : IsAffineOpen U) :
    let s : Fin r → (unitObj X ⟶ T) := fun i =>
      idealTwistGenerator J T inc G (e.symm i)
    let q := sectionTuple F T s
    ∀ k : Γ(kernel q, U), ∀ w : Γ(J ⊗ T, U),
      ModularCurves.tensorSection F T U ((kernel.ι q).val.app (op U) k)
        ((idealTwistMap J T inc).val.app (op U) w) = 0 := by
  let s : Fin r → (unitObj X ⟶ T) := fun i =>
    idealTwistGenerator J T inc G (e.symm i)
  let q : F ⟶ biproduct (fun _ : Fin r => F ⊗ T) := sectionTuple F T s
  change ∀ k : Γ(kernel q, U), ∀ w : Γ(J ⊗ T, U),
    ModularCurves.tensorSection F T U ((kernel.ι q).val.app (op U) k)
      ((idealTwistMap J T inc).val.app (op U) w) = 0
  intro k w
  let a : J ⊗ T ⟶ T := idealTwistMap J T inc
  let m : Γ(F, U) := (kernel.ι q).val.app (op U) k
  let p : Γ(J ⊗ T, U) →ₗ[Γ(X, U)] Γ(F ⊗ T, U) :=
    { toFun := fun z => ModularCurves.tensorSection F T U m (a.val.app (op U) z)
      map_add' := fun z z' =>
        (congrArg (ModularCurves.tensorSection F T U m)
          ((a.val.app (op U)).hom.map_add z z')).trans
          (native_tensorSection_add_right F T U m _ _)
      map_smul' := fun c z =>
        (congrArg (ModularCurves.tensorSection F T U m)
          ((a.val.app (op U)).hom.map_smul c z)).trans
          (native_tensorSection_smul_right F T U c m _) }
  have hcomp (i : G.I) : kernel.ι q ≫
      sectionMultiplication F T (idealTwistGenerator J T inc G i) = 0 := by
    have h : kernel.ι q ≫ sectionMultiplication F T (s (e i)) = 0 :=
      kernel_lift_component (fun _ : Fin r => F ⊗ T)
        (fun j => sectionMultiplication F T (s j)) (e i)
    have he : sectionMultiplication F T (s (e i)) =
        sectionMultiplication F T (idealTwistGenerator J T inc G i) :=
      congrArg (fun j => sectionMultiplication F T (idealTwistGenerator J T inc G j))
        (e.symm_apply_apply i)
    exact (congrArg (fun f => kernel.ι q ≫ f) he).symm.trans h
  have hgen (i : G.I) : p
      ((SchemeGeneratingSectionsUnit.generatorHom G i).val.app (op U)
        (1 : Γ(X, U))) = 0 := by
    have hc := congrArg (fun f : kernel q ⟶ F ⊗ T => f.val.app (op U) k) (hcomp i)
    have hc' : (sectionMultiplication F T (idealTwistGenerator J T inc G i)).val.app
        (op U) m = 0 := hc
    have hm := sectionMultiplication_apply F T (idealTwistGenerator J T inc G i) U m
    have ht : (idealTwistGenerator J T inc G i).val.app (op U) (1 : Γ(X, U)) =
        a.val.app (op U)
          ((SchemeGeneratingSectionsUnit.generatorHom G i).val.app (op U)
            (1 : Γ(X, U))) := rfl
    exact (congrArg (ModularCurves.tensorSection F T U m) ht).symm.trans
      (hm.symm.trans hc')
  let : (J ⊗ T).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight J T hT
  let S : Set Γ(J ⊗ T, U) := Set.range fun i : G.I =>
    (SchemeGeneratingSectionsUnit.generatorHom G i).val.app (op U) (1 : Γ(X, U))
  have hle : Submodule.span Γ(X, U) S ≤ p.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have htop : Submodule.span Γ(X, U) S = ⊤ := finiteGenerator_span (J ⊗ T) G U hU
  have hw : w ∈ Submodule.span Γ(X, U) S :=
    htop.symm ▸ (show w ∈ (⊤ : Submodule Γ(X, U) Γ(J ⊗ T, U)) from trivial)
  exact hle hw

private theorem native_tensorSection_zero_left {X : Scheme.{u}}
    (F T : X.Modules) (U : X.Opens) (t : Γ(T, U)) :
    ModularCurves.tensorSection F T U 0 t = 0 := by
  let e := ((ModularCurves.monoidalTensorObjIso F T).inv.val.app (op U)).hom
  exact (congrArg (fun z => e z)
    (CanonicalGeometry.tensorSection_zero_left F T U t)).trans e.map_zero

private theorem kernel_ideal_smul_zero_of_frame {X : Scheme.{u}}
    (F J T : X.Modules) [J.IsQuasicoherent] (inc : J ⟶ unitObj X)
    (hT : IsInvertible T) (G : (J ⊗ T).GeneratingSections) [G.IsFiniteType]
    (r : ℕ) (e : G.I ≃ Fin r) (U : X.Opens) (hU : IsAffineOpen U)
    (eT : T.restrict U.ι ≅ unitObj U.toScheme) :
    let s : Fin r → (unitObj X ⟶ T) := fun i =>
      idealTwistGenerator J T inc G (e.symm i)
    let q := sectionTuple F T s
    ∀ k : Γ(kernel q, U), ∀ b : Γ(J, U),
      (show Γ(X, U) from inc.val.app (op U) b) •
        ((kernel.ι q).val.app (op U) k) = 0 := by
  let s : Fin r → (unitObj X ⟶ T) := fun i =>
    idealTwistGenerator J T inc G (e.symm i)
  let q := sectionTuple F T s
  change ∀ k : Γ(kernel q, U), ∀ b : Γ(J, U),
    (show Γ(X, U) from inc.val.app (op U) b) •
      ((kernel.ι q).val.app (op U) k) = 0
  intro k b
  let m : Γ(F, U) := (kernel.ι q).val.app (op U) k
  let a : Γ(X, U) := inc.val.app (op U) b
  obtain ⟨t, ht⟩ := exists_tensorSection_bijective_of_frame T U eT
  have hz : ModularCurves.tensorSection F T U m
      ((idealTwistMap J T inc).val.app (op U)
        (ModularCurves.tensorSection J T U b t)) = 0 :=
    kernel_twistedIdeal_tensor_zero F J T inc hT G r e U hU k
      (ModularCurves.tensorSection J T U b t)
  have hzero : ModularCurves.tensorSection F T U (a • m) t = 0 :=
    (ModularCurves.tensorSection_smul F T U a m t).trans
      ((congrArg (ModularCurves.tensorSection F T U m)
        (idealTwistMap_tensorSection J T inc U b t).symm).trans hz)
  exact (ht F).1 (hzero.trans (native_tensorSection_zero_left F T U t).symm)

private theorem kernel_stalkIdeal_smul_zero {X : Scheme.{u}}
    (F T : X.Modules) (I : X.IdealSheafData) [I.toModules.IsQuasicoherent]
    (hT : IsInvertible T) (G : (I.toModules ⊗ T).GeneratingSections) [G.IsFiniteType]
    (r : ℕ) (e : G.I ≃ Fin r) :
    let s : Fin r → (unitObj X ⟶ T) := fun i =>
      idealTwistGenerator I.toModules T I.toModulesInclusion G (e.symm i)
    let q := sectionTuple F T s
    ∀ (x : X) (a : X.presheaf.stalk x), a ∈ I.stalkIdeal x →
      ∀ m : (kernel q).presheaf.stalk x, a • m = 0 := by
  let s : Fin r → (unitObj X ⟶ T) := fun i =>
    idealTwistGenerator I.toModules T I.toModulesInclusion G (e.symm i)
  let q := sectionTuple F T s
  let K := kernel q
  change ∀ (x : X) (a : X.presheaf.stalk x), a ∈ I.stalkIdeal x →
    ∀ m : K.presheaf.stalk x, a • m = 0
  intro x a ha m
  let inc : K ⟶ F := kernel.ι q
  let v : K.presheaf.stalk x →+ F.presheaf.stalk x :=
    ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map inc).hom
  obtain ⟨ι, U, hU, eU⟩ :=
    SchemeInvertibleTensorQuasicoherent.exists_affine_trivializing_cover T hT
  have hxcover : x ∈ ⨆ i, (U i).1 := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  obtain ⟨V, hVU, hxV, kV, hkV⟩ := K.presheaf.exists_le_germ_eq m hxi
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let A : X.affineOpens := ⟨W, hW⟩
  let k : Γ(K, W) := K.presheaf.map (homOfLE hWV).op kV
  have hk : K.presheaf.germ W x hxW k = m :=
    (K.presheaf.germ_res_apply (homOfLE hWV) x hxW kV).trans hkV
  let frame : T.restrict W.ι ≅ unitObj W.toScheme :=
    restrictOpenTrivialization (hWV.trans hVU) (eU i).some
  let n : Γ(F, W) := inc.val.app (op W) k
  have hn : F.presheaf.germ W x hxW n = v m :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
      ((Scheme.Modules.toPresheaf X).map inc) k).symm.trans (congrArg v hk)
  let J : Ideal (X.presheaf.stalk x) :=
    (⊥ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)).colon {v m}
  have hmap : (I.ideal A).map (X.presheaf.germ W x hxW).hom ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    let bI : Γ(I.toModules, W) := (I.toModulesSectionsEquiv A).symm ⟨b, hb⟩
    have hbI : (show Γ(X, W) from I.toModulesInclusion.val.app (op W) bI) = b := rfl
    have hlocal : b • n = 0 :=
      (congrArg (fun c : Γ(X, W) => c • n) hbI).symm.trans
        (kernel_ideal_smul_zero_of_frame F I.toModules T I.toModulesInclusion hT G
          r e W hW frame k bI)
    apply Submodule.mem_colon_singleton.mpr
    change X.presheaf.germ W x hxW b • v m = 0
    exact (congrArg (fun z : F.presheaf.stalk x => X.presheaf.germ W x hxW b • z)
      hn).symm.trans
        ((PresheafOfModules.germ_smul (R := X.presheaf) F.val x W hxW b n).symm.trans
          ((congrArg (F.presheaf.germ W x hxW) hlocal).trans
            (F.presheaf.germ W x hxW).hom.map_zero))
  have hle : I.stalkIdeal x ≤ J :=
    (I.stalkIdeal_eq_map_germ A hxW).trans_le hmap
  have hzero : a • v m = 0 := Submodule.mem_colon_singleton.mp (hle ha)
  apply kernel_stalk_injective q x
  exact (SchemeModuleStalkLinearity.stalkMap_smul inc x a m).trans
    (hzero.trans (map_zero v).symm)

private theorem original_stalkFunctor_additive {X : Scheme.{u}} (x : X) :
    (Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive := by
  constructor
  intro M N f g
  ext m
  obtain ⟨U, hxU, s, rfl⟩ := M.presheaf.exists_germ_eq m
  have hfg := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    ((Scheme.Modules.toPresheaf X).map (f + g)) s
  have hf := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    ((Scheme.Modules.toPresheaf X).map f) s
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    ((Scheme.Modules.toPresheaf X).map g) s
  have hadd : N.presheaf.germ U x hxU ((f + g).val.app (op U) s) =
      N.presheaf.germ U x hxU (f.val.app (op U) s) +
        N.presheaf.germ U x hxU (g.val.app (op U) s) :=
    (N.presheaf.germ U x hxU).hom.map_add _ _
  exact hfg.trans (hadd.trans (congrArg₂ (fun a b => a + b) hf.symm hg.symm))

private theorem additive_map_biproduct_lift_apply_zero {C : Type*}
    [Category C] [Preadditive C] {n : ℕ} (B : Fin n → C)
    [HasBiproduct B] {A : C} (E : C ⥤ AddCommGrpCat.{u}) [E.Additive]
    (f : ∀ i, A ⟶ B i) (m : E.obj A)
    (hm : ∀ i, E.map (f i) m = 0) : E.map (biproduct.lift f) m = 0 := by
  let q := biproduct.lift f
  have hq : q = ∑ i, f i ≫ biproduct.ι B i := by
    calc
      q = q ≫ 𝟙 _ := (Category.comp_id q).symm
      _ = q ≫ ∑ i, biproduct.π B i ≫ biproduct.ι B i :=
        congrArg (fun z => q ≫ z) (biproduct.total (f := B)).symm
      _ = ∑ i, q ≫ (biproduct.π B i ≫ biproduct.ι B i) :=
        Preadditive.comp_sum _ _ _
      _ = ∑ i, f i ≫ biproduct.ι B i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ biproduct.ι B i) (biproduct.lift_π f i))
  have heq : E.map q = ∑ i, E.map (f i) ≫ E.map (biproduct.ι B i) := by
    exact (congrArg (fun z => E.map z) hq).trans
      ((E.map_sum _ _).trans (Finset.sum_congr rfl (fun i _ => E.map_comp _ _)))
  let ev : (E.obj A ⟶ E.obj (biproduct B)) →+ E.obj (biproduct B) :=
    { toFun := fun z => z m
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsum : E.map q m = ∑ i, E.map (biproduct.ι B i) (E.map (f i) m) :=
    (congrArg ev heq).trans (map_sum ev _ _)
  exact hsum.trans (Finset.sum_eq_zero (fun i _ =>
    (congrArg (fun z => E.map (biproduct.ι B i) z) (hm i)).trans
      (E.map (biproduct.ι B i)).hom.map_zero))

private theorem native_tensorSection_germ_zero_left {X : Scheme.{u}}
    (F T : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U)
    (s : Γ(F, U)) (t : Γ(T, U)) (hs : F.presheaf.germ U x hx s = 0) :
    (F ⊗ T).presheaf.germ U x hx (ModularCurves.tensorSection F T U s t) = 0 := by
  have heq : F.presheaf.germ U x hx s = F.presheaf.germ U x hx 0 :=
    hs.trans (F.presheaf.germ U x hx).hom.map_zero.symm
  obtain ⟨V, hxV, i, j, hij⟩ := F.presheaf.germ_eq x hx hx s 0 heq
  have hsV : F.presheaf.map i.op s = 0 := hij.trans (map_zero _)
  have hthin : homOfLE i.le = i := Subsingleton.elim _ _
  have hres : (F ⊗ T).presheaf.map i.op (ModularCurves.tensorSection F T U s t) =
      ModularCurves.tensorSection F T V (F.presheaf.map i.op s)
        (T.presheaf.map i.op t) := by
    have h := ModularCurves.tensorSection_restrict F T i.le s t
    cases hthin
    exact h
  have hz : (F ⊗ T).presheaf.map i.op (ModularCurves.tensorSection F T U s t) = 0 :=
    hres.trans ((congrArg (fun z => ModularCurves.tensorSection F T V z
      (T.presheaf.map i.op t)) hsV).trans
        (native_tensorSection_zero_left F T V _))
  exact ((F ⊗ T).presheaf.germ_res_apply i x hxV _).symm.trans
    ((congrArg ((F ⊗ T).presheaf.germ V x hxV) hz).trans
      ((F ⊗ T).presheaf.germ V x hxV).hom.map_zero)

private theorem kernel_stalk_lift_of_ideal_annihilation {X : Scheme.{u}}
    (F T : X.Modules) (I : X.IdealSheafData) (hT : IsInvertible T)
    (G : (I.toModules ⊗ T).GeneratingSections) (r : ℕ) (e : G.I ≃ Fin r)
    (x : X) (m : F.presheaf.stalk x)
    (hm : ∀ a : X.presheaf.stalk x, a ∈ I.stalkIdeal x → a • m = 0) :
    let s : Fin r → (unitObj X ⟶ T) := fun i =>
      idealTwistGenerator I.toModules T I.toModulesInclusion G (e.symm i)
    let q := sectionTuple F T s
    ∃ k : (kernel q).presheaf.stalk x,
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (kernel.ι q)) k = m := by
  let s : Fin r → (unitObj X ⟶ T) := fun i =>
    idealTwistGenerator I.toModules T I.toModulesInclusion G (e.symm i)
  let q := sectionTuple F T s
  change ∃ k : (kernel q).presheaf.stalk x,
    ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (kernel.ι q)) k = m
  apply kernel_stalk_lift q x m
  obtain ⟨ι, U, hU, eU⟩ :=
    SchemeInvertibleTensorQuasicoherent.exists_affine_trivializing_cover T hT
  have hxcover : x ∈ ⨆ i, (U i).1 := by rw [hU]; trivial
  obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  obtain ⟨V, hVU, hxV, nV, hnV⟩ := F.presheaf.exists_le_germ_eq m hxj
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let A : X.affineOpens := ⟨W, hW⟩
  let n : Γ(F, W) := F.presheaf.map (homOfLE hWV).op nV
  have hn : F.presheaf.germ W x hxW n = m :=
    (F.presheaf.germ_res_apply (homOfLE hWV) x hxW nV).trans hnV
  let frame : T.restrict W.ι ≅ unitObj W.toScheme :=
    restrictOpenTrivialization (hWV.trans hVU) (eU j).some
  obtain ⟨t, ht⟩ := exists_tensorSection_bijective_of_frame T W frame
  let E := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let : E.Additive := original_stalkFunctor_additive x
  have hcomponents (i : Fin r) : E.map (sectionMultiplication F T (s i)) m = 0 := by
    let w : Γ(I.toModules ⊗ T, W) :=
      (SchemeGeneratingSectionsUnit.generatorHom G (e.symm i)).val.app (op W)
        (1 : Γ(X, W))
    obtain ⟨b, hb⟩ := (ht I.toModules).2 w
    let a : Γ(X, W) := I.toModulesInclusion.val.app (op W) b
    have ha : a ∈ I.ideal A := (I.toModulesSectionsEquiv A b).property
    have hax : X.presheaf.germ W x hxW a ∈ I.stalkIdeal x :=
      I.map_germ_le_stalkIdeal A hxW (Ideal.mem_map_of_mem _ ha)
    have hzero : F.presheaf.germ W x hxW (a • n) = 0 :=
      (PresheafOfModules.germ_smul (R := X.presheaf) F.val x W hxW a n).trans
        ((congrArg (fun z : F.presheaf.stalk x => X.presheaf.germ W x hxW a • z)
          hn).trans (hm _ hax))
    have hgen : (s i).val.app (op W) (1 : Γ(X, W)) = a • t :=
      (congrArg (fun z => (idealTwistMap I.toModules T I.toModulesInclusion).val.app
        (op W) z) hb).symm.trans
          (idealTwistMap_tensorSection I.toModules T I.toModulesInclusion W b t)
    have hvalue : (sectionMultiplication F T (s i)).val.app (op W) n =
        ModularCurves.tensorSection F T W (a • n) t :=
      (sectionMultiplication_apply F T (s i) W n).trans
        ((congrArg (ModularCurves.tensorSection F T W n) hgen).trans
          (ModularCurves.tensorSection_smul F T W a n t).symm)
    have hnat := TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
      ((Scheme.Modules.toPresheaf X).map (sectionMultiplication F T (s i))) n
    exact (congrArg (fun z => E.map (sectionMultiplication F T (s i)) z) hn).symm.trans
      (hnat.trans ((congrArg ((F ⊗ T).presheaf.germ W x hxW) hvalue).trans
        (native_tensorSection_germ_zero_left F T W x hxW (a • n) t hzero)))
  exact additive_map_biproduct_lift_apply_zero (fun _ : Fin r => F ⊗ T) E
    (fun i => sectionMultiplication F T (s i)) m hcomponents


/-- An actual projective scheme internally supplies its same coherent ideal
annihilator as a genuine finite kernel. Its original native stalk image is
exactly the annihilator of the same original ideal stalk at every point. -/
theorem exists_projective_coherent_annihilator {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (K : X.Modules) (a : K ⟶ F), K.IsQuasicoherent ∧ K.IsFiniteType ∧ Mono a ∧
      (∀ (x : X) (r : X.presheaf.stalk x), r ∈ I.stalkIdeal x →
        ∀ m : K.presheaf.stalk x, r • m = 0) ∧
      (∀ (x : X) (m : F.presheaf.stalk x),
        (∀ r : X.presheaf.stalk x, r ∈ I.stalkIdeal x → r • m = 0) →
          ∃ n : K.presheaf.stalk x,
            ((Scheme.Modules.toPresheaf X ⋙
              TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map a) n = m) := by
  classical
  have hp : IsProjectiveFactorization p := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let hFP : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) I.toModules :=
    I.isFinitePresentation_toModules
  let : I.toModules.IsQuasicoherent :=
    @SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
      _ _ _ X.ringCatSheaf _ _ I.toModules hFP
  let : I.toModules.IsFiniteType :=
    @SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
      _ _ _ X.ringCatSheaf _ _ I.toModules hFP
  obtain ⟨d, i, hi, _⟩ := hp
  let : IsClosedImmersion i := hi
  let j : Fin (d + 1) := 0
  obtain ⟨N, hN⟩ := ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections
    i I.toModules j
  let T : X.Modules := (Scheme.Modules.pullback i).obj
    (MvPolynomial.coordinateHyperplaneTwist (R := k) j (N : ℤ))
  have hT : IsInvertible T :=
    (MvPolynomial.coordinateHyperplaneTwist_isInvertible j (N : ℤ)).pullback i
  obtain ⟨G, hG⟩ := hN N le_rfl
  let : G.IsFiniteType := hG
  let : Finite G.I := hG.finite
  let : Fintype G.I := Fintype.ofFinite G.I
  let r := Fintype.card G.I
  let e : G.I ≃ Fin r := Fintype.equivFin G.I
  let s : Fin r → (unitObj X ⟶ T) := fun b =>
    idealTwistGenerator I.toModules T I.toModulesInclusion G (e.symm b)
  let q := sectionTuple F T s
  let K := kernel q
  let a : K ⟶ F := kernel.ι q
  have hQC : K.IsQuasicoherent := sectionKernel_quasicoherent F T hT s
  have hFT : K.IsFiniteType := sectionKernel_finiteType F T hT s
  refine ⟨K, a, hQC, hFT, ?_, ?_, ?_⟩
  · dsimp only [a]
    infer_instance
  · exact kernel_stalkIdeal_smul_zero F T I hT G r e
  · intro x m hm
    exact kernel_stalk_lift_of_ideal_annihilation F T I hT G r e x m hm

#check @finiteGenerator_span
#print axioms finiteGenerator_span
#check @exists_projective_coherent_annihilator
#print axioms exists_projective_coherent_annihilator

end EnvelopeProperty.SeshadriAmplenessCriterion
