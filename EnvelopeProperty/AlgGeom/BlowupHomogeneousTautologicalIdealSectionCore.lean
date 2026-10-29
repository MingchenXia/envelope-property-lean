import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalSectionCoefficients
import EnvelopeProperty.Alterations.Geometry.BlowupProjectiveEmbedding
import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import EnvelopeProperty.AlgGeom.IdealModulePullbackSections
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Original homogeneous forms in their actual geometric ideal tensor -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory HomogeneousLocalization MvPolynomial
open Alterations.Geometry.ProjectiveIdeal

universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The original native dehomogenized form is the same whole homogeneous
coefficient, including the zero polynomial and degree zero. -/
theorem nativeFormSection_eq_homogeneousCoefficient (i : Fin (n+1)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) :
    nativeFormSection (R := R) i F =
      ProjectiveHomogeneousSections.coefficient i d F hF := by
  have hs : nativeFormSection (R := R) i F =
      (nativeHomogeneousChartSectionsIso (R := R) i).hom.hom
        (homogeneousChartRatioHom i (coordinateDehom i F)) := rfl
  have he := congrArg (fun z => (nativeHomogeneousChartSectionsIso (R := R) i).hom.hom z)
    (homogeneousChartRatioHom_dehom_of_isHomogeneous i hF)
  have hh := congrArg (fun f : CommRingCat.of (HomogeneousChartRing R i) ⟶
      Γ(NativeProjectiveScheme R n, nativeCoordinateOpen i) =>
        f.hom (ProjectiveHomogeneousSections.fraction i d F hF))
    (nativeHomogeneousChartSectionsIso_hom (R := R) i)
  exact hs.trans (he.trans hh)

private theorem moduleMap_restrict {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    f.val.app (.op V) (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (f.val.app (.op U) s) :=
  PresheafOfModules.naturality_apply f.val (homOfLE h).op s

private theorem topRestriction_trans {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (s : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE h).op
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s := by
  rw [← M.presheaf.map_comp_apply]
  exact congrArg (fun k => M.presheaf.map k s) (Subsingleton.elim _ _)

private theorem mono_sections_injective {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (U : X.Opens) :
    Function.Injective (f.val.app (.op U)) := by
  let : Mono f.val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map f))
  exact PresheafOfModules.injective_of_mono f.val (.op U)

/-- Local actual lifts through a monomorphism glue to a whole actual lift.
The overlap equality is derived from their common original included image. -/
private theorem exists_sectionLift_of_local {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] {ι : Type*} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (s : Γ(N, ⊤)) (t : ∀ i, Γ(M, U i))
    (ht : ∀ i, f.val.app (.op (U i)) (t i) =
      N.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op s) :
    ∃ r : Γ(M, ⊤), f.val.app (.op ⊤) r = s := by
  have hcpt : ∀ a b,
      M.presheaf.map (TopologicalSpace.Opens.infLELeft (U a) (U b)).op (t a) =
        M.presheaf.map (TopologicalSpace.Opens.infLERight (U a) (U b)).op (t b) := by
    intro a b
    apply mono_sections_injective f (U a ⊓ U b)
    have ha := moduleMap_restrict f (inf_le_left : U a ⊓ U b ≤ U a) (t a)
    have hb := moduleMap_restrict f (inf_le_right : U a ⊓ U b ≤ U b) (t b)
    rw [ht a, topRestriction_trans] at ha
    rw [ht b, topRestriction_trans] at hb
    exact ha.trans hb.symm
  obtain ⟨r, hr, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩
    U ⊤ (fun _ => homOfLE le_top) hcover.ge t hcpt
  refine ⟨r, ?_⟩
  apply TopCat.Presheaf.IsSheaf.section_ext (F := N.val.presheaf) N.isSheaf
  intro x _hx
  have hx : x ∈ iSup U := hcover.ge (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨U i, le_top, hi, ?_⟩
  exact (moduleMap_restrict f (le_top : U i ≤ ⊤) r).symm.trans
    ((congrArg (fun z => f.val.app (.op (U i)) z) (hr i)).trans (ht i))

private theorem tensorIdealMap_mono {X : Scheme.{u}} (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (I : X.IdealSheafData) :
    Mono (SchemeTensorObjMorphisms.tensorObjIdealMap L I.toModules I.toModulesInclusion) := by
  let i : I.toModules ⟶ Scheme.Modules.unitObj X := I.toModulesInclusion
  let : Mono i := I.toModulesInclusion_mono
  let : Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i) :=
    SchemeTensorObjMorphisms.mono_tensorObjMap_left L hL i
  change Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i ≫
    (Scheme.Modules.tensorObjUnitIso L).hom)
  infer_instance

private theorem presheaf_comp_apply {X : Scheme.{u}} {M N P : X.PresheafOfModules}
    (f : M ⟶ N) (g : N ⟶ P) (U : X.Opens) (z : M.obj (.op U)) :
    ((f ≫ g).app (.op U)).hom z = (g.app (.op U)).hom ((f.app (.op U)).hom z) := rfl

private def tensorPureSection {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) : Γ(Scheme.Modules.tensorObj M N, U) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (M.val ⊗ N.val)).app (.op U)) (x ⊗ₜ y)

private theorem tensorIdealMap_unit {X : Scheme.{u}} (L N : X.Modules)
    (i : N ⟶ Scheme.Modules.unitObj X) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (L.val ⊗ N.val) ≫
      (SchemeTensorObjMorphisms.tensorObjIdealMap L N i).val =
        (𝟙 L.val ⊗ₘ i.val) ≫ (ρ_ L.val).hom := by
  let Sh : X.PresheafOfModules ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let c := Scheme.Modules.sheafifyValIso L
  let f : L.val ⊗ N.val ⟶ L.val := (𝟙 L.val ⊗ₘ i.val) ≫ (ρ_ L.val).hom
  have hmap : SchemeTensorObjMorphisms.tensorObjIdealMap L N i = Sh.map f ≫ c.hom := by
    change Sh.map (𝟙 L.val ⊗ₘ i.val) ≫ Sh.map (ρ_ L.val).hom ≫ c.hom =
      Sh.map ((𝟙 L.val ⊗ₘ i.val) ≫ (ρ_ L.val).hom) ≫ c.hom
    exact (Category.assoc (Sh.map (𝟙 L.val ⊗ₘ i.val))
      (Sh.map (ρ_ L.val).hom) c.hom).symm.trans
        (congrArg (fun k : Sh.obj (L.val ⊗ N.val) ⟶ Sh.obj L.val => k ≫ c.hom)
          (Sh.map_comp (𝟙 L.val ⊗ₘ i.val) (ρ_ L.val).hom).symm)
  have hn := adj.unit_naturality f
  change adj.unit.app (L.val ⊗ N.val) ≫ (Sh.map f).val =
    f ≫ adj.unit.app L.val at hn
  have ht := adj.right_triangle_components L
  change adj.unit.app L.val ≫ c.hom.val = 𝟙 L.val at ht
  have hv : (SchemeTensorObjMorphisms.tensorObjIdealMap L N i).val =
      (Sh.map f).val ≫ c.hom.val :=
    (congrArg (fun k : Scheme.Modules.tensorObj L N ⟶ L => k.val) hmap).trans
      (SheafOfModules.comp_val (Sh.map f) c.hom)
  calc
    _ = adj.unit.app (L.val ⊗ N.val) ≫ (Sh.map f).val ≫ c.hom.val :=
      congrArg (fun k : (Scheme.Modules.tensorObj L N).val ⟶ L.val =>
        adj.unit.app (L.val ⊗ N.val) ≫ k) hv
    _ = f ≫ adj.unit.app L.val ≫ c.hom.val :=
      (Category.assoc (adj.unit.app (L.val ⊗ N.val)) (Sh.map f).val c.hom.val).symm.trans
        ((congrArg (fun k : L.val ⊗ N.val ⟶ (Sh.obj L.val).val => k ≫ c.hom.val) hn).trans
          (Category.assoc f (adj.unit.app L.val) c.hom.val))
    _ = f := (congrArg (fun k : L.val ⟶ L.val => f ≫ k) ht).trans (Category.comp_id f)

private theorem tensorIdealMap_pure {X : Scheme.{u}} (L N : X.Modules)
    (i : N ⟶ Scheme.Modules.unitObj X) (U : X.Opens)
    (x : Γ(L, U)) (a : Γ(N, U)) :
    (SchemeTensorObjMorphisms.tensorObjIdealMap L N i).val.app (.op U)
        (tensorPureSection L N U x a) =
      (show Γ(X, U) from i.val.app (.op U) a) • x := by
  let originalLModule : Module (X.ringCatSheaf.obj.obj (.op U)) (L.val.obj (.op U)) :=
    inferInstance
  let originalUnitModule : Module (X.ringCatSheaf.obj.obj (.op U))
      ((Scheme.Modules.unitObj X).val.obj (.op U)) := inferInstance
  let : Module ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
      (L.val.obj (.op U)) := originalLModule
  let : Module ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
      ((Scheme.Modules.unitObj X).val.obj (.op U)) := originalUnitModule
  let : Module (((CategoryTheory.sheafToPresheaf
      (_root_.Opens.grothendieckTopology X) CommRingCat).obj X.sheaf ⋙
        forget₂ CommRingCat RingCat).obj (.op U)) (L.val.obj (.op U)) := originalLModule
  let : Module (((CategoryTheory.sheafToPresheaf
      (_root_.Opens.grothendieckTopology X) CommRingCat).obj X.sheaf ⋙
        forget₂ CommRingCat RingCat).obj (.op U))
      ((Scheme.Modules.unitObj X).val.obj (.op U)) := originalUnitModule
  let xx : L.val.obj (.op U) := x
  let aa : N.val.obj (.op U) := a
  let b : (Scheme.Modules.unitObj X).val.obj (.op U) := i.val.app (.op U) aa
  let c : Γ(X, U) := b
  let z : (L.val ⊗ N.val).obj (.op U) := x ⊗ₜ a
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (L.val ⊗ N.val)
  let j := SchemeTensorObjMorphisms.tensorObjIdealMap L N i
  have h := congrArg (fun k : L.val ⊗ N.val ⟶ L.val => (k.app (.op U)).hom z)
    (tensorIdealMap_unit L N i)
  have h₁ := presheaf_comp_apply η j.val U z
  have h₂ := presheaf_comp_apply (𝟙 L.val ⊗ₘ i.val) (ρ_ L.val).hom U z
  have h₀ : j.val.app (.op U) (tensorPureSection L N U x a) =
      (ρ_ L.val).hom.app (.op U) (((𝟙 L.val ⊗ₘ i.val).app (.op U)) z) :=
    h₁.symm.trans (h.trans h₂)
  have ht : ((𝟙 L.val ⊗ₘ i.val).app (.op U)) z = xx ⊗ₜ b := rfl
  have hu := ConcreteCategory.congr_hom
    (PresheafOfModules.rightUnitor_hom_app L.val (.op U))
    (xx ⊗ₜ b)
  exact h₀.trans ((congrArg ((ρ_ L.val).hom.app (.op U)) ht).trans
    (hu.trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply
      (R := X.sheaf.obj.obj (.op U)) (M := L.val.obj (.op U)) xx c)))

private theorem frameSection_relation {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(M, ⊤)) :
    M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      ModularCurves.overTrivializationCoefficient M U e s •
        ModularCurves.overTrivializationSection M U e 1 := by
  let c : Γ(X, U) := ModularCurves.overTrivializationCoefficient M U e s
  let w : Γ(M, U) := ModularCurves.overTrivializationSection M U e 1
  let g := e.inv.val.app (.op (Over.mk (𝟙 U)))
  have h := congrArg (fun k : M.over U ⟶ M.over U =>
    k.val.app (.op (Over.mk (𝟙 U)))) e.hom_inv_id
  have hv := ConcreteCategory.congr_hom h
    (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
  change g c = M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s at hv
  let R0 : RingCat := (X.ringCatSheaf.over U).obj.obj (.op (Over.mk (𝟙 U)))
  let c0 : R0 := c
  let ww : (M.over U).val.obj (.op (Over.mk (𝟙 U))) := w
  have hs := g.hom.map_smul c0 (1 : R0)
  change g (c0 * 1) = c0 • ww at hs
  exact hv.symm.trans ((congrArg (fun r : R0 => g r) (mul_one c0).symm).trans hs)

private theorem exists_idealTensorLift_of_coefficients {X : Scheme.{u}}
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (I : X.IdealSheafData)
    {ι : Type*} (U : ι → X.affineOpens) (hcover : (⨆ a, (U a).1) = ⊤)
    (e : ∀ a, L.over (U a).1 ≅ SheafOfModules.unit (X.ringCatSheaf.over (U a).1))
    (s : Γ(L, ⊤))
    (hcoeff : ∀ a, ModularCurves.overTrivializationCoefficient L (U a).1 (e a) s ∈
      I.ideal (U a)) :
    ∃ r : Γ(Scheme.Modules.tensorObj L I.toModules, ⊤),
      (SchemeTensorObjMorphisms.tensorObjIdealMap L I.toModules I.toModulesInclusion).val.app
        (.op ⊤) r = s := by
  let i : I.toModules ⟶ Scheme.Modules.unitObj X := I.toModulesInclusion
  let f := SchemeTensorObjMorphisms.tensorObjIdealMap L I.toModules i
  let : Mono f := tensorIdealMap_mono L hL I
  let c (a : ι) : Γ(X, (U a).1) :=
    ModularCurves.overTrivializationCoefficient L (U a).1 (e a) s
  let w (a : ι) : Γ(L, (U a).1) :=
    ModularCurves.overTrivializationSection L (U a).1 (e a) 1
  let aI (a : ι) : Γ(I.toModules, (U a).1) :=
    (I.toModulesSectionsEquiv (U a)).symm ⟨c a, hcoeff a⟩
  let t (a : ι) := tensorPureSection L I.toModules (U a).1 (w a) (aI a)
  have ht : ∀ a, f.val.app (.op (U a).1) (t a) =
      L.presheaf.map (homOfLE (le_top : (U a).1 ≤ ⊤)).op s := by
    intro a
    have ha : (show Γ(X, (U a).1) from i.val.app (.op (U a).1) (aI a)) = c a := rfl
    have hp := tensorIdealMap_pure L I.toModules i (U a).1 (w a) (aI a)
    exact hp.trans ((congrArg (fun r : Γ(X, (U a).1) => r • w a) ha).trans
      (frameSection_relation L (U a).1 (e a) s).symm)
  exact exists_sectionLift_of_local f (fun a => (U a).1) hcover s t ht

private theorem nativeForm_mem_chartIdeal
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : MvPolynomial (Fin (n+1)) R) (hFJ : F ∈ J.toIdeal) (i : Fin (n+1)) :
    nativeFormSection (R := R) i F ∈
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).ideal
        (Alterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen i) := by
  let v : J.toIdeal → MvPolynomial (Fin (n+1)) R := Subtype.val
  have hspan : Ideal.span (Set.range v) = J.toIdeal := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact a.property
    · intro a ha
      exact Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩
  have hm : nativeFormSection (R := R) i F ∈
      Ideal.span (Set.range (fun a : J.toIdeal => nativeFormSection i (v a))) :=
    Ideal.subset_span (Set.mem_range_self (⟨F, hFJ⟩ : J.toIdeal))
  exact Eq.mpr (congrArg (fun K : Ideal
      Γ(Alterations.projectiveSpace R n, nativeCoordinateOpen i) =>
        nativeFormSection i F ∈ K)
    (Alterations.Geometry.BlowupProjectiveEmbedding.coordinateIdeal_span J v hspan i)) hm

private theorem originalForm_mem_pulledIdeal {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : MvPolynomial (Fin (n+1)) R) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) :
    Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm j U i hi F ∈
      ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).ideal U := by
  let V := Alterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen (R := R) i
  let D := GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J
  have hm := Ideal.mem_map_of_mem (j.appLE (nativeCoordinateOpen i) U.1 hi).hom
    (nativeForm_mem_chartIdeal J F hFJ i)
  exact Eq.mpr (congrArg (fun K : Ideal Γ(X, U.1) =>
      Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm j U i hi F ∈ K)
    (Alterations.Geometry.BlowupProjectiveEmbedding.ideal_comap_affine D j U V hi)) hm

private theorem unitScalar_atOne {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    SchemeLineSectionEvaluation.sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r :=
  Scheme.Modules.topSectionHom_app_top_apply_one (Scheme.Modules.unitObj X) r

private theorem unitScalar_injective {X : Scheme.{u}} :
    Function.Injective (ModularCurves.unitEndomorphismOfTopSection (X := X)) := by
  intro r s h
  exact (unitScalar_atOne r).symm.trans
    ((congrArg SchemeLineSectionEvaluation.sectionAtOne h).trans (unitScalar_atOne s))

private theorem sectionHom_atOne {X : Scheme.{u}} (M : X.Modules)
    (α : Scheme.Modules.unitObj X ⟶ M) :
    SchemeModuleGlobalSections.sectionHom M (SchemeLineSectionEvaluation.sectionAtOne α) = α := by
  have hone : Scheme.Modules.topSectionHom (Scheme.Modules.unitObj X)
      (1 : Γ(X, ⊤)) = 𝟙 (Scheme.Modules.unitObj X) :=
    ModularCurves.unitEndomorphismOfTopSection_one
  have h := ModularCurves.topSectionHom_comp
    (M := Scheme.Modules.unitObj X) (N := M) (show Γ(X, ⊤) from 1) α
  have hleft : Scheme.Modules.topSectionHom (Scheme.Modules.unitObj X)
      (1 : Γ(X, ⊤)) ≫ α = α :=
    (congrArg (fun k : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X => k ≫ α) hone).trans
      (Category.id_comp α)
  exact h.symm.trans hleft

private theorem pullbackRestrictFrame_hom {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.pullbackIsoOfRestrictIso M U
      (Scheme.Modules.restrictIsoOfPullbackIso M U e)).hom = e.hom := by
  let c := Scheme.Modules.restrictFunctorIsoPullback U.ι
  change c.inv.app M ≫ (c.hom.app M ≫ e.hom) = e.hom
  exact (Category.assoc (c.inv.app M) (c.hom.app M) e.hom).symm.trans
    ((congrArg (fun k : (Scheme.Modules.pullback U.ι).obj M ⟶
        (Scheme.Modules.pullback U.ι).obj M => k ≫ e.hom)
      (Iso.inv_hom_id_app c M)).trans (Category.id_comp e.hom))

private theorem coefficient_of_pullbackScalar {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : (Scheme.Modules.pullback U.1.ι).obj M ≅ Scheme.Modules.unitObj U.1.toScheme)
    (s : Γ(M, ⊤)) (c : Γ(X, U.1))
    (h : SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι
        (SchemeModuleGlobalSections.sectionHom M s) ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (ModularCurves.affineOpenTopSection U c)) :
    ModularCurves.overTrivializationCoefficient M U.1
        (Scheme.Modules.overTrivializationOfRestrictIso M U.1
          (Scheme.Modules.restrictIsoOfPullbackIso M U.1 e)) s = c := by
  let E := Scheme.Modules.restrictIsoOfPullbackIso M U.1 e
  have h₀ := SchemeLineSectionEvaluation.sectionHom_localScalar M U E s
  have hp := congrArg
    (fun k : (Scheme.Modules.pullback U.1.ι).obj M ⟶ Scheme.Modules.unitObj U.1.toScheme =>
      SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι
        (SchemeModuleGlobalSections.sectionHom M s) ≫ k)
    (pullbackRestrictFrame_hom M U.1 e)
  have hh := h₀.symm.trans (hp.trans h)
  have htop := unitScalar_injective hh
  have hc := congrArg (ModularCurves.affineOpenAmbientSection U) htop
  have hcoeff : ModularCurves.localTrivializationCoefficient M U E s = c :=
    (ModularCurves.affineOpenAmbientSection_topSection U _).symm.trans
      (hc.trans (ModularCurves.affineOpenAmbientSection_topSection U c))
  exact (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso
    M U E s).trans hcoeff

private theorem ringIsoSquare_apply {A A' B B' : CommRingCat}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : eA.hom ≫ g = f ≫ eB.hom) (a : A') :
    f.hom (eA.inv.hom a) = eB.inv.hom (g.hom a) := by
  apply (ConcreteCategory.bijective_of_isIso eB.hom).1
  have hp := congrArg (fun k : A ⟶ B' => k.hom (eA.inv.hom a)) h
  simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] using hp.symm

private theorem resLE_affineTopSection {X Y : Scheme.{u}} (j : X ⟶ Y)
    (V : Y.affineOpens) (U : X.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1) (c : Γ(Y, V.1)) :
    (j.resLE V.1 U.1 h).appTop.hom (ModularCurves.affineOpenTopSection V c) =
      ModularCurves.affineOpenTopSection U ((j.appLE V.1 U.1 h).hom c) := by
  let E := AlgebraicGeometry.arrowResLEAppIso j V.1 U.1 h
  have hsquare : V.1.topIso.hom ≫ j.appLE V.1 U.1 h =
      (j.resLE V.1 U.1 h).appTop ≫ U.1.topIso.hom := E.hom.w
  have hp := ringIsoSquare_apply V.1.topIso U.1.topIso
    (j.resLE V.1 U.1 h).appTop (j.appLE V.1 U.1 h) hsquare c
  exact (congrArg (j.resLE V.1 U.1 h).appTop.hom
    (ModularCurves.affineOpenTopSection_eq_topIso_inv V c)).trans
      (hp.trans (ModularCurves.affineOpenTopSection_eq_topIso_inv U _).symm)

private def pulledAffineFrame {X Y : Scheme.{u}} (j : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1)
    (M : Y.Modules)
    (e : (Scheme.Modules.pullback V.1.ι).obj M ≅ Scheme.Modules.unitObj V.1.toScheme) :
    (Scheme.Modules.pullback U.1.ι).obj ((Scheme.Modules.pullback j).obj M) ≅
      Scheme.Modules.unitObj U.1.toScheme :=
  (Scheme.Modules.pullbackComp U.1.ι j).app M ≪≫
    Scheme.Modules.frameViaFactor (j.resLE V.1 U.1 h) V.1.ι (U.1.ι ≫ j)
      (Scheme.Hom.resLE_comp_ι j h) e

private theorem pulledAffineFrame_scalar {X Y : Scheme.{u}} (j : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : U.1 ≤ j ⁻¹ᵁ V.1)
    (M : Y.Modules)
    (e : (Scheme.Modules.pullback V.1.ι).obj M ≅ Scheme.Modules.unitObj V.1.toScheme)
    (α : Scheme.Modules.unitObj Y ⟶ M) (c : Γ(Y, V.1))
    (hc : SchemeLineSectionEvaluation.pullbackSectionHom V.1.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (ModularCurves.affineOpenTopSection V c)) :
    SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι
        (SchemeLineSectionEvaluation.pullbackSectionHom j α) ≫
      (pulledAffineFrame j U V h M e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.affineOpenTopSection U ((j.appLE V.1 U.1 h).hom c)) := by
  let p := j.resLE V.1 U.1 h
  let a : Scheme.Modules.unitObj U.1.toScheme ⟶
      (Scheme.Modules.pullback U.1.ι).obj ((Scheme.Modules.pullback j).obj M) :=
    SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι
      (SchemeLineSectionEvaluation.pullbackSectionHom j α)
  let C := (Scheme.Modules.pullbackComp U.1.ι j).app M
  let E := Scheme.Modules.frameViaFactor p V.1.ι (U.1.ι ≫ j)
    (Scheme.Hom.resLE_comp_ι j h) e
  have hcomp : a ≫ C.hom = SchemeLineSectionEvaluation.pullbackSectionHom (U.1.ι ≫ j) α :=
    SchemeLineSectionEvaluation.pullbackSectionHom_comp U.1.ι j α
  have hleft : a ≫ (pulledAffineFrame j U V h M e).hom =
      SchemeLineSectionEvaluation.pullbackSectionHom (U.1.ι ≫ j) α ≫ E.hom :=
    (Category.assoc a C.hom E.hom).symm.trans (congrArg (fun k => k ≫ E.hom) hcomp)
  have hscalar := SchemeLineSectionEvaluation.frameViaFactor_sectionHom_scalar
    p V.1.ι (U.1.ι ≫ j) (Scheme.Hom.resLE_comp_ι j h) e α
    (ModularCurves.affineOpenTopSection V c) hc
  have hr := resLE_affineTopSection j V U h c
  exact hleft.trans (hscalar.trans (congrArg ModularCurves.unitEndomorphismOfTopSection hr))

private def originalFormFrame {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n) (U : X.affineOpens)
    (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (d : ℕ) :
    (Scheme.Modules.pullback U.1.ι).obj ((Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)) ≅
      Scheme.Modules.unitObj U.1.toScheme :=
  pulledAffineFrame j U
    (Alterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen (R := R) i) hi
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    (Scheme.Modules.pullbackIsoOfRestrictIso _ (nativeCoordinateOpen (R := R) i)
      (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i (0 : Fin (n+1)) d))

private theorem originalFormFrame_scalar {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n) (U : X.affineOpens)
    (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) :
    SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι
        (SchemeLineSectionEvaluation.pullbackSectionHom j
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)) ≫
        (originalFormFrame j U i hi d).hom =
      ModularCurves.unitEndomorphismOfTopSection (ModularCurves.affineOpenTopSection U
        (Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm j U i hi F)) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  let V := Alterations.Geometry.BlowupProjectiveEmbedding.coordinateAffineOpen (R := R) i
  let α := ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF
  let e := Scheme.Modules.pullbackIsoOfRestrictIso M V.1
    (coordinateHyperplanePoleSheafPowerTrivialization (R := R) i (0 : Fin (n+1)) d)
  have hraw := homogeneous_localScalar (R := R) i d F hF
  have h := pulledAffineFrame_scalar j U V hi M e α
    (ProjectiveHomogeneousSections.coefficient i d F hF) hraw
  have hc := congrArg (j.appLE V.1 U.1 hi).hom
    (nativeFormSection_eq_homogeneousCoefficient i d F hF).symm
  exact h.trans (congrArg (fun c : Γ(X, U.1) =>
    ModularCurves.unitEndomorphismOfTopSection (ModularCurves.affineOpenTopSection U c)) hc)

private theorem subordinateAffineOpens_cover {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n) :
    (⨆ a : Alterations.Geometry.BlowupProjectiveEmbedding.SubordinateAffineSite j,
      a.1.1) = ⊤ := by
  apply top_unique
  intro x _
  have hx : j x ∈ ⨆ i : Fin (n+1), nativeCoordinateOpen (R := R) i := by
    rw [iSup_nativeCoordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨U, hU, hxU, hUi⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ j ⁻¹ᵁ nativeCoordinateOpen i from hi)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, i, hUi⟩, hxU⟩

theorem exists_originalFormIdealSection {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal) :
    ∃ r : Γ(Scheme.Modules.tensorObj ((Scheme.Modules.pullback j).obj
        (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d))
        ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).toModules, ⊤),
      (SchemeTensorObjMorphisms.tensorObjIdealMap _ _
        ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).toModulesInclusion).val.app
        (.op ⊤) r = SchemeLineSectionEvaluation.sectionAtOne
          (SchemeLineSectionEvaluation.pullbackSectionHom j
            (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)) := by
  let M := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d
  let L := (Scheme.Modules.pullback j).obj M
  let I := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let α : Scheme.Modules.unitObj X ⟶ L := SchemeLineSectionEvaluation.pullbackSectionHom j
    (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)
  let s : Γ(L, ⊤) := SchemeLineSectionEvaluation.sectionAtOne α
  let A := Alterations.Geometry.BlowupProjectiveEmbedding.SubordinateAffineSite j
  let U (a : A) : X.affineOpens := ⟨a.1.1, a.1.2⟩
  let i (a : A) := Alterations.Geometry.BlowupProjectiveEmbedding.subordinateCoordinate j a
  have hi (a : A) : (U a).1 ≤ j ⁻¹ᵁ nativeCoordinateOpen (i a) :=
    Alterations.Geometry.BlowupProjectiveEmbedding.subordinateCoordinate_le j a
  let e (a : A) := originalFormFrame j (U a) (i a) (hi a) d
  let E (a : A) := Scheme.Modules.overTrivializationOfRestrictIso L (U a).1
    (Scheme.Modules.restrictIsoOfPullbackIso L (U a).1 (e a))
  have hcoeff (a : A) : ModularCurves.overTrivializationCoefficient L (U a).1 (E a) s ∈
      I.ideal (U a) := by
    have hs := congrArg (fun k : Scheme.Modules.unitObj X ⟶ L =>
      SchemeLineSectionEvaluation.pullbackSectionHom (U a).1.ι k ≫ (e a).hom)
      (sectionHom_atOne L α)
    have hc := coefficient_of_pullbackScalar L (U a) (e a) s
      (Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm j (U a) (i a) (hi a) F)
      (hs.trans (originalFormFrame_scalar j (U a) (i a) (hi a) d F hF))
    exact Eq.mpr (congrArg (fun c : Γ(X, (U a).1) => c ∈ I.ideal (U a)) hc)
      (originalForm_mem_pulledIdeal j J F hFJ (U a) (i a) (hi a))
  exact exists_idealTensorLift_of_coefficients L
    ((coordinateHyperplanePoleSheafPower_isInvertible (R := R) (0 : Fin (n+1)) d).pullback j)
    I U (subordinateAffineOpens_cover j) E s hcoeff

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
