import EnvelopeProperty.ComplexGeometry.Schemes.CotangentAffineComparison
import EnvelopeProperty.ComplexGeometry.Schemes.BundleTensorLocalization
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Smooth cotangent sheaves on genuine scheme charts

Transport the actual cotangent sheaf through open-immersion restrictions,
identify its genuine affine coordinate differentials, and derive free local
frames from smooth presentations. All covers and scalar structures arise
from the structural scheme morphism.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PrimeSpectrum

namespace ComplexSchemes

universe u

noncomputable section

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]

/-- The actual inverse structure-ring isomorphisms of an open immersion. -/
def openImmersionStructurePresheafMap : Y.presheaf ⟶ g.opensFunctor.op ⋙ X.presheaf :=
  { app U := (g.appIso U.unop).inv }

/-- Actual restriction of a structure-module presheaf along an open immersion. -/
def openImmersionPresheafRestrict (P : X.PresheafOfModules) : Y.PresheafOfModules :=
  (PresheafOfModules.pushforward
    (Functor.whiskerRight (openImmersionStructurePresheafMap g)
      (forget₂ CommRingCat RingCat))).obj P

set_option backward.isDefEq.respectTransparency false in
/-- The actual restricted sheafification unit. -/
def openImmersionSheafificationMap (P : X.PresheafOfModules) :
    openImmersionPresheafRestrict g P ⟶
      ((Scheme.Modules.restrictFunctor g).obj ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)).val :=
  { app U := ModuleCat.ofHom
      (X := (openImmersionPresheafRestrict g P).obj U)
      (Y := ((Scheme.Modules.restrictFunctor g).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)).val.obj U)
      { toFun := ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P).app (g.opensFunctor.op.obj U)
        map_add' := (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P).app (g.opensFunctor.op.obj U)).hom.map_add
        map_smul' a x := (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P).app (g.opensFunctor.op.obj U)).hom.map_smul
            ((g.appIso U.unop).inv a) x }
    naturality i := by
      ext x
      exact congr($(((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).naturality (g.opensFunctor.op.map i)).hom x) }

/-- The underlying map is the literal restricted abelian-presheaf unit. -/
theorem openImmersionSheafificationMap_underlying (P : X.PresheafOfModules) :
    (PresheafOfModules.toPresheaf _).map (openImmersionSheafificationMap g P) =
      Functor.whiskerLeft g.opensFunctor.op
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := rfl

/-- Open-immersion restriction preserves local bijectivity of the genuine
sheafification unit. -/
theorem openImmersionSheafificationMap_locally_bijective (P : X.PresheafOfModules) :
    Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf _).map (openImmersionSheafificationMap g P)) ∧
    Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf _).map (openImmersionSheafificationMap g P)) := by
  rw [openImmersionSheafificationMap_underlying,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  have hinj : Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) P.presheaf) :=
    ((_root_.Opens.grothendieckTopology X).W_toSheafify P.presheaf).isLocallyInjective
  have hsurj : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) P.presheaf) :=
    ((_root_.Opens.grothendieckTopology X).W_toSheafify P.presheaf).isLocallySurjective
  constructor
  · exact ⟨fun x y h ↦ g.opensFunctor.cover_lift _ _ (hinj.equalizerSieve_mem x y h)⟩
  · exact ⟨fun s ↦ g.opensFunctor.cover_lift _ _ (hsurj.imageSieve_mem s)⟩

/-- Sheafification inverts the genuinely restricted unit. -/
theorem openImmersionSheafificationMap_becomes_iso (P : X.PresheafOfModules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (openImmersionSheafificationMap g P)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf Y.ringCatSheaf)]
  change IsIso ((presheafToSheaf (_root_.Opens.grothendieckTopology Y)
    AddCommGrpCat).map ((PresheafOfModules.toPresheaf _).map
      (openImmersionSheafificationMap g P)))
  rw [← GrothendieckTopology.W_iff]
  exact (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
    (openImmersionSheafificationMap_locally_bijective g P)

/-- The actual sheafification counit on a scheme is an isomorphism. -/
def schemeSheafificationCounitIso (S : Y.Modules) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj S.val ≅ S := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  exact (asIso adj.counit).app S

/-- Genuine sheafification commutes with open-immersion restriction. -/
def openImmersionSheafificationIso (P : X.PresheafOfModules) :
    (Scheme.Modules.restrictFunctor g).obj ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        (openImmersionPresheafRestrict g P) := by
  have := openImmersionSheafificationMap_becomes_iso g P
  exact (asIso ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
    (openImmersionSheafificationMap g P)) ≪≫
      schemeSheafificationCounitIso
        ((Scheme.Modules.restrictFunctor g).obj ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P))).symm

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section

variable {R B C : CommRingCat.{u}} (f : R ⟶ B) (f' : R ⟶ C)
    (e : B ≅ C) (h : f ≫ e.hom = f')

set_option backward.isDefEq.respectTransparency false in
/-- A coefficient-ring isomorphism gives a bijective canonical map of
actual relative Kähler modules. -/
theorem kaehlerCoefficientMap_bijective :
    Function.Bijective (CommRingCat.KaehlerDifferential.map
      (f := f) (f' := f') (g := 𝟙 R) (g' := e.hom) (by simpa using h.symm)) := by

  have hc : 𝟙 R ≫ f' = f ≫ e.hom := by simpa using h.symm
  let := f.hom.toAlgebra
  let := f'.hom.toAlgebra
  let := e.hom.hom.toAlgebra
  have : IsScalarTower R B C :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h).symm
  have : IsLocalization (.powers (1 : B)) C :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨n, rfl⟩ := hb
      simp)
      e.commRingCatIsoToRingEquiv.bijective
  have hloc : IsLocalizedModule (.powers (1 : B))
      (CommRingCat.KaehlerDifferential.map
        (f := f) (f' := f') (g := 𝟙 R) (g' := e.hom) hc).hom := by
    change IsLocalizedModule (.powers (1 : B)) (_root_.KaehlerDifferential.map R R B C)
    infer_instance
  let := hloc
  have : IsLocalization (.powers (1 : B)) B :=
    IsLocalization.of_le_isUnit (by simp)
  have : IsLocalizedModule (.powers (1 : B))
      (LinearMap.id : CommRingCat.KaehlerDifferential f →ₗ[B]
        CommRingCat.KaehlerDifferential f) :=
    isLocalizedModule_id (.powers (1 : B)) (CommRingCat.KaehlerDifferential f) B
  let E := IsLocalizedModule.linearEquiv (.powers (1 : B))
    (LinearMap.id : CommRingCat.KaehlerDifferential f →ₗ[B]
      CommRingCat.KaehlerDifferential f)
    (CommRingCat.KaehlerDifferential.map
      (f := f) (f' := f') (g := 𝟙 R) (g' := e.hom) hc).hom
  convert E.bijective using 1
  funext x
  exact (IsLocalizedModule.linearEquiv_apply (.powers (1 : B)) _ _ x).symm

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X) [IsOpenImmersion g]

/-- Structural constants commute with the actual open-immersion coefficient
isomorphism. -/
theorem openImmersion_constantSquare (U : Y.Opensᵒᵖ) :
    (schemeConstantPresheafMap f).app (g.opensFunctor.op.obj U) ≫ (g.appIso U.unop).hom =
      (schemeConstantPresheafMap (g ≫ f)).app U := by
  have htop : g.appLE ⊤ ⊤ (by simp) = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ Y.presheaf.map (𝟙 (op (⊤ : Y.Opens))) = g.appTop
    simp
  have hm : X.presheaf.map (g.opensFunctor.op.obj U).unop.leTop.op ≫
      (g.appIso U.unop).hom = g.appTop ≫ Y.presheaf.map U.unop.leTop.op := by
    change X.presheaf.map (g ''ᵁ U.unop).leTop.op ≫ _ = _
    rw [g.appIso_hom']
    exact ((g.map_appLE (g.preimage_image_eq U.unop).ge
      (g ''ᵁ U.unop).leTop.op).trans
      (g.appLE_map (U := ⊤) (V := ⊤) (by simp) U.unop.leTop.op).symm).trans
        (congrArg (fun h ↦ h ≫ Y.presheaf.map U.unop.leTop.op) htop)

  ext k
  change (g.appIso U.unop).hom
      (X.presheaf.map (g.opensFunctor.op.obj U).unop.leTop.op
        (f.appTop ((Scheme.ΓSpecIso (.of K)).inv k))) =
    Y.presheaf.map U.unop.leTop.op
      (g.appTop (f.appTop ((Scheme.ΓSpecIso (.of K)).inv k)))
  exact congr($(hm).hom (f.appTop ((Scheme.ΓSpecIso (.of K)).inv k)))

/-- The inverse coefficient isomorphism sends the restricted structural
constants to the original structural constants. -/
theorem openImmersion_constantSquare_inv (U : Y.Opensᵒᵖ) :
    (schemeConstantPresheafMap (g ≫ f)).app U ≫ (g.appIso U.unop).inv =
      (schemeConstantPresheafMap f).app (g.opensFunctor.op.obj U) := by
  ext k
  have hk : (g.appIso U.unop).hom
      ((schemeConstantPresheafMap f).app (g.opensFunctor.op.obj U) k) =
    (schemeConstantPresheafMap (g ≫ f)).app U k :=
    congr($(openImmersion_constantSquare f g U).hom k)
  exact (congrArg (fun z ↦ (g.appIso U.unop).inv z) hk.symm).trans
    ((g.appIso U.unop).commRingCatIsoToRingEquiv.left_inv _)

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse coefficient isomorphisms induce a morphism from the
cotangent presheaf of the restricted structural morphism. -/
def cotangentPresheafOpenImmersionMap :
    cotangentPresheaf (g ≫ f) ⟶ openImmersionPresheafRestrict g (cotangentPresheaf f) where
  app U := CommRingCat.KaehlerDifferential.map
    (f := (schemeConstantPresheafMap (g ≫ f)).app U)
    (f' := (schemeConstantPresheafMap f).app (g.opensFunctor.op.obj U))
    (g := 𝟙 (CommRingCat.of K))
    (g' := (g.appIso U.unop).inv)
    (by
      dsimp [constantRingPresheaf]
      exact (Category.id_comp _).trans (openImmersion_constantSquare_inv f g U).symm)
  naturality {U V} i := by
    apply CommRingCat.KaehlerDifferential.ext
      (f := (schemeConstantPresheafMap (g ≫ f)).app U)
    intro a
    have hU : 𝟙 (CommRingCat.of K) ≫ (schemeConstantPresheafMap f).app (g.opensFunctor.op.obj U) =
        (schemeConstantPresheafMap (g ≫ f)).app U ≫ (g.appIso U.unop).inv :=
      (Category.id_comp _).trans (openImmersion_constantSquare_inv f g U).symm
    have hV : 𝟙 (CommRingCat.of K) ≫ (schemeConstantPresheafMap f).app (g.opensFunctor.op.obj V) =
        (schemeConstantPresheafMap (g ≫ f)).app V ≫ (g.appIso V.unop).inv :=
      (Category.id_comp _).trans (openImmersion_constantSquare_inv f g V).symm
    change CommRingCat.KaehlerDifferential.map hV
        ((cotangentPresheaf (g ≫ f)).map i (CommRingCat.KaehlerDifferential.d a)) =
      (openImmersionPresheafRestrict g (cotangentPresheaf f)).map i
        (CommRingCat.KaehlerDifferential.map hU (CommRingCat.KaehlerDifferential.d a))
    rw [CommRingCat.KaehlerDifferential.map_d]
    change CommRingCat.KaehlerDifferential.map hV
        ((cotangentPresheaf (g ≫ f)).map i ((cotangentPresheafDerivation (g ≫ f)).d a)) =
      (cotangentPresheaf f).map (g.opensFunctor.op.map i)
        ((cotangentPresheafDerivation f).d ((g.appIso U.unop).inv a))
    refine (congrArg (CommRingCat.KaehlerDifferential.map hV)
      ((cotangentPresheafDerivation (g ≫ f)).d_map i a).symm).trans ?_
    exact (CommRingCat.KaehlerDifferential.map_d hV (Y.presheaf.map i a)).trans
      ((congrArg (cotangentPresheafDerivation f).d
        (congr($(g.appIso_inv_naturality i).hom a))).trans
        ((cotangentPresheafDerivation f).d_map (g.opensFunctor.op.map i)
          ((g.appIso U.unop).inv a)))

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X) [IsOpenImmersion g]

set_option backward.isDefEq.respectTransparency false in
/-- The actual cotangent presheaf respects open-immersion restriction. -/
def cotangentPresheafOpenImmersionIso :
    cotangentPresheaf (g ≫ f) ≅ openImmersionPresheafRestrict g (cotangentPresheaf f) :=
  PresheafOfModules.isoMk
    (fun U ↦ (LinearEquiv.ofBijective
      ((cotangentPresheafOpenImmersionMap f g).app U).hom
      (kaehlerCoefficientMap_bijective
        ((schemeConstantPresheafMap (g ≫ f)).app U)
        ((schemeConstantPresheafMap f).app (g.opensFunctor.op.obj U))
        (g.appIso U.unop).symm (openImmersion_constantSquare_inv f g U))).toModuleIso)
    (fun {_ _} i ↦ (cotangentPresheafOpenImmersionMap f g).naturality i)

/-- The actual cotangent sheaf respects open-immersion restriction. -/
def cotangentSheafOpenImmersionIso :
    (Scheme.Modules.restrictFunctor g).obj (cotangentSheaf f) ≅ cotangentSheaf (g ≫ f) :=
  openImmersionSheafificationIso g (cotangentPresheaf f) ≪≫
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
      (cotangentPresheafOpenImmersionIso f g).symm

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The affine coordinate structural morphism is exactly the morphism
induced by the genuine structural constants on the affine chart. -/
theorem affineChartStructuralMap {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ f = Spec.map ((schemeConstantPresheafMap f).app (.op V)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV
    (show V ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  congr 1

/-- Every point has a genuine affine chart whose actual structural
constant-ring map is standard smooth of the prescribed relative dimension. -/
theorem smooth_cotangent_affine_chart (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n
        ((schemeConstantPresheafMap f).app (.op V)).hom := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim y (f x)) ▸ e hx
  subst U
  refine ⟨V, hV, hx, ?_⟩
  have hs := hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
  rw [Nat.add_zero] at hs
  exact hs

set_option backward.isDefEq.respectTransparency false in
/-- Open-immersion restriction preserves actual free sheaves, with the
isomorphism induced by the free sheaf universal property. -/
def openImmersionRestrictFreeIso {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (I : Type u) :
    (Scheme.Modules.restrictFunctor g).obj
        (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) I := by
  letI : Limits.PreservesColimitsOfShape (Discrete I) (Scheme.Modules.restrictFunctor g) :=
    (Scheme.Modules.restrictAdjunction g).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor g) I
    (Scheme.Modules.restrictUnitIso g).symm).symm

set_option backward.isDefEq.respectTransparency false in
/-- The open-site equivalence preserves actual free sheaves. -/
def schemeOverEquivInverseFreeIso (V : X.Opens) (I : Type u) :
    (Scheme.Modules.overEquiv V).inverse.obj
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over V) I := by
  letI : Limits.PreservesColimitsOfShape (Discrete I) (Scheme.Modules.overEquiv V).inverse :=
    (Scheme.Modules.overEquiv V).symm.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact (SheafOfModules.mapFreeIso (Scheme.Modules.overEquiv V).inverse I
    (V.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).symm

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

set_option backward.isDefEq.respectTransparency false in
/-- A standard-smooth genuine affine coordinate chart gives an actual
rank-`n` free frame for the cotangent sheaf on its open site. -/
def standardSmoothCotangentAffineChartFrame {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((schemeConstantPresheafMap f).app (.op V)).hom) :
    (cotangentSheaf f).over V ≅
      SheafOfModules.free (R := X.ringCatSheaf.over V) (ULift.{u} (Fin n)) := by
  let A : CommRingCat := Γ(X, V)
  let φ : CommRingCat.of K ⟶ A := (schemeConstantPresheafMap f).app (.op V)
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K A := hs
  have he : hV.fromSpec ≫ f = affineStructuralMap K A := affineChartStructuralMap f hV
  let E : (Scheme.Modules.restrictFunctor hV.fromSpec).obj (cotangentSheaf f) ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf) (ULift.{u} (Fin n)) :=
    cotangentSheafOpenImmersionIso f hV.fromSpec ≪≫
      eqToIso (congrArg cotangentSheaf he) ≪≫
      standardSmoothAffineCotangentSheafFrame K A n
  let EV : (Scheme.Modules.restrictFunctor V.ι).obj (cotangentSheaf f) ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) :=
    (Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).symm.app
      (cotangentSheaf f) ≪≫
    (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app
      (cotangentSheaf f) ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso E ≪≫
      openImmersionRestrictFreeIso hV.isoSpec.hom (ULift.{u} (Fin n))
  exact (Scheme.Modules.overEquiv V).unitIso.app ((cotangentSheaf f).over V) ≪≫
    (Scheme.Modules.overEquiv V).inverse.mapIso
      ((Scheme.Modules.overFunctorEquiv V).app (cotangentSheaf f) ≪≫ EV) ≪≫
    schemeOverEquivInverseFreeIso V (ULift.{u} (Fin n))

/-- Smoothness produces a genuine rank-`n` cotangent frame around every point. -/
theorem smooth_cotangent_local_frame (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      Nonempty ((cotangentSheaf f).over V ≅
        SheafOfModules.free (R := X.ringCatSheaf.over V) (ULift.{u} (Fin n))) := by
  obtain ⟨V, hV, hx, hs⟩ := smooth_cotangent_affine_chart f n x
  exact ⟨V, hV, hx, ⟨standardSmoothCotangentAffineChartFrame f hV n hs⟩⟩

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (n : ℕ) [SmoothOfRelativeDimension n f]

/-- A genuine smooth affine chart chosen around each point, including its
actual structural standard-smooth ring map. -/
def smoothCotangentChart (x : X) :
    {V : X.Opens // IsAffineOpen V ∧ x ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n
        ((schemeConstantPresheafMap f).app (.op V)).hom} := by
  let h := smooth_cotangent_affine_chart f n x
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

/-- The derived free cotangent frame on the selected smooth chart. -/
def smoothCotangentChartFrame (x : X) :
    (cotangentSheaf f).over (smoothCotangentChart f n x).val ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (smoothCotangentChart f n x).val)
        (ULift.{u} (Fin n)) :=
  standardSmoothCotangentAffineChartFrame f
    (smoothCotangentChart f n x).property.1 n (smoothCotangentChart f n x).property.2.2

/-- The selected genuine affine charts form an actual covering family. -/
theorem smoothCotangentCharts_coversTop :
    (_root_.Opens.grothendieckTopology X).CoversTop
      (fun x : X ↦ (smoothCotangentChart f n x).val) := by
  rw [_root_.Opens.coversTop_iff]
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, (smoothCotangentChart f n x).property.2.1⟩

/-- Native local generator data obtained from the actual smooth cotangent
frames, all with index set `Fin n`. -/
def smoothCotangentLocalGeneratorsData : (cotangentSheaf f).LocalGeneratorsData where
  I := X
  X x := (smoothCotangentChart f n x).val
  coversTop := smoothCotangentCharts_coversTop f n
  generators x := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over (smoothCotangentChart f n x).val)
    (ULift.{u} (Fin n))).ofEpi (smoothCotangentChartFrame f n x).inv

/-- The actual native local generators are bases of the cotangent sheaf. -/
theorem smoothCotangentLocalGeneratorsData_isLocallyFreeData :
    (smoothCotangentLocalGeneratorsData f n).IsLocallyFreeData := by
  constructor
  intro x
  dsimp only [smoothCotangentLocalGeneratorsData] at x
  change IsIso ((SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over (smoothCotangentChart f n x).val)
    (ULift.{u} (Fin n))).ofEpi (smoothCotangentChartFrame f n x).inv).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  exact (congrArg IsIso (Category.id_comp (smoothCotangentChartFrame f n x).inv)).mpr
    (inferInstance : IsIso (smoothCotangentChartFrame f n x).inv)

include n in
/-- The actual cotangent sheaf of a smooth scheme over `K` is locally free;
the constructed local frames have exactly `n` generators. -/
theorem smooth_cotangentSheaf_locallyFree : (cotangentSheaf f).IsLocallyFree := by
  have := smoothCotangentLocalGeneratorsData_isLocallyFreeData f n
  exact (smoothCotangentLocalGeneratorsData f n).isLocallyFree

end
end ComplexSchemes

namespace ComplexSchemes
universe u
noncomputable section
variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The genuine structural algebra on an open coordinate ring. -/
@[instance_reducible]
def affineChartAlgebra (V : X.Opens) : Algebra K Γ(X, V) :=
  (show CommRingCat.of K ⟶ Γ(X, V) from
    (schemeConstantPresheafMap f).app (.op V)).hom.toAlgebra

/-- The chart structural map is the actual affine structural map for the
algebra obtained from the given scheme morphism. -/
theorem affineChartStructuralMap_eq_affineStructuralMap {V : X.Opens}
    (hV : IsAffineOpen V) :
    letI := affineChartAlgebra f V
    hV.fromSpec ≫ f = affineStructuralMap K Γ(X, V) :=
  affineChartStructuralMap f hV

/-- The actual cotangent sheaf restricted to a genuine affine chart is the
associated sheaf of its genuine coordinate Kähler module. -/
def affineChartCotangentSheafIso {V : X.Opens} (hV : IsAffineOpen V) :
    letI := affineChartAlgebra f V
    (Scheme.Modules.restrictFunctor hV.fromSpec).obj (cotangentSheaf f) ≅
      affineCotangentTilde K Γ(X, V) := by
  letI := affineChartAlgebra f V
  exact cotangentSheafOpenImmersionIso f hV.fromSpec ≪≫
    eqToIso (congrArg cotangentSheaf
      (affineChartStructuralMap_eq_affineStructuralMap f hV)) ≪≫
    affineCotangentSheafIso K Γ(X, V)

end
end ComplexSchemes
