import EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpen

/-! # Native composition inside the SAME original whole base-open comparison

This private implementation prefix proves the original ideal--line transport
composition from the existing native ideal comparison and monoidal pullback
coherence. The actual generated-pair comparison is the subsequent consumer.
No matching or monomorphism result is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpenComposition
open NadelNefBigGlobalGenerators SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable instance actualPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullback f).Monoidal := pullbackMonoidal f

private def directLine {V X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (f : V ⟶ X) : V.Modules :=
  (D.comap f).toModules ⊗ (pullback f).obj B

private def compTargetIso {V U X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (f : V ⟶ U) (g : U ⟶ X) :
    directLine (D.comap g) ((pullback g).obj B) f ≅ directLine D B (f ≫ g) :=
  tensorIso (Scheme.IdealSheafData.toModulesEqualityIso _ _ (D.comap_comp f g)).symm
    ((pullbackComp f g).app B)

private def directLineCongr {V X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) {f g : V ⟶ X} (h : f = g) :
    directLine D B f ≅ directLine D B g := eqToIso (congrArg (directLine D B) h)

private def idealLineCongr {X : Scheme.{u}} {D E : X.IdealSheafData}
    (h : D = E) (B : X.Modules) : D.toModules ⊗ B ≅ E.toModules ⊗ B :=
  eqToIso (congrArg (fun I : X.IdealSheafData => I.toModules ⊗ B) h)

private theorem comapTensorMap_eq {V X : Scheme.{u}}
    (D : X.IdealSheafData) (f : V ⟶ X) (B : X.Modules) :
    comapTensorMap D f B =
      (Functor.Monoidal.μIso (pullback f) D.toModules B).inv ≫
        D.toModulesComapPullbackMap f ▷ (pullback f).obj B := rfl

private theorem comapIdealMap_comp {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (f : V ⟶ U) (g : U ⟶ X) :
    (pullback f).map (D.toModulesComapPullbackMap g) ≫
        (D.comap g).toModulesComapPullbackMap f ≫
        (Scheme.IdealSheafData.toModulesEqualityIso _ _ (D.comap_comp f g)).inv =
      (pullbackComp f g).hom.app D.toModules ≫
        D.toModulesComapPullbackMap (f ≫ g) := by
  apply (cancel_mono
    (Scheme.IdealSheafData.toModulesEqualityIso _ _ (D.comap_comp f g)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (D.toModulesComapPullbackMap_comp f g).symm

private theorem comapTensorMap_comp {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (f : V ⟶ U) (g : U ⟶ X) (B : X.Modules) :
    (pullback f).map (comapTensorMap D g B) ≫
        comapTensorMap (D.comap g) f ((pullback g).obj B) ≫
        ((Scheme.IdealSheafData.toModulesEqualityIso _ _ (D.comap_comp f g)).inv ⊗ₘ
          (pullbackComp f g).hom.app B) =
      (pullbackComp f g).hom.app (D.toModules ⊗ B) ≫
        comapTensorMap D (f ≫ g) B := by
  rw [comapTensorMap_eq, comapTensorMap_eq, comapTensorMap_eq]
  simp only [Functor.map_comp, Functor.Monoidal.μIso_inv, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [whiskerRight_comp_tensorHom, whiskerRight_comp_tensorHom]
  rw [comapIdealMap_comp, ← tensorHom_comp_whiskerRight]
  have ht := Scheme.Modules.pullbackComp_inverse_tensorator f g D.toModules B
  simp only [Functor.Monoidal.μIso_inv] at ht
  simpa only [Category.assoc] using
    congrArg (fun q => q ≫ D.toModulesComapPullbackMap (f ≫ g) ▷
      (pullback (f ≫ g)).obj B) ht

private theorem compTargetIso_hom {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (f : V ⟶ U) (g : U ⟶ X) :
    (compTargetIso D B f g).hom =
      ((Scheme.IdealSheafData.toModulesEqualityIso _ _ (D.comap_comp f g)).inv ⊗ₘ
        (pullbackComp f g).hom.app B) := rfl

private theorem generatorHom_comapGenerators_comp {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (f : V ⟶ U) (g : U ⟶ X) (B : X.Modules)
    (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections) (i : G.I) :
    generatorHom (comapGenerators (D.comap g) f ((pullback g).obj B) (hB.pullback g)
        (comapGenerators D g B hB G)) i ≫
        ((Scheme.IdealSheafData.toModulesEqualityIso _ _ (D.comap_comp f g)).inv ⊗ₘ
          (pullbackComp f g).hom.app B) =
      generatorHom (comapGenerators D (f ≫ g) B hB G) i := by
  rw [generatorHom_generators, generatorHom_generators, generatorHom_generators]
  simp only [pullbackSectionHom, Functor.map_comp, Category.assoc]
  rw [comapTensorMap_comp]
  simpa only [pullbackSectionHom, Functor.map_comp, Category.assoc] using
    congrArg (fun q => q ≫ comapTensorMap D (f ≫ g) B)
      (pullbackSectionHom_comp f g (generatorHom G i))

private theorem generatorHom_comapGenerators_compIso {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (f : V ⟶ U) (g : U ⟶ X) (B : X.Modules)
    (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections) (i : G.I) :
    generatorHom (comapGenerators (D.comap g) f ((pullback g).obj B) (hB.pullback g)
        (comapGenerators D g B hB G)) i ≫ (compTargetIso D B f g).hom =
      generatorHom (comapGenerators D (f ≫ g) B hB G) i := by
  rw [compTargetIso_hom]
  exact generatorHom_comapGenerators_comp D f g B hB G i

private theorem generatorHom_comapGenerators_congr {V X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) {f g : V ⟶ X} (h : f = g) (i : G.I) :
    generatorHom (comapGenerators D f B hB G) i ≫ (directLineCongr D B h).hom =
      generatorHom (comapGenerators D g B hB G) i := by
  subst g
  exact Category.comp_id _

private theorem generatorHom_comapGenerators_ideal_eq {V X : Scheme.{u}}
    {D E : X.IdealSheafData} (h : D = E) (f : V ⟶ X)
    (B : X.Modules) (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections)
    (i : G.I) :
    generatorHom (comapGenerators D f B hB G) i ≫
        (@idealLineCongr V (D.comap f) (E.comap f)
          (congrArg (fun I : X.IdealSheafData => I.comap f) h)
          ((pullback f).obj B)).hom =
      generatorHom (comapGenerators E f B hB
        (G.ofEpi (@idealLineCongr X D E h B).hom)) i := by
  subst E
  simp only [idealLineCongr, eqToIso_refl, Iso.refl_hom, Category.comp_id,
    generatorHom_generators, generatorHom_ofEpi]

private theorem comapTensorMap_isIso_of_isOpenImmersion {V X : Scheme.{u}}
    (D : X.IdealSheafData) (f : V ⟶ X) [IsOpenImmersion f] (B : X.Modules) :
    IsIso (comapTensorMap D f B) := by
  let := D.toModulesComapPullbackMap_isIso_of_isOpenImmersion f
  unfold comapTensorMap
  infer_instance

private theorem fourIso_transport {C : Type*} [Category C]
    {T A B C' D E : C} (a : A ≅ B) (b : B ≅ C') (c : C' ≅ D) (d : E ≅ D)
    (x : T ⟶ A) (y : T ⟶ B) (z : T ⟶ C') (w : T ⟶ D) (v : T ⟶ E)
    (ha : x ≫ a.hom = y) (hb : y ≫ b.hom = z) (hc : z ≫ c.hom = w)
    (hd : v ≫ d.hom = w) :
    x ≫ (a ≪≫ b ≪≫ c ≪≫ d.symm).hom = v := by
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [ha, hb, hc, ← hd]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem generatorHom_pullback_comap {V X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) (f : V ⟶ X) (i : G.I) :
    generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G) i ≫
        comapTensorMap D f B = generatorHom (comapGenerators D f B hB G) i :=
  (congrArg (fun q => q ≫ comapTensorMap D f B)
    (generatorHom_pullback f G i)).trans (generatorHom_generators D f B hB G i).symm

/-! The whole square is computed on an arbitrary original section, before
using any GeneratingSections structures. The final basis theorem only
composes separately checked normal-form equalities. -/
private def transportSection {V X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (f : V ⟶ X) (σ : unitObj X ⟶ D.toModules ⊗ B) :
    unitObj V ⟶ directLine D B f :=
  pullbackSectionHom f σ ≫ comapTensorMap D f B

private theorem transportSection_comp {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (f : V ⟶ U) (g : U ⟶ X)
    (σ : unitObj X ⟶ D.toModules ⊗ B) :
    transportSection (D.comap g) ((pullback g).obj B) f (transportSection D B g σ) ≫
        (compTargetIso D B f g).hom = transportSection D B (f ≫ g) σ := by
  rw [compTargetIso_hom]
  simp only [transportSection, pullbackSectionHom, Functor.map_comp, Category.assoc]
  rw [comapTensorMap_comp]
  simpa only [pullbackSectionHom, Functor.map_comp, Category.assoc] using
    congrArg (fun q => q ≫ comapTensorMap D (f ≫ g) B)
      (pullbackSectionHom_comp f g σ)

private theorem transportSection_congr {V X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) {f g : V ⟶ X} (h : f = g)
    (σ : unitObj X ⟶ D.toModules ⊗ B) :
    transportSection D B f σ ≫ (directLineCongr D B h).hom =
      transportSection D B g σ := by
  subst g
  exact Category.comp_id _

private def squareFamilyIso {V Y U X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (c : V ⟶ Y) [IsOpenImmersion c] (π : Y ⟶ X)
    (r : V ⟶ U) (j : U ⟶ X) (hc : c ≫ π = r ≫ j) :
    (pullback c).obj (directLine D B π) ≅
      directLine (D.comap j) ((pullback j).obj B) r := by
  let := comapTensorMap_isIso_of_isOpenImmersion (D.comap π) c ((pullback π).obj B)
  exact asIso (comapTensorMap (D.comap π) c ((pullback π).obj B)) ≪≫
    compTargetIso D B c π ≪≫ directLineCongr D B hc ≪≫
      (compTargetIso D B r j).symm

private theorem transportSection_square {V Y U X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules)
    (c : V ⟶ Y) [IsOpenImmersion c] (π : Y ⟶ X)
    (r : V ⟶ U) (j : U ⟶ X) (hc : c ≫ π = r ≫ j)
    (σ : unitObj X ⟶ D.toModules ⊗ B) :
    pullbackSectionHom c (transportSection D B π σ) ≫
        (squareFamilyIso D B c π r j hc).hom =
      transportSection (D.comap j) ((pullback j).obj B) r (transportSection D B j σ) := by
  let := comapTensorMap_isIso_of_isOpenImmersion (D.comap π) c ((pullback π).obj B)
  exact fourIso_transport
    (asIso (comapTensorMap (D.comap π) c ((pullback π).obj B)))
    (compTargetIso D B c π) (directLineCongr D B hc) (compTargetIso D B r j)
    (pullbackSectionHom c (transportSection D B π σ))
    (transportSection (D.comap π) ((pullback π).obj B) c (transportSection D B π σ))
    (transportSection D B (c ≫ π) σ) (transportSection D B (r ≫ j) σ)
    (transportSection (D.comap j) ((pullback j).obj B) r (transportSection D B j σ))
    rfl (transportSection_comp D B c π σ) (transportSection_congr D B hc σ)
    (transportSection_comp D B r j σ)

private theorem generatorHom_pullback_comap_normalForm {V Y X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) (c : V ⟶ Y) (π : Y ⟶ X) (i : G.I) :
    generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections c
        (comapGenerators D π B hB G)) i =
      pullbackSectionHom c (transportSection D B π (generatorHom G i)) :=
  (generatorHom_pullback c (comapGenerators D π B hB G) i).trans
    (congrArg (fun q => pullbackSectionHom c q) (generatorHom_generators D π B hB G i))

private theorem generatorHom_two_comaps_normalForm {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) (r : V ⟶ U) (j : U ⟶ X) (i : G.I) :
    generatorHom (comapGenerators (D.comap j) r ((pullback j).obj B) (hB.pullback j)
        (comapGenerators D j B hB G)) i =
      transportSection (D.comap j) ((pullback j).obj B) r
        (transportSection D B j (generatorHom G i)) :=
  (generatorHom_generators (D.comap j) r ((pullback j).obj B) (hB.pullback j)
    (comapGenerators D j B hB G) i).trans
      (congrArg (fun q => transportSection (D.comap j) ((pullback j).obj B) r q)
        (generatorHom_generators D j B hB G i))

private theorem generatorHom_squareFamilyIso {V Y U X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections)
    (c : V ⟶ Y) [IsOpenImmersion c] (π : Y ⟶ X)
    (r : V ⟶ U) (j : U ⟶ X) (hc : c ≫ π = r ≫ j) (i : G.I) :
    generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections c
        (comapGenerators D π B hB G)) i ≫
        (squareFamilyIso D B c π r j hc).hom =
      generatorHom (comapGenerators (D.comap j) r ((pullback j).obj B)
        (hB.pullback j) (comapGenerators D j B hB G)) i :=
  (congrArg (fun q => q ≫ (squareFamilyIso D B c π r j hc).hom)
    (generatorHom_pullback_comap_normalForm D B hB G c π i)).trans
      ((transportSection_square D B c π r j hc (generatorHom G i)).trans
        (generatorHom_two_comaps_normalForm D B hB G r j i).symm)

private theorem baseTriangle {X : Scheme.{u}} (D : X.IdealSheafData) (U : X.affineOpens) :
    Scheme.IdealSheafData.blowUp.ι D U ≫ D.blowUpπ =
      affineBlowUp.π (D.ideal U) ≫ U.2.fromSpec := by
  rw [Scheme.IdealSheafData.blowUp.ι_π, Category.assoc, IsAffineOpen.isoSpec_inv_ι]

private def baseFinalIdealIso {X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (U : X.affineOpens) :
    directLine (D.comap U.2.fromSpec) ((pullback U.2.fromSpec).obj B)
        (affineBlowUp.π (D.ideal U)) ≅
      (affineBlowUp.exceptionalIdeal (D.ideal U)).toModules ⊗
        (pullback (affineBlowUp.π (D.ideal U))).obj ((pullback U.2.fromSpec).obj B) :=
  @idealLineCongr (affineBlowUp (D.ideal U))
    ((D.comap U.2.fromSpec).comap (affineBlowUp.π (D.ideal U)))
    ((NadelBlowupCanonicalExceptionalGenerators.originalIdeal (D.ideal U)).comap
      (affineBlowUp.π (D.ideal U)))
    (congrArg (fun I : (Spec Γ(X, U.1)).IdealSheafData =>
      I.comap (affineBlowUp.π (D.ideal U))) (Scheme.IdealSheafData.comap_fromSpec D U))
    ((pullback (affineBlowUp.π (D.ideal U))).obj ((pullback U.2.fromSpec).obj B))

private def baseFamilyIso {X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (U : X.affineOpens) :
    (pullback (Scheme.IdealSheafData.blowUp.ι D U)).obj
        (directLine D B D.blowUpπ) ≅
      (affineBlowUp.exceptionalIdeal (D.ideal U)).toModules ⊗
        (pullback (affineBlowUp.π (D.ideal U))).obj ((pullback U.2.fromSpec).obj B) :=
  squareFamilyIso D B (Scheme.IdealSheafData.blowUp.ι D U) D.blowUpπ
    (affineBlowUp.π (D.ideal U)) U.2.fromSpec (baseTriangle D U) ≪≫
      baseFinalIdealIso D B U

private def baseSourceGenerators {X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections)
    (U : X.affineOpens) :
    ((NadelBlowupCanonicalExceptionalGenerators.originalIdeal (D.ideal U)).toModules ⊗
      (pullback U.2.fromSpec).obj B).GeneratingSections :=
  (comapGenerators D U.2.fromSpec B hB G).ofEpi
    (idealLineCongr (Scheme.IdealSheafData.comap_fromSpec D U)
      ((pullback U.2.fromSpec).obj B)).hom

private theorem twoIso_transport {C : Type*} [Category C]
    {T A B D : C} (a : A ≅ B) (b : B ≅ D)
    (x : T ⟶ A) (y : T ⟶ B) (z : T ⟶ D)
    (ha : x ≫ a.hom = y) (hb : y ≫ b.hom = z) :
    x ≫ (a ≪≫ b).hom = z :=
  (Category.assoc x a.hom b.hom).symm.trans
    ((congrArg (fun q => q ≫ b.hom) ha).trans hb)

private theorem generatorHom_baseSquareFamilyIso {X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) (U : X.affineOpens) (i : G.I) :
    generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections
        (Scheme.IdealSheafData.blowUp.ι D U)
        (comapGenerators D D.blowUpπ B hB G)) i ≫
        (squareFamilyIso D B (Scheme.IdealSheafData.blowUp.ι D U) D.blowUpπ
          (affineBlowUp.π (D.ideal U)) U.2.fromSpec (baseTriangle D U)).hom =
      generatorHom (comapGenerators (D.comap U.2.fromSpec)
        (affineBlowUp.π (D.ideal U)) ((pullback U.2.fromSpec).obj B)
        (hB.pullback U.2.fromSpec) (comapGenerators D U.2.fromSpec B hB G)) i :=
  generatorHom_squareFamilyIso D B hB G (Scheme.IdealSheafData.blowUp.ι D U)
    D.blowUpπ (affineBlowUp.π (D.ideal U)) U.2.fromSpec (baseTriangle D U) i

/- The original generic comparison is assembled BEFORE specializing the
base scheme to a section-ring spectrum.  The existential seals the whole
actual map identity; no comparison or closedness certificate is an input
to the native producer below. -/
private theorem twoIso_family_exists {C : Type*} [Category C]
    {T A B D : C} {ι : Type*} (a : A ≅ B) (b : B ≅ D)
    (x : ι → (T ⟶ A)) (y : ι → (T ⟶ B)) (z : ι → (T ⟶ D))
    (ha : ∀ i, x i ≫ a.hom = y i) (hb : ∀ i, y i ≫ b.hom = z i) :
    ∃ e : A ≅ D, ∀ i, x i ≫ e.hom = z i :=
  ⟨a ≪≫ b, fun i => twoIso_transport a b (x i) (y i) (z i) (ha i) (hb i)⟩

private theorem generatorHom_twostage_ideal_eq {V U X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) (r : V ⟶ U) (j : U ⟶ X)
    (E : U.IdealSheafData) (hE : D.comap j = E) (i : G.I) :
    generatorHom (comapGenerators (D.comap j) r ((pullback j).obj B) (hB.pullback j)
        (comapGenerators D j B hB G)) i ≫
        (@idealLineCongr V ((D.comap j).comap r) (E.comap r)
          (congrArg (fun I : U.IdealSheafData => I.comap r) hE)
          ((pullback r).obj ((pullback j).obj B))).hom =
      generatorHom (comapGenerators E r ((pullback j).obj B) (hB.pullback j)
        ((comapGenerators D j B hB G).ofEpi
          (idealLineCongr hE ((pullback j).obj B)).hom)) i :=
  @generatorHom_comapGenerators_ideal_eq V U (D.comap j) E hE r
    ((pullback j).obj B) (hB.pullback j) (comapGenerators D j B hB G) i

private theorem exists_square_idealFamilyIso {V Y U X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections)
    (c : V ⟶ Y) [IsOpenImmersion c] (π : Y ⟶ X)
    (r : V ⟶ U) (j : U ⟶ X) (hc : c ≫ π = r ≫ j)
    (E : U.IdealSheafData) (hE : D.comap j = E) :
    ∃ e : (pullback c).obj (directLine D B π) ≅ directLine E ((pullback j).obj B) r,
      ∀ i : G.I,
        generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections c
            (comapGenerators D π B hB G)) i ≫ e.hom =
          generatorHom (comapGenerators E r ((pullback j).obj B) (hB.pullback j)
            ((comapGenerators D j B hB G).ofEpi
              (idealLineCongr hE ((pullback j).obj B)).hom)) i := by
  subst E
  refine ⟨squareFamilyIso D B c π r j hc, ?_⟩
  intro i
  apply (generatorHom_squareFamilyIso D B hB G c π r j hc i).trans
  simp only [idealLineCongr, eqToIso_refl, Iso.refl_hom,
    generatorHom_generators, generatorHom_ofEpi, Category.comp_id]

/-- The module/category of this SAME original affine source family is
explicitly the original Spec Γ(X,U), before the native ideal is inserted. -/
private def actualBaseLocalGenerators {X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) (U : X.affineOpens) :
    let E : (Spec Γ(X, U.1)).IdealSheafData :=
      NadelBlowupCanonicalExceptionalGenerators.originalIdeal (D.ideal U)
    (E.toModules ⊗ (pullback U.2.fromSpec).obj B).GeneratingSections :=
  (comapGenerators D U.2.fromSpec B hB G).ofEpi
    (idealLineCongr (Scheme.IdealSheafData.comap_fromSpec D U)
      ((pullback U.2.fromSpec).obj B)).hom

private theorem exists_actualBaseFamilyIso {X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) (U : X.affineOpens) :
    let E : (Spec Γ(X, U.1)).IdealSheafData :=
      NadelBlowupCanonicalExceptionalGenerators.originalIdeal (D.ideal U)
    ∃ e : (pullback (Scheme.IdealSheafData.blowUp.ι D U)).obj (directLine D B D.blowUpπ) ≅
        directLine (X := Spec Γ(X, U.1)) E ((pullback U.2.fromSpec).obj B)
          (affineBlowUp.π (D.ideal U)),
      ∀ i : G.I,
        generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections
            (Scheme.IdealSheafData.blowUp.ι D U)
            (comapGenerators D D.blowUpπ B hB G)) i ≫ e.hom =
          generatorHom (comapGenerators (X := Spec Γ(X, U.1)) E
            (affineBlowUp.π (D.ideal U)) ((pullback U.2.fromSpec).obj B)
            (hB.pullback U.2.fromSpec) (actualBaseLocalGenerators D B hB G U)) i :=
  @exists_square_idealFamilyIso (affineBlowUp (D.ideal U)) D.blowUp (Spec Γ(X, U.1)) X
    D B hB G (Scheme.IdealSheafData.blowUp.ι D U) inferInstance D.blowUpπ
    (affineBlowUp.π (D.ideal U)) U.2.fromSpec (baseTriangle D U)
    (NadelBlowupCanonicalExceptionalGenerators.originalIdeal (D.ideal U))
    (Scheme.IdealSheafData.comap_fromSpec D U)

end EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpenComposition

namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpenComposition
open NadelNefBigGlobalGenerators SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def actualBaseFamilyIso {X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections)
    (U : X.affineOpens) :
    (pullback (Scheme.IdealSheafData.blowUp.ι D U)).obj (directLine D B D.blowUpπ) ≅
      (affineBlowUp.exceptionalIdeal (D.ideal U)).toModules ⊗
        (pullback (affineBlowUp.π (D.ideal U))).obj ((pullback U.2.fromSpec).obj B) :=
  (exists_actualBaseFamilyIso D B hB G U).choose

private theorem actualBaseFamilyIso_basis {X : Scheme.{u}} (D : X.IdealSheafData)
    (B : X.Modules) (hB : IsInvertible B) (G : (D.toModules ⊗ B).GeneratingSections)
    (U : X.affineOpens) (i : G.I) :
    generatorHom (ClosedProjectiveGlobalGeneration.pullback_generatingSections
        (Scheme.IdealSheafData.blowUp.ι D U) (comapGenerators D D.blowUpπ B hB G)) i ≫
        (actualBaseFamilyIso D B hB G U).hom =
      generatorHom (comapGenerators (X := Spec Γ(X, U.1))
        (NadelBlowupCanonicalExceptionalGenerators.originalIdeal (D.ideal U))
        (affineBlowUp.π (D.ideal U)) ((pullback U.2.fromSpec).obj B)
        (hB.pullback U.2.fromSpec) (actualBaseLocalGenerators D B hB G U)) i :=
  (exists_actualBaseFamilyIso D B hB G U).choose_spec i

private noncomputable instance actualBaseLocalGeneratorsFintype {X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I] (U : X.affineOpens) :
    Fintype (actualBaseLocalGenerators D B hB G U).I :=
  (inferInstance : Fintype G.I)

private theorem pulledSection_frame_compare {T U Y : Scheme.{u}}
    (t : T ⟶ U) (c : U ⟶ Y) {M : Y.Modules} {N : U.Modules}
    (E : (pullback c).obj M ≅ N) (e : (pullback t).obj N ≅ unitObj T)
    (σ : unitObj Y ⟶ M) (τ : unitObj U ⟶ N)
    (h : pullbackSectionHom c σ ≫ E.hom = τ) :
    pullbackSectionHom (t ≫ c) σ ≫
        ((pullbackComp t c).symm.app M ≪≫ (pullback t).mapIso E ≪≫ e).hom =
      pullbackSectionHom t τ ≫ e.hom := by
  have h1 : pullbackSectionHom (t ≫ c) σ ≫ (pullbackComp t c).inv.app M =
      pullbackSectionHom t (pullbackSectionHom c σ) := by
    apply (cancel_mono ((pullbackComp t c).hom.app M)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact (pullbackSectionHom_comp t c σ).symm
  have h2 : pullbackSectionHom t (pullbackSectionHom c σ) ≫ (pullback t).map E.hom =
      pullbackSectionHom t τ := by
    simpa only [pullbackSectionHom, Functor.map_comp, Category.assoc] using
      congrArg (fun q => pullbackSectionHom t q) h
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, h1, h2]

/- Actual SAME-family consumer of the checked native comparison producer. -/
private theorem affineTupleMap_coeff {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] {m : ℕ} (r : R →+* A) (s : A →+* C) (a : Fin (m + 1) → C)
    (ha : Ideal.span (Set.range a) = ⊤) :
    Alterations.Geometry.FiniteProjective.affineTupleMap s a ha ≫
        Alterations.Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap r m =
      Alterations.Geometry.FiniteProjective.affineTupleMap (s.comp r) a ha := by
  simp only [Alterations.Geometry.FiniteProjective.affineTupleMap,
    Alterations.Geometry.BlowupProjectiveEmbedding.affineProjectiveMap, Category.assoc,
    Alterations.Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap_comp]

private theorem baseCoefficients_spec {R A : Type u} [CommRing R] [CommRing A]
    {T : Scheme.{u}} (q : T ⟶ Spec (.of A)) (r : R →+* A) :
    GeneratedLineProjectiveAffineMap.baseCoefficients (q ≫ Spec.map (CommRingCat.ofHom r)) =
      (GeneratedLineProjectiveAffineMap.baseCoefficients q).comp r := by
  ext x
  change q.appTop.hom ((Spec.map (CommRingCat.ofHom r)).appTop.hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom x)) =
    q.appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom (r x))
  exact congrArg q.appTop.hom
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r)) x).symm

private theorem affineMap_coeff {R A : Type u} [CommRing R] [CommRing A]
    {T : Scheme.{u}} [IsAffine T] {L : T.Modules}
    (q : T ⟶ Spec (.of A)) (r : R →+* A) (G : L.GeneratingSections) [Fintype G.I]
    (e : L ≅ unitObj T) :
    GeneratedLineProjectiveAffineMap.affineMap q G e ≫
        Alterations.Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap r
          (Fintype.card G.I) =
      GeneratedLineProjectiveAffineMap.affineMap (q ≫ Spec.map (CommRingCat.ofHom r)) G e := by
  unfold GeneratedLineProjectiveAffineMap.affineMap
  rw [Category.assoc, affineTupleMap_coeff]
  apply congrArg (fun a => T.isoSpec.hom ≫ a)
  exact Alterations.Geometry.FiniteProjective.affineTupleMap_congr
    (baseCoefficients_spec q r).symm rfl _ _

private theorem tensorInvertible {Y : Scheme.{u}} {M N : Y.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) : IsInvertible (M ⊗ N) :=
  (hM.tensorObj hN).of_iso (ModularCurves.monoidalTensorObjIso M N)

private theorem affineFramedMap_structure_actual {A : Type u} [CommRing A]
    (I : Ideal A) (B : (Spec (.of A)).Modules) (hB : IsInvertible B)
    (G : ((NadelBlowupCanonicalExceptionalGenerators.originalIdeal I).toModules ⊗ B).GeneratingSections)
    [Fintype G.I] :
    NadelNefBigGlobalPairClosed.affineFramedMap I B hB G ≫
        Alterations.projectiveSpaceStructure A (Fintype.card G.I) = affineBlowUp.π I := by
  let H := comapGenerators (NadelBlowupCanonicalExceptionalGenerators.originalIdeal I)
    (affineBlowUp.π I) B hB G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact GeneratedLineProjectiveMap.projectiveMap_structure (affineBlowUp.π I)
    (tensorInvertible (affineBlowUp.isInvertible_exceptionalIdeal I).isInvertibleModule_toModules
      (hB.pullback (affineBlowUp.π I))) H

private theorem exists_pivotCompatibleFrames {X : Scheme.{u}}
    (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I] (U : X.affineOpens)
    (e : (pullback U.2.fromSpec).obj B ≅ unitObj (Spec Γ(X, U.1))) (a : D.ideal U) :
    let I := D.ideal U
    let πU := affineBlowUp.π I
    let c := Scheme.IdealSheafData.blowUp.ι D U
    let t := affineBlowUp.chart I a
    let Bu := (pullback U.2.fromSpec).obj B
    let LG := directLine D B D.blowUpπ
    let LL := (affineBlowUp.exceptionalIdeal I).toModules ⊗ (pullback πU).obj Bu
    let HG := comapGenerators D D.blowUpπ B hB G
    let GU := actualBaseLocalGenerators D B hB G U
    let HL := comapGenerators (X := Spec Γ(X, U.1))
      (NadelBlowupCanonicalExceptionalGenerators.originalIdeal I) πU Bu (hB.pullback U.2.fromSpec) GU
    let HGT := ClosedProjectiveGlobalGeneration.pullback_generatingSections (t ≫ c) HG
    let HLT := ClosedProjectiveGlobalGeneration.pullback_generatingSections t HL
    ∃ (EL : (pullback t).obj LL ≅ unitObj (Spec (.of (affineBlowUpAlgebra I a))))
      (EG : (pullback (t ≫ c)).obj LG ≅ unitObj (Spec (.of (affineBlowUpAlgebra I a)))),
      ∀ i : G.I, SchemeGeneratedLineCoefficients.coefficient HGT EG i =
        SchemeGeneratedLineCoefficients.coefficient HLT EL i := by
  let I := D.ideal U
  let πU := affineBlowUp.π I
  let c := Scheme.IdealSheafData.blowUp.ι D U
  let t := affineBlowUp.chart I a
  let Bu := (pullback U.2.fromSpec).obj B
  let LG := directLine D B D.blowUpπ
  let LL := (affineBlowUp.exceptionalIdeal I).toModules ⊗ (pullback πU).obj Bu
  let HG := comapGenerators D D.blowUpπ B hB G
  let GU := actualBaseLocalGenerators D B hB G U
  let HL := comapGenerators (X := Spec Γ(X, U.1)) (NadelBlowupCanonicalExceptionalGenerators.originalIdeal I)
    πU Bu (hB.pullback U.2.fromSpec) GU
  let HC := ClosedProjectiveGlobalGeneration.pullback_generatingSections c HG
  let HGT := ClosedProjectiveGlobalGeneration.pullback_generatingSections (t ≫ c) HG
  let HLT := ClosedProjectiveGlobalGeneration.pullback_generatingSections t HL
  let : Fintype HG.I := (inferInstance : Fintype G.I)
  let : Fintype GU.I := (inferInstance : Fintype G.I)
  let : Fintype HL.I := (inferInstance : Fintype G.I)
  let : Fintype HGT.I := (inferInstance : Fintype G.I)
  let : Fintype HLT.I := (inferInstance : Fintype G.I)
  let E := actualBaseFamilyIso D B hB G U
  let EL : (pullback t).obj LL ≅ unitObj (Spec (.of (affineBlowUpAlgebra I a))) :=
    (pullback t).mapIso (NadelNefBigGlobalFrames.untwist
      (affineBlowUp.exceptionalIdeal I).toModules ((pullback πU).obj Bu)
      ((pullback πU).mapIso e ≪≫ pullbackUnitIso πU)) ≪≫
        NadelNefBigExceptionalFrames.chartFrame I a
  let EG : (pullback (t ≫ c)).obj LG ≅
      unitObj (Spec (.of (affineBlowUpAlgebra I a))) :=
    (pullbackComp t c).symm.app LG ≪≫ (pullback t).mapIso E ≪≫ EL
  have hgen (i : G.I) : generatorHom HGT i ≫ EG.hom = generatorHom HLT i ≫ EL.hom := by
    have hf : generatorHom HC i ≫ E.hom = generatorHom HL i :=
      actualBaseFamilyIso_basis D B hB G U i
    have hs : pullbackSectionHom c (generatorHom HG i) ≫ E.hom = generatorHom HL i :=
      (congrArg (fun q => q ≫ E.hom) (generatorHom_pullback c HG i)).symm.trans hf
    rw [generatorHom_pullback, generatorHom_pullback]
    exact pulledSection_frame_compare t c E EL (generatorHom HG i) (generatorHom HL i) hs
  have hcoeff (i : G.I) : SchemeGeneratedLineCoefficients.coefficient HGT EG i =
      SchemeGeneratedLineCoefficients.coefficient HLT EL i := by
    exact (SchemeGeneratedLineCoefficients.coefficient_apply HGT EG i).trans
      ((congrArg (fun s : unitObj (Spec (.of (affineBlowUpAlgebra I a))) ⟶
          unitObj (Spec (.of (affineBlowUpAlgebra I a))) =>
        s.val.app (Opposite.op ⊤) (1 : Γ(Spec (.of (affineBlowUpAlgebra I a)), ⊤)))
          (hgen i)).trans
        (SchemeGeneratedLineCoefficients.coefficient_apply HLT EL i).symm)
  exact ⟨EL, EG, hcoeff⟩

private theorem onPivot {k : Type u} [Field k] {X : Scheme.{u}}
    (D : X.IdealSheafData) (p : X ⟶ Spec (.of k)) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I] (U : X.affineOpens)
    (e : (pullback U.2.fromSpec).obj B ≅ unitObj (Spec Γ(X, U.1))) (a : D.ideal U) :
    (affineBlowUp.chart (D.ideal U) a ≫ Scheme.IdealSheafData.blowUp.ι D U) ≫
        NadelNefBigGlobalPairClosed.globalMap D p B hB G =
      (affineBlowUp.chart (D.ideal U) a ≫
        NadelNefBigGlobalPairClosed.affineFramedMap (D.ideal U)
          ((pullback U.2.fromSpec).obj B) (hB.pullback U.2.fromSpec)
          (actualBaseLocalGenerators D B hB G U)) ≫
        Alterations.Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap
          (Alterations.Geometry.BlowupProjectiveEmbedding.affineBaseCoefficients p U)
          (Fintype.card G.I) := by
  let I := D.ideal U
  let πU := affineBlowUp.π I
  let c := Scheme.IdealSheafData.blowUp.ι D U
  let t := affineBlowUp.chart I a
  let Bu := (pullback U.2.fromSpec).obj B
  let LG := directLine D B D.blowUpπ
  let LL := (affineBlowUp.exceptionalIdeal I).toModules ⊗ (pullback πU).obj Bu
  let HG := comapGenerators D D.blowUpπ B hB G
  let GU := actualBaseLocalGenerators D B hB G U
  let HL := comapGenerators (X := Spec Γ(X, U.1)) (NadelBlowupCanonicalExceptionalGenerators.originalIdeal I)
    πU Bu (hB.pullback U.2.fromSpec) GU
  let HGT := ClosedProjectiveGlobalGeneration.pullback_generatingSections (t ≫ c) HG
  let HLT := ClosedProjectiveGlobalGeneration.pullback_generatingSections t HL
  let : Fintype HG.I := (inferInstance : Fintype G.I)
  let : Fintype GU.I := (inferInstance : Fintype G.I)
  let : Fintype HL.I := (inferInstance : Fintype G.I)
  let : Fintype HGT.I := (inferInstance : Fintype G.I)
  let : Fintype HLT.I := (inferInstance : Fintype G.I)
  obtain ⟨EL, EG, hcoeff⟩ := exists_pivotCompatibleFrames D B hB G U e a
  have hLG : IsInvertible LG :=
    tensorInvertible (Scheme.IdealSheafData.blowUp.isInvertible_comap_π D).isInvertibleModule_toModules
      (hB.pullback D.blowUpπ)
  have hLL : IsInvertible LL :=
    tensorInvertible (affineBlowUp.isInvertible_exceptionalIdeal I).isInvertibleModule_toModules
      ((hB.pullback U.2.fromSpec).pullback πU)
  have hg := NadelNefBigGeneratedOpenMap.projectiveMap_on_affine_openMap (t ≫ c)
    (D.blowUpπ ≫ p) LG hLG HG EG
  have hl := NadelNefBigGeneratedOpenMap.projectiveMap_on_affine_openMap t πU LL hLL HL EL
  change (t ≫ c) ≫ NadelNefBigGlobalPairClosed.globalMap D p B hB G =
    (t ≫ NadelNefBigGlobalPairClosed.affineFramedMap I Bu
      (hB.pullback U.2.fromSpec) GU) ≫ _
  change t ≫ NadelNefBigGlobalPairClosed.affineFramedMap I Bu
      (hB.pullback U.2.fromSpec) GU =
    GeneratedLineProjectiveAffineMap.affineMap (t ≫ πU) HLT EL at hl
  change (t ≫ c) ≫ NadelNefBigGlobalPairClosed.globalMap D p B hB G =
    GeneratedLineProjectiveAffineMap.affineMap ((t ≫ c) ≫ (D.blowUpπ ≫ p)) HGT EG at hg
  rw [hl, hg]
  have hmap : GeneratedLineProjectiveAffineMap.affineMap (t ≫ πU) HLT EL ≫
      Alterations.Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap
        (Alterations.Geometry.BlowupProjectiveEmbedding.affineBaseCoefficients p U)
        (Fintype.card G.I) =
      GeneratedLineProjectiveAffineMap.affineMap ((t ≫ πU) ≫ Spec.map (CommRingCat.ofHom
        (Alterations.Geometry.BlowupProjectiveEmbedding.affineBaseCoefficients p U))) HLT EL :=
    affineMap_coeff (t ≫ πU)
      (Alterations.Geometry.BlowupProjectiveEmbedding.affineBaseCoefficients p U) HLT EL
  apply Eq.trans ?_ hmap.symm
  have hc : c ≫ D.blowUpπ = πU ≫ U.2.fromSpec := by
    rw [Scheme.IdealSheafData.blowUp.ι_π, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι]
  have hbase : (t ≫ c) ≫ (D.blowUpπ ≫ p) =
      (t ≫ πU) ≫ Spec.map (CommRingCat.ofHom
        (Alterations.Geometry.BlowupProjectiveEmbedding.affineBaseCoefficients p U)) := by
    rw [Alterations.Geometry.BlowupProjectiveEmbedding.affineBaseCoefficients_structure]
    simp only [Category.assoc]
    rw [← Category.assoc c, hc]
    simp only [Category.assoc]
  change (Spec (.of (affineBlowUpAlgebra I a))).isoSpec.hom ≫ _ =
    (Spec (.of (affineBlowUpAlgebra I a))).isoSpec.hom ≫ _
  apply congrArg (fun q => (Spec (.of (affineBlowUpAlgebra I a))).isoSpec.hom ≫ q)
  exact Alterations.Geometry.FiniteProjective.affineTupleMap_congr
    (congrArg GeneratedLineProjectiveAffineMap.baseCoefficients hbase)
    (congrArg SchemeGeneratedLineCoefficients.paddedCoefficients (funext hcoeff)) _ _

-- The original whole affine maps agree by their internally produced coefficient
-- identities. The same original pair is then closed by locality on its actual
-- framed target cover; no matching, local-closedness or Mono premise is supplied.

open NadelNefBigGlobalPairBaseOpen NadelNefBigGlobalPairClosed
open GeneratedLineFramedAffineCover
open Alterations Alterations.Geometry.BlowupProjectiveEmbedding
open Alterations.Geometry.ProjectiveSpaceBaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (D : X.IdealSheafData) (p : X ⟶ Spec (.of k))
  (B : X.Modules) (hB : IsInvertible B)
  (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I]

private theorem globalMap_restrict_coeff (U : X.affineOpens)
    (e : (pullback U.2.fromSpec).obj B ≅ unitObj (Spec Γ(X, U.1))) :
    Scheme.IdealSheafData.blowUp.ι D U ≫ globalMap D p B hB G =
      affineFramedMap (D.ideal U) ((pullback U.2.fromSpec).obj B)
        (hB.pullback U.2.fromSpec) (actualBaseLocalGenerators D B hB G U) ≫
        projectiveCoefficientMap (affineBaseCoefficients p U) (Fintype.card G.I) := by
  apply (affineBlowUp.affineOpenCover (D.ideal U)).cover.hom_ext
  intro a
  exact (Category.assoc (affineBlowUp.chart (D.ideal U) a)
    (Scheme.IdealSheafData.blowUp.ι D U) (globalMap D p B hB G)).symm.trans
      ((onPivot D p B hB G U e a).trans
        (Category.assoc (affineBlowUp.chart (D.ideal U) a)
          (affineFramedMap (D.ideal U) ((pullback U.2.fromSpec).obj B)
            (hB.pullback U.2.fromSpec) (actualBaseLocalGenerators D B hB G U))
          (projectiveCoefficientMap (affineBaseCoefficients p U) (Fintype.card G.I))))

private theorem baseProjectivePair_eq (U : X.affineOpens)
    (e : (pullback U.2.fromSpec).obj B ≅ unitObj (Spec Γ(X, U.1))) :
    baseProjectivePair D p B hB G U =
      affineFramedMap (D.ideal U) ((pullback U.2.fromSpec).obj B)
        (hB.pullback U.2.fromSpec) (actualBaseLocalGenerators D B hB G U) := by
  apply (isPullback_projectiveCoefficientMap (affineBaseCoefficients p U)
    (Fintype.card G.I)).hom_ext
  · rw [baseProjectivePair_coeff, globalMap_restrict_coeff D p B hB G U e]
  · rw [baseProjectivePair_structure]
    exact (affineFramedMap_structure_actual (D.ideal U) ((pullback U.2.fromSpec).obj B)
      (hB.pullback U.2.fromSpec) (actualBaseLocalGenerators D B hB G U)).symm

theorem basePair_isClosedImmersion (U : X.affineOpens)
    (e : (pullback U.2.fromSpec).obj B ≅ unitObj (Spec Γ(X, U.1))) :
    IsClosedImmersion (basePair D p B hB G U) := by
  let GU := actualBaseLocalGenerators D B hB G U
  let : Fintype GU.I := (inferInstance : Fintype G.I)
  have h : IsClosedImmersion (baseProjectivePair D p B hB G U) := by
    rw [baseProjectivePair_eq D p B hB G U e]
    exact affineFramedMap_isClosedImmersion (D.ideal U) ((pullback U.2.fromSpec).obj B)
      (hB.pullback U.2.fromSpec) GU e
  let : IsClosedImmersion (basePair D p B hB G U ≫
      (baseTargetProjectiveIso p (Fintype.card G.I) U).hom) := h
  exact IsClosedImmersion.of_comp_isClosedImmersion (basePair D p B hB G U)
    (baseTargetProjectiveIso p (Fintype.card G.I) U).hom

private def framedBaseCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers (FramedAffineSite B)
    (fun U => Spec Γ(X, U.1.1)) (fun U => U.1.2.fromSpec) (by
      intro x
      obtain ⟨U, hxU, e⟩ := exists_framed_affine B hB x
      have hx : x ∈ U.2.fromSpec.opensRange := by
        rw [U.2.opensRange_fromSpec]
        exact hxU
      obtain ⟨z, hz⟩ := hx
      exact ⟨⟨U, e⟩, z, hz⟩)

theorem globalPair_isClosedImmersion : IsClosedImmersion (globalPair D p B hB G) := by
  let C : (Limits.pullback p (projectiveSpaceStructure k (Fintype.card G.I))).OpenCover :=
    (framedBaseCover B hB).pullback₁
      (Limits.pullback.fst p (projectiveSpaceStructure k (Fintype.card G.I)))
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) C
  intro V
  let U : X.affineOpens := ⟨V.1.1, V.1.2⟩
  let eU : (pullback U.2.fromSpec).obj B ≅ unitObj (Spec Γ(X, U.1)) :=
    frameViaFactor U.2.isoSpec.inv U.1.ι U.2.fromSpec U.2.isoSpec_inv_ι (frame B V)
  let : IsClosedImmersion (basePair D p B hB G U) :=
    basePair_isClosedImmersion D p B hB G U eU
  let E := (basePair_isPullback D p B hB G U).flip.isoPullback
  have h : C.pullbackHom (globalPair D p B hB G) V =
      E.inv ≫ basePair D p B hB G U := by
    apply (cancel_epi E.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (basePair_isPullback D p B hB G U).flip.isoPullback_hom_snd
  rw [h]
  infer_instance

theorem globalPair_mono : Mono (globalPair D p B hB G) := by
  let : IsClosedImmersion (globalPair D p B hB G) :=
    globalPair_isClosedImmersion D p B hB G
  infer_instance

end EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpenComposition
