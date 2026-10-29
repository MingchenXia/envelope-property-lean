import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalDegreeZero
import ModularCurves.ForMathlib.SchemeModuleSheaf
import ModularCurves.ForMathlib.TotalComplexModuleForget
import Mathlib.Topology.Sheaves.Abelian

/-! # Actual stalks commute with the same original module Cech total and augmentation -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechStalkTotal
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace Opposite
open DeligneIllusieLocalContinuationCechAugmentation DeligneIllusieLocalContinuationCechBicomplex
open DeligneIllusieLocalContinuationCechTotalAugmentation
universe u
variable {X : Scheme.{u}}

/-- The actual original module-to-additive-sheaf functor followed by the actual stalk. -/
def stalkFunctor (X : Scheme.{u}) (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toSheaf X ⋙
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

/-- Additivity is internally inherited from the actual two native functors. -/
instance stalkFunctor_additive (x : X) : (stalkFunctor X x).Additive := by
  dsimp only [stalkFunctor]
  infer_instance

private instance stalkFunctor_finiteLimits (x : X) : PreservesFiniteLimits (stalkFunctor X x) := by
  dsimp only [stalkFunctor]
  infer_instance

private instance stalkFunctor_finiteColimits (x : X) : PreservesFiniteColimits (stalkFunctor X x) := by
  dsimp only [stalkFunctor]
  infer_instance

/-- Native exactness of the actual composite gives genuine homology preservation. -/
instance stalkFunctor_preservesHomology (x : X) : (stalkFunctor X x).PreservesHomology :=
  Functor.preservesHomologyOfExact (stalkFunctor X x)

private abbrev mapBicomplex (x : X)
    (K : HomologicalComplex₂ X.Modules (.up ℕ) (.up ℕ)) :
    HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  (((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K

private theorem mapBicomplex_outer (x : X)
    (K : HomologicalComplex₂ X.Modules (.up ℕ) (.up ℕ)) (i i' j : ℕ) :
    ((mapBicomplex x K).d i i').f j = (stalkFunctor X x).map ((K.d i i').f j) := rfl

private theorem mapBicomplex_inner (x : X)
    (K : HomologicalComplex₂ X.Modules (.up ℕ) (.up ℕ)) (i j j' : ℕ) :
    ((mapBicomplex x K).X i).d j j' = (stalkFunctor X x).map ((K.X i).d j j') := rfl

private instance finiteDiagonal (n : ℕ) :
    Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
  change Finite {ij : ℕ × ℕ // ij.1 + ij.2 = n}
  let e : {ij : ℕ × ℕ // ij.1 + ij.2 = n} → Fin (n+1) × Fin (n+1) :=
    fun ij => (⟨ij.1.1, by have := ij.2; omega⟩, ⟨ij.1.2, by have := ij.2; omega⟩)
  exact Finite.of_injective e (by
    intro a b h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h))

variable {x : X} (K : HomologicalComplex₂ X.Modules (.up ℕ) (.up ℕ))

private def stalkTotalDiagramIso (n : ℕ) :
    Discrete.functor
        (K.toGradedObject.mapObjFun
          (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) ⋙
      (stalkFunctor X x) ≅
    Discrete.functor
      ((mapBicomplex x K).toGradedObject.mapObjFun
        (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) :=
  Discrete.natIso fun _ => Iso.refl _

/-- The degreewise isomorphism underlying `stalkTotalIsoForK (x := x)`. -/
private def stalkTotalXIso (n : ℕ) :
    (stalkFunctor X x).obj ((K.total (.up ℕ)).X n) ≅
      (((mapBicomplex x K).total (.up ℕ)).X n) :=
  preservesColimitIso (stalkFunctor X x)
      (Discrete.functor
        (K.toGradedObject.mapObjFun
          (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)) ≪≫
    HasColimit.isoOfNatIso (stalkTotalDiagramIso (x := x) K n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise total-complex comparison sends a forgotten coproduct
injection to the corresponding injection of the forgotten bicomplex. -/
@[reassoc]
private theorem stalk_map_ιTotal_stalkTotalXIso_hom
    (i j n : ℕ)
    (h : ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) (i, j) = n) :
    (stalkFunctor X x).map
        (K.ιTotal (.up ℕ) i j n h) ≫
      (stalkTotalXIso (x := x) K n).hom =
    (mapBicomplex x K).ιTotal (.up ℕ) i j n h := by
  change
    (stalkFunctor X x).map
        (colimit.ι
          (Discrete.functor
            (K.toGradedObject.mapObjFun
              (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n))
          ⟨(i, j), by simpa using h⟩) ≫
      (preservesColimitIso (stalkFunctor X x)
          (Discrete.functor
            (K.toGradedObject.mapObjFun
              (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)) ≪≫
        HasColimit.isoOfNatIso
          (stalkTotalDiagramIso (x := x) K n)).hom =
      colimit.ι
        (Discrete.functor
          ((mapBicomplex x K).toGradedObject.mapObjFun
            (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n))
        ⟨(i, j), by simpa using h⟩
  rw [Iso.trans_hom, ← Category.assoc]
  rw [ι_preservesColimitIso_hom]
  rw [HasColimit.isoOfNatIso_ι_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem stalk_ιTotal_stalkTotalXIso_inv
    (i j n : ℕ)
    (h : ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) (i, j) = n) :
    (mapBicomplex x K).ιTotal (.up ℕ) i j n h ≫
      (stalkTotalXIso (x := x) K n).inv =
    (stalkFunctor X x).map
      (K.ιTotal (.up ℕ) i j n h) := by
  rw [← stalk_map_ιTotal_stalkTotalXIso_hom (x := x) K i j n h]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem stalk_map_ιTotalOrZero_stalkTotalXIso_hom
    (i j n : ℕ) :
    (stalkFunctor X x).map
        (K.ιTotalOrZero (.up ℕ) i j n) ≫
      (stalkTotalXIso (x := x) K n).hom =
    (mapBicomplex x K).ιTotalOrZero (.up ℕ) i j n := by
  by_cases h :
      ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ) (i, j) = n
  · rw [K.ιTotalOrZero_eq (.up ℕ) i j n h,
      (mapBicomplex x K).ιTotalOrZero_eq (.up ℕ) i j n h]
    exact
      stalk_map_ιTotal_stalkTotalXIso_hom (x := x) K i j n h
  · rw [K.ιTotalOrZero_eq_zero (.up ℕ) i j n h,
      (mapBicomplex x K).ιTotalOrZero_eq_zero (.up ℕ) i j n h]
    rw [Functor.map_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem stalk_map_d₁_stalkTotalXIso_hom
    {i i' : ℕ} (h : (ComplexShape.up ℕ).Rel i i') (j n : ℕ) :
    (stalkFunctor X x).map
        (K.d₁ (.up ℕ) i j n) ≫
      (stalkTotalXIso (x := x) K n).hom =
    (mapBicomplex x K).d₁ (.up ℕ) i j n := by
  rw [K.d₁_eq' (.up ℕ) h j n,
    (mapBicomplex x K).d₁_eq' (.up ℕ) h j n]
  rw [mapBicomplex_outer]
  rw [Functor.map_units_smul, Functor.map_comp]
  rw [Linear.units_smul_comp, Category.assoc,
    stalk_map_ιTotalOrZero_stalkTotalXIso_hom (x := x)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem stalk_map_d₂_stalkTotalXIso_hom
    (i : ℕ) {j j' : ℕ} (h : (ComplexShape.up ℕ).Rel j j') (n : ℕ) :
    (stalkFunctor X x).map
        (K.d₂ (.up ℕ) i j n) ≫
      (stalkTotalXIso (x := x) K n).hom =
    (mapBicomplex x K).d₂ (.up ℕ) i j n := by
  rw [K.d₂_eq' (.up ℕ) i h n,
    (mapBicomplex x K).d₂_eq' (.up ℕ) i h n]
  rw [mapBicomplex_inner]
  rw [Functor.map_units_smul, Functor.map_comp]
  rw [Linear.units_smul_comp, Category.assoc,
    stalk_map_ιTotalOrZero_stalkTotalXIso_hom (x := x)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem stalk_map_D₁_stalkTotalXIso_hom
    (n n' : ℕ) :
    (stalkFunctor X x).map
        (K.D₁ (.up ℕ) n n') ≫
      (stalkTotalXIso (x := x) K n').hom =
    (stalkTotalXIso (x := x) K n).hom ≫
      (mapBicomplex x K).D₁ (.up ℕ) n n' := by
  apply (cancel_epi (stalkTotalXIso (x := x) K n).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  rw [stalk_ιTotal_stalkTotalXIso_inv_assoc (x := x)]
  rw [← Functor.map_comp_assoc, K.ι_D₁]
  rw [stalk_map_d₁_stalkTotalXIso_hom (x := x) K
    (show (ComplexShape.up ℕ).Rel i (i + 1) by rfl) j n']
  rw [(mapBicomplex x K).ι_D₁]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem stalk_map_D₂_stalkTotalXIso_hom
    (n n' : ℕ) :
    (stalkFunctor X x).map
        (K.D₂ (.up ℕ) n n') ≫
      (stalkTotalXIso (x := x) K n').hom =
    (stalkTotalXIso (x := x) K n).hom ≫
      (mapBicomplex x K).D₂ (.up ℕ) n n' := by
  apply (cancel_epi (stalkTotalXIso (x := x) K n).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  rw [stalk_ιTotal_stalkTotalXIso_inv_assoc (x := x)]
  rw [← Functor.map_comp_assoc, K.ι_D₂]
  rw [stalk_map_d₂_stalkTotalXIso_hom (x := x) K i
    (show (ComplexShape.up ℕ).Rel j (j + 1) by rfl) n']
  rw [(mapBicomplex x K).ι_D₂]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem stalk_map_total_d_stalkTotalXIso_hom
    (n n' : ℕ) :
    (stalkFunctor X x).map
        ((K.total (.up ℕ)).d n n') ≫
      (stalkTotalXIso (x := x) K n').hom =
    (stalkTotalXIso (x := x) K n).hom ≫
      ((mapBicomplex x K).total (.up ℕ)).d n n' := by
  rw [HomologicalComplex₂.total_d, HomologicalComplex₂.total_d,
    Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
    stalk_map_D₁_stalkTotalXIso_hom (x := x),
    stalk_map_D₂_stalkTotalXIso_hom (x := x)]

/-- Forgetting the module structure commutes with the first-quadrant total
complex. -/
private def stalkTotalIsoForK :
    ((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).obj
        (K.total (.up ℕ)) ≅
      (mapBicomplex x K).total (.up ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => stalkTotalXIso (x := x) K n)
    (fun n n' _ =>
      (stalk_map_total_d_stalkTotalXIso_hom (x := x) K n n').symm)


variable {ι : Type u} (U : ι → X.Opens) (E : CochainComplex X.Modules ℕ) (x : X)

/-- The SAME original native Cech bicomplex, mapped by the actual stalk functor twice. -/
def stalkBicomplex : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  mapBicomplex x (bicomplex U E)

/-- The actual ENTIRE stalk--total cochain isomorphism for the SAME original bicomplex. -/
def totalStalkIso :
    ((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).obj (totalComplex U E) ≅
      HomologicalComplex₂.total (stalkBicomplex U E x) (.up ℕ) :=
  stalkTotalIsoForK (x := x) (bicomplex U E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalkHorizontal_comm (q q' : ℕ) :
    (stalkFunctor X x).map (augmentation U (E.X q)) ≫
        ((stalkBicomplex U E x).d q q').f 0 =
      (((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).obj E).d q q' ≫
        (stalkFunctor X x).map (augmentation U (E.X q')) := by
  change (stalkFunctor X x).map (augmentation U (E.X q)) ≫
      (stalkFunctor X x).map (((bicomplex U E).d q q').f 0) =
    (stalkFunctor X x).map (E.d q q') ≫
      (stalkFunctor X x).map (augmentation U (E.X q'))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f => (stalkFunctor X x).map f) (augmentation_naturality U (E.d q q'))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalkHorizontal_zero (q : ℕ) :
    (stalkFunctor X x).map (augmentation U (E.X q)) ≫
      ((stalkBicomplex U E x).X q).d 0 1 = 0 := by
  change (stalkFunctor X x).map (augmentation U (E.X q)) ≫
      (stalkFunctor X x).map (((bicomplex U E).X q).d 0 1) = 0
  have h : augmentation U (E.X q) ≫ ((bicomplex U E).X q).d 0 1 = 0 :=
    augmentationToBicomplex_inner_d U E q
  exact ((stalkFunctor X x).map_comp _ _).symm.trans
    ((congrArg (fun f => (stalkFunctor X x).map f) h).trans (Functor.map_zero (stalkFunctor X x) _ _))

/-- The actual native edge of the SAME stalk bicomplex, from the SAME mapped original units. -/
def stalkAugmentation :
    ((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).obj E ⟶
      HomologicalComplex₂.total (stalkBicomplex U E x) (.up ℕ) :=
  HomologicalComplex₂.totalUpNatHorizontalEdge (stalkBicomplex U E x)
    (((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).obj E)
    (fun q => (stalkFunctor X x).map (augmentation U (E.X q)))
    (fun q q' _ => stalkHorizontal_comm U E x q q')
    (fun q => stalkHorizontal_zero U E x q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping the SAME original total augmentation gives this native stalk edge as a WHOLE cochain map. -/
theorem totalAugmentation_stalk_square :
    ((stalkFunctor X x).mapHomologicalComplex (.up ℕ)).map (totalAugmentation U E) ≫
      (totalStalkIso U E x).hom = stalkAugmentation U E x := by
  apply HomologicalComplex.hom_ext
  intro q
  change (stalkFunctor X x).map
      (augmentation U (E.X q) ≫ HomologicalComplex₂.ιTotal (bicomplex U E) (.up ℕ) q 0 q rfl) ≫
      (stalkTotalXIso (x := x) (bicomplex U E) q).hom =
    (stalkFunctor X x).map (augmentation U (E.X q)) ≫
      HomologicalComplex₂.ιTotal (mapBicomplex x (bicomplex U E)) (.up ℕ) q 0 q rfl
  rw [Functor.map_comp, Category.assoc,
    stalk_map_ιTotal_stalkTotalXIso_hom (x := x)]

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechStalkTotal
