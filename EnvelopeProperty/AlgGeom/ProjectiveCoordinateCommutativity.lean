import EnvelopeProperty.AlgGeom.ProjectiveCoordinateScalars

/-! # The actual local scalars and commutation of projective coordinate multiplication

The elementary unit calculation adapts the private argument in native PoleSheaf.
-/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u

namespace EnvelopeProperty.ProjectiveCoordinateCommutativity

attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

private theorem map_eq_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} {f g : A ⟶ B}
    (h : G.map f = G.map g) : F.map f = F.map g := by
  let : IsIso (e.hom.app B) := (e.app B).isIso_hom
  apply (cancel_mono (e.hom.app B)).mp
  rw [e.hom.naturality f, e.hom.naturality g, h]

private theorem map_comp_eq_of_frame_scalars
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E : C} {T : D} (a : F.obj A ≅ T) (b : F.obj B ≅ T) (c : F.obj E ≅ T)
    (r s : T ⟶ T) (f f' : A ⟶ B) (g g' : B ⟶ E)
    (hf : F.map f ≫ b.hom = a.hom ≫ r)
    (hf' : F.map f' ≫ b.hom = a.hom ≫ s)
    (hg : F.map g ≫ c.hom = b.hom ≫ s)
    (hg' : F.map g' ≫ c.hom = b.hom ≫ r)
    (hrs : r ≫ s = s ≫ r) : F.map (f ≫ g) = F.map (f' ≫ g') := by
  apply (cancel_mono c.hom).mp
  calc
    _ = a.hom ≫ r ≫ s := by
      rw [F.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
    _ = a.hom ≫ s ≫ r := by rw [hrs]
    _ = _ := by
      symm
      rw [F.map_comp, Category.assoc, hg', ← Category.assoc, hf', Category.assoc]

private theorem tensorUnitIso_hom_naturality_left
    {D : Type*} [Category D] [MonoidalCategory D]
    {X Y : D} (e : 𝟙_ D ≅ X) (f : Y ⟶ X) :
    (f ⊗ₘ e.hom) ≫ (e.inv ⊗ₘ e.inv) ≫ (λ_ (𝟙_ D)).hom ≫ e.hom =
      (ρ_ Y).hom ≫ f := by
  rw [← Category.assoc (f ⊗ₘ e.hom) (e.inv ⊗ₘ e.inv), tensorHom_comp_tensorHom,
    e.hom_inv_id, unitors_equal]
  have h := rightUnitor_naturality (f ≫ e.inv)
  calc
    _ = ((f ≫ e.inv ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = (((f ≫ e.inv) ▷ 𝟙_ D) ≫ (ρ_ (𝟙_ D)).hom) ≫ e.hom := by rw [tensorHom_id]
    _ = ((ρ_ Y).hom ≫ (f ≫ e.inv)) ≫ e.hom := congrArg (fun k => k ≫ e.hom) h
    _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
private theorem tensorFrame_insert_scalar {X : Scheme.{u}}
    (M N : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme)
    (g : N.restrict U.ι ≅ unitObj U.toScheme)
    (s : 𝟙_ X.Modules ⟶ N) (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
    (hs : (restrictFunctor U.ι).map s ≫ g.hom =
      (ModularCurves.restrictMonoidalUnitIso U.ι ≪≫
        ModularCurves.monoidalUnitObjIso U.toScheme).hom ≫
          ModularCurves.unitEndomorphismOfTopSection r) :
    (restrictFunctor U.ι).map ((ρ_ M).inv ≫ M ◁ s) ≫
        (SchemeModuleTensorFrames.tensorFrame M N U e g).hom =
      e.hom ≫ ModularCurves.unitEndomorphismOfTopSection r := by
  let F := restrictFunctor U.ι
  let : (Scheme.Modules.pullback U.ι).Monoidal := Scheme.Modules.pullbackMonoidal U.ι
  let : F.Monoidal := Functor.Monoidal.transport (restrictFunctorIsoPullback U.ι).symm
  let eZero : F.obj (𝟙_ X.Modules) ≅ unitObj U.toScheme :=
    ModularCurves.restrictMonoidalUnitIso U.ι ≪≫ ModularCurves.monoidalUnitObjIso U.toScheme
  let d := ModularCurves.unitEndomorphismOfTopSection r
  have hg : F.map s ≫ g.hom = eZero.hom ≫ d := hs
  have htensor : (𝟙 (F.obj M) ⊗ₘ F.map s) ≫ (e.hom ⊗ₘ g.hom) =
      (e.hom ⊗ₘ eZero.hom) ≫ (𝟙 _ ⊗ₘ d) := by
    calc
      _ = (𝟙 (F.obj M) ≫ e.hom) ⊗ₘ (F.map s ≫ g.hom) :=
        tensorHom_comp_tensorHom _ _ _ _
      _ = e.hom ⊗ₘ (eZero.hom ≫ d) := by rw [Category.id_comp, hg]
      _ = _ := (tensorHom_comp_tensorHom e.hom eZero.hom (𝟙 _) d).symm
  have hsource : (ρ_ (F.obj M)).inv ≫ (F.obj M ◁ Functor.LaxMonoidal.ε F) ≫
      (e.hom ⊗ₘ eZero.hom) ≫ (ModularCurves.unitObjTensorIso U.toScheme).hom = e.hom := by
    let eU := ModularCurves.monoidalUnitObjIso U.toScheme
    have heZero : eZero.hom = Functor.OplaxMonoidal.η F ≫ eU.hom := rfl
    have hfirst : (F.obj M ◁ Functor.LaxMonoidal.ε F) ≫
        (e.hom ⊗ₘ eZero.hom) = e.hom ⊗ₘ eU.hom := by
      rw [heZero, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
        ← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]
    have hsecond : (e.hom ⊗ₘ eU.hom) ≫ (ModularCurves.unitObjTensorIso U.toScheme).hom =
        (ρ_ (F.obj M)).hom ≫ e.hom := by
      simpa only [eU, ModularCurves.unitObjTensorIso, Iso.trans_hom, tensorIso_hom,
        Iso.symm_hom] using tensorUnitIso_hom_naturality_left eU e.hom
    calc
      _ = (ρ_ (F.obj M)).inv ≫
          ((F.obj M ◁ Functor.LaxMonoidal.ε F) ≫ (e.hom ⊗ₘ eZero.hom)) ≫
            (ModularCurves.unitObjTensorIso U.toScheme).hom := by simp only [Category.assoc]
      _ = (ρ_ (F.obj M)).inv ≫ (e.hom ⊗ₘ eU.hom) ≫
          (ModularCurves.unitObjTensorIso U.toScheme).hom := by rw [hfirst]
      _ = e.hom := by rw [hsecond]; simp
  rw [← id_tensorHom]
  change F.map ((ρ_ M).inv ≫ (𝟙 M ⊗ₘ s)) ≫
      (ModularCurves.restrictMonoidalTensorIso U.ι M N).hom ≫
        (e.hom ⊗ₘ g.hom) ≫ (ModularCurves.unitObjTensorIso U.toScheme).hom = e.hom ≫ d
  rw [F.map_comp, Functor.Monoidal.map_rightUnitor_inv, Functor.Monoidal.map_tensor, F.map_id]
  change ((ρ_ (F.obj M)).inv ≫ (F.obj M ◁ Functor.LaxMonoidal.ε F) ≫
      Functor.LaxMonoidal.μ F M (𝟙_ X.Modules)) ≫
    (Functor.OplaxMonoidal.δ F M (𝟙_ X.Modules) ≫ (𝟙 (F.obj M) ⊗ₘ F.map s) ≫
      Functor.LaxMonoidal.μ F M N) ≫ Functor.OplaxMonoidal.δ F M N ≫
        (e.hom ⊗ₘ g.hom) ≫ (ModularCurves.unitObjTensorIso U.toScheme).hom = e.hom ≫ d
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← Category.assoc (𝟙 (F.obj M) ⊗ₘ F.map s) (e.hom ⊗ₘ g.hom), htensor]
  have hunitD : (𝟙 (unitObj U.toScheme) ⊗ₘ d) ≫
        (ModularCurves.unitObjTensorIso U.toScheme).hom =
      (ModularCurves.unitObjTensorIso U.toScheme).hom ≫ d := by
    simpa only [ModularCurves.unitEndomorphismOfTopSection_one, one_mul] using
      ModularCurves.unitObjTensorIso_hom_comp_scalars U.toScheme 1 r
  rw [Category.assoc (e.hom ⊗ₘ eZero.hom) (𝟙 (unitObj U.toScheme) ⊗ₘ d)
    (ModularCurves.unitObjTensorIso U.toScheme).hom, hunitD]
  simpa only [Category.assoc] using congrArg (fun k => k ≫ d) hsource

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_monoidalUnitObjIso {X : Scheme.{u}} (U : X.Opens) :
    (restrictFunctor U.ι).map (ModularCurves.monoidalUnitObjIso X).hom ≫
        (restrictUnitIso U.ι).hom =
      (ModularCurves.restrictMonoidalUnitIso U.ι ≪≫
        ModularCurves.monoidalUnitObjIso U.toScheme).hom := by
  have h := ModularCurves.restrictFunctor_map_monoidalUnitObjIso_hom_comp_unitTrivialization U
  have he : (ModularCurves.restrictTrivializationOfOverIso (unitObj X) U (Iso.refl _)).hom =
      (restrictUnitIso U.ι).hom := by
    let H := (overEquiv U).functor
    change ((overFunctorEquiv U).app (unitObj X)).inv ≫
        H.map (𝟙 ((unitObj X).over U)) ≫ 𝟙 _ = (restrictUnitIso U.ι).hom
    erw [H.map_id, Category.comp_id, overFunctorEquiv_unitP]
    rfl
  rw [he] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem tensorFrame_comp_section_scalar {X : Scheme.{u}}
    (M N Q : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme)
    (g : N.restrict U.ι ≅ unitObj U.toScheme)
    (t : Q.restrict U.ι ≅ unitObj U.toScheme)
    (f : unitObj X ⟶ N) (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
    (v : M ⊗ N ⟶ Q)
    (hf : (restrictFunctor U.ι).map f ≫ g.hom =
      (restrictUnitIso U.ι).hom ≫ ModularCurves.unitEndomorphismOfTopSection r)
    (hv : (restrictFunctor U.ι).map v ≫ t.hom =
      (SchemeModuleTensorFrames.tensorFrame M N U e g).hom) :
    (restrictFunctor U.ι).map
        ((ρ_ M).inv ≫ M ◁ ((ModularCurves.monoidalUnitObjIso X).hom ≫ f) ≫ v) ≫
      t.hom = e.hom ≫ ModularCurves.unitEndomorphismOfTopSection r := by
  let F := restrictFunctor U.ι
  let s := (ModularCurves.monoidalUnitObjIso X).hom ≫ f
  have hs : F.map s ≫ g.hom =
      (ModularCurves.restrictMonoidalUnitIso U.ι ≪≫
        ModularCurves.monoidalUnitObjIso U.toScheme).hom ≫
          ModularCurves.unitEndomorphismOfTopSection r := by
    dsimp only [s]
    rw [F.map_comp, Category.assoc, hf, ← Category.assoc, restrict_monoidalUnitObjIso]
  have hi := tensorFrame_insert_scalar (X := X) M N U e g s r hs
  change F.map ((ρ_ M).inv ≫ M ◁ s ≫ v) ≫ t.hom = _
  calc
    _ = F.map ((ρ_ M).inv ≫ M ◁ s) ≫ (F.map v ≫ t.hom) := by
      simp only [F.map_comp, Category.assoc]
    _ = _ := by rw [hv]; exact hi

variable {R : Type u} [CommRing R] {σ : Type}

set_option backward.isDefEq.respectTransparency false in
/-- In every standard coordinate frame, the original integer coordinate
multiplication has the literal coordinate-ratio scalar. -/
theorem coordinateMul_restrict_hom (j i h : σ) (a : ℤ) :
    (restrictFunctor (coordinateOpen (R := R) h).ι).map
        (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i a) ≫
      (coordinateHyperplaneTwistTrivialization (R := R) h j (a + 1)).hom =
    (coordinateHyperplaneTwistTrivialization (R := R) h j a).hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.affineOpenTopSection
          ⟨coordinateOpen (R := R) h, coordinateOpen_isAffineOpen h⟩
          (coordinateHyperplaneLocalEquation (R := R) h i)) := by
  exact tensorFrame_comp_section_scalar
    (X := Proj (homogeneousSubmodule σ R))
    (coordinateHyperplaneTwist (R := R) j a)
    (coordinateHyperplaneTwist (R := R) j 1)
    (coordinateHyperplaneTwist (R := R) j (a + 1))
    (coordinateOpen (R := R) h)
    (coordinateHyperplaneTwistTrivialization (R := R) h j a)
    (coordinateHyperplaneTwistTrivialization (R := R) h j 1)
    (coordinateHyperplaneTwistTrivialization (R := R) h j (a + 1))
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) j i 1)
    (ModularCurves.affineOpenTopSection
      ⟨coordinateOpen (R := R) h, coordinateOpen_isAffineOpen h⟩
      (coordinateHyperplaneLocalEquation (R := R) h i))
    (ProjectiveTwistTensorAddition.tensorIso (R := R) j j j a 1).hom
    (ProjectiveCoordinateScalars.coordinateSectionHom_restrict_hom (R := R) j i h)
    (ProjectiveCoordinateScalars.tensorIso_restrict_hom (R := R) j j j h a 1)

set_option backward.isDefEq.respectTransparency false in
/-- The two original coordinate multiplications commute as actual whole
morphisms between the same integer projective twists. -/
theorem coordinateMul_comm (j i k : σ) (a : ℤ) :
    ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i a ≫
        ProjectiveCoordinateMultiplication.coordinateMul (R := R) j k (a + 1) =
      ProjectiveCoordinateMultiplication.coordinateMul (R := R) j k a ≫
        ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i (a + 1) := by
  let P := Proj (homogeneousSubmodule σ R)
  have hcover : ∀ x : P, ∃ h : σ, x ∈ coordinateOpen (R := R) h := by
    intro x
    have hx : x ∈ ⨆ h : σ, coordinateOpen (R := R) h := by
      rw [iSup_coordinateOpen_eq_top]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  apply SchemeModuleMorphismGluing.bundleHom_ext (X := P) _ _
    (coordinateOpen (R := R)) hcover
  intro h
  let U : P.Opens := coordinateOpen (R := R) h
  let F : P.Modules ⥤ U.toScheme.Modules := restrictFunctor U.ι
  apply (overEquiv U).functor.map_injective
  apply map_eq_of_iso (overFunctorEquiv U)
  let e (b : ℤ) : F.obj (coordinateHyperplaneTwist (R := R) j b) ≅ unitObj U.toScheme :=
    coordinateHyperplaneTwistTrivialization (R := R) h j b
  let r (c : σ) : Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ModularCurves.affineOpenTopSection (Y := P)
      ⟨U, coordinateOpen_isAffineOpen (R := R) h⟩
      (coordinateHyperplaneLocalEquation (R := R) h c)
  let di := ModularCurves.unitEndomorphismOfTopSection (X := U.toScheme) (r i)
  let dk := ModularCurves.unitEndomorphismOfTopSection (X := U.toScheme) (r k)
  have hcomm : di ≫ dk = dk ≫ di := by
    dsimp only [di, dk]
    rw [ModularCurves.unitEndomorphismOfTopSection_comp,
      ModularCurves.unitEndomorphismOfTopSection_comp, mul_comm]
  exact map_comp_eq_of_frame_scalars F (e a) (e (a + 1)) (e (a + 1 + 1)) di dk
    (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i a)
    (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j k a)
    (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j k (a + 1))
    (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i (a + 1))
    (coordinateMul_restrict_hom (R := R) j i h a)
    (coordinateMul_restrict_hom (R := R) j k h a)
    (coordinateMul_restrict_hom (R := R) j k h (a + 1))
    (coordinateMul_restrict_hom (R := R) j i h (a + 1)) hcomm

/-- The same original coordinate square commutes after tensoring by every
module, without any flatness or quasicoherence hypothesis. -/
theorem moduleCoordinateMul_comm
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (j i k : σ) (a : ℤ) :
    ProjectiveCoordinateMultiplication.moduleCoordinateMul M j i a ≫
        ProjectiveCoordinateMultiplication.moduleCoordinateMul M j k (a + 1) =
      ProjectiveCoordinateMultiplication.moduleCoordinateMul M j k a ≫
        ProjectiveCoordinateMultiplication.moduleCoordinateMul M j i (a + 1) := by
  change (tensorLeft M).map (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i a) ≫
      (tensorLeft M).map (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j k (a + 1)) =
    (tensorLeft M).map (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j k a) ≫
      (tensorLeft M).map (ProjectiveCoordinateMultiplication.coordinateMul (R := R) j i (a + 1))
  rw [← Functor.map_comp, ← Functor.map_comp, coordinateMul_comm (R := R)]

end EnvelopeProperty.ProjectiveCoordinateCommutativity
