import EnvelopeProperty.Local.PLOriginalModelCompatibilityNativeResidueNorm
import EnvelopeProperty.Local.PLOriginalModelCompatibilityRatioSectionFrames
import EnvelopeProperty.Global.NativeTestConfigurationModelPotential
import EnvelopeProperty.Global.NativeTestConfigurationFibreOneCompatibility
import EnvelopeProperty.Berkovich.SchemeLineModelTensorNorms
import EnvelopeProperty.Berkovich.SchemeLineSectionNormPullback
import EnvelopeProperty.Berkovich.SchemeLineModelHomComposition
import EnvelopeProperty.Berkovich.SchemeLineFibreSectionNorms
import EnvelopeProperty.AlgGeom.SchemeTensorObjUnits
import EnvelopeProperty.AlgGeom.CartierCanonicalTensorPullback
import EnvelopeProperty.AlgGeom.CartierPullbackTensorCoherence
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # The model potential of a twisted canonical Cartier ratio line

Let `C` be a test configuration of `X`, let `π : C.total ⟶ X` be a morphism
compatible with the action and with the fibre-one identification, let `L` be
an invertible module on `X`, and let `K, J` be invertible ideal sheaves on
`C.total` whose supports miss the whole noncentral open `C.unitOpen`.  The
twisted ratio line is `M = π^*L ⊗ K ⊗ J^∨`.  We prove that its native model
potential (`TestConfiguration.gaussNativeModelPotential`, the potential of the
Fubini–Study constructions of `Global/NativeTestConfigurationModelPotential`)
is, at every trivially valued point `x` of `X`,

  `pot_M(x) = -log ‖σ‖(z)`,

where `z` is the radius-`r` Gauss point of the test configuration over `x`
and `σ` is the canonical ratio section `K^{-1} ⊗ (J ↪ O)^∨` of `K ⊗ J^∨`
(`RatioSectionTransport.canonicalPulledRatioSection`), provided the action
comparison of `M` is the tensor of the canonical twist comparison and the
canonical Cartier group comparison, and the fibre-one comparison of `M` is the
tensor of the canonical twist identification and a trivialisation of the ratio
on fibre one (`hα`, `he₁`, `hαT`, `hαR` below: they are the structural laws of
the comparisons of `Local/PLOriginalModelCompatibility{GmTwistedLine,FibreOne}`).

Mathematically (FHX, proof of Lemma 5.5; BJ22 §§2–3 for the model metric of a
test configuration): on the noncentral open the action identifies `M` with the
pullback of `M|_{t=1}`; the canonical ratio section is invariant
(`RatioSectionTransport.cartierRatioGroupLinearization_canonicalSection`), it
restricts on fibre one to a global unit `ε` of the proper fibre, and the twist
part is the pullback of `L`.  Hence the transport of `π^*s ⊗ σ` to `X × 𝔾ₘ` is
`pr₁^*(ε s)`, whose reference norm at the Gauss point is `‖s‖(x)`, while its
model norm is `‖s‖(x) · ‖σ‖(z)`.  Comparing both with the defining factor of
the potential (`gaussCompatibleNormFactor_residue_formula`) and choosing a
global section `s` of `L` with `‖s‖(x) ≠ 0` gives the identity.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry Opposite
open Scheme.Modules
open scoped NNReal ENNReal Classical
noncomputable section
universe u

namespace EnvelopeProperty.PLOriginalModelCompatibility.TwistedRatioCalculus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance twistedRatioCalculusModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance twistedRatioCalculusPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
open SchemeLineSectionEvaluation SchemeTensorSectionHoms RatioSectionTransport

variable {X Y Z : Scheme.{u}}

/-! ### Calculus of pulled sections -/

/-- Pulled sections compose with pulled module morphisms. -/
theorem pullbackSectionHom_map (f : X ⟶ Y) {P Q : Y.Modules} (τ : unitObj Y ⟶ P)
    (β : P ⟶ Q) :
    pullbackSectionHom f τ ≫ (pullback f).map β = pullbackSectionHom f (τ ≫ β) := by
  simp only [pullbackSectionHom, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The inverse composition comparison of a section pulled along a composite. -/
theorem pullbackSectionHom_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z) {P : Z.Modules}
    (τ : unitObj Z ⟶ P) :
    pullbackSectionHom (f ≫ g) τ ≫ (pullbackComp f g).inv.app P =
      pullbackSectionHom f (pullbackSectionHom g τ) := by
  rw [← SchemeLineSectionEvaluation.pullbackSectionHom_comp f g τ, Category.assoc,
    Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- `pullbackCongr` along a reflexivity proof is the identity. -/
theorem pullbackCongr_rfl_hom_app (f : X ⟶ Y) (P : Y.Modules) :
    (pullbackCongr (rfl : f = f)).hom.app P = 𝟙 _ :=
  rfl

/-- Pulled sections along equal morphisms agree through `pullbackCongr`. -/
theorem pullbackSectionHom_congr {f f' : X ⟶ Y} (h : f = f') {P : Y.Modules}
    (τ : unitObj Y ⟶ P) :
    pullbackSectionHom f τ ≫ (pullbackCongr h).hom.app P = pullbackSectionHom f' τ := by
  subst h
  exact Category.comp_id _

/-- A scalar factor of a section is pulled back to the pulled scalar. -/
theorem pullbackSectionHom_scalar (f : X ⟶ Y) {P : Y.Modules}
    (ε : unitObj Y ⟶ unitObj Y) (τ : unitObj Y ⟶ P) :
    pullbackSectionHom f (ε ≫ τ) =
      (pullbackSectionHom f ε ≫ (pullbackUnitIso f).hom) ≫ pullbackSectionHom f τ := by
  simp only [pullbackSectionHom, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Pulled scalars along a composite are iterated pulled scalars. -/
theorem pullbackSectionHom_unit_comp (f : X ⟶ Y) (g : Y ⟶ Z) (ε : unitObj Z ⟶ unitObj Z) :
    pullbackSectionHom (f ≫ g) ε ≫ (pullbackUnitIso (f ≫ g)).hom =
      pullbackSectionHom f (pullbackSectionHom g ε ≫ (pullbackUnitIso g).hom) ≫
        (pullbackUnitIso f).hom := by
  have hu : (pullbackComp f g).hom.app (unitObj Z) ≫ (pullbackUnitIso (f ≫ g)).hom =
      (pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom :=
    ModularCurves.pullbackUnitIso_compLow f g
  rw [← SchemeLineSectionEvaluation.pullbackSectionHom_comp f g ε, Category.assoc, hu,
    ← Category.assoc, pullbackSectionHom_map]

/-- Pulled scalars along equal morphisms agree. -/
theorem pullbackSectionHom_unit_congr {f f' : X ⟶ Y} (h : f = f')
    (ε : unitObj Y ⟶ unitObj Y) :
    pullbackSectionHom f ε ≫ (pullbackUnitIso f).hom =
      pullbackSectionHom f' ε ≫ (pullbackUnitIso f').hom := by
  subst h
  rfl

/-- Morphisms out of the structure sheaf are determined by the image of `1`. -/
theorem unitHom_ext {P : X.Modules} {a b : unitObj X ⟶ P}
    (h : sectionAtOne a = sectionAtOne b) : a = b := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply a.val i (1 : Γ(X, ⊤))
  have hb := PresheafOfModules.naturality_apply b.val i (1 : Γ(X, ⊤))
  change a.val.app V (X.presheaf.map i (1 : Γ(X, ⊤))) = P.presheaf.map i (sectionAtOne a) at ha
  change b.val.app V (X.presheaf.map i (1 : Γ(X, ⊤))) = P.presheaf.map i (sectionAtOne b) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun q => P.presheaf.map i q) h).trans hb.symm)

/-- A morphism out of the structure sheaf is the top-section morphism of its value at `1`. -/
theorem topSectionHom_sectionAtOne {P : X.Modules} (a : unitObj X ⟶ P) :
    Scheme.Modules.topSectionHom P (sectionAtOne a) = a := by
  apply unitHom_ext
  exact Scheme.Modules.topSectionHom_app_top_apply_one P _

/-- The value at `1` of a tensor section is the pure tensor of the values. -/
theorem sectionAtOne_tensorSectionHom {P Q : X.Modules} (a : unitObj X ⟶ P)
    (b : unitObj X ⟶ Q) :
    sectionAtOne (tensorSectionHom a b) =
      ModularCurves.tensorSection P Q ⊤ (sectionAtOne a) (sectionAtOne b) := by
  have h := ModularCurves.topSectionHom_tensorSection P Q (sectionAtOne a) (sectionAtOne b)
  rw [topSectionHom_sectionAtOne, topSectionHom_sectionAtOne] at h
  have h' : tensorSectionHom a b = Scheme.Modules.topSectionHom (P ⊗ Q)
      (ModularCurves.tensorSection P Q ⊤ (sectionAtOne a) (sectionAtOne b)) := h.symm
  rw [h']
  exact Scheme.Modules.topSectionHom_app_top_apply_one _ _

/-- The structure-sheaf multiplication followed by the monoidal right unit is trivial. -/
theorem unitObjTensorIso_inv_rightUnit :
    (ModularCurves.unitObjTensorIso X).inv ≫
        unitObj X ◁ (ModularCurves.monoidalUnitObjIso X).inv ≫ (ρ_ (unitObj X)).hom =
      𝟙 _ := by
  have hd : (ModularCurves.unitObjTensorIso X).inv =
      (ModularCurves.monoidalUnitObjIso X).inv ≫ (λ_ (𝟙_ X.Modules)).inv ≫
        ((ModularCurves.monoidalUnitObjIso X).hom ⊗ₘ (ModularCurves.monoidalUnitObjIso X).hom) := by
    simp only [ModularCurves.unitObjTensorIso, Iso.trans_inv, tensorIso_inv, Iso.symm_inv,
      Category.assoc]
  rw [hd]
  simp only [Category.assoc]
  rw [MonoidalCategory.tensorHom_def, Category.assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
    whiskerLeft_id, Category.id_comp, rightUnitor_naturality, unitors_inv_equal,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- The associated form of `unitObjTensorIso_inv_rightUnit`. -/
theorem unitObjTensorIso_inv_rightUnit_assoc {P : X.Modules} (h : unitObj X ⟶ P) :
    (ModularCurves.unitObjTensorIso X).inv ≫
        unitObj X ◁ (ModularCurves.monoidalUnitObjIso X).inv ≫ (ρ_ (unitObj X)).hom ≫ h = h := by
  have e := unitObjTensorIso_inv_rightUnit (X := X)
  calc _ = ((ModularCurves.unitObjTensorIso X).inv ≫
        unitObj X ◁ (ModularCurves.monoidalUnitObjIso X).inv ≫ (ρ_ (unitObj X)).hom) ≫ h := by
        simp only [Category.assoc]
    _ = h := by rw [e, Category.id_comp]

/-- A tensor section with a scalar second factor contracts by the right unit. -/
theorem tensorSectionHom_rightUnit {P : X.Modules} (a : unitObj X ⟶ P)
    (c : unitObj X ⟶ unitObj X) :
    tensorSectionHom a c ≫ P ◁ (ModularCurves.monoidalUnitObjIso X).inv ≫ (ρ_ P).hom = c ≫ a := by
  have hc := Scheme.Modules.unitHom_eq_globalScalar c
  have hs : tensorSectionHom a c = c ≫ tensorSectionHom a (𝟙 _) := by
    have h := tensorSectionHom_precomp_scalars a (𝟙 (unitObj X)) 1
      ((c.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))
    rw [ModularCurves.unitEndomorphismOfTopSection_one, Category.id_comp, Category.comp_id,
      one_mul, ← hc] at h
    exact h
  rw [hs, Category.assoc]
  congr 1
  unfold tensorSectionHom
  rw [tensorHom_id, Category.assoc, ← whisker_exchange_assoc, rightUnitor_naturality,
    unitObjTensorIso_inv_rightUnit_assoc]

/-! ### Explicit tensor sections of pulled explicit tensor products -/

/-- The explicit tensor section of `f^*(T ⊗ R)` built from sections of `f^*T` and `f^*R`. -/
def pulledTensorSection (f : X ⟶ Y) {T R : Y.Modules} (a : unitObj X ⟶ (pullback f).obj T)
    (b : unitObj X ⟶ (pullback f).obj R) :
    unitObj X ⟶ (pullback f).obj (Scheme.Modules.tensorObj T R) :=
  tensorSectionHom a b ≫ (Functor.Monoidal.μIso (pullback f) T R).hom ≫
    (pullback f).map (ModularCurves.monoidalTensorObjIso T R).hom

/-- The pullback tensorators are compatible with the pullback composition comparison. -/
theorem tensorator_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (T R : Z.Modules) :
    (Functor.Monoidal.μIso (pullback f) ((pullback g).obj T) ((pullback g).obj R)).hom ≫
        (pullback f).map (Functor.Monoidal.μIso (pullback g) T R).hom ≫
          (pullbackComp f g).hom.app (T ⊗ R) =
      ((pullbackComp f g).hom.app T ⊗ₘ (pullbackComp f g).hom.app R) ≫
        (Functor.Monoidal.μIso (pullback (f ≫ g)) T R).hom := by
  have h2 := Scheme.Modules.pullbackComp_inverse_tensorator f g T R
  apply (cancel_mono (Functor.Monoidal.μIso (pullback (f ≫ g)) T R).inv).mp
  simp only [Category.assoc]
  rw [← h2]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_assoc, Category.comp_id]

/-- An explicit tensor section of an iterated pullback, transported by the composition
comparison, is the explicit tensor section along the composite. -/
theorem pulledTensorSection_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) {T R : Z.Modules}
    (a : unitObj X ⟶ (pullback f).obj ((pullback g).obj T))
    (b : unitObj X ⟶ (pullback f).obj ((pullback g).obj R)) :
    tensorSectionHom a b ≫
        (Functor.Monoidal.μIso (pullback f) ((pullback g).obj T) ((pullback g).obj R)).hom ≫
        (pullback f).map ((Functor.Monoidal.μIso (pullback g) T R).hom ≫
          (pullback g).map (ModularCurves.monoidalTensorObjIso T R).hom) ≫
        (pullbackComp f g).hom.app (Scheme.Modules.tensorObj T R) =
      pulledTensorSection (f ≫ g) (a ≫ (pullbackComp f g).hom.app T)
        (b ≫ (pullbackComp f g).hom.app R) := by
  have h3 : (pullback f).map ((pullback g).map (ModularCurves.monoidalTensorObjIso T R).hom) ≫
      (pullbackComp f g).hom.app (Scheme.Modules.tensorObj T R) =
      (pullbackComp f g).hom.app (T ⊗ R) ≫
        (pullback (f ≫ g)).map (ModularCurves.monoidalTensorObjIso T R).hom :=
    (pullbackComp f g).hom.naturality (ModularCurves.monoidalTensorObjIso T R).hom
  unfold pulledTensorSection
  rw [← tensorSectionHom_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [h3, reassoc_of% (tensorator_pullbackComp f g T R)]

/-- Pullback of an explicit tensor section. -/
theorem pullbackSectionHom_pulledTensorSection (f : X ⟶ Y) (g : Y ⟶ Z) {T R : Z.Modules}
    (a : unitObj Y ⟶ (pullback g).obj T) (b : unitObj Y ⟶ (pullback g).obj R) :
    pullbackSectionHom f (pulledTensorSection g a b) ≫
        (pullbackComp f g).hom.app (Scheme.Modules.tensorObj T R) =
      pulledTensorSection (f ≫ g) (pullbackSectionHom f a ≫ (pullbackComp f g).hom.app T)
        (pullbackSectionHom f b ≫ (pullbackComp f g).hom.app R) := by
  have h1 := SchemeTensorSectionHoms.pullback_tensorSectionHom f a b
  have h1' : pullbackSectionHom f (tensorSectionHom a b) =
      tensorSectionHom (pullbackSectionHom f a) (pullbackSectionHom f b) ≫
        (Functor.Monoidal.μIso (pullback f) ((pullback g).obj T) ((pullback g).obj R)).hom := by
    rw [← h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← pulledTensorSection_comp_hom f g (pullbackSectionHom f a) (pullbackSectionHom f b)]
  unfold pulledTensorSection
  rw [← pullbackSectionHom_map, h1']
  simp only [Category.assoc]

/-- Explicit tensor sections along equal morphisms agree through `pullbackCongr`. -/
theorem pulledTensorSection_congr {f f' : X ⟶ Y} (h : f = f') {T R : Y.Modules}
    (a : unitObj X ⟶ (pullback f).obj T) (b : unitObj X ⟶ (pullback f).obj R) :
    pulledTensorSection f a b ≫ (pullbackCongr h).hom.app (Scheme.Modules.tensorObj T R) =
      pulledTensorSection f' (a ≫ (pullbackCongr h).hom.app T)
        (b ≫ (pullbackCongr h).hom.app R) := by
  subst h
  simp only [pullbackCongr_rfl_hom_app, Category.comp_id]

/-- The explicit tensor section in the image of a tensor-form comparison along a base
change `h`, when the comparison has the tensor law `hα`. -/
theorem pulledTensorSection_pullbackIsoAlong {W : Scheme.{u}} (f g : Y ⟶ Z) (h : W ⟶ Y)
    {T R : Z.Modules}
    (α : (pullback f).obj (Scheme.Modules.tensorObj T R) ≅
      (pullback g).obj (Scheme.Modules.tensorObj T R))
    (αT : (pullback f).obj T ≅ (pullback g).obj T) (αR : (pullback f).obj R ≅ (pullback g).obj R)
    (hα : (Functor.Monoidal.μIso (pullback f) T R).hom ≫
        (pullback f).map (ModularCurves.monoidalTensorObjIso T R).hom ≫ α.hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback g) T R).hom ≫
        (pullback g).map (ModularCurves.monoidalTensorObjIso T R).hom)
    (a : unitObj W ⟶ (pullback (h ≫ f)).obj T) (b : unitObj W ⟶ (pullback (h ≫ f)).obj R) :
    pulledTensorSection (h ≫ f) a b ≫ (pullbackIsoAlong f g α h).hom =
      pulledTensorSection (h ≫ g) (a ≫ (pullbackIsoAlong f g αT h).hom)
        (b ≫ (pullbackIsoAlong f g αR h).hom) := by
  let a' := a ≫ (pullbackComp h f).inv.app T
  let b' := b ≫ (pullbackComp h f).inv.app R
  have ha : a' ≫ (pullbackComp h f).hom.app T = a := by
    simp only [a', Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hb : b' ≫ (pullbackComp h f).hom.app R = b := by
    simp only [b', Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hα' := congrArg (fun q => (pullback h).map q) hα
  simp only [CategoryTheory.Functor.map_comp] at hα'
  have hn : (Functor.Monoidal.μIso (pullback h) ((pullback f).obj T) ((pullback f).obj R)).hom ≫
      (pullback h).map (αT.hom ⊗ₘ αR.hom) =
      ((pullback h).map αT.hom ⊗ₘ (pullback h).map αR.hom) ≫
        (Functor.Monoidal.μIso (pullback h) ((pullback g).obj T) ((pullback g).obj R)).hom :=
    (Functor.LaxMonoidal.μ_natural (pullback h) αT.hom αR.hom).symm
  have hlhs := pulledTensorSection_comp_hom h f a' b'
  rw [ha, hb] at hlhs
  have hrhs := pulledTensorSection_comp_hom h g (a' ≫ (pullback h).map αT.hom)
    (b' ≫ (pullback h).map αR.hom)
  have hT : (a' ≫ (pullback h).map αT.hom) ≫ (pullbackComp h g).hom.app T =
      a ≫ (pullbackIsoAlong f g αT h).hom := by
    simp only [a', pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Category.assoc]
  have hR : (b' ≫ (pullback h).map αR.hom) ≫ (pullbackComp h g).hom.app R =
      b ≫ (pullbackIsoAlong f g αR h).hom := by
    simp only [b', pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Category.assoc]
  rw [hT, hR] at hrhs
  rw [← hlhs, ← hrhs, ← tensorSectionHom_comp]
  simp only [pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_comp]
  rw [reassoc_of% hα', reassoc_of% hn, ← tensorSectionHom_comp, ← tensorSectionHom_comp]
  simp only [Category.assoc]

/-- The canonical ratio section as an explicit tensor section. -/
theorem canonicalPulledRatioSection_eq_pulledTensorSection (I J : Y.IdealSheafData)
    (hJ : J.IsInvertible) (f : X ⟶ Y) [IsIso (I.pullbackModuleInclusion f)] :
    canonicalPulledRatioSection I J hJ f = pulledTensorSection f
      (asIso (I.pullbackModuleInclusion f)).inv
      (pullbackSectionHom f
        (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion)) := by
  unfold canonicalPulledRatioSection pulledTensorSection
  simp only [Scheme.Modules.canonicalTensorPullbackIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- Canonical ratio sections along equal morphisms agree. -/
theorem canonicalPulledRatioSection_congr (I J : Y.IdealSheafData) (hJ : J.IsInvertible)
    {f f' : X ⟶ Y} (h : f = f') [IsIso (I.pullbackModuleInclusion f)]
    [IsIso (I.pullbackModuleInclusion f')] :
    canonicalPulledRatioSection I J hJ f ≫ (pullbackCongr h).hom.app (I.ratioModule J) =
      canonicalPulledRatioSection I J hJ f' := by
  subst h
  exact Category.comp_id _

/-- The inverse pulled numerator inclusion along a composite. -/
theorem pullbackSectionHom_inclusionInverse (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso (I.pullbackModuleInclusion g)] [IsIso (I.pullbackModuleInclusion (f ≫ g))] :
    pullbackSectionHom f (asIso (I.pullbackModuleInclusion g)).inv ≫
        (pullbackComp f g).hom.app I.toModules =
      (asIso (I.pullbackModuleInclusion (f ≫ g))).inv := by
  apply (cancel_mono (I.pullbackModuleInclusion (f ≫ g))).mp
  rw [Category.assoc, I.pullbackModuleInclusion_comp f g]
  simp only [asIso_inv, IsIso.inv_hom_id]
  rw [← Category.assoc, pullbackSectionHom_map, IsIso.inv_hom_id]
  simp only [pullbackSectionHom, CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id]

/-- The canonical ratio section is natural under pullback. -/
theorem pullbackSectionHom_canonicalPulledRatioSection (I J : Z.IdealSheafData)
    (hJ : J.IsInvertible) (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso (I.pullbackModuleInclusion g)]
    [IsIso (I.pullbackModuleInclusion (f ≫ g))] :
    pullbackSectionHom f (canonicalPulledRatioSection I J hJ g) ≫
        (pullbackComp f g).hom.app (I.ratioModule J) =
      canonicalPulledRatioSection I J hJ (f ≫ g) := by
  rw [canonicalPulledRatioSection_eq_pulledTensorSection I J hJ g,
    canonicalPulledRatioSection_eq_pulledTensorSection I J hJ (f ≫ g)]
  refine (pullbackSectionHom_pulledTensorSection f g _ _).trans ?_
  rw [pullbackSectionHom_inclusionInverse I f g,
    SchemeLineSectionEvaluation.pullbackSectionHom_comp f g]

/-- A twisted canonical ratio section, pulled back along `f`, then transported by the
composition comparison, is the twisted canonical ratio section along the composite. -/
theorem pullbackSectionHom_twistedCanonicalSection (I J : Z.IdealSheafData) (hJ : J.IsInvertible)
    (f : X ⟶ Y) (g : Y ⟶ Z) {N : Z.Modules} (τ : unitObj Z ⟶ N)
    [IsIso (I.pullbackModuleInclusion g)] [IsIso (I.pullbackModuleInclusion (f ≫ g))] :
    pullbackSectionHom f (pulledTensorSection g (pullbackSectionHom g τ)
        (canonicalPulledRatioSection I J hJ g)) ≫
        (pullbackComp f g).hom.app (Scheme.Modules.tensorObj N (I.ratioModule J)) =
      pulledTensorSection (f ≫ g) (pullbackSectionHom (f ≫ g) τ)
        (canonicalPulledRatioSection I J hJ (f ≫ g)) := by
  rw [pullbackSectionHom_pulledTensorSection, SchemeLineSectionEvaluation.pullbackSectionHom_comp,
    pullbackSectionHom_canonicalPulledRatioSection]

/-- The inverse form of `pullbackSectionHom_twistedCanonicalSection`. -/
theorem twistedCanonicalSection_comp_inv (I J : Z.IdealSheafData) (hJ : J.IsInvertible)
    (f : X ⟶ Y) (g : Y ⟶ Z) {N : Z.Modules} (τ : unitObj Z ⟶ N)
    [IsIso (I.pullbackModuleInclusion g)] [IsIso (I.pullbackModuleInclusion (f ≫ g))] :
    pulledTensorSection (f ≫ g) (pullbackSectionHom (f ≫ g) τ)
        (canonicalPulledRatioSection I J hJ (f ≫ g)) ≫
        (pullbackComp f g).inv.app (Scheme.Modules.tensorObj N (I.ratioModule J)) =
      pullbackSectionHom f (pulledTensorSection g (pullbackSectionHom g τ)
        (canonicalPulledRatioSection I J hJ g)) := by
  rw [← pullbackSectionHom_twistedCanonicalSection I J hJ f g τ, Category.assoc,
    Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- A twisted canonical ratio section along equal morphisms. -/
theorem twistedCanonicalSection_congr (I J : Y.IdealSheafData) (hJ : J.IsInvertible)
    {f f' : X ⟶ Y} (h : f = f') {N : Y.Modules} (τ : unitObj Y ⟶ N)
    [IsIso (I.pullbackModuleInclusion f)] [IsIso (I.pullbackModuleInclusion f')] :
    pulledTensorSection f (pullbackSectionHom f τ) (canonicalPulledRatioSection I J hJ f) ≫
        (pullbackCongr h).hom.app (Scheme.Modules.tensorObj N (I.ratioModule J)) =
      pulledTensorSection f' (pullbackSectionHom f' τ) (canonicalPulledRatioSection I J hJ f') := by
  subst h
  exact Category.comp_id _

/-- A section pulled back along `f` is fixed by a comparison along a base change `h` when the
comparison fixes the pulled section. -/
theorem pullbackSectionHom_pullbackIsoAlong {W : Scheme.{u}} (f g : Y ⟶ Z) (h : W ⟶ Y)
    {N : Z.Modules} (β : (pullback f).obj N ≅ (pullback g).obj N) (τ : unitObj Z ⟶ N)
    (hβ : pullbackSectionHom f τ ≫ β.hom = pullbackSectionHom g τ) :
    pullbackSectionHom (h ≫ f) τ ≫ (pullbackIsoAlong f g β h).hom =
      pullbackSectionHom (h ≫ g) τ := by
  simp only [pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom]
  rw [← Category.assoc, pullbackSectionHom_comp_inv, ← Category.assoc, pullbackSectionHom_map, hβ,
    SchemeLineSectionEvaluation.pullbackSectionHom_comp]

/-- The value at `1` of an explicit tensor section is the generic tensor section. -/
theorem sectionAtOne_pulledTensorSection {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {S : Scheme.{u}} {fS : S ⟶ Spec (CommRingCat.of R)} [IsProper fS]
    (y : Berkovich.RelativeSchemeValuedPoint v fS) {T Q : S.Modules}
    (a : unitObj _ ⟶ (pullback (S.fromSpecResidueField y.1.point)).obj T)
    (b : unitObj _ ⟶ (pullback (S.fromSpecResidueField y.1.point)).obj Q) :
    sectionAtOne (pulledTensorSection (S.fromSpecResidueField y.1.point) a b) =
      Berkovich.RelativeSchemeValuedPoint.genericTensorSection y (sectionAtOne a)
        (sectionAtOne b) := by
  unfold pulledTensorSection Berkovich.RelativeSchemeValuedPoint.genericTensorSection
  rw [← sectionAtOne_tensorSectionHom]
  rfl

/-! ### Structural laws of the tensor-form comparisons -/

/-- The tensor law of a comparison of explicit tensor products built factorwise through the
canonical tensor-pullback isomorphisms. -/
theorem canonicalTensorPullbackIso_comparison_tensor_law (f g : Y ⟶ Z) (T R : Z.Modules)
    (αT : (pullback f).obj T ≅ (pullback g).obj T) (αR : (pullback f).obj R ≅ (pullback g).obj R) :
    (Functor.Monoidal.μIso (pullback f) T R).hom ≫
        (pullback f).map (ModularCurves.monoidalTensorObjIso T R).hom ≫
        (Scheme.Modules.canonicalTensorPullbackIso f T R ≪≫ tensorObjCongr αT αR ≪≫
          (Scheme.Modules.canonicalTensorPullbackIso g T R).symm).hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback g) T R).hom ≫
        (pullback g).map (ModularCurves.monoidalTensorObjIso T R).hom := by
  have hn := ModularCurves.cartierMonoidalTensorObjIso_hom_natural αT αR
  simp only [Scheme.Modules.canonicalTensorPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_assoc, reassoc_of% hn, Iso.hom_inv_id_assoc]

/-- The comparison of a pullback along an invariant projection fixes pulled sections. -/
theorem invariantComparison_pullbackSectionHom {P N : Scheme.{u}} (a p : P ⟶ N) (q : N ⟶ Z)
    (h : a ≫ q = p ≫ q) (L : Z.Modules) (s : unitObj Z ⟶ L) :
    pullbackSectionHom a (pullbackSectionHom q s) ≫
        ((pullbackComp a q).app L ≪≫ (pullbackCongr h).app L ≪≫
          ((pullbackComp p q).app L).symm).hom =
      pullbackSectionHom p (pullbackSectionHom q s) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, SchemeLineSectionEvaluation.pullbackSectionHom_comp, ← Category.assoc,
    pullbackSectionHom_congr, pullbackSectionHom_comp_inv]

/-- An explicit tensor section followed by a trivialisation of its second factor. -/
theorem pulledTensorSection_unitTrivialization (f : Y ⟶ Z) {T R : Z.Modules}
    (e : (pullback f).obj R ≅ unitObj Y) (a : unitObj Y ⟶ (pullback f).obj T)
    (b : unitObj Y ⟶ (pullback f).obj R) {Q : Y.Modules} (h : (pullback f).obj T ⟶ Q) :
    pulledTensorSection f a b ≫ (Scheme.Modules.canonicalTensorPullbackIso f T R).hom ≫
        (tensorObjCongr (Iso.refl _) e).hom ≫ (tensorObjUnitIso _).hom ≫ h =
      (b ≫ e.hom) ≫ a ≫ h := by
  have hu := SchemeTensorObjMorphisms.tensorObjUnitIso_monoidal ((pullback f).obj T)
  have hn := ModularCurves.cartierMonoidalTensorObjIso_hom_natural
    (Iso.refl ((pullback f).obj T)) e
  have hr := tensorSectionHom_rightUnit a (b ≫ e.hom)
  unfold pulledTensorSection
  simp only [Scheme.Modules.canonicalTensorPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_assoc, reassoc_of% hn, reassoc_of% hu, Iso.refl_hom,
    ← Category.assoc, tensorSectionHom_comp, Category.comp_id, reassoc_of% hr]

/-- The residue pullback of the fibre of a twisted canonical ratio section is the fibre of
the pulled twisted canonical ratio section. -/
theorem pullbackResidueSection_twistedCanonical (g : Y ⟶ Z) (y : Y) (I J : Z.IdealSheafData)
    (hJ : J.IsInvertible) {N : Z.Modules} (τ : unitObj Z ⟶ N)
    [IsIso (I.pullbackModuleInclusion (Z.fromSpecResidueField (g y)))]
    [IsIso (I.pullbackModuleInclusion
      (Spec.map (g.residueFieldMap y) ≫ Z.fromSpecResidueField (g y)))]
    [IsIso (I.pullbackModuleInclusion (Y.fromSpecResidueField y ≫ g))]
    [IsIso (I.pullbackModuleInclusion g)] :
    Berkovich.SchemeValuedPoint.pullbackResidueSection g y
        (sectionAtOne (pulledTensorSection (Z.fromSpecResidueField (g y))
          (pullbackSectionHom (Z.fromSpecResidueField (g y)) τ)
          (canonicalPulledRatioSection I J hJ (Z.fromSpecResidueField (g y))))) =
      sectionAtOne (pullbackSectionHom (Y.fromSpecResidueField y)
        (pulledTensorSection g (pullbackSectionHom g τ)
          (canonicalPulledRatioSection I J hJ g))) := by
  unfold Berkovich.SchemeValuedPoint.pullbackResidueSection
    Berkovich.SchemeValuedPoint.pullbackResidueSectionHom
    Berkovich.SchemeValuedPoint.residueModulePullbackIso Scheme.Modules.frameFactorIso
  rw [topSectionHom_sectionAtOne]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Category.assoc, pullbackSectionHom_twistedCanonicalSection I J hJ, ← Category.assoc,
    twistedCanonicalSection_congr I J hJ (g.SpecMap_residueFieldMap_fromSpecResidueField y),
    twistedCanonicalSection_comp_inv I J hJ]

/-- The transported residue section of the fibre of a twisted canonical ratio section is the
fibre of the transported pulled section. -/
theorem transportedResidueSection_twistedCanonical (g : Y ⟶ Z) (I J : Z.IdealSheafData)
    (hJ : J.IsInvertible) {N : Z.Modules} {P : Y.Modules} (τ : unitObj Z ⟶ N)
    (Φ : (pullback g).obj (Scheme.Modules.tensorObj N (I.ratioModule J)) ≅ P)
    (y : Berkovich.SchemeValuedPoint Y)
    [IsIso (I.pullbackModuleInclusion (Z.fromSpecResidueField (g y.point)))]
    [IsIso (I.pullbackModuleInclusion
      (Spec.map (g.residueFieldMap y.point) ≫ Z.fromSpecResidueField (g y.point)))]
    [IsIso (I.pullbackModuleInclusion (Y.fromSpecResidueField y.point ≫ g))]
    [IsIso (I.pullbackModuleInclusion g)] :
    Berkovich.SchemeFramedSectionPullback.transportedResidueSection g Φ y
        (sectionAtOne (pulledTensorSection (Z.fromSpecResidueField (g y.point))
          (pullbackSectionHom (Z.fromSpecResidueField (g y.point)) τ)
          (canonicalPulledRatioSection I J hJ (Z.fromSpecResidueField (g y.point))))) =
      sectionAtOne (pullbackSectionHom (Y.fromSpecResidueField y.point)
        (pulledTensorSection g (pullbackSectionHom g τ) (canonicalPulledRatioSection I J hJ g) ≫
          Φ.hom)) := by
  unfold Berkovich.SchemeFramedSectionPullback.transportedResidueSection
  rw [pullbackResidueSection_twistedCanonical g y.point I J hJ τ, ← pullbackSectionHom_map]
  try rfl

/-- A morphism pushed through a seven-fold composite of isomorphisms, one factor at a time;
the factors are given by arbitrary presentations `mᵢ` of their underlying morphisms. -/
theorem comp_trans_seven_hom {𝒞 : Type*} [Category 𝒞] {V A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : 𝒞}
    (d₀ : A₀ ≅ A₁) (d₁ : A₁ ≅ A₂) (d₂ : A₂ ≅ A₃) (d₃ : A₃ ≅ A₄) (d₄ : A₄ ≅ A₅) (d₅ : A₅ ≅ A₆)
    (d₆ : A₆ ≅ A₇) (m₀ : A₀ ⟶ A₁) (m₁ : A₁ ⟶ A₂) (m₂ : A₂ ⟶ A₃) (m₃ : A₃ ⟶ A₄)
    (m₄ : A₄ ⟶ A₅) (m₅ : A₅ ⟶ A₆) (m₆ : A₆ ⟶ A₇)
    (e₀ : d₀.hom = m₀) (e₁ : d₁.hom = m₁) (e₂ : d₂.hom = m₂) (e₃ : d₃.hom = m₃)
    (e₄ : d₄.hom = m₄) (e₅ : d₅.hom = m₅) (e₆ : d₆.hom = m₆)
    (y₀ : V ⟶ A₀) (y₁ : V ⟶ A₁) (y₂ : V ⟶ A₂) (y₃ : V ⟶ A₃) (y₄ : V ⟶ A₄)
    (y₅ : V ⟶ A₅) (y₆ : V ⟶ A₆) (y₇ : V ⟶ A₇)
    (h₀ : y₀ ≫ m₀ = y₁) (h₁ : y₁ ≫ m₁ = y₂) (h₂ : y₂ ≫ m₂ = y₃)
    (h₃ : y₃ ≫ m₃ = y₄) (h₄ : y₄ ≫ m₄ = y₅) (h₅ : y₅ ≫ m₅ = y₆)
    (h₆ : y₆ ≫ m₆ = y₇) :
    y₀ ≫ (d₀ ≪≫ d₁ ≪≫ d₂ ≪≫ d₃ ≪≫ d₄ ≪≫ d₅ ≪≫ d₆).hom = y₇ := by
  subst e₀ e₁ e₂ e₃ e₄ e₅ e₆ h₀ h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Iso.trans_hom, Category.assoc]

end EnvelopeProperty.PLOriginalModelCompatibility.TwistedRatioCalculus

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (C : TestConfiguration k X)

/-- The whole noncentral-open line comparison as an explicit composite of isomorphisms, with
the action step written as the base-change comparison `pullbackIsoAlong`. -/
theorem unitOpenLineIso_eq_explicit (M : C.total.Modules) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L) :
    C.unitOpenLineIso M L α e₁ =
      (pullbackCongr C.lineActionLift_action.symm).app M ≪≫
        pullbackIsoAlong C.lineActionMap C.lineProjectionMap α C.unitOpenActionLift.left ≪≫
        (pullbackCongr C.lineActionLift_projection).app M ≪≫
        ((pullbackComp C.unitOpenFibreProjection.left C.fibreOneInclusion.left).app M).symm ≪≫
        (pullback C.unitOpenFibreProjection.left).mapIso e₁ ≪≫
        (pullbackComp C.unitOpenFibreProjection.left C.fibreOneIso.hom.left).app L ≪≫
        (pullbackCongr C.lineActionLift_original).app L := by
  unfold unitOpenLineIso
  congr 2

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open PLOriginalModelCompatibility.TwistedRatioCalculus
open PLOriginalModelCompatibility.RatioSectionTransport
open SchemeLineSectionEvaluation SchemeTensorSectionHoms
open Berkovich Berkovich.RelativeSchemeValuedPoint Berkovich.SchemeFramedSectionPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance twistedRatioModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance twistedRatioPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (C : TestConfiguration k X)
private local instance twistedRatioProjectionProper : IsProper C.projection := C.projection_isProper

/-- Every map factoring through the noncentral open pulls an ideal missing that open back
to an invertible inclusion. -/
theorem twistedRatio_inclusion_isIso (I : C.total.IdealSheafData)
    (hIU : C.unitOpen ≤ I.support.compl) {Y : Scheme.{u}} (q : Y ⟶ C.unitOpen.toScheme)
    (f : Y ⟶ C.total) (hq : q ≫ C.unitOpen.ι = f) : IsIso (I.pullbackModuleInclusion f) :=
  offSupportFactorInclusion_isIso I C.unitOpen hIU q f hq

section TwistedRatio

variable (π : C.total ⟶ X.left) (L : X.left.Modules) (K J : C.total.IdealSheafData)
  (hJ : J.IsInvertible)

/-- The section law of an action comparison of `π^*L` which is the comparison of an
invariant projection `π` (`act ≫ π = prj ≫ π`). -/
theorem twistedRatio_twistLaw_of_iso
    (hinv : C.lineActionMap ≫ π = C.lineProjectionMap ≫ π)
    (αT : (pullback C.lineActionMap).obj ((pullback π).obj L) ≅
      (pullback C.lineProjectionMap).obj ((pullback π).obj L))
    (hαT : αT = (pullbackComp C.lineActionMap π).app L ≪≫ (pullbackCongr hinv).app L ≪≫
      ((pullbackComp C.lineProjectionMap π).app L).symm)
    (s : unitObj X.left ⟶ L) :
    pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫ αT.hom =
      pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s) := by
  subst hαT
  exact invariantComparison_pullbackSectionHom _ _ _ hinv L s

/-- The section law of a fibre-one comparison of `π^*L ⊗ K ⊗ J^∨` which is the tensor of the
canonical identification of `π^*L` on fibre one and a trivialisation `eR` of the ratio. -/
theorem twistedRatio_fibreOneLaw_of_iso
    (hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left)
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    (e₁ : (pullback C.fibreOneInclusion.left).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (he₁ : e₁ = (Scheme.Modules.canonicalTensorPullbackIso C.fibreOneInclusion.left
        ((pullback π).obj L) (K.ratioModule J) ≪≫ tensorObjCongr (Iso.refl _) eR ≪≫
        tensorObjUnitIso _ ≪≫ (pullbackComp C.fibreOneInclusion.left π).app L) ≪≫
      (pullbackCongr hπ₁).app L)
    (a : unitObj (fibreOneOver k C.projection).left ⟶
      (pullback C.fibreOneInclusion.left).obj ((pullback π).obj L))
    (b : unitObj (fibreOneOver k C.projection).left ⟶
      (pullback C.fibreOneInclusion.left).obj (K.ratioModule J)) :
    pulledTensorSection C.fibreOneInclusion.left a b ≫ e₁.hom =
      (b ≫ eR.hom) ≫ a ≫ (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫
        (pullbackCongr hπ₁).hom.app L := by
  subst he₁
  have h := pulledTensorSection_unitTrivialization C.fibreOneInclusion.left eR a b
    ((pullbackComp C.fibreOneInclusion.left π).hom.app L ≫ (pullbackCongr hπ₁).hom.app L)
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc] at h ⊢
  exact h

/-- Transport of the twisted canonical section through the map congruence `v = ℓ ≫ act`. -/
theorem twistedRatio_section_step0
    [IsIso (K.pullbackModuleInclusion C.unitOpenInclusion.left)]
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
    (s : unitObj X.left ⟶ L) :
    pulledTensorSection C.unitOpenInclusion.left
      (pullbackSectionHom C.unitOpenInclusion.left (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ C.unitOpenInclusion.left) ≫
      (pullbackCongr C.lineActionLift_action.symm).hom.app
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) =
    pulledTensorSection (C.unitOpenActionLift.left ≫ C.lineActionMap)
      (pullbackSectionHom (C.unitOpenActionLift.left ≫ C.lineActionMap) (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap)) :=
  twistedCanonicalSection_congr K J hJ C.lineActionLift_action.symm (pullbackSectionHom π s)

/-- Transport of the twisted canonical section through the pulled action comparison along `ℓ`. -/
theorem twistedRatio_section_step1
    (α : (pullback C.lineActionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.lineProjectionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (αT : (pullback C.lineActionMap).obj ((pullback π).obj L) ≅
      (pullback C.lineProjectionMap).obj ((pullback π).obj L))
    (αR : (pullback C.lineActionMap).obj (K.ratioModule J) ≅
      (pullback C.lineProjectionMap).obj (K.ratioModule J))
    (hα : (Functor.Monoidal.μIso (pullback C.lineActionMap) ((pullback π).obj L)
          (K.ratioModule J)).hom ≫
        (pullback C.lineActionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom ≫
        α.hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback C.lineProjectionMap)
          ((pullback π).obj L) (K.ratioModule J)).hom ≫
        (pullback C.lineProjectionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom)
    (hαT : ∀ s : unitObj X.left ⟶ L,
      pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫ αT.hom =
        pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s))
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))]
    (hαR : canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap) ≫
        (pullbackIsoAlong C.lineActionMap C.lineProjectionMap αR C.unitOpenActionLift.left).hom =
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap))
    (s : unitObj X.left ⟶ L) :
    pulledTensorSection (C.unitOpenActionLift.left ≫ C.lineActionMap)
      (pullbackSectionHom (C.unitOpenActionLift.left ≫ C.lineActionMap) (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap)) ≫
      (pullbackIsoAlong C.lineActionMap C.lineProjectionMap α C.unitOpenActionLift.left).hom =
    pulledTensorSection (C.unitOpenActionLift.left ≫ C.lineProjectionMap)
      (pullbackSectionHom (C.unitOpenActionLift.left ≫ C.lineProjectionMap)
        (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap)) := by
  rw [pulledTensorSection_pullbackIsoAlong _ _ _ α αT αR hα,
    pullbackSectionHom_pullbackIsoAlong _ _ _ αT _ (hαT s), hαR]

/-- Transport of the twisted canonical section through the map congruence `ℓ ≫ prj = ζ ≫ ι₁`. -/
theorem twistedRatio_section_step2
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))]
    [IsIso (K.pullbackModuleInclusion (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left))]
    (s : unitObj X.left ⟶ L) :
    pulledTensorSection (C.unitOpenActionLift.left ≫ C.lineProjectionMap)
      (pullbackSectionHom (C.unitOpenActionLift.left ≫ C.lineProjectionMap)
        (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap)) ≫
      (pullbackCongr C.lineActionLift_projection).hom.app
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) =
    pulledTensorSection (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left)
      (pullbackSectionHom (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left)
        (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ
        (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left)) :=
  twistedCanonicalSection_congr K J hJ C.lineActionLift_projection (pullbackSectionHom π s)

/-- Transport of the twisted canonical section through the inverse composition comparison along
`ζ ≫ ι₁`. -/
theorem twistedRatio_section_step3
    [IsIso (K.pullbackModuleInclusion (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left))]
    [IsIso (K.pullbackModuleInclusion C.fibreOneInclusion.left)]
    (s : unitObj X.left ⟶ L) :
    pulledTensorSection (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left)
      (pullbackSectionHom (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left)
        (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ
        (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left)) ≫
      (pullbackComp C.unitOpenFibreProjection.left C.fibreOneInclusion.left).inv.app
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) =
    pullbackSectionHom C.unitOpenFibreProjection.left
      (pulledTensorSection C.fibreOneInclusion.left
        (pullbackSectionHom C.fibreOneInclusion.left (pullbackSectionHom π s))
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left)) :=
  twistedCanonicalSection_comp_inv K J hJ C.unitOpenFibreProjection.left C.fibreOneInclusion.left
    (pullbackSectionHom π s)

/-- Transport of the twisted canonical section through the pulled fibre-one identification. -/
theorem twistedRatio_section_step4
    (hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left)
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    (e₁ : (pullback C.fibreOneInclusion.left).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (he₁ : ∀ (a : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj ((pullback π).obj L))
      (b : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj (K.ratioModule J)),
      pulledTensorSection C.fibreOneInclusion.left a b ≫ e₁.hom =
        (b ≫ eR.hom) ≫ a ≫ (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫
          (pullbackCongr hπ₁).hom.app L)
    [IsIso (K.pullbackModuleInclusion C.fibreOneInclusion.left)]
    (s : unitObj X.left ⟶ L) :
    pullbackSectionHom C.unitOpenFibreProjection.left
      (pulledTensorSection C.fibreOneInclusion.left
        (pullbackSectionHom C.fibreOneInclusion.left (pullbackSectionHom π s))
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left)) ≫
      (pullback C.unitOpenFibreProjection.left).map e₁.hom =
    (pullbackSectionHom C.unitOpenFibreProjection.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
        (pullbackUnitIso C.unitOpenFibreProjection.left).hom) ≫
      pullbackSectionHom C.unitOpenFibreProjection.left
        (pullbackSectionHom C.fibreOneIso.hom.left s) := by
  have hinner : pullbackSectionHom C.fibreOneInclusion.left (pullbackSectionHom π s) ≫
      (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫ (pullbackCongr hπ₁).hom.app L =
      pullbackSectionHom C.fibreOneIso.hom.left s := by
    rw [← Category.assoc, SchemeLineSectionEvaluation.pullbackSectionHom_comp,
      pullbackSectionHom_congr]
  rw [pullbackSectionHom_map, he₁, hinner, pullbackSectionHom_scalar]

/-- Transport of the twisted canonical section through the composition comparison along `ζ ≫ φ₁`. -/
theorem twistedRatio_section_step5
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    [IsIso (K.pullbackModuleInclusion C.fibreOneInclusion.left)]
    (s : unitObj X.left ⟶ L) :
    ((pullbackSectionHom C.unitOpenFibreProjection.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
        (pullbackUnitIso C.unitOpenFibreProjection.left).hom) ≫
      pullbackSectionHom C.unitOpenFibreProjection.left
        (pullbackSectionHom C.fibreOneIso.hom.left s)) ≫
      (pullbackComp C.unitOpenFibreProjection.left C.fibreOneIso.hom.left).hom.app L =
    (pullbackSectionHom C.unitOpenFibreProjection.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
        (pullbackUnitIso C.unitOpenFibreProjection.left).hom) ≫
      pullbackSectionHom (C.unitOpenFibreProjection.left ≫ C.fibreOneIso.hom.left) s := by
  rw [Category.assoc, SchemeLineSectionEvaluation.pullbackSectionHom_comp]

/-- Transport of the twisted canonical section through the map congruence `ζ ≫ φ₁ = w`. -/
theorem twistedRatio_section_step6
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    [IsIso (K.pullbackModuleInclusion C.fibreOneInclusion.left)]
    (s : unitObj X.left ⟶ L) :
    ((pullbackSectionHom C.unitOpenFibreProjection.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
        (pullbackUnitIso C.unitOpenFibreProjection.left).hom) ≫
      pullbackSectionHom (C.unitOpenFibreProjection.left ≫ C.fibreOneIso.hom.left) s) ≫
      (pullbackCongr C.lineActionLift_original).hom.app L =
    (pullbackSectionHom C.unitOpenFibreProjection.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
        (pullbackUnitIso C.unitOpenFibreProjection.left).hom) ≫
      pullbackSectionHom C.unitOpenOriginalProjection.left s := by
  rw [Category.assoc, pullbackSectionHom_congr]

/-- **Transport of the twisted canonical section on the noncentral open.**  Along the
whole noncentral-open line comparison, the twisted canonical ratio section `π^*s ⊗ σ`
becomes `ε · w^*s`, where `ε` is the pulled fibre-one value of the canonical ratio
section in the fibre-one trivialisation `eR`. -/
theorem twistedRatio_unitOpenLineIso_section
    (hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left)
    (α : (pullback C.lineActionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.lineProjectionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (αT : (pullback C.lineActionMap).obj ((pullback π).obj L) ≅
      (pullback C.lineProjectionMap).obj ((pullback π).obj L))
    (αR : (pullback C.lineActionMap).obj (K.ratioModule J) ≅
      (pullback C.lineProjectionMap).obj (K.ratioModule J))
    (hα : (Functor.Monoidal.μIso (pullback C.lineActionMap) ((pullback π).obj L)
          (K.ratioModule J)).hom ≫
        (pullback C.lineActionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom ≫
        α.hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback C.lineProjectionMap)
          ((pullback π).obj L) (K.ratioModule J)).hom ≫
        (pullback C.lineProjectionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom)
    (hαT : ∀ s : unitObj X.left ⟶ L,
      pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫ αT.hom =
        pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s))
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    (e₁ : (pullback C.fibreOneInclusion.left).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (he₁ : ∀ (a : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj ((pullback π).obj L))
      (b : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj (K.ratioModule J)),
      pulledTensorSection C.fibreOneInclusion.left a b ≫ e₁.hom =
        (b ≫ eR.hom) ≫ a ≫ (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫
          (pullbackCongr hπ₁).hom.app L)
    [IsIso (K.pullbackModuleInclusion C.unitOpenInclusion.left)]
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))]
    [IsIso (K.pullbackModuleInclusion
      (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left))]
    [IsIso (K.pullbackModuleInclusion C.fibreOneInclusion.left)]
    (hαR : canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap) ≫
        (pullbackIsoAlong C.lineActionMap C.lineProjectionMap αR C.unitOpenActionLift.left).hom =
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap))
    (s : unitObj X.left ⟶ L) :
    pulledTensorSection C.unitOpenInclusion.left
        (pullbackSectionHom C.unitOpenInclusion.left (pullbackSectionHom π s))
        (canonicalPulledRatioSection K J hJ C.unitOpenInclusion.left) ≫
        (C.unitOpenLineIso (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) L α
          e₁).hom =
      (pullbackSectionHom C.unitOpenFibreProjection.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.unitOpenFibreProjection.left).hom) ≫
        pullbackSectionHom C.unitOpenOriginalProjection.left s := by
  rw [unitOpenLineIso_eq_explicit]
  exact comp_trans_seven_hom _ _ _ _ _ _ _
    ((pullbackCongr C.lineActionLift_action.symm).hom.app
      (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (pullbackIsoAlong C.lineActionMap C.lineProjectionMap α C.unitOpenActionLift.left).hom
    ((pullbackCongr C.lineActionLift_projection).hom.app
      (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    ((pullbackComp C.unitOpenFibreProjection.left C.fibreOneInclusion.left).inv.app
      (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    ((pullback C.unitOpenFibreProjection.left).map e₁.hom)
    ((pullbackComp C.unitOpenFibreProjection.left C.fibreOneIso.hom.left).hom.app L)
    ((pullbackCongr C.lineActionLift_original).hom.app L)
    (Iso.app_hom _ _) rfl (Iso.app_hom _ _) ((Iso.symm_hom _).trans (Iso.app_inv _ _))
    (Functor.mapIso_hom _ _) (Iso.app_hom _ _) (Iso.app_hom _ _) _ _ _ _ _ _ _ _
    (C.twistedRatio_section_step0 π L K J hJ s)
    (C.twistedRatio_section_step1 π L K J hJ α αT αR hα hαT hαR s)
    (C.twistedRatio_section_step2 π L K J hJ s)
    (C.twistedRatio_section_step3 π L K J hJ s)
    (C.twistedRatio_section_step4 π L K J hJ hπ₁ eR e₁ he₁ s)
    (C.twistedRatio_section_step5 L K J hJ eR s)
    (C.twistedRatio_section_step6 L K J hJ eR s)

/-- **Transport of the twisted canonical section to `X × 𝔾ₘ`.**  The section of
`productTotalMap^* M` obtained from `π^*s ⊗ σ` on the noncentral open is sent by the
whole product line comparison to `pr₁^*(ε_X · s)`, with `ε_X` the fibre-one value of the
canonical ratio section transported to `X`. -/
theorem twistedRatio_productTotalLineIso_section
    (hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left)
    (α : (pullback C.lineActionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.lineProjectionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (αT : (pullback C.lineActionMap).obj ((pullback π).obj L) ≅
      (pullback C.lineProjectionMap).obj ((pullback π).obj L))
    (αR : (pullback C.lineActionMap).obj (K.ratioModule J) ≅
      (pullback C.lineProjectionMap).obj (K.ratioModule J))
    (hα : (Functor.Monoidal.μIso (pullback C.lineActionMap) ((pullback π).obj L)
          (K.ratioModule J)).hom ≫
        (pullback C.lineActionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom ≫
        α.hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback C.lineProjectionMap)
          ((pullback π).obj L) (K.ratioModule J)).hom ≫
        (pullback C.lineProjectionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom)
    (hαT : ∀ s : unitObj X.left ⟶ L,
      pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫ αT.hom =
        pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s))
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    (e₁ : (pullback C.fibreOneInclusion.left).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (he₁ : ∀ (a : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj ((pullback π).obj L))
      (b : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj (K.ratioModule J)),
      pulledTensorSection C.fibreOneInclusion.left a b ≫ e₁.hom =
        (b ≫ eR.hom) ≫ a ≫ (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫
          (pullbackCongr hπ₁).hom.app L)
    [IsIso (K.pullbackModuleInclusion C.unitOpenInclusion.left)]
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
    [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))]
    [IsIso (K.pullbackModuleInclusion
      (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left))]
    [IsIso (K.pullbackModuleInclusion C.fibreOneInclusion.left)]
    (hαR : canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap) ≫
        (pullbackIsoAlong C.lineActionMap C.lineProjectionMap αR C.unitOpenActionLift.left).hom =
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap))
    (s : unitObj X.left ⟶ L) :
    (pullbackSectionHom C.unitOpenIso.inv.left
        (pulledTensorSection C.unitOpenInclusion.left
          (pullbackSectionHom C.unitOpenInclusion.left (pullbackSectionHom π s))
          (canonicalPulledRatioSection K J hJ C.unitOpenInclusion.left)) ≫
        (pullbackComp C.unitOpenIso.inv.left C.unitOpenInclusion.left).hom.app
          (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J))) ≫
        (C.productTotalLineIso (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) L α
          e₁).hom =
      pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        ((pullbackSectionHom C.fibreOneIso.inv.left
            (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s) := by
  have hφ : C.fibreOneIso.hom.left ≫ C.fibreOneIso.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hζ : C.unitOpenIso.inv.left ≫ C.unitOpenFibreProjection.left =
      (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ≫ C.fibreOneIso.inv.left := by
    calc C.unitOpenIso.inv.left ≫ C.unitOpenFibreProjection.left =
          C.unitOpenIso.inv.left ≫ C.unitOpenFibreProjection.left ≫
            C.fibreOneIso.hom.left ≫ C.fibreOneIso.inv.left := by
          rw [hφ, Category.comp_id]
      _ = (C.unitOpenIso.inv.left ≫ (C.unitOpenFibreProjection.left ≫
            C.fibreOneIso.hom.left)) ≫ C.fibreOneIso.inv.left := by
          simp only [Category.assoc]
      _ = _ := by rw [C.lineActionLift_original, C.unitOpenIso_inv_originalProjection]
  have hS := C.twistedRatio_unitOpenLineIso_section π L K J hJ hπ₁ α αT αR hα hαT eR e₁ he₁ hαR s
  unfold productTotalLineIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc (pullbackSectionHom C.unitOpenIso.inv.left _), pullbackSectionHom_map, hS,
    pullbackSectionHom_scalar]
  simp only [Category.assoc]
  rw [← Category.assoc (pullbackSectionHom C.unitOpenIso.inv.left
      (pullbackSectionHom C.unitOpenOriginalProjection.left s)),
    SchemeLineSectionEvaluation.pullbackSectionHom_comp, pullbackSectionHom_congr]
  rw [← Category.assoc (pullbackSectionHom C.fibreOneIso.inv.left _) _ s,
    pullbackSectionHom_scalar (fst X (ProjBerk.nativeMultiplicativeGroup k)).left]
  have hε : pullbackSectionHom C.unitOpenIso.inv.left
        (pullbackSectionHom C.unitOpenFibreProjection.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.unitOpenFibreProjection.left).hom) ≫
        (pullbackUnitIso C.unitOpenIso.inv.left).hom =
      pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        (pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫
        (pullbackUnitIso (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).hom := by
    rw [← pullbackSectionHom_unit_comp, pullbackSectionHom_unit_congr hζ,
      pullbackSectionHom_unit_comp]
  rw [← Category.assoc, hε]

/-- The residue map of the product Gauss point factors through the noncentral open. -/
theorem twistedRatio_productGauss_mem_unitOpen
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (r : ℝ≥0) (hr : 0 < r) :
    C.productTotalMap (C.productGaussSource x r hr).1.point ∈ C.unitOpen := by
  change C.unitOpen.ι (C.unitOpenIso.inv.left (C.productGaussSource x r hr).1.point) ∈ C.unitOpen
  exact (C.unitOpenIso.inv.left (C.productGaussSource x r hr).1.point).2

/-- The residue-field inclusion of the total Gauss point is invertible on a numerator
missing the noncentral open. -/
theorem twistedRatio_residue_inclusion_isIso (hKU : C.unitOpen ≤ K.support.compl)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) (r : ℝ≥0) (hr : 0 < r) :
    IsIso (K.pullbackModuleInclusion
      (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))) :=
  C.twistedRatio_inclusion_isIso K hKU _ _
    (SchemeSupportLineFrames.supportGenericFactor_comp _ C.unitOpen
      (C.twistedRatio_productGauss_mem_unitOpen x r hr))

/-- The pulled zero section is zero. -/
theorem twistedRatio_affinePullbackUnitTop_zero {Y Z : Scheme.{u}} (g : Y ⟶ Z) (N : Z.Modules) :
    Scheme.Modules.affinePullbackUnitTop g N 0 = 0 := by
  simp [Scheme.Modules.affinePullbackUnitTop]
  exact map_zero _

/-- The original projection of the total Gauss point over `x` is `x`. -/
theorem twistedRatio_mapOverBase_productGauss
    (hπw : C.unitOpenOriginalProjection.left = C.unitOpenInclusion.left ≫ π)
    (hπbase : π ≫ X.hom =
      C.projection ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    (r : ℝ≥0) (hr : 0 < r) (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom) :
    RelativeSchemeValuedPoint.mapOverBase (Polynomial.C : k →+* Polynomial k)
      (fun c => Spectrum.gauss_val_C _ r c) π hπbase
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) = x := by
  apply Subtype.ext
  change SchemeValuedPoint.map π
    (SchemeValuedPoint.map C.productTotalMap (C.productGaussSource x r hr).1) = x.1
  rw [← SchemeValuedPoint.map_comp]
  have hp : C.productTotalMap ≫ π = (fst X (ProjBerk.nativeMultiplicativeGroup k)).left := by
    change (C.unitOpenIso.inv.left ≫ C.unitOpenInclusion.left) ≫ π = _
    rw [Category.assoc, ← hπw, C.unitOpenIso_inv_originalProjection]
  rw [hp]
  exact SchemePointLaurentGauss.productPoint_fst X.hom x r hr

/-- **The defining factor of the model potential of a twisted ratio line.**  For every
original center-open frame of `L`, the native transition factor at the Gauss point over `x`
equals the model norm of the canonical ratio section at the total Gauss point. -/
theorem gaussCompatibleNormFactor_twistedRatio
    (hπw : C.unitOpenOriginalProjection.left = C.unitOpenInclusion.left ≫ π)
    (hπbase : π ≫ X.hom =
      C.projection ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    (hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left)
    (hL : IsInvertible L) (hR : IsInvertible (K.ratioModule J))
    (hM : IsInvertible (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (hKU : C.unitOpen ≤ K.support.compl) (hJU : C.unitOpen ≤ J.support.compl)
    (α : (pullback C.lineActionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.lineProjectionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (αT : (pullback C.lineActionMap).obj ((pullback π).obj L) ≅
      (pullback C.lineProjectionMap).obj ((pullback π).obj L))
    (αR : (pullback C.lineActionMap).obj (K.ratioModule J) ≅
      (pullback C.lineProjectionMap).obj (K.ratioModule J))
    (hα : (Functor.Monoidal.μIso (pullback C.lineActionMap) ((pullback π).obj L)
          (K.ratioModule J)).hom ≫
        (pullback C.lineActionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom ≫
        α.hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback C.lineProjectionMap)
          ((pullback π).obj L) (K.ratioModule J)).hom ≫
        (pullback C.lineProjectionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom)
    (hαT : ∀ s : unitObj X.left ⟶ L,
      pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫ αT.hom =
        pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s))
    (hαR : ∀ [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
      [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))],
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap) ≫
        (pullbackIsoAlong C.lineActionMap C.lineProjectionMap αR C.unitOpenActionLift.left).hom =
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap))
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    (e₁ : (pullback C.fibreOneInclusion.left).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (he₁ : ∀ (a : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj ((pullback π).obj L))
      (b : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj (K.ratioModule J)),
      pulledTensorSection C.fibreOneInclusion.left a b ≫ e₁.hom =
        (b ≫ eR.hom) ≫ a ≫ (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫
          (pullbackCongr hπ₁).hom.app L)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (s : unitObj X.left ⟶ L)
    (hs : letI : IsProper X.hom := C.original_isProper
      modelLineNorm Valuation.one_apply_le_one x hL (fibreSection x s) ≠ 0)
    (U : X.left.Opens)
    (hc : letI : IsProper X.hom := C.original_isProper
      center Valuation.one_apply_le_one x ∈ U)
    (hy : (C.productGaussSource x r hr).1.point ∈
      (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
    (eU : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    letI := C.twistedRatio_residue_inclusion_isIso K hKU x r hr
    C.gaussCompatibleNormFactor (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) hM
        r hr hru x L α e₁ U hy eU =
      modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hR
        (sectionAtOne (canonicalPulledRatioSection K J hJ
          (C.total.fromSpecResidueField
            (C.productTotalMap (C.productGaussSource x r hr).1.point)))) := by
  let : IsProper X.hom := C.original_isProper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : X.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance
  let : L.IsQuasicoherent := hL.isQuasicoherent
  -- every relevant map factors through the noncentral open
  have hzU := C.twistedRatio_productGauss_mem_unitOpen x r hr
  have hqz := SchemeSupportLineFrames.supportGenericFactor_comp
    (C.productTotalMap (C.productGaussSource x r hr).1.point) C.unitOpen hzU
  have hlam : C.fibreOneUnitOpenInclusion.left ≫ C.unitOpen.ι = C.fibreOneInclusion.left :=
    congrArg Over.Hom.left C.fibreOneUnitOpenInclusion_inclusion
  have : IsIso (K.pullbackModuleInclusion
      (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))) :=
    C.twistedRatio_residue_inclusion_isIso K hKU x r hr
  have : IsIso (K.pullbackModuleInclusion
      (Spec.map (C.productTotalMap.residueFieldMap (C.productGaussSource x r hr).1.point) ≫
        C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))) :=
    C.twistedRatio_inclusion_isIso K hKU
      (Spec.map (C.productTotalMap.residueFieldMap (C.productGaussSource x r hr).1.point) ≫
        SchemeSupportLineFrames.supportGenericFactor _ C.unitOpen hzU) _
      ((Category.assoc _ _ _).trans (congrArg (fun g => Spec.map
        (C.productTotalMap.residueFieldMap (C.productGaussSource x r hr).1.point) ≫ g) hqz))
  have : IsIso (K.pullbackModuleInclusion
      ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField
        (C.productGaussSource x r hr).1.point ≫ C.productTotalMap)) :=
    C.twistedRatio_inclusion_isIso K hKU
      ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField
        (C.productGaussSource x r hr).1.point ≫ C.unitOpenIso.inv.left) _ (Category.assoc _ _ _)
  have : IsIso (K.pullbackModuleInclusion C.productTotalMap) :=
    C.twistedRatio_inclusion_isIso K hKU C.unitOpenIso.inv.left _ rfl
  have : IsIso (K.pullbackModuleInclusion (C.unitOpenIso.inv.left ≫ C.unitOpenInclusion.left)) :=
    C.twistedRatio_inclusion_isIso K hKU C.unitOpenIso.inv.left _ rfl
  have : IsIso (K.pullbackModuleInclusion C.unitOpenInclusion.left) :=
    C.twistedRatio_inclusion_isIso K hKU (𝟙 _) _ (Category.id_comp _)
  have : IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap)) :=
    C.twistedRatio_inclusion_isIso K hKU (𝟙 _) _
      ((Category.id_comp _).trans C.lineActionLift_action.symm)
  have : IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap)) :=
    C.twistedRatio_inclusion_isIso K hKU (C.unitOpenFibreProjection.left ≫
      C.fibreOneUnitOpenInclusion.left) _
      ((Category.assoc _ _ _).trans ((congrArg (fun g => C.unitOpenFibreProjection.left ≫ g)
        hlam).trans C.lineActionLift_projection.symm))
  have : IsIso (K.pullbackModuleInclusion
      (C.unitOpenFibreProjection.left ≫ C.fibreOneInclusion.left)) :=
    C.twistedRatio_inclusion_isIso K hKU (C.unitOpenFibreProjection.left ≫
      C.fibreOneUnitOpenInclusion.left) _
      ((Category.assoc _ _ _).trans (congrArg (fun g => C.unitOpenFibreProjection.left ≫ g) hlam))
  have : IsIso (K.pullbackModuleInclusion C.fibreOneInclusion.left) :=
    C.twistedRatio_inclusion_isIso K hKU C.fibreOneUnitOpenInclusion.left _ hlam
  have : IsIso (J.pullbackModuleInclusion C.fibreOneInclusion.left) :=
    C.twistedRatio_inclusion_isIso J hJU C.fibreOneUnitOpenInclusion.left _ hlam
  -- the fibre-one value of the canonical ratio section, transported to `X`
  have : IsIso (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left) :=
    canonicalPulledRatioSection_isIso K J hJ C.fibreOneInclusion.left
  have hεX : IsIso (pullbackSectionHom C.fibreOneIso.inv.left
      (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
      (pullbackUnitIso C.fibreOneIso.inv.left).hom) := by
    unfold pullbackSectionHom
    infer_instance
  -- (1) the model norm of the twisted canonical section at the total Gauss point
  have hpt := C.twistedRatio_mapOverBase_productGauss π hπw hπbase r hr x
  have hN1 : modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hM
      (sectionAtOne (pulledTensorSection
        (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))
        (pullbackSectionHom
          (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))
          (pullbackSectionHom π s))
        (canonicalPulledRatioSection K J hJ
          (C.total.fromSpecResidueField
            (C.productTotalMap (C.productGaussSource x r hr).1.point))))) =
      modelLineNorm Valuation.one_apply_le_one x hL (fibreSection x s) *
        modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
          (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hR
          (sectionAtOne (canonicalPulledRatioSection K J hJ
            (C.total.fromSpecResidueField
              (C.productTotalMap (C.productGaussSource x r hr).1.point)))) := by
    have hsec := sectionAtOne_pulledTensorSection
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr))
      (pullbackSectionHom
        (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))
        (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ
        (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point)))
    refine (congrArg (modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hM)
        hsec).trans ?_
    refine (modelLineNorm_genericTensorSection (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr))
      (hL.pullback π) hR _ _).trans ?_
    congr 1
    refine (modelLineNorm_pullbackSection_eq_overBase (Polynomial.C : k →+* Polynomial k)
      (fun c => Spectrum.gauss_val_C _ r c) π hπbase Valuation.one_apply_le_one
      (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr))
      hL s).trans ?_
    rw [hpt]
  -- (2) the transport of the twisted canonical section to the product
  have hprod := C.twistedRatio_productTotalLineIso_section π L K J hJ hπ₁ α αT αR hα hαT eR e₁
    he₁ hαR s
  have hG : pulledTensorSection C.productTotalMap
      (pullbackSectionHom C.productTotalMap (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ C.productTotalMap) =
      pullbackSectionHom C.unitOpenIso.inv.left
        (pulledTensorSection C.unitOpenInclusion.left
          (pullbackSectionHom C.unitOpenInclusion.left (pullbackSectionHom π s))
          (canonicalPulledRatioSection K J hJ C.unitOpenInclusion.left)) ≫
        (pullbackComp C.unitOpenIso.inv.left C.unitOpenInclusion.left).hom.app
          (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) :=
    (pullbackSectionHom_twistedCanonicalSection K J hJ C.unitOpenIso.inv.left
      C.unitOpenInclusion.left (pullbackSectionHom π s)).symm
  have hT1 := transportedResidueSection_twistedCanonical C.productTotalMap K J hJ
    (pullbackSectionHom π s) (C.productTotalLineIso
      (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) L α e₁)
    (C.productGaussSource x r hr).1
  rw [hG, hprod] at hT1
  -- (3) the reference coefficient of the transported section at the product Gauss point
  have hnorm : modelLineNorm Valuation.one_apply_le_one x hL
      (fibreSection x ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)) =
      modelLineNorm Valuation.one_apply_le_one x hL (fibreSection x s) := by
    rw [modelLineNorm_fibreSection, modelLineNorm_fibreSection,
      modelHomNorm_comp _ x (Scheme.Modules.isInvertible_unit (X := X.left))
        (Scheme.Modules.isInvertible_unit (X := X.left)) hL]
    have h1 := modelHomNorm_iso Valuation.one_apply_le_one x
      (Scheme.Modules.isInvertible_unit (X := X.left))
      (Scheme.Modules.isInvertible_unit (X := X.left)) (asIso (pullbackSectionHom
        C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom))
    rw [asIso_hom] at h1
    rw [h1, one_mul]
  have hm₀ : Scheme.Modules.affinePullbackUnitTop (X.left.fromSpecResidueField x.1.point) L
      (sectionAtOne ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)) =
      fibreSection x ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s) := by
    unfold fibreSection
    rw [affinePullbackUnitTop_eq_sectionAtOne, topSectionHom_sectionAtOne]
  have hm₀ne : sectionAtOne ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s) ≠ 0 := by
    intro h0
    apply hs
    rw [← hnorm, ← hm₀, h0, twistedRatio_affinePullbackUnitTop_zero]
    exact (modelLineNorm_eq_zero_iff Valuation.one_apply_le_one x hL 0).mpr rfl
  have hσ : sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
      ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)) =
      Scheme.Modules.affinePullbackUnitTop (fst X (ProjBerk.nativeMultiplicativeGroup k)).left L
        (sectionAtOne ((pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)) := by
    rw [affinePullbackUnitTop_eq_sectionAtOne, topSectionHom_sectionAtOne]
  have hcoeffs : SchemeModuleLaurentCoefficients.coefficients X.hom L
      (sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        ((pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s))) =
      Finsupp.single 0 (sectionAtOne ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)) := by
    have h := SchemeModuleLaurentCoefficients.coefficients_monomial X.hom L 0
      (sectionAtOne ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s))
    rw [LaurentPolynomial.T_zero, map_one, one_smul] at h
    rw [hσ]
    exact h
  have hLau := SchemeSupportFrameEvaluation.laurentSupportFrame_value X.hom x
    Valuation.one_apply_le_one L hL U hc eU r hr
    (sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
      ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)))
  have hsupp : (SchemeModuleLaurentCoefficients.coefficients X.hom L
      (sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        ((pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)))).support = {0} := by
    rw [hcoeffs]
    exact Finsupp.support_single 0 hm₀ne
  have hval : SchemeModuleLaurentCoefficients.coefficients X.hom L
      (sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        ((pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s))) 0 =
      (sectionAtOne ((pullbackSectionHom C.fibreOneIso.inv.left
        (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
          (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)) := by
    rw [hcoeffs]
    exact Finsupp.single_eq_same
  have hsup : (SchemeModuleLaurentCoefficients.coefficients X.hom L
      (sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        ((pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s)))).support.sup
      (fun i => modelLineNorm Valuation.one_apply_le_one x hL
        (Scheme.Modules.affinePullbackUnitTop (X.left.fromSpecResidueField x.1.point) L
          (SchemeModuleLaurentCoefficients.coefficients X.hom L
            (sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        ((pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s))) i)) * r ^ i) =
      modelLineNorm Valuation.one_apply_le_one x hL (fibreSection x s) := by
    rw [hsupp]
    simp only [Finset.sup_singleton]
    rw [hval, zpow_zero, mul_one, hm₀, hnorm]
  replace hLau := hLau.trans hsup
  have hσy : sectionAtOne (pullbackSectionHom
      ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField
        (C.productGaussSource x r hr).1.point)
      (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
        ((pullbackSectionHom C.fibreOneIso.inv.left
          (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
            (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s))) =
      Scheme.Modules.affinePullbackUnitTop
        ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.fromSpecResidueField
          (C.productGaussSource x r hr).1.point)
        ((pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj L)
        (sectionAtOne (pullbackSectionHom (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
          ((pullbackSectionHom C.fibreOneIso.inv.left
            (canonicalPulledRatioSection K J hJ C.fibreOneInclusion.left ≫ eR.hom) ≫
              (pullbackUnitIso C.fibreOneIso.inv.left).hom) ≫ s))) := by
    rw [affinePullbackUnitTop_eq_sectionAtOne, topSectionHom_sectionAtOne]
  -- (4) comparison through the defining residue formula of the factor
  have hformula := C.gaussCompatibleNormFactor_residue_formula
    (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) hM r hr hru x L α e₁ U hy eU
    (sectionAtOne (pulledTensorSection
      (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))
      (pullbackSectionHom
        (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point))
        (pullbackSectionHom π s))
      (canonicalPulledRatioSection K J hJ
        (C.total.fromSpecResidueField (C.productTotalMap (C.productGaussSource x r hr).1.point)))))
  rw [hT1, hσy] at hformula
  have key := hformula.trans (congrArg (fun t => C.gaussCompatibleNormFactor
    (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) hM r hr hru x L α e₁ U hy eU *
      t) hLau)
  exact mul_right_cancel₀ hs ((key.symm.trans hN1).trans (mul_comm _ _))

/-- **The native factor of a twisted canonical ratio line**: it is the model norm of the
canonical ratio section at the total Gauss point. -/
theorem gaussNativeNormFactor_twistedRatio
    (hπw : C.unitOpenOriginalProjection.left = C.unitOpenInclusion.left ≫ π)
    (hπbase : π ≫ X.hom =
      C.projection ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    (hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left)
    (hL : IsInvertible L) (hR : IsInvertible (K.ratioModule J))
    (hM : IsInvertible (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (hKU : C.unitOpen ≤ K.support.compl) (hJU : C.unitOpen ≤ J.support.compl)
    (α : (pullback C.lineActionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.lineProjectionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (αT : (pullback C.lineActionMap).obj ((pullback π).obj L) ≅
      (pullback C.lineProjectionMap).obj ((pullback π).obj L))
    (αR : (pullback C.lineActionMap).obj (K.ratioModule J) ≅
      (pullback C.lineProjectionMap).obj (K.ratioModule J))
    (hα : (Functor.Monoidal.μIso (pullback C.lineActionMap) ((pullback π).obj L)
          (K.ratioModule J)).hom ≫
        (pullback C.lineActionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom ≫
        α.hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback C.lineProjectionMap)
          ((pullback π).obj L) (K.ratioModule J)).hom ≫
        (pullback C.lineProjectionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom)
    (hαT : ∀ s : unitObj X.left ⟶ L,
      pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫ αT.hom =
        pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s))
    (hαR : ∀ [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
      [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))],
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap) ≫
        (pullbackIsoAlong C.lineActionMap C.lineProjectionMap αR C.unitOpenActionLift.left).hom =
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap))
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    (e₁ : (pullback C.fibreOneInclusion.left).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (he₁ : ∀ (a : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj ((pullback π).obj L))
      (b : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj (K.ratioModule J)),
      pulledTensorSection C.fibreOneInclusion.left a b ≫ e₁.hom =
        (b ≫ eR.hom) ≫ a ≫ (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫
          (pullbackCongr hπ₁).hom.app L)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (s : unitObj X.left ⟶ L)
    (hs : letI : IsProper X.hom := C.original_isProper
      modelLineNorm Valuation.one_apply_le_one x hL (fibreSection x s) ≠ 0) :
    letI := C.twistedRatio_residue_inclusion_isIso K hKU x r hr
    C.gaussNativeNormFactor (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) hM
        L α e₁ hL r hr hru x =
      modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hR
        (sectionAtOne (canonicalPulledRatioSection K J hJ
          (C.total.fromSpecResidueField
            (C.productTotalMap (C.productGaussSource x r hr).1.point)))) := by
  let : IsProper X.hom := C.original_isProper
  unfold gaussNativeNormFactor
  exact C.gaussCompatibleNormFactor_twistedRatio π L K J hJ hπw hπbase hπ₁ hL hR hM hKU hJU α αT αR
    hα hαT hαR eR e₁ he₁ r hr hru x s hs _ (C.originalCenterOpenFrame L hL x).2.2 _
    (C.originalCenterOpenFrame L hL x).2.1


/-- **The model potential of a twisted canonical ratio line.**  At every trivially valued
original point `x`, the native model potential (used by the finite Fubini–Study
constructions) of `π^*L ⊗ K ⊗ J^∨` is minus the logarithm of the model norm of the
canonical ratio section at the radius-`r` total Gauss point over `x`. -/
theorem gaussNativeModelPotential_twistedRatio
    (hπw : C.unitOpenOriginalProjection.left = C.unitOpenInclusion.left ≫ π)
    (hπbase : π ≫ X.hom =
      C.projection ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    (hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left)
    (hL : IsInvertible L) (hR : IsInvertible (K.ratioModule J))
    (hM : IsInvertible (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (hKU : C.unitOpen ≤ K.support.compl) (hJU : C.unitOpen ≤ J.support.compl)
    (α : (pullback C.lineActionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.lineProjectionMap).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)))
    (αT : (pullback C.lineActionMap).obj ((pullback π).obj L) ≅
      (pullback C.lineProjectionMap).obj ((pullback π).obj L))
    (αR : (pullback C.lineActionMap).obj (K.ratioModule J) ≅
      (pullback C.lineProjectionMap).obj (K.ratioModule J))
    (hα : (Functor.Monoidal.μIso (pullback C.lineActionMap) ((pullback π).obj L)
          (K.ratioModule J)).hom ≫
        (pullback C.lineActionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom ≫
        α.hom =
      (αT.hom ⊗ₘ αR.hom) ≫ (Functor.Monoidal.μIso (pullback C.lineProjectionMap)
          ((pullback π).obj L) (K.ratioModule J)).hom ≫
        (pullback C.lineProjectionMap).map
          (ModularCurves.monoidalTensorObjIso ((pullback π).obj L) (K.ratioModule J)).hom)
    (hαT : ∀ s : unitObj X.left ⟶ L,
      pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫ αT.hom =
        pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s))
    (hαR : ∀ [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
      [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))],
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineActionMap) ≫
        (pullbackIsoAlong C.lineActionMap C.lineProjectionMap αR C.unitOpenActionLift.left).hom =
      canonicalPulledRatioSection K J hJ (C.unitOpenActionLift.left ≫ C.lineProjectionMap))
    (eR : (pullback C.fibreOneInclusion.left).obj (K.ratioModule J) ≅
      unitObj (fibreOneOver k C.projection).left)
    (e₁ : (pullback C.fibreOneInclusion.left).obj
        (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) ≅
      (pullback C.fibreOneIso.hom.left).obj L)
    (he₁ : ∀ (a : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj ((pullback π).obj L))
      (b : unitObj (fibreOneOver k C.projection).left ⟶
        (pullback C.fibreOneInclusion.left).obj (K.ratioModule J)),
      pulledTensorSection C.fibreOneInclusion.left a b ≫ e₁.hom =
        (b ≫ eR.hom) ≫ a ≫ (pullbackComp C.fibreOneInclusion.left π).hom.app L ≫
          (pullbackCongr hπ₁).hom.app L)
    (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)
    (s : unitObj X.left ⟶ L)
    (hs : letI : IsProper X.hom := C.original_isProper
      modelLineNorm Valuation.one_apply_le_one x hL (fibreSection x s) ≠ 0) :
    letI := C.twistedRatio_residue_inclusion_isIso K hKU x r hr
    C.gaussNativeModelPotential (Scheme.Modules.tensorObj ((pullback π).obj L) (K.ratioModule J)) hM
        L α e₁ hL r hr hru x =
      -Real.log (modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hR
        (sectionAtOne (canonicalPulledRatioSection K J hJ
          (C.total.fromSpecResidueField
            (C.productTotalMap (C.productGaussSource x r hr).1.point)))) : ℝ) := by
  unfold gaussNativeModelPotential
  exact congrArg (fun c : ℝ≥0 => -Real.log (c : ℝ))
    (C.gaussNativeNormFactor_twistedRatio π L K J hJ hπw hπbase hπ₁ hL hR hM hKU hJU α αT αR
      hα hαT hαR eR e₁ he₁ r hr hru x s hs)

end TwistedRatio

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
