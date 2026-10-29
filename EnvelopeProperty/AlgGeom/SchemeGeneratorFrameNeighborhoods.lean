import EnvelopeProperty.AlgGeom.GeneratedLineLocalCoefficients

/-! # Genuine original generator frames on actual original affine neighborhoods -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeGeneratorFrameNeighborhoods
open SchemeLineSectionEvaluation GeneratedLineLocalCoefficients SchemeGeneratingSectionsUnit
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {L : X.Modules}

/-- The original open restriction diagram retains the actual original top-section identifications. -/
theorem homOfLE_topIso {U W : X.Opens} (h : W ≤ U) :
    U.topIso.hom ≫ X.presheaf.map (homOfLE h).op ≫ W.topIso.inv =
      (X.homOfLE h).appTop := by
  rw [Scheme.homOfLE_appTop]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv,
    ← X.presheaf.map_comp, ← op_comp]
  exact X.presheaf.congr_map (Subsingleton.elim _ _)

/-- A SAME original local coefficient becomes a true unit on its actual original basic open. -/
theorem basicOpen_localCoefficient_isUnit (U : X.Opens) (r : Γ(U.toScheme, ⊤)) :
    IsUnit ((X.homOfLE (X.basicOpen_le (U.topIso.hom.hom r))).appTop.hom r) := by
  let c := U.topIso.hom.hom r
  let W := X.basicOpen c
  have h := (X.toRingedSpace.isUnit_res_basicOpen c).map W.topIso.inv.hom
  have he := homOfLE_topIso (X.basicOpen_le c)
  have hv := congrArg (fun q => q.hom r) he
  exact hv ▸ h

/-- The original scalar equation pulls to a true original section isomorphism on its own basic open. -/
theorem section_isIso_on_basicOpen (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme)
    (s : unitObj X ⟶ L) (r : Γ(U.toScheme, ⊤))
    (hr : pullbackSectionHom U.ι s ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r) :
    IsIso (pullbackSectionHom (X.basicOpen (U.topIso.hom.hom r)).ι s) := by
  let W := X.basicOpen (U.topIso.hom.hom r)
  let h : W ≤ U := X.basicOpen_le _
  let E := frameViaFactor (X.homOfLE h) U.ι W.ι (X.homOfLE_ι h) e
  have hu := basicOpen_localCoefficient_isUnit U r
  have hscalar := frameViaFactor_sectionHom_scalar (X.homOfLE h) U.ι W.ι
    (X.homOfLE_ι h) e s r hr
  have hi : IsIso (ModularCurves.unitEndomorphismOfTopSection ((X.homOfLE h).appTop.hom r)) := by
    rw [← hu.unit_spec]
    exact (ModularCurves.unitAutomorphismOfTopUnit hu.unit).isIso_hom
  have : IsIso (pullbackSectionHom W.ι s ≫ E.hom) := hscalar ▸ hi
  exact IsIso.of_isIso_comp_right (pullbackSectionHom W.ι s) E.hom

/-- EVERY original point has an actual original affine neighborhood on which
one SAME original global generator is an isomorphism. No cover is supplied. -/
theorem exists_affine_generator_frame (hL : IsInvertible L) (G : L.GeneratingSections) (x : X) :
    ∃ U : X.AffineZariskiSite, x ∈ U.1 ∧ ∃ i : G.I,
      IsIso (pullbackSectionHom U.1.ι (generatorHom G i)) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := GeneratedLineFramedAffineCover.exists_framed_affine L hL x
  let H := SchemeGeneratedLineCoefficients.framedGenerators
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.ι G) e
  obtain ⟨i, hi⟩ := SchemeGeneratorCoefficientOpens.exists_mem_basicOpen H ⟨x, hxU⟩
  let r := localCoefficient G U.1 e i
  let c := U.1.topIso.hom.hom r
  let W := X.basicOpen c
  have hW : IsAffineOpen W := U.2.basicOpen c
  have he : U.1.ι ''ᵁ U.1.toScheme.basicOpen r = W := by
    have h := U.1.ι_image_basicOpen_topIso_inv c
    rw [show U.1.topIso.inv.hom c = r from U.1.topIso.hom_inv_id_apply r] at h
    exact h
  have hxW : x ∈ W := by
    rw [← he]
    exact ⟨⟨x, hxU⟩, hi, rfl⟩
  exact ⟨⟨W, hW⟩, hxW, i,
    section_isIso_on_basicOpen U.1 e (generatorHom G i) r (localCoefficient_scalar G U.1 e i)⟩

/-- The canonical true original local frame is the inverse of the SAME original generator. -/
def generatorFrame (G : L.GeneratingSections) (U : X.Opens) (i : G.I)
    (hi : IsIso (pullbackSectionHom U.ι (generatorHom G i))) :
    (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme :=
  letI := hi
  (asIso (pullbackSectionHom U.ι (generatorHom G i))).symm

/-- That SAME actual original generator is EXACTLY one in its canonical actual frame. -/
theorem generatorFrame_section (G : L.GeneratingSections) (U : X.Opens) (i : G.I)
    (hi : IsIso (pullbackSectionHom U.ι (generatorHom G i))) :
    pullbackSectionHom U.ι (generatorHom G i) ≫ (generatorFrame G U i hi).hom = 𝟙 _ := by
  let := hi
  exact (asIso (pullbackSectionHom U.ι (generatorHom G i))).hom_inv_id

private theorem unitScalar_one {B : Scheme.{u}} (r : Γ(B, ⊤))
    (h : ModularCurves.unitEndomorphismOfTopSection r = 𝟙 (unitObj B)) : r = 1 := by
  have hh := congrArg (fun q : unitObj B ⟶ unitObj B =>
    (q.val.app (op ⊤)).hom (1 : Γ(B, ⊤))) h
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply] at hh
  simp only [homOfLE_refl, op_id, one_mul] at hh
  change (B.presheaf.map (𝟙 (op (⊤ : B.Opens)))).hom r = 1 at hh
  rw [B.presheaf.map_id] at hh
  exact hh

/-- The actual original coefficient of the SAME chosen generator is literally one. -/
theorem localCoefficient_generatorFrame (G : L.GeneratingSections) (U : X.Opens) (i : G.I)
    (hi : IsIso (pullbackSectionHom U.ι (generatorHom G i))) :
    localCoefficient G U (generatorFrame G U i hi) i = 1 :=
  unitScalar_one _ ((localCoefficient_scalar G U (generatorFrame G U i hi) i).symm.trans
    (generatorFrame_section G U i hi))

end EnvelopeProperty.SchemeGeneratorFrameNeighborhoods
