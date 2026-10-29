import EnvelopeProperty.Char0.RoundedCanonicalOpenFactorization
import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionBaseChange
import EnvelopeProperty.AlgGeom.FlatSectionKernel

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Char0.AffineOpenGlobalRoundedKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
variable {X Y : Scheme.{u}} (f : Y ⟶ X) (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)

/-- The genuine original tensor-dual Hom module under actual native pullback. -/
def homSectionPullbackIso (B : X.Modules) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj B)
        (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A)) :=
  (Scheme.Modules.pullback f).mapIso (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).symm ≪≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) B (Scheme.Modules.dualObj A)).symm ≪≫
    whiskerLeftIso ((Scheme.Modules.pullback f).obj B)
      (SchemeInvertibleHomSection.rightDualPullbackEvaluationIso f A hA) ≪≫
    ModularCurves.monoidalTensorObjIso ((Scheme.Modules.pullback f).obj B)
      (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A))

/-- The same original whole Hom section is preserved by the actual tensor-dual comparison. -/
theorem homSectionPullbackIso_section (B : X.Modules) (φ : A ⟶ B) :
    (Scheme.Modules.pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (SchemeInvertibleHomSection.equiv A hA B φ) ≫
      (homSectionPullbackIso f A hA B).hom =
    SchemeInvertibleHomSection.equiv ((Scheme.Modules.pullback f).obj A) (hA.pullback f)
      ((Scheme.Modules.pullback f).obj B) ((Scheme.Modules.pullback f).map φ) := by
  let F := Scheme.Modules.pullback f
  let uX := ModularCurves.monoidalUnitObjIso X
  let uY := ModularCurves.monoidalUnitObjIso Y
  have hu : uY.hom ≫ (Scheme.Modules.pullbackUnitIso f).inv =
      (Functor.Monoidal.εIso F).hom ≫ F.map uX.hom := by
    have h := congrArg Iso.hom (Scheme.Modules.pullback_monoidalUnitObjIso f)
    change (Functor.Monoidal.εIso F).inv ≫ uY.hom =
      F.map uX.hom ≫ (Scheme.Modules.pullbackUnitIso f).hom at h
    apply (cancel_epi (Functor.Monoidal.εIso F).inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he := SchemeInvertibleHomSection.equiv_pullback_monoidal f A hA B φ
  apply (cancel_epi uY.hom).mp
  apply (cancel_mono (ModularCurves.monoidalTensorObjIso (F.obj B)
    (Scheme.Modules.dualObj (F.obj A))).inv).mp
  simp only [homSectionPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, whiskerLeftIso_hom, F, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc uY.hom (Scheme.Modules.pullbackUnitIso f).inv, hu]
  simpa only [Functor.map_comp, Category.assoc, F, uX, uY] using he.symm

/-- The whole tensor-dual comparison is natural in the actual original target map. -/
theorem homSectionPullbackIso_naturality {B C : X.Modules} (ψ : B ⟶ C) :
    (homSectionPullbackIso f A hA B).hom ≫
      SchemeTensorObjMorphisms.tensorObjMap ((Scheme.Modules.pullback f).map ψ)
        (𝟙 (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj A))) =
      (Scheme.Modules.pullback f).map
        (SchemeTensorObjMorphisms.tensorObjMap ψ (𝟙 (Scheme.Modules.dualObj A))) ≫
      (homSectionPullbackIso f A hA C).hom := by
  let F := Scheme.Modules.pullback f
  let d := SchemeInvertibleHomSection.rightDualPullbackEvaluationIso f A hA
  apply (cancel_mono (ModularCurves.monoidalTensorObjIso (F.obj C)
    (Scheme.Modules.dualObj (F.obj A))).inv).mp
  simp only [homSectionPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    whiskerLeftIso_hom, Category.assoc, F]
  rw [SchemeTensorObjMorphisms.tensorObjMap_monoidal (F.map ψ)
    (𝟙 (Scheme.Modules.dualObj (F.obj A)))]
  simp only [F, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id, tensorHom_id]
  rw [whisker_exchange]
  rw [Functor.Monoidal.μIso_inv, Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [← F.map_comp_assoc]
  have ht := SchemeTensorObjMorphisms.tensorObjMap_monoidal ψ (𝟙 (Scheme.Modules.dualObj A))
  simp only [tensorHom_id] at ht
  rw [← ht]
  simp only [F.map_comp, Category.assoc, Functor.Monoidal.μIso_inv, F]

/-- Arbitrary sections of the actual pulled original tensor-ideal have the actual
whole-map factorization criterion, with the same derived original dual comparison. -/
theorem homSectionPullbackIso_idealLift_iff (B I : X.Modules)
    (i : I ⟶ Scheme.Modules.unitObj X)
    (χ : (Scheme.Modules.pullback f).obj A ⟶ (Scheme.Modules.pullback f).obj B) :
    (∃ s : Scheme.Modules.unitObj Y ⟶
        (Scheme.Modules.pullback f).obj
          (Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) I),
      s ≫ (Scheme.Modules.pullback f).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap
          (Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) I i) =
        SchemeInvertibleHomSection.equiv ((Scheme.Modules.pullback f).obj A) (hA.pullback f)
          ((Scheme.Modules.pullback f).obj B) χ ≫ (homSectionPullbackIso f A hA B).inv) ↔
      ∃ θ : (Scheme.Modules.pullback f).obj A ⟶
          (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObj B I),
        θ ≫ (Scheme.Modules.pullback f).map (SchemeTensorObjMorphisms.tensorObjIdealMap B I i) = χ := by
  let F := Scheme.Modules.pullback f
  let D := Scheme.Modules.dualObj A
  let j := SchemeTensorObjMorphisms.tensorObjIdealMap B I i
  let inc := SchemeTensorObjMorphisms.tensorObjIdealMap (Scheme.Modules.tensorObj B D) I i
  let eB := homSectionPullbackIso f A hA B
  let eS := F.mapIso (SchemeTensorObjMorphisms.tensorObjIdealShuffleIso B I D).symm ≪≫
    homSectionPullbackIso f A hA (Scheme.Modules.tensorObj B I)
  have hs : eS.hom ≫ SchemeTensorObjMorphisms.tensorObjMap (F.map j)
      (𝟙 (Scheme.Modules.dualObj (F.obj A))) = F.map inc ≫ eB.hom := by
    simp only [eS, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    rw [homSectionPullbackIso_naturality]
    rw [← F.map_comp_assoc, SchemeTensorObjMorphisms.tensorObjIdealShuffleIso_inclusion]
    simp only [D, Iso.inv_hom_id_assoc, inc, eB]
  have he := SchemeInvertibleHomSection.equiv_lift_iff (F.obj A) (hA.pullback f) χ (F.map j)
  constructor
  · rintro ⟨s, h⟩
    apply he.mp
    refine ⟨s ≫ eS.hom, ?_⟩
    rw [Category.assoc, hs, ← Category.assoc, h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, eB, F]
  · intro h
    obtain ⟨s, h⟩ := he.mpr h
    refine ⟨s ≫ eS.inv, ?_⟩
    apply (cancel_mono eB.hom).mp
    rw [Category.assoc, ← hs]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, eB, F] using h

/-- EVERY chart scalar acts on the same whole pulled Hom section through the actual source action. -/
theorem homSectionPullbackIso_scalar_section (B : X.Modules) (φ : A ⟶ B) (b : Γ(Y, ⊤)) :
    SchemeModuleGlobalSections.sectionHom (X := Y) (Scheme.Modules.unitObj Y) b ≫
      (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (SchemeInvertibleHomSection.equiv (X := X) A hA B φ) =
    SchemeInvertibleHomSection.equiv (X := Y) ((Scheme.Modules.pullback f).obj A) (hA.pullback f)
      ((Scheme.Modules.pullback f).obj B)
      (SchemeUnitScalarAction.globalScalarAction (X := Y) ((Scheme.Modules.pullback f).obj A) b ≫
        (Scheme.Modules.pullback f).map φ) ≫ (homSectionPullbackIso f A hA B).inv := by
  apply (cancel_mono (homSectionPullbackIso f A hA B).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [homSectionPullbackIso_section]
  exact (SchemeUnitScalarAction.unitAction_equiv (X := Y) ((Scheme.Modules.pullback f).obj A)
    (hA.pullback f) ((Scheme.Modules.pullback f).obj B)
    (SchemeModuleGlobalSections.sectionHom (X := Y) (Scheme.Modules.unitObj Y) b)
    ((Scheme.Modules.pullback f).map φ)).symm

/-- EVERY coefficient lift of the whole pulled original Hom section is the whole
pulled-map factorization; all scalar and tensor comparisons are internally derived. -/
theorem homSectionPullbackIso_scalar_idealLift_iff (B I : X.Modules)
    (i : I ⟶ Scheme.Modules.unitObj X) (φ : A ⟶ B) (b : Γ(Y, ⊤)) :
    (∃ s : Scheme.Modules.unitObj Y ⟶
        (Scheme.Modules.pullback f).obj
          (Scheme.Modules.tensorObj (Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) I),
      s ≫ (Scheme.Modules.pullback f).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap
          (Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A)) I i) =
        SchemeModuleGlobalSections.sectionHom (X := Y) (Scheme.Modules.unitObj Y) b ≫
          (Scheme.Modules.pullbackUnitIso f).inv ≫
            (Scheme.Modules.pullback f).map (SchemeInvertibleHomSection.equiv (X := X) A hA B φ)) ↔
      ∃ θ : (Scheme.Modules.pullback f).obj A ⟶
          (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObj B I),
        θ ≫ (Scheme.Modules.pullback f).map (SchemeTensorObjMorphisms.tensorObjIdealMap B I i) =
          SchemeUnitScalarAction.globalScalarAction (X := Y) ((Scheme.Modules.pullback f).obj A) b ≫
            (Scheme.Modules.pullback f).map φ := by
  rw [homSectionPullbackIso_scalar_section]
  exact homSectionPullbackIso_idealLift_iff f A hA B I i _

end EnvelopeProperty.Char0.AffineOpenGlobalRoundedKernel

namespace EnvelopeProperty.Char0.AffineOpenGlobalRoundedKernel
open RoundedCanonicalModule
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem idealInclusionMono {W : Scheme.{u}} (I : W.IdealSheafData) :
    Mono I.toModulesInclusion := by
  let F := Scheme.Modules.toPresheafOfModules W
  have : Mono (F.map I.toModulesInclusion) := by
    change Mono I.toSubmodule.ι
    infer_instance
  exact F.mono_of_mono_map inferInstance

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (h : Z ⟶ Y) [IsOpenImmersion h]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The actual original rounded inclusion remains monic under genuine original open pullback. -/
theorem mono_pullback_relativeRoundedInclusion :
    Mono ((Scheme.Modules.pullback h).map (relativeRoundedInclusion f g n J hJ q)) := by
  let K := RoundedSncIdealSheaf.rounded J hJ q
  let L := relative f g n
  let F := Scheme.Modules.pullback h
  let i := (K.comap h).toModulesInclusion
  let : Mono i := idealInclusionMono (K.comap h)
  have hm := SchemeTensorObjMorphisms.mono_tensorObjMap_left (F.obj L)
    ((relative_isInvertible f g n).pullback h) i
  let : Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 (F.obj L)) i) := hm
  have hi : Mono (SchemeTensorObjMorphisms.tensorObjIdealMap (F.obj L)
      (K.comap h).toModules i) := by
    unfold SchemeTensorObjMorphisms.tensorObjIdealMap
    infer_instance
  let : Mono (SchemeTensorObjMorphisms.tensorObjIdealMap (F.obj L)
      (K.comap h).toModules i) := hi
  have he := SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion h L K
  change Mono (F.map (SchemeTensorObjMorphisms.tensorObjIdealMap L K.toModules K.toModulesInclusion))
  rw [← he]
  infer_instance

/-- The actual whole original quotient differential section under genuine native pullback. -/
def pulledQuotientDifferentialSection : Scheme.Modules.unitObj Z ⟶
    (Scheme.Modules.pullback h).obj (quotient f g n J hJ q) :=
  (Scheme.Modules.pullbackUnitIso h).inv ≫
    (Scheme.Modules.pullback h).map (quotientDifferentialSection f g n J hJ q)

private theorem sectionHom_eq_zero_iff {W : Scheme.{u}} (M : W.Modules) (s : Γ(M, ⊤)) :
    SchemeModuleGlobalSections.sectionHom M s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    have h1 := congrArg (fun α => α.val.app (.op (⊤ : W.Opens)) (show Γ(W, ⊤) from 1)) hs
    change (1 : Γ(W, ⊤)) • M.presheaf.map (homOfLE (le_top : (⊤ : W.Opens) ≤ ⊤)).op s = 0 at h1
    simpa using h1
  · rintro rfl
    apply Scheme.Modules.hom_ext
    intro U
    ext a
    change (show Γ(W, U) from a) • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 0 = 0
    rw [map_zero, smul_zero]

/-- EVERY original chart coefficient is tested in the SAME pulled global quotient,
by actual factorization through the entire pulled original rounded inclusion. -/
theorem pulledQuotientDifferentialSection_apply_eq_zero_iff_lift (b : Γ(Z, ⊤)) :
    (pulledQuotientDifferentialSection f g n h J hJ q).val.app (.op ⊤) b = 0 ↔
      ∃ s : Scheme.Modules.unitObj Z ⟶
          (Scheme.Modules.pullback h).obj (relativeRounded f g n J hJ q),
        s ≫ (Scheme.Modules.pullback h).map (relativeRoundedInclusion f g n J hJ q) =
          SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj Z) b ≫
            (Scheme.Modules.pullbackUnitIso h).inv ≫
              (Scheme.Modules.pullback h).map (differentialSection f g n) := by
  let F := Scheme.Modules.pullback h
  let r := SchemeModuleGlobalSections.sectionHom (Scheme.Modules.unitObj Z) b
  let d := differentialSection f g n
  let inc := relativeRoundedInclusion f g n J hJ q
  let π := quotientProjection f g n J hJ q
  let T := ShortComplex.mk inc π (relativeRoundedInclusion_quotientProjection f g n J hJ q)
  have he : T.Exact := ShortComplex.exact_cokernel inc
  let : Epi T.g := by
    change Epi (cokernel.π inc)
    infer_instance
  have hm : (T.map F).Exact := he.map_of_epi_of_preservesCokernel F inferInstance inferInstance
  let : Mono (F.map inc) := mono_pullback_relativeRoundedInclusion f g n h J hJ q
  let : Mono (T.map F).f := by change Mono (F.map inc); infer_instance
  have hc : (r ≫ (Scheme.Modules.pullbackUnitIso h).inv ≫ F.map d) ≫ F.map π =
      SchemeModuleGlobalSections.sectionHom (F.obj (quotient f g n J hJ q))
        ((pulledQuotientDifferentialSection f g n h J hJ q).val.app (.op ⊤) b) := by
    have hs := SchemeModuleGlobalSections.sectionHom_comp
      (M := Scheme.Modules.unitObj Z) b (pulledQuotientDifferentialSection f g n h J hJ q)
    simpa only [pulledQuotientDifferentialSection, quotientDifferentialSection,
      Functor.map_comp, Category.assoc, r, d, F, π] using hs
  constructor
  · intro hb
    apply hm.lift' (r ≫ (Scheme.Modules.pullbackUnitIso h).inv ≫ F.map d)
    exact hc.trans ((sectionHom_eq_zero_iff _ _).mpr hb)
  · rintro ⟨s, hs⟩
    apply (sectionHom_eq_zero_iff _ _).mp
    rw [← hc, ← hs, Category.assoc, ← F.map_comp, relativeRoundedInclusion_quotientProjection,
      F.map_zero, comp_zero]


/-- EVERY original chart coefficient in the SAME pulled global quotient is
measured by factorization of the whole pulled ORIGINAL absolute differential. -/
theorem pulledQuotientDifferentialSection_apply_eq_zero_iff_pulledFactorization
    (b : Γ(Z, ⊤)) :
    (pulledQuotientDifferentialSection f g n h J hJ q).val.app (.op ⊤) b = 0 ↔
      ∃ θ : (Scheme.Modules.pullback h).obj
          ((Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)) ⟶
          (Scheme.Modules.pullback h).obj (absolute (g ≫ f) n J hJ q),
        θ ≫ (Scheme.Modules.pullback h).map (absoluteRoundedInclusion (g ≫ f) n J hJ q) =
          SchemeUnitScalarAction.globalScalarAction (X := Z)
            ((Scheme.Modules.pullback h).obj
              ((Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n))) b ≫
              (Scheme.Modules.pullback h).map
                (CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n) := by
  let A := (Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)
  let B := CanonicalGeometry.canonicalLineSheaf (g ≫ f) n
  let hA := (CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g
  let I := idealModule J hJ q
  let i := idealModuleInclusion J hJ q
  let φ := CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n
  exact (pulledQuotientDifferentialSection_apply_eq_zero_iff_lift f g n h J hJ q b).trans
    (homSectionPullbackIso_scalar_idealLift_iff h A hA B I i φ b)


private theorem factorizationIso {W : Scheme.{u}}
    {A A' B B' I I' : W.Modules} (eA : A' ≅ A) (eB : B ≅ B') (eI : I ≅ I')
    (inc : I ⟶ B) (inc' : I' ⟶ B') (hs : eI.hom ≫ inc' = inc ≫ eB.hom)
    (δ : A ⟶ B) :
    (∃ θ : A ⟶ I, θ ≫ inc = δ) ↔
      ∃ θ : A' ⟶ I', θ ≫ inc' = eA.hom ≫ δ ≫ eB.hom := by
  constructor
  · rintro ⟨θ, hθ⟩
    refine ⟨eA.hom ≫ θ ≫ eI.hom, ?_⟩
    simp only [Category.assoc]
    rw [hs, ← Category.assoc θ inc, hθ]
  · rintro ⟨θ, hθ⟩
    refine ⟨eA.inv ≫ θ ≫ eI.inv, ?_⟩
    apply (cancel_mono eB.hom).mp
    have hi : eI.inv ≫ inc ≫ eB.hom = inc' := by
      rw [← hs, Iso.inv_hom_id_assoc]
    simp only [Category.assoc]
    rw [hi, hθ, Iso.inv_hom_id_assoc]

private theorem absoluteInclusionCongr {W : Scheme.{u}}
    (f₁ f₂ : W ⟶ Spec (.of k)) (e : f₁ = f₂) (n : ℕ)
    (J : W.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (eqToIso (congrArg (fun t => absolute t n J hJ q) e)).hom ≫
      absoluteRoundedInclusion f₂ n J hJ q =
      absoluteRoundedInclusion f₁ n J hJ q ≫
        (eqToIso (congrArg (fun t => CanonicalGeometry.canonicalLineSheaf t n) e)).hom := by
  cases e
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

private theorem compositeSquare {W : Scheme.{u}} {A₀ A₁ A₂ B₀ B₁ B₂ : W.Modules}
    (e₀ : A₀ ⟶ A₁) (e₁ : A₁ ⟶ A₂) (i₀ : A₀ ⟶ B₀)
    (i₁ : A₁ ⟶ B₁) (i₂ : A₂ ⟶ B₂) (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂)
    (h₀ : e₀ ≫ i₁ = i₀ ≫ b₀) (h₁ : e₁ ≫ i₂ = i₁ ≫ b₁) :
    (e₀ ≫ e₁) ≫ i₂ = i₀ ≫ b₀ ≫ b₁ := by
  rw [Category.assoc, h₁, ← Category.assoc, h₀, Category.assoc]

private theorem scalarNaturality {W : Scheme.{u}} {A B : W.Modules}
    (b : Γ(W, ⊤)) (ψ : A ⟶ B) :
    SchemeUnitScalarAction.globalScalarAction A b ≫ ψ =
      ψ ≫ SchemeUnitScalarAction.globalScalarAction B b := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change ψ.val.app (.op U) ((SchemeUnitScalarAction.globalScalarAction A b).val.app (.op U) m) =
    (SchemeUnitScalarAction.globalScalarAction B b).val.app (.op U) (ψ.val.app (.op U) m)
  rw [SchemeUnitScalarAction.globalScalarAction_apply,
    SchemeUnitScalarAction.globalScalarAction_apply]
  exact (ψ.val.app (.op U)).hom.map_smul _ _

private theorem scalarComposite {W : Scheme.{u}} {A' A B B' : W.Modules}
    (e : A' ⟶ A) (s : A ⟶ A) (s' : A' ⟶ A')
    (d : A ⟶ B) (b : B ⟶ B') (d' : A' ⟶ B')
    (hs : s' ≫ e = e ≫ s) (hd : e ≫ d ≫ b = d') :
    e ≫ (s ≫ d) ≫ b = s' ≫ d' := by
  simp only [Category.assoc]
  rw [← Category.assoc e s, ← hs]
  simpa only [Category.assoc] using congrArg (fun t => s' ≫ t) hd

/-- EVERY coefficient of the SAME pulled original global quotient has exactly the
original open-composite vanishing criterion. No reconstructed quotient is substituted. -/
theorem pulledQuotientDifferentialSection_apply_eq_zero_iff_openComposite [CharZero k]
    (b : Γ(Z, ⊤)) :
    letI : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
    (pulledQuotientDifferentialSection f g n h J hJ q).val.app (.op ⊤) b = 0 ↔
      (quotientDifferentialSection f (h ≫ g) n (J.comap h)
        (hJ.comap_of_smooth (g ≫ f) h) q).val.app (.op ⊤) b = 0 := by
  let : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
  let : SmoothOfRelativeDimension n ((h ≫ g) ≫ f) := by
    rw [Category.assoc]
    exact (Nat.zero_add n) ▸
      (smoothOfRelativeDimension_comp (f := h) (n := 0) (m := n) (g ≫ f))
  let F := Scheme.Modules.pullback h
  let A := (Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)
  let B := CanonicalGeometry.canonicalLineSheaf (g ≫ f) n
  let d : A ⟶ B := CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n
  let I := absolute (g ≫ f) n J hJ q
  let inc := absoluteRoundedInclusion (g ≫ f) n J hJ q
  let JL := J.comap h
  let hJL := hJ.comap_of_smooth (g ≫ f) h
  let eA := (Scheme.Modules.pullbackComp h g).symm.app (CanonicalGeometry.canonicalLineSheaf f n)
  let eS := (Category.assoc h g f).symm
  let δh := CanonicalGeometry.exteriorCotangentSheafPullbackMap (g ≫ f) h n
  let : IsIso δh := CanonicalGeometry.isIso_exteriorCotangentSheafPullbackMap_openImmersion
    (g ≫ f) h n
  let eB := asIso δh ≪≫ eqToIso (congrArg (fun t => CanonicalGeometry.canonicalLineSheaf t n) eS)
  let eI := absoluteOpenPullbackIso (g ≫ f) h n J hJ q ≪≫
    eqToIso (congrArg (fun t => absolute t n JL hJL q) eS)
  have hs : eI.hom ≫ absoluteRoundedInclusion ((h ≫ g) ≫ f) n JL hJL q =
      F.map inc ≫ eB.hom := by
    have he := absoluteInclusionCongr (W := Z) (h ≫ (g ≫ f)) ((h ≫ g) ≫ f) eS n JL hJL q
    have ho := absoluteOpenPullbackIso_inclusion (g ≫ f) h n J hJ q
    exact compositeSquare (W := Z) _ _ _ _ _ _ _ ho he
  have hd : eA.hom ≫ F.map d ≫ eB.hom =
      CanonicalGeometry.exteriorCotangentSheafPullbackMap f (h ≫ g) n :=
    (CanonicalGeometry.exteriorCotangentSheafPullbackMap_comp f g h n).symm
  have ha := scalarNaturality (W := Z) b eA.hom
  have hδ : eA.hom ≫ (SchemeUnitScalarAction.globalScalarAction (X := Z) (F.obj A) b ≫ F.map d) ≫ eB.hom =
      SchemeUnitScalarAction.globalScalarAction (X := Z) _ b ≫
        CanonicalGeometry.exteriorCotangentSheafPullbackMap f (h ≫ g) n := by
    exact scalarComposite (W := Z) _ _ _ _ _ _ ha hd
  have hf := factorizationIso (W := Z) eA eB eI (F.map inc)
    (absoluteRoundedInclusion ((h ≫ g) ≫ f) n JL hJL q) hs
    (SchemeUnitScalarAction.globalScalarAction (X := Z) (F.obj A) b ≫ F.map d)
  rw [hδ] at hf
  exact (pulledQuotientDifferentialSection_apply_eq_zero_iff_pulledFactorization f g n h J hJ q b).trans
    (hf.trans (quotientDifferentialSection_apply_eq_zero_iff_factorization
      f (h ≫ g) n JL hJL q b).symm)

end EnvelopeProperty.Char0.AffineOpenGlobalRoundedKernel
