import EnvelopeProperty.AlgGeom.SchemeModuleMorphismGluing
import ModularCurves.EllipticCurve.PoleSheaf

/-! # Genuine coefficient-preserving comparisons from matching original frame transitions -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleFrameGluing

private theorem comparison_eq_of_common_transition
    {C : Type*} [Category C] {A B T : C}
    (e e' : A ≅ T) (g g' : B ≅ T) (c : T ⟶ T)
    (he : e.hom = e'.hom ≫ c) (hg : g.hom = g'.hom ≫ c) :
    e ≪≫ g.symm = e' ≪≫ g'.symm := by
  apply Iso.ext
  apply (cancel_mono g.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hg]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he

variable {X : Scheme.{u}} (M N : X.Modules)

/-- The original coefficient-preserving comparison of two genuine local frames. -/
def frameComparison (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme)
    (g : N.restrict U.ι ≅ unitObj U.toScheme) : M.over U ≅ N.over U :=
  overTrivializationOfRestrictIso M U e ≪≫
    (overTrivializationOfRestrictIso N U g).symm

/-- A common transition of the ACTUAL original frame maps cancels in their
whole original coefficient-preserving comparison. -/
theorem frameComparison_eq_of_common_transition (U : X.Opens)
    (e e' : M.restrict U.ι ≅ unitObj U.toScheme)
    (g g' : N.restrict U.ι ≅ unitObj U.toScheme)
    (c : unitObj U.toScheme ⟶ unitObj U.toScheme)
    (he : e.hom = e'.hom ≫ c) (hg : g.hom = g'.hom ≫ c) :
    frameComparison M N U e g = frameComparison M N U e' g' := by
  have h := congrArg Iso.hom (comparison_eq_of_common_transition e e' g g' c he hg)
  apply Iso.ext
  apply (overEquiv U).functor.map_injective
  simp only [frameComparison, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    overTrivializationOfRestrictIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.map_preimage,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  exact congrArg (fun t => (overFunctorEquiv U).hom.app M ≫ t ≫
    (overFunctorEquiv U).inv.app N) h

/-- Restriction preserves the SAME original frame comparison, with all actual
site and open-subscheme comparisons retained. -/
theorem frameComparison_restrict {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme)
    (g : N.restrict U.ι ≅ unitObj U.toScheme) :
    SchemeModuleMorphismGluing.bundleHomRestrictionIso M N (homOfLE h)
        (frameComparison M N U e g) =
      frameComparison M N V (restrictOpenTrivialization h e)
        (restrictOpenTrivialization h g) := by
  unfold frameComparison
  rw [overTrivializationOfRestrictOpenTrivialization,
    overTrivializationOfRestrictOpenTrivialization]
  apply Iso.ext
  simp only [SchemeModuleMorphismGluing.bundleHomRestrictionIso,
    ModularCurves.SheafOfModules.restrictOverTrivialization,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.symm_inv]
  rfl

/-- Genuinely matching original frame transitions construct an ACTUAL whole
original module isomorphism, deriving the original overlap comparison equalities. -/
def glueOfFrames {ι : Type*} (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (htrans : ∀ i j, ∃ c : unitObj (U i ⊓ U j).toScheme ⟶ unitObj (U i ⊓ U j).toScheme,
      (restrictOpenTrivialization (inf_le_left : U i ⊓ U j ≤ U i) (e i)).hom =
        (restrictOpenTrivialization (inf_le_right : U i ⊓ U j ≤ U j) (e j)).hom ≫ c ∧
      (restrictOpenTrivialization (inf_le_left : U i ⊓ U j ≤ U i) (g i)).hom =
        (restrictOpenTrivialization (inf_le_right : U i ⊓ U j ≤ U j) (g j)).hom ≫ c) :
    M ≅ N := by
  refine SchemeModuleMorphismGluing.bundleGlueIso M N U hcover
    (fun i => frameComparison M N (U i) (e i) (g i)) ?_
  intro i j
  have hleft := congrArg Iso.hom
    (frameComparison_restrict M N (inf_le_left : U i ⊓ U j ≤ U i) (e i) (g i))
  have hright := congrArg Iso.hom
    (frameComparison_restrict M N (inf_le_right : U i ⊓ U j ≤ U j) (e j) (g j))
  obtain ⟨c, he, hg⟩ := htrans i j
  exact hleft.trans ((congrArg Iso.hom
    (frameComparison_eq_of_common_transition M N _ _ _ _ _ c he hg)).trans hright.symm)

/-- The actual whole isomorphism retains every original coefficient-preserving local frame comparison. -/
theorem glueOfFrames_restrict {ι : Type*} (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (htrans : ∀ i j, ∃ c : unitObj (U i ⊓ U j).toScheme ⟶ unitObj (U i ⊓ U j).toScheme,
      (restrictOpenTrivialization (inf_le_left : U i ⊓ U j ≤ U i) (e i)).hom =
        (restrictOpenTrivialization (inf_le_right : U i ⊓ U j ≤ U j) (e j)).hom ≫ c ∧
      (restrictOpenTrivialization (inf_le_left : U i ⊓ U j ≤ U i) (g i)).hom =
        (restrictOpenTrivialization (inf_le_right : U i ⊓ U j ≤ U j) (g j)).hom ≫ c) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso
        (glueOfFrames M N U hcover e g htrans) = frameComparison M N (U i) (e i) (g i) := by
  unfold glueOfFrames
  apply SchemeModuleMorphismGluing.bundleGlueIso_restrict

end EnvelopeProperty.SchemeModuleFrameGluing
