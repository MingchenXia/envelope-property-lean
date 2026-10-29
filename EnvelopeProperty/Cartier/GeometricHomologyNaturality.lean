import EnvelopeProperty.Cartier.GeometricAffineHomology
import EnvelopeProperty.Cartier.GeometricCotangentRestrictions
import EnvelopeProperty.AlgGeom.AffineOpenCanonicalSectionHomology
import EnvelopeProperty.AlgGeom.SchemeSectionHomologyRestriction

/-! # Canonical homology comparison and original geometric restrictions -/

noncomputable section
namespace EnvelopeProperty.Cartier.GeometricHomologyNaturality
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u

section Identity
universe v' u'
variable {C : Type u'} [Category.{v'} C] [Abelian C]

private theorem comparison_id (S : ShortComplex C) :
    LeftExactHomologyComparison.map S (𝟭 C) = 𝟙 S.homology := by
  have hc : (LeftExactHomologyComparison.cyclesIso S (𝟭 C)).hom = 𝟙 S.cycles := by
    apply (cancel_mono S.iCycles).mp
    exact (LeftExactHomologyComparison.cyclesIso_hom_iCycles S (𝟭 C)).trans
      (Category.id_comp S.iCycles).symm
  apply (cancel_epi S.homologyπ).mp
  exact (LeftExactHomologyComparison.homologyπ_map S (𝟭 C)).trans
    ((congrArg (fun a : S.cycles ⟶ S.cycles => a ≫ S.homologyπ) hc).trans
      ((Category.id_comp S.homologyπ).trans (Category.comp_id S.homologyπ).symm))
end Identity

section Composition
universe v' u'
variable {C : Type u'} [Category.{v'} C]

private theorem follow_three {a b c d e f g : C}
    {l : a ⟶ b} {r : b ⟶ c} {l' : a ⟶ d} {r' : d ⟶ c}
    (h : l ≫ r = l' ≫ r') (u : c ⟶ e) (v : e ⟶ f) (w : f ⟶ g) :
    l ≫ (r ≫ u ≫ v) ≫ w = l' ≫ (r' ≫ u) ≫ v ≫ w := by
  simpa only [Category.assoc] using congrArg (fun x => x ≫ u ≫ v ≫ w) h

private theorem pre_post {a b c d e : C} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (h : f ≫ g = k) (l : d ⟶ a) (r : c ⟶ e) :
    l ≫ f ≫ g ≫ r = l ≫ (k ≫ r) := by
  simpa only [Category.assoc] using congrArg (fun x => l ≫ x ≫ r) h
end Composition

private instance gammaAdditive (A : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := A)).Additive where
  map_add := by intro M N a b; rfl

private instance gammaZero (A : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := A)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private instance tildeZero (A : CommRingCat.{u}) :
    (tilde.functor A).PreservesZeroMorphisms where
  map_zero _ _ := AlgebraicGeometry.tilde.map_zero

private instance gammaLimits (A : CommRingCat.{u}) :
    PreservesFiniteLimits (moduleSpecΓFunctor (R := A)) := by
  let : (moduleSpecΓFunctor (R := A)).IsRightAdjoint := (tilde.adjunction (R := A)).isRightAdjoint
  infer_instance

private instance tildeLimits (A : CommRingCat.{u}) : PreservesFiniteLimits (tilde.functor A) :=
  TildeExactness.preservesFiniteLimits A

private instance tildeHomology (A : CommRingCat.{u}) : (tilde.functor A).PreservesHomology :=
  TildeExactness.preservesHomology A

/-- The entire original tilde/counit homology transport has exactly the canonical forward map. -/
theorem affineCounitHomology_canonical (A : CommRingCat.{u})
    (K : CochainComplex (Spec A).Modules ℕ) [∀ r, (K.X r).IsQuasicoherent] (q : ℕ) :
    (tilde.isoTop ((AffineQuasicoherentComplexHomology.sectionComplex A K).homology q)).hom ≫
        (moduleSpecΓFunctor (R := A)).map (AffineQuasicoherentComplexHomology.homologyIso A K q).hom =
      LeftExactHomologyComparison.map (K.sc q) (moduleSpecΓFunctor (R := A)) := by
  let S := K.sc q
  let G := moduleSpecΓFunctor (R := A)
  let L := tilde.functor A
  let ε := (tilde.adjunction (R := A)).counit
  let μ := (S.map G).mapHomologyIso L
  let : (G ⋙ L).PreservesZeroMorphisms :=
    ⟨fun M N => (congrArg L.map (G.map_zero M N)).trans (L.map_zero _ _)⟩
  let : PreservesFiniteLimits (G ⋙ L) := comp_preservesFiniteLimits G L
  have hcomp : LeftExactHomologyComparison.map S (G ⋙ L) =
      μ.hom ≫ L.map (LeftExactHomologyComparison.map S G) :=
    (LeftExactHomologyCoherence.map_comp S G L).trans
      (congrArg (fun a => a ≫ L.map (LeftExactHomologyComparison.map S G))
        (LeftExactHomologyCoherence.map_eq_mapHomologyIso (S.map G) L))
  have hn₀ := LeftExactHomologyComparison.natTrans_naturality (S := S) (𝟭 (Spec A).Modules) ε
  let Hε := ShortComplex.homologyMap (S.mapNatTrans ε)
  have hn : Hε = μ.hom ≫ (L.map (LeftExactHomologyComparison.map S G) ≫ ε.app S.homology) :=
    (Category.comp_id Hε).symm.trans
      ((congrArg (fun a : (S.map (𝟭 (Spec A).Modules)).homology ⟶ S.homology => Hε ≫ a)
        (comparison_id S)).symm.trans
        (hn₀.trans ((congrArg (fun a => a ≫ ε.app S.homology) hcomp).trans
          (Category.assoc _ _ _))))
  have hm : (AffineQuasicoherentComplexHomology.homologyIso A K q).hom =
      L.map (LeftExactHomologyComparison.map S G) ≫ ε.app S.homology := by
    change μ.inv ≫ Hε = _
    exact (congrArg (fun a => μ.inv ≫ a) hn).trans (μ.inv_hom_id_assoc _)
  change (tilde.adjunction (R := A)).homEquiv _ _
      (AffineQuasicoherentComplexHomology.homologyIso A K q).hom = _
  exact (congrArg ((tilde.adjunction (R := A)).homEquiv _ _) hm).trans
    ((tilde.adjunction (R := A)).homEquiv _ _ |>.apply_symm_apply
      (LeftExactHomologyComparison.map S G))

private instance evaluationZero {Z : Scheme.{u}} (W : Z.Opens) :
    (SheafOfModules.evaluation Z.ringCatSheaf (op W)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private instance evaluationLimits {Z : Scheme.{u}} (W : Z.Opens) :
    PreservesFiniteLimits (SheafOfModules.evaluation Z.ringCatSheaf (op W)) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := Z.ringCatSheaf) (op W)

private instance chartGammaZero {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W) :
    (Scheme.Modules.restrictFunctor hW.fromSpec ⋙
      moduleSpecΓFunctor (R := Γ(Z, W))).PreservesZeroMorphisms where
  map_zero M N :=
    (congrArg (moduleSpecΓFunctor (R := Γ(Z, W))).map
      ((Scheme.Modules.restrictFunctor hW.fromSpec).map_zero M N)).trans
        ((moduleSpecΓFunctor (R := Γ(Z, W))).map_zero _ _)

private instance chartGammaLimits {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W) :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor hW.fromSpec ⋙
      moduleSpecΓFunctor (R := Γ(Z, W))) := by
  let : PreservesLimits (Scheme.Modules.restrictFunctor hW.fromSpec) :=
    Scheme.Modules.restrictFunctor_preservesLimits hW.fromSpec
  exact comp_preservesFiniteLimits _ _

private theorem moduleSectionsIso_hom_eq {Z : Scheme.{u}} {W : Z.Opens}
    (hW : IsAffineOpen W) (M : Z.Modules) :
    (GeometricAffineHomology.moduleSectionsIso hW M).hom =
      (AffineRestrictionSections.sectionsIso hW M).hom := by
  let : Module Γ(Z, W) (M.val.obj (op W)) := (M.val.obj (op W)).isModule
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem sectionComplexIso_hom_eq {Z : Scheme.{u}} {W : Z.Opens}
    (hW : IsAffineOpen W) (K : CochainComplex Z.Modules ℕ) :
    (GeometricAffineHomology.sectionComplexIso hW K).hom =
      (AffineRestrictionSections.complexIso hW K).hom := by
  apply HomologicalComplex.Hom.ext
  funext r
  exact moduleSectionsIso_hom_eq hW (K.X r)

/-- The frozen geometric comparison is the same entire original canonical evaluation map. -/
theorem homologySectionsIso_hom_eq {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)
    (K : CochainComplex Z.Modules ℕ) [∀ r, (K.X r).IsQuasicoherent] (q : ℕ) :
    (GeometricAffineHomology.homologySectionsIso hW K q).hom =
      SchemeSectionHomology.comparison K W q := by
  let A := Z.presheaf.obj (op W)
  let j := hW.fromSpec
  let S := K.sc q
  let F : Z.Modules ⥤ (Spec A).Modules := Scheme.Modules.restrictFunctor j
  let G : (Spec A).Modules ⥤ ModuleCat A := moduleSpecΓFunctor (R := A)
  let L : ModuleCat A ⥤ (Spec A).Modules := tilde.functor A
  let E : Z.Modules ⥤ ModuleCat A := SheafOfModules.evaluation Z.ringCatSheaf (op W)
  let : E.Additive := ⟨by intro M N a b; rfl⟩
  let : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := Z.ringCatSheaf) (op W)
  let : PreservesLimits F := Scheme.Modules.restrictFunctor_preservesLimits j
  let : F.PreservesHomology := SchemeOpenRestrictionHomology.preservesHomology j
  let : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
  let : (F ⋙ G).PreservesZeroMorphisms :=
    ⟨fun M N => (congrArg G.map (F.map_zero M N)).trans (G.map_zero _ _)⟩
  let KC := SchemeOpenRestrictionHomology.restrictedComplex j K
  let : ∀ r, (KC.X r).IsQuasicoherent := by
    intro r
    let : (K.X r).IsQuasicoherent := (inferInstance : ∀ a, (K.X a).IsQuasicoherent) r
    change ((K.X r).restrict j).IsQuasicoherent
    infer_instance
  let EV := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let eΓ := (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q).mapIso
    (GeometricAffineHomology.sectionComplexIso hW K)
  let β := AffineRestrictionSections.functorIso hW
  have hn₀ := LeftExactHomologyComparison.natTrans_naturality (S := S) E β.hom
  have hsc : ShortComplex.homologyMap (S.mapNatTrans β.hom) = eΓ.hom := by
    change HomologicalComplex.homologyMap (AffineRestrictionSections.complexIso hW K).hom q =
      HomologicalComplex.homologyMap (GeometricAffineHomology.sectionComplexIso hW K).hom q
    exact congrArg (fun a => HomologicalComplex.homologyMap a q) (sectionComplexIso_hom_eq hW K).symm
  have hβ : eΓ.hom ≫ SchemeSectionHomology.comparison K W q =
      LeftExactHomologyComparison.map S (F ⋙ G) ≫
        (GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom :=
    (congrArg (fun a => a ≫ SchemeSectionHomology.comparison K W q) hsc.symm).trans
      (hn₀.trans (congrArg (fun a => LeftExactHomologyComparison.map S (F ⋙ G) ≫ a)
        (moduleSectionsIso_hom_eq hW (K.homology q)).symm))
  have hη : eΓ.inv ≫
        (tilde.isoTop ((AffineQuasicoherentComplexHomology.sectionComplex A KC).homology q)).hom =
      (tilde.isoTop (EV.homology q)).hom ≫ G.map (L.map eΓ.inv) :=
    (tilde.toTildeΓNatIso (R := A)).hom.naturality eΓ.inv
  have hfrozen : (GeometricAffineHomology.homologySectionsIso hW K q).hom =
      eΓ.inv ≫
        ((tilde.isoTop ((AffineQuasicoherentComplexHomology.sectionComplex A KC).homology q)).hom ≫
          G.map (AffineQuasicoherentComplexHomology.homologyIso A KC q).hom) ≫
        G.map (SchemeOpenRestrictionHomology.homologyIso j K q).hom ≫
        (GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom := by
    change (tilde.isoTop (EV.homology q)).hom ≫
      G.map (L.map eΓ.inv ≫ (AffineQuasicoherentComplexHomology.homologyIso A KC q).hom ≫
        (SchemeOpenRestrictionHomology.homologyIso j K q).hom) ≫
        (GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom = _
    have hmap : G.map (L.map eΓ.inv ≫
        (AffineQuasicoherentComplexHomology.homologyIso A KC q).hom ≫
        (SchemeOpenRestrictionHomology.homologyIso j K q).hom) =
        G.map (L.map eΓ.inv) ≫
          G.map (AffineQuasicoherentComplexHomology.homologyIso A KC q).hom ≫
          G.map (SchemeOpenRestrictionHomology.homologyIso j K q).hom :=
      (G.map_comp (L.map eΓ.inv) _).trans
        (congrArg (fun a => G.map (L.map eΓ.inv) ≫ a)
          (G.map_comp (AffineQuasicoherentComplexHomology.homologyIso A KC q).hom
            (SchemeOpenRestrictionHomology.homologyIso j K q).hom))
    exact (congrArg (fun a => (tilde.isoTop (EV.homology q)).hom ≫ a ≫
      (GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom) hmap).trans
        (follow_three (C := ModuleCat A) hη.symm
          (G.map (AffineQuasicoherentComplexHomology.homologyIso A KC q).hom)
          (G.map (SchemeOpenRestrictionHomology.homologyIso j K q).hom)
          (GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom)

  have hF : (SchemeOpenRestrictionHomology.homologyIso j K q).hom =
      LeftExactHomologyComparison.map S F :=
    (LeftExactHomologyCoherence.map_eq_mapHomologyIso S F).symm
  have hm : ((tilde.isoTop ((AffineQuasicoherentComplexHomology.sectionComplex A KC).homology q)).hom ≫
        G.map (AffineQuasicoherentComplexHomology.homologyIso A KC q).hom) ≫
        G.map (SchemeOpenRestrictionHomology.homologyIso j K q).hom =
      LeftExactHomologyComparison.map S (F ⋙ G) :=
    (congrArg (fun a => a ≫ G.map (SchemeOpenRestrictionHomology.homologyIso j K q).hom)
      (affineCounitHomology_canonical A KC q)).trans
      ((congrArg (fun a => LeftExactHomologyComparison.map (S.map F) G ≫ G.map a) hF).trans
        (LeftExactHomologyCoherence.map_comp S F G).symm)
  have hfinal : (GeometricAffineHomology.homologySectionsIso hW K q).hom =
      eΓ.inv ≫ (LeftExactHomologyComparison.map S (F ⋙ G) ≫
        (GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom) :=
    hfrozen.trans (pre_post hm eΓ.inv
      (GeometricAffineHomology.moduleSectionsIso hW (K.homology q)).hom)
  exact hfinal.trans ((congrArg (fun a => eΓ.inv ≫ a) hβ.symm).trans (eΓ.inv_hom_id_assoc _))

/-- The whole frozen affine homology comparison commutes with genuine original open restriction. -/
theorem homologySectionsIso_restrict {Z : Scheme.{u}} {U V : Z.Opens} (i : U ⟶ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (K : CochainComplex Z.Modules ℕ) [∀ r, (K.X r).IsQuasicoherent] (q : ℕ) :
    SchemeSectionHomologyRestriction.restrictionHomologyMap K i q ≫
        (ModuleCat.restrictScalars (Z.presheaf.map i.op).hom).map
          (GeometricAffineHomology.homologySectionsIso hU K q).hom =
      (GeometricAffineHomology.homologySectionsIso hV K q).hom ≫ (K.homology q).val.map i.op := by
  rw [homologySectionsIso_hom_eq, homologySectionsIso_hom_eq]
  exact SchemeSectionHomologyRestriction.comparison_restriction K i q

end EnvelopeProperty.Cartier.GeometricHomologyNaturality
