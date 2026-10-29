import EnvelopeProperty.Cartier.GeometricComplexExchange
import EnvelopeProperty.Cartier.GeometricLocalCartier
import EnvelopeProperty.Cartier.GeometricRelativeFrobeniusQuasicoherent
import EnvelopeProperty.AlgGeom.AffineQuasicoherentComplexHomology
import EnvelopeProperty.AlgGeom.SchemeOpenRestrictionHomology

/-! # Actual affine evaluation and native homology of the original geometric complex -/

noncomputable section
namespace EnvelopeProperty.Cartier.GeometricAffineHomology
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u

variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W)
local notation "A" => Z.presheaf.obj (op W)
local notation "j" => hW.fromSpec

private theorem imageTop : (j) ''ᵁ (⊤ : (Spec A).Opens) = W := by
  simp

private theorem fromSpec_appLE_top :
    (j).appLE W ⊤ hW.fromSpec_preimage_self.symm.le = (Scheme.ΓSpecIso A).inv := by
  let P := (Spec A).presheaf
  let e : (⊤ : (Spec A).Opens) ≤ (j) ⁻¹ᵁ W := hW.fromSpec_preimage_self.symm.le
  have hc : P.map (eqToHom hW.fromSpec_preimage_self).op ≫
      P.map (homOfLE e).op = 𝟙 (P.obj (op ⊤)) :=
    (P.map_comp _ _).symm.trans ((congrArg P.map
      (show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op =
        𝟙 (op (⊤ : (Spec A).Opens)) from Subsingleton.elim _ _)).trans (P.map_id _))
  have hf := congrArg
    (fun a : A ⟶ P.obj (op ((j) ⁻¹ᵁ W)) => a ≫ P.map (homOfLE e).op)
      hW.fromSpec_app_self
  exact hf.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun a => (Scheme.ΓSpecIso A).inv ≫ a) hc).trans (Category.comp_id _)))

private theorem scalarTriangle :
    (Scheme.ΓSpecIso A).inv ≫ ((j).appIso ⊤).inv ≫
      Z.presheaf.map (eqToHom (imageTop hW).symm).op = 𝟙 A := by
  let e : (⊤ : (Spec A).Opens) ≤ (j) ⁻¹ᵁ W := hW.fromSpec_preimage_self.symm.le
  let t := Z.presheaf.map (eqToHom (imageTop hW).symm).op
  have hs := congrArg
    (fun a : A ⟶ Γ(Z, (j) ''ᵁ (⊤ : (Spec A).Opens)) => a ≫ t)
      (Scheme.Hom.appLE_appIso_inv (j) e)
  have hc (a : op W ⟶ op ((j) ''ᵁ (⊤ : (Spec A).Opens))) :
      Z.presheaf.map a ≫ t = 𝟙 A :=
    (Z.presheaf.map_comp _ _).symm.trans ((congrArg Z.presheaf.map
      (show a ≫ (eqToHom (imageTop hW).symm).op = 𝟙 (op W) from
        Subsingleton.elim _ _)).trans (Z.presheaf.map_id _))
  change (Scheme.ΓSpecIso A).inv ≫ ((j).appIso ⊤).inv ≫ t = 𝟙 A
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a : A ⟶ Γ(Spec A, ⊤) => (a ≫ ((j).appIso ⊤).inv) ≫ t)
      (fromSpec_appLE_top hW).symm).trans (hs.trans (hc _)))

/-- The original affine-chart restriction has exactly the original sections and scalar action. -/
def moduleSectionsIso (M : Z.Modules) :
    (moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.restrictFunctor (j)).obj M) ≅
      M.val.obj (op W) := by
  let i := eqToHom (imageTop hW).symm
  letI : Module A (M.val.obj (op W)) := (M.val.obj (op W)).isModule
  letI : Module Γ(Z, (j) ''ᵁ (⊤ : (Spec A).Opens))
      ((moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.restrictFunctor (j)).obj M)) :=
    (M.val.obj (op ((j) ''ᵁ (⊤ : (Spec A).Opens)))).isModule
  let L : (moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.restrictFunctor (j)).obj M) →ₗ[A]
      M.val.obj (op W) :=
    { toFun := M.presheaf.map i.op
      map_add' := (M.presheaf.map i.op).hom.map_add
      map_smul' := by
        intro r s
        change M.presheaf.map i.op
          (((j).appIso ⊤).inv.hom
            (((Spec A).presheaf.map (𝟙 (op (⊤ : (Spec A).Opens)))).hom
              ((Scheme.ΓSpecIso A).inv.hom r)) • s) = r • M.presheaf.map i.op s
        have hid := ConcreteCategory.congr_hom ((Spec A).presheaf.map_id (op ⊤))
          ((Scheme.ΓSpecIso A).inv.hom r)
        have he := congrArg (fun a : Γ(Spec A, ⊤) =>
          M.presheaf.map i.op ((((j).appIso ⊤).inv.hom a) • s)) hid
        have hs := M.map_smul i (((j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso A).inv.hom r)) s
        have hr := ConcreteCategory.congr_hom (scalarTriangle hW) r
        exact he.trans (hs.trans (congrArg (fun a : A => a • M.presheaf.map i.op s) hr)) }
  exact (LinearEquiv.ofBijective L
    (ConcreteCategory.bijective_of_isIso (M.presheaf.map i.op))).toModuleIso

/-- Every original section is its exact original open-transport restriction. -/
theorem moduleSectionsIso_apply (M : Z.Modules)
    (s : (moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.restrictFunctor (j)).obj M)) :
    (moduleSectionsIso hW M).hom.hom s =
      M.presheaf.map (eqToHom (imageTop hW).symm).op s := rfl

private def moduleSectionsNatIso :
    Scheme.Modules.restrictFunctor (j) ⋙ moduleSpecΓFunctor (R := A) ≅
      SheafOfModules.evaluation Z.ringCatSheaf (op W) := by
  refine NatIso.ofComponents (moduleSectionsIso hW) ?_
  intro M N φ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (eqToHom (imageTop hW).symm).op) s).symm

/-- The original chart-section components give the entire native section-complex isomorphism. -/
def sectionComplexIso (K : CochainComplex Z.Modules ℕ) :
    AffineQuasicoherentComplexHomology.sectionComplex A
        (SchemeOpenRestrictionHomology.restrictedComplex (j) K) ≅
      ((SheafOfModules.evaluation Z.ringCatSheaf (op W)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q => moduleSectionsIso hW (K.X q)) ?_
  intro q r _
  exact ((moduleSectionsNatIso hW).hom.naturality (K.d q r)).symm

/-- Every degree component is exactly the original section and open-transport isomorphism. -/
theorem sectionComplexIso_hom_f_apply (K : CochainComplex Z.Modules ℕ) (q : ℕ)
    (s : (moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.restrictFunctor (j)).obj (K.X q))) :
    ((sectionComplexIso hW K).hom.f q).hom s = (moduleSectionsIso hW (K.X q)).hom.hom s := rfl

/-- Actual homology of sections equals sections of the same actual global homology sheaf. -/
def homologySectionsIso (K : CochainComplex Z.Modules ℕ)
    [∀ q, (K.X q).IsQuasicoherent] (q : ℕ) :
    (((SheafOfModules.evaluation Z.ringCatSheaf (op W)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q ≅ (K.homology q).val.obj (op W) := by
  let KC := SchemeOpenRestrictionHomology.restrictedComplex (j) K
  let : ∀ r, (KC.X r).IsQuasicoherent := by
    intro r
    let : (K.X r).IsQuasicoherent := (inferInstance : ∀ a, (K.X a).IsQuasicoherent) r
    change ((K.X r).restrict (j)).IsQuasicoherent
    infer_instance
  let EV := ((SheafOfModules.evaluation Z.ringCatSheaf (op W)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K
  let eΓ := (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q).mapIso
    (sectionComplexIso hW K)
  let eH : tilde (EV.homology q) ≅ (Scheme.Modules.restrictFunctor (j)).obj (K.homology q) :=
    (tilde.functor A).mapIso eΓ.symm ≪≫
      AffineQuasicoherentComplexHomology.homologyIso A KC q ≪≫
        SchemeOpenRestrictionHomology.homologyIso (j) K q
  exact tilde.isoTop (EV.homology q) ≪≫
    (moduleSpecΓFunctor (R := A)).mapIso eH ≪≫ moduleSectionsIso hW (K.homology q)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
variable {U : X.Opens} (hU : IsAffineOpen U)
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "WU" => RelativeTwistedAffineBasis.twistedOpen f p U
local notation "Kglobal" => SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)

/-- The actual original geometric complex satisfies affine homology/section exchange internally. -/
def geometricHomologySectionsIso (q : ℕ) :
    (GeometricComplexExchange.sectionComplex f p n U).homology q ≅
      ((Kglobal).homology q).val.obj (op WU) := by
  let : ∀ r, ((Kglobal).X r).IsQuasicoherent :=
    fun r => GeometricRelativeFrobeniusQuasicoherent.complex_term_isQuasicoherent f p n r
  exact homologySectionsIso (RelativeTwistedAffineBasis.twistedOpen_isAffine f p U hU) (Kglobal) q

variable (v : Fin n → Γ(X, U))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- Original geometric Cartier sections with the actual ORIGINAL global homology-sheaf target. -/
def localSheafCartierSectionsIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (CanonicalGeometry.exteriorCotangentSheaf g q).val.obj (op WU) ≅
      ((Kglobal).homology q).val.obj (op WU) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact GeometricLocalCartier.inverseCartierIso f p hU n v hv q ≪≫
    geometricHomologySectionsIso f p n hU q

/-- Every original unit form has its exact native-Cartier and actual global-homology value. -/
theorem localSheafCartierSectionsIso_unit (q : ℕ)
    (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op WU)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (localSheafCartierSectionsIso f p n hU v hv q).hom.hom
        ((GeometricLocalCartier.twistedUnitIso f p hU n v hv q).hom.hom ω) =
      (geometricHomologySectionsIso f p n hU q).hom.hom
        ((GeometricLocalCartier.nativeInverseCartierIso f p hU n v hv q).hom.hom
          ((GeometricLocalCartier.rawDomainIso f p hU q).hom.hom ω)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact congrArg (geometricHomologySectionsIso f p n hU q).hom.hom
    (GeometricLocalCartier.inverseCartierIso_unit f p hU n v hv q ω)

/-- The entire map on original global homology sections is independent of honest coordinates. -/
theorem localSheafCartierSectionsIso_chartChange (w : Fin n → Γ(X, U))
    (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) w).toRingHom.Etale) (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    localSheafCartierSectionsIso f p n hU v hv q = localSheafCartierSectionsIso f p n hU w hw q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact congrArg (fun e : (CanonicalGeometry.exteriorCotangentSheaf g q).val.obj (op WU) ≅
    (GeometricComplexExchange.sectionComplex f p n U).homology q =>
      e ≪≫ geometricHomologySectionsIso f p n hU q)
        (GeometricLocalCartier.inverseCartierIso_chartChange f p hU n v hv w hw q)

end EnvelopeProperty.Cartier.GeometricAffineHomology
