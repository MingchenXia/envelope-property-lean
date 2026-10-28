import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineDifferential
import EnvelopeProperty.Cartier.RelativeCartierContinuationNativeChartChange
import Mathlib.Algebra.Homology.Additive

/-! # The original global geometric relative complex on its actual affine charts -/

noncomputable section
namespace EnvelopeProperty.Cartier.GeometricComplexExchange
open AlgebraicGeometry CategoryTheory Opposite
universe u

private instance evaluationAdditive {Z : Scheme.{u}} (V : Z.Opens) :
    (SheafOfModules.evaluation Z.ringCatSheaf (op V)).Additive := by
  dsimp only [SheafOfModules.evaluation]
  infer_instance

private def pushforwardSectionsIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (M : X.Modules) :
    (ModuleCat.restrictScalars (g.app W).hom).obj (M.val.obj (op (g ⁻¹ᵁ W))) ≅
      ((Scheme.Modules.pushforward g).obj M).val.obj (op W) := by
  let A := (ModuleCat.restrictScalars (g.app W).hom).obj
    (M.val.obj (op (g ⁻¹ᵁ W)))
  let B : ModuleCat Γ(Y, W) := ((Scheme.Modules.pushforward g).obj M).val.obj (op W)
  change A ≅ B
  exact
    { hom := ModuleCat.ofHom (R := Γ(Y, W)) (X := A) (Y := B)
        { toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      inv := ModuleCat.ofHom (R := Γ(Y, W)) (X := B) (Y := A)
        { toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      hom_inv_id := by ext s; rfl
      inv_hom_id := by ext s; rfl }

private def preimageSectionsIso {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)
    (U : X.Opens) (h : g ⁻¹ᵁ W = U) (M : X.Modules) :
    (ModuleCat.restrictScalars (g.appLE W U h.symm.le).hom).obj (M.val.obj (op U)) ≅
      ((Scheme.Modules.pushforward g).obj M).val.obj (op W) := by
  subst U
  exact (ModuleCat.restrictScalarsCongr
    (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_eq_app g))).app
      (M.val.obj (op (g ⁻¹ᵁ W))) ≪≫ pushforwardSectionsIso g W M

private theorem preimageSectionsIso_apply {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (U : X.Opens) (h : g ⁻¹ᵁ W = U) (M : X.Modules)
    (s : M.val.obj (op U)) :
    (preimageSectionsIso g W U h M).hom.hom s = M.presheaf.map (eqToHom h).op s := by
  subst U
  simp [preimageSectionsIso, pushforwardSectionsIso]
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f
variable (n : ℕ) [SmoothOfRelativeDimension n f]
local notation "K" => SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "W" U => RelativeTwistedAffineBasis.twistedOpen f p U

/-- Native evaluation of the actual global complex on the original twisted open. -/
def sectionComplex (U : X.Opens) : CochainComplex (ModuleCat Γ(Y, W U)) ℕ :=
  ((SheafOfModules.evaluation (Y).ringCatSheaf (op (W U))).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (K)

variable {U : X.Opens} (hU : IsAffineOpen U) (v : Fin n → Γ(X, U))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
local notation "σ" => RelativeTwistedAffineCharts.sectionsIso f p U hU
local notation "μ" => RelativeTwistedAffineSections.relativeSectionMap f p U

/-- The original native affine complex with the actual chart section-ring action. -/
def nativeSectionComplex :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    CochainComplex (ModuleCat Γ(Y, W U)) ℕ := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact ((ModuleCat.restrictScalars (σ).hom.hom).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (SchemeRelativeFrobeniusAffineDeRham.complex v hv p)

/-- The actual exterior unit and original preimage equality give the whole chart form iso. -/
def formIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeSectionComplex f p n hU v hv).X q ≅ (sectionComplex f p n U).X q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let β := SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k Γ(X, U)) p
  let M := ModuleCat.of Γ(X, U) (⋀[Γ(X, U)]^q (KaehlerDifferential k Γ(X, U)))
  let Ω := CanonicalGeometry.exteriorCotangentSheaf f q
  let e : M ≅ Ω.val.obj (op U) := (EtaleAffineSectionDifferential.unitEquiv f hU v hv q).toModuleIso
  have hμ : (μ).hom = β.hom.comp (σ).hom.hom :=
    congrArg CommRingCat.Hom.hom (RelativeTwistedAffineSections.relativeSectionMap_eq f p U hU)
  exact ((ModuleCat.restrictScalarsComp' (σ).hom.hom β.hom (μ).hom hμ).symm.app M) ≪≫
    (ModuleCat.restrictScalars (μ).hom).mapIso e ≪≫
      preimageSectionsIso (Fr) (W U) U (RelativeTwistedAffineBasis.relative_preimage f p U) Ω

/-- Every original form is exactly its original unit section on the actual preimage. -/
theorem formIso_apply (q : ℕ)
    (ω : ⋀[Γ(X, U)]^q (CommRingCat.KaehlerDifferential
      ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (formIso f p n hU v hv q).hom.hom ω =
      (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
          (EtaleAffineSectionDifferential.unitEquiv f hU v hv q ω) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  change (preimageSectionsIso (Fr) (W U) U
    (RelativeTwistedAffineBasis.relative_preimage f p U)
      (CanonicalGeometry.exteriorCotangentSheaf f q)).hom.hom
        (EtaleAffineSectionDifferential.unitEquiv f hU v hv q ω) = _
  exact preimageSectionsIso_apply _ _ _ _ _ _

/-- The actual native differentials commute with the original chart components. -/
theorem differential_formIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeSectionComplex f p n hU v hv).d q (q + 1) ≫
        (formIso f p n hU v hv (q + 1)).hom =
      (formIso f p n hU v hv q).hom ≫ (sectionComplex f p n U).d q (q + 1) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  change (formIso f p n hU v hv (q + 1)).hom.hom
      (((nativeSectionComplex f p n hU v hv).d q (q + 1)).hom ω) =
    ((sectionComplex f p n U).d q (q + 1)).hom
      ((formIso f p n hU v hv q).hom.hom ω)
  have hdn : ((nativeSectionComplex f p n hU v hv).d q (q + 1)).hom ω =
      EtaleDeRham.differential v hv q ω := by
    exact congrArg (fun d =>
      ((ModuleCat.restrictScalars (σ).hom.hom).map d).hom ω)
      (CochainComplex.of_d _ (SchemeRelativeFrobeniusAffineDeRham.differential v hv p) q)
  have hdg (s : (sectionComplex f p n U).X q) :
      ((sectionComplex f p n U).d q (q + 1)).hom s =
        (SchemeRelativeFrobeniusBasisDifferential.differential f p n q).mapPresheaf.app
          (op (W U)) s := by
    exact congrArg (fun d : SchemeRelativeFrobeniusDeRham.formModule f p q ⟶
        SchemeRelativeFrobeniusDeRham.formModule f p (q + 1) =>
      ((SheafOfModules.evaluation (Y).ringCatSheaf (op (W U))).map d).hom s)
      (CochainComplex.of_d _ (SchemeRelativeFrobeniusBasisDifferential.differential f p n) q)
  have hφ₀ := formIso_apply f p n hU v hv q ω
  have hφ₁ := formIso_apply f p n hU v hv (q + 1) (EtaleDeRham.differential v hv q ω)
  have hs := ConcreteCategory.congr_hom
    (SchemeRelativeFrobeniusAffineDifferential.differential_twistedOpen f p n hU v hv q)
      (EtaleAffineSectionDifferential.unitEquiv f hU v hv q ω)
  change (SchemeRelativeFrobeniusBasisDifferential.differential f p n q).mapPresheaf.app
      (op (W U)) ((CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
          (EtaleAffineSectionDifferential.unitEquiv f hU v hv q ω)) =
    (CanonicalGeometry.exteriorCotangentSheaf f (q + 1)).presheaf.map
      (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
        (EtaleAffineSectionDifferential.differential f hU v hv q
          (EtaleAffineSectionDifferential.unitEquiv f hU v hv q ω)) at hs
  have hu := EtaleAffineSectionDifferential.differential_unit f hU v hv q ω
  have hs' := hs.trans (congrArg
    ((CanonicalGeometry.exteriorCotangentSheaf f (q + 1)).presheaf.map
      (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op) hu)
  exact (congrArg (formIso f p n hU v hv (q + 1)).hom.hom hdn).trans
    (hφ₁.trans (hs'.symm.trans ((hdg _).symm.trans
      (congrArg ((sectionComplex f p n U).d q (q + 1)).hom hφ₀.symm))))

/-- Whole original native chart complex equals the actual evaluated global geometric complex. -/
def complexIso :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    nativeSectionComplex f p n hU v hv ≅ sectionComplex f p n U := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦ formIso f p n hU v hv q) ?_
  intro q r h
  have hr : q + 1 = r := h
  subst r
  exact (differential_formIso f p n hU v hv q).symm

/-- Every degree of the whole complex map preserves the original unit section. -/
theorem complexIso_hom_f_apply (q : ℕ)
    (ω : ⋀[Γ(X, U)]^q (CommRingCat.KaehlerDifferential
      ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ((complexIso f p n hU v hv).hom.f q).hom ω =
      (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
          (EtaleAffineSectionDifferential.unitEquiv f hU v hv q ω) :=
  formIso_apply f p n hU v hv q ω

variable (w : Fin n → Γ(X, U))
variable (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) w).toRingHom.Etale)

/-- The entire original honest-tuple chart-change square holds internally. -/
theorem chartChange_square :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ((ModuleCat.restrictScalars (σ).hom.hom).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (RelativeNativeChartChange.complexIso v hv w hw p).hom ≫
          (complexIso f p n hU w hw).hom = (complexIso f p n hU v hv).hom := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  ext q ω
  rfl

/-- Native homology of the same whole geometric chart exchange in every degree. -/
def homologyIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeSectionComplex f p n hU v hv).homology q ≅ (sectionComplex f p n U).homology q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (HomologicalComplex.homologyFunctor (ModuleCat Γ(Y, W U)) (ComplexShape.up ℕ) q).mapIso
    (complexIso f p n hU v hv)

/-- Actual native homology preserves the whole original chart-change square. -/
theorem homology_chartChange_square (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (HomologicalComplex.homologyFunctor (ModuleCat Γ(Y, W U)) (ComplexShape.up ℕ) q).map
        (((ModuleCat.restrictScalars (σ).hom.hom).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RelativeNativeChartChange.complexIso v hv w hw p).hom) ≫
      (homologyIso f p n hU w hw q).hom = (homologyIso f p n hU v hv q).hom := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let H := HomologicalComplex.homologyFunctor (ModuleCat Γ(Y, W U)) (ComplexShape.up ℕ) q
  exact (H.map_comp _ _).symm.trans (congrArg H.map (chartChange_square f p n hU v hv w hw))

end EnvelopeProperty.Cartier.GeometricComplexExchange
