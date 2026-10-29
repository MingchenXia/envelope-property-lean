import EnvelopeProperty.Cartier.GeometricComplexExchange
import EnvelopeProperty.Cartier.RelativeCartierContinuationGlobalExteriorExchange
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # Local Cartier on the actual evaluated geometric complex -/

noncomputable section
namespace EnvelopeProperty.Cartier.GeometricLocalCartier
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "W" U => RelativeTwistedAffineBasis.twistedOpen f p U
variable {U : X.Opens} (hU : IsAffineOpen U)
local notation "σ" => RelativeTwistedAffineCharts.sectionsIso f p U hU
local notation "δ" => RelativeTwistedAffineSections.coefficientSectionMap f p U
local notation "T" => RelativeFrobenius.twist (algebraMap k (X.presheaf.obj (op U))) p
local notation "c" => RelativeFrobenius.coefficientMap (algebraMap k (X.presheaf.obj (op U))) p
local notation "ΩY" q => CanonicalGeometry.exteriorCotangentSheaf g q
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra

/-- The original native twist exterior module with the actual chart section-ring action. -/
def nativeDomain (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ModuleCat Γ(Y, W U) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (ModuleCat.restrictScalars (σ).hom.hom).obj
    (ModuleCat.of (T) (⋀[T]^q (KaehlerDifferential k (T))))

/-- The original universal exterior map of the proved actual coefficient square. -/
def rawDomainIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W U)) ≅
      nativeDomain f p hU q := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact RelativeGlobalExteriorExchange.exteriorIso (δ) (c) (σ)
    (RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU) q

/-- Every original cotangent wedge keeps the original universal σ-image, including degree zero. -/
theorem rawDomainIso_wedge (q : ℕ) (m : Fin q → CommRingCat.KaehlerDifferential (δ)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    letI : Module Γ(Y, W U) (CommRingCat.KaehlerDifferential (δ)) :=
      (CommRingCat.KaehlerDifferential (δ)).isModule;
    (rawDomainIso f p hU q).hom.hom (exteriorPower.ιMulti Γ(Y, W U) q (M := CommRingCat.KaehlerDifferential (δ)) m) =
      exteriorPower.ιMulti (T) q
        (fun i => RelativeGlobalExteriorExchange.cotangentSemilinear (δ) (c) (σ)
          (RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU) (m i)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let : Module Γ(Y, W U) (CommRingCat.KaehlerDifferential (δ)) :=
    (CommRingCat.KaehlerDifferential (δ)).isModule
  exact RelativeGlobalExteriorExchange.exteriorIso_wedge (δ) (c) (σ)
    (RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU) q m

variable (n : ℕ) (v : Fin n → Γ(X, U))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- The original exterior unit on the actual twisted affine open is an isomorphism. -/
def twistedUnitIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W U)) ≅
      (ΩY q).val.obj (op (W U)) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  letI := CanonicalGeometry.cotangentOpenAlgebra g (W U)
  let A := Γ(Y, W U)
  letI : Algebra k A := CanonicalGeometry.cotangentOpenAlgebra g (W U)
  let σ₀ : A ≅ T := σ
  let M : ModuleCat A := (ModuleCat.restrictScalars σ₀.hom.hom).obj
    (ModuleCat.of (T) (KaehlerDifferential k (T)))
  letI : Module A (KaehlerDifferential k (T)) := M.isModule
  let ρ : (T) ≃+* A :=
    { __ := σ₀.inv.hom
      invFun := σ₀.hom
      left_inv := Iso.inv_hom_id_apply σ₀
      right_inv := Iso.hom_inv_id_apply σ₀ }
  let bT : Module.Basis (Fin n) A M :=
    (RelativeEtaleCartierDomain.cotangentBasis v hv p).mapCoeffs ρ (by
      intro t x
      change σ₀.hom.hom (σ₀.inv.hom t) • x = t • x
      exact congrArg (fun a : T => a • x) (Iso.inv_hom_id_apply σ₀ t))
  let e := RelativeGlobalCotangentExchange.cotangentIso (δ) (c) σ₀
    (RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU)
  let bA : Module.Basis (Fin n) A (KaehlerDifferential k A) := bT.map e.toLinearEquiv.symm
  exact (LinearEquiv.ofBijective
    ((CanonicalGeometry.exteriorSheafificationMap
      (CanonicalGeometry.cotangentPresheaf g) q).app (op (W U))).hom
    (CanonicalGeometry.affineChartExteriorSheafificationMap_bijective g
      (RelativeTwistedAffineBasis.twistedOpen_isAffine f p U hU) bA q)).toModuleIso

/-- Every raw form retains its exact original geometric source unit section. -/
theorem twistedUnitIso_apply (q : ℕ)
    (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W U))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (twistedUnitIso f p hU n v hv q).hom.hom ω =
      (CanonicalGeometry.exteriorSheafificationMap
        (CanonicalGeometry.cotangentPresheaf g) q).app (op (W U)) ω := rfl

/-- The actual geometric cotangent sections identify with the native twist source. -/
def domainIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (ΩY q).val.obj (op (W U)) ≅ nativeDomain f p hU q := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (twistedUnitIso f p hU n v hv q).symm ≪≫ rawDomainIso f p hU q

variable [SmoothOfRelativeDimension n f]
local notation "Kv" => SchemeRelativeFrobeniusAffineDeRham.complex v hv p

/-- Native scalar-restriction homology followed by the exact actual complex exchange. -/
def homologyTransferIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (ModuleCat.restrictScalars (σ).hom.hom).obj ((Kv).homology q) ≅
      (GeometricComplexExchange.sectionComplex f p n U).homology q := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (ModuleComplexNativeCycleClasses.restrictionHomologyIso (σ).hom.hom (Kv) q).symm ≪≫
    GeometricComplexExchange.homologyIso f p n hU v hv q

/-- The original native Cartier map with the actual evaluated global target. -/
def nativeInverseCartierIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    nativeDomain f p hU q ≅
      (GeometricComplexExchange.sectionComplex f p n U).homology q := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (ModuleCat.restrictScalars (σ).hom.hom).mapIso
      (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q) ≪≫
    homologyTransferIso f p hU n v hv q

/-- Every native form has precisely its original native Cartier value under the derived exchange. -/
theorem nativeInverseCartierIso_apply (q : ℕ)
    (ω : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      ⋀[T]^q (KaehlerDifferential k (T))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeInverseCartierIso f p hU n v hv q).hom.hom ω =
      (homologyTransferIso f p hU n v hv q).hom.hom
        ((RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom.hom ω) := rfl

/-- Actual original geometric cotangent sections map isomorphically to actual evaluated homology. -/
def inverseCartierIso (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (ΩY q).val.obj (op (W U)) ≅
      (GeometricComplexExchange.sectionComplex f p n U).homology q := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact domainIso f p hU n v hv q ≪≫ nativeInverseCartierIso f p hU n v hv q

/-- Every original source unit section keeps the canonical native-Cartier composition. -/
theorem inverseCartierIso_unit (q : ℕ)
    (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W U))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (inverseCartierIso f p hU n v hv q).hom.hom
        ((twistedUnitIso f p hU n v hv q).hom.hom ω) =
      (nativeInverseCartierIso f p hU n v hv q).hom.hom
        ((rawDomainIso f p hU q).hom.hom ω) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact congrArg (fun a => (nativeInverseCartierIso f p hU n v hv q).hom.hom
    ((rawDomainIso f p hU q).hom.hom a))
      (Iso.hom_inv_id_apply (twistedUnitIso f p hU n v hv q) ω)

private def restrictedCycle (q : ℕ)
    (z : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      LinearMap.ker ((Kv).sc q).g.hom) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    LinearMap.ker ((GeometricComplexExchange.nativeSectionComplex f p n hU v hv).sc q).g.hom := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  exact ⟨z.val, z.property⟩

/-- The actual whole complex map sends each original native cycle to its actual geometric cycle. -/
def imageCycle (q : ℕ)
    (z : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      LinearMap.ker ((Kv).sc q).g.hom) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    LinearMap.ker ((GeometricComplexExchange.sectionComplex f p n U).sc q).g.hom := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat Γ(Y, W U))
    (ComplexShape.up ℕ) q).map (GeometricComplexExchange.complexIso f p n hU v hv).hom
  let z' := restrictedCycle f p hU n v hv q z
  refine ⟨ψ.τ₂ z'.val, ?_⟩
  have h := congrArg (fun a => a z'.val) ψ.comm₂₃
  change ((GeometricComplexExchange.sectionComplex f p n U).sc q).g (ψ.τ₂ z'.val) =
    ψ.τ₃ (((GeometricComplexExchange.nativeSectionComplex f p n hU v hv).sc q).g z'.val) at h
  exact h.trans ((congrArg ψ.τ₃ z'.property).trans ψ.τ₃.hom.map_zero)

/-- Every original cycle retains exactly its original exterior unit and preimage identification. -/
theorem imageCycle_val (q : ℕ)
    (z : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      LinearMap.ker ((Kv).sc q).g.hom) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (imageCycle f p hU n v hv q z).val =
      (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
          (EtaleAffineSectionDifferential.unitEquiv f hU v hv q z.val) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact GeometricComplexExchange.complexIso_hom_f_apply f p n hU v hv q z.val

/-- The same actual homology transfer preserves the exact class of every original unit cycle. -/
theorem homologyTransferIso_cycleClass (q : ℕ)
    (z : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      LinearMap.ker ((Kv).sc q).g.hom) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (homologyTransferIso f p hU n v hv q).hom.hom
        (ModuleComplexNativeCycleClasses.cycleClass (Kv) q z) =
      ModuleComplexNativeCycleClasses.cycleClass
        (GeometricComplexExchange.sectionComplex f p n U) q (imageCycle f p hU n v hv q z) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let E := ModuleComplexNativeCycleClasses.restrictionHomologyIso (σ).hom.hom (Kv) q
  let z' := restrictedCycle f p hU n v hv q z
  have hp := ModuleComplexNativeCycleClasses.restrictionHomologyIso_cycleClass
    (σ).hom.hom (Kv) q z' z rfl
  have hi : E.inv.hom (ModuleComplexNativeCycleClasses.cycleClass (Kv) q z) =
      ModuleComplexNativeCycleClasses.cycleClass
        (GeometricComplexExchange.nativeSectionComplex f p n hU v hv) q z' :=
    (congrArg E.inv.hom hp).symm.trans (Iso.hom_inv_id_apply E _)
  have hc := ModuleComplexNativeCycleClasses.homologyMap_cycleClass
    (GeometricComplexExchange.complexIso f p n hU v hv).hom q z'
      (imageCycle f p hU n v hv q z) rfl
  exact (congrArg (GeometricComplexExchange.homologyIso f p n hU v hv q).hom.hom hi).trans hc

variable (w : Fin n → Γ(X, U))
variable (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) w).toRingHom.Etale)

omit [SmoothOfRelativeDimension n f] in
/-- The whole original source unit is independent of the honest tuple used to prove bijectivity. -/
theorem twistedUnitIso_chartChange (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    twistedUnitIso f p hU n v hv q = twistedUnitIso f p hU n w hw q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  apply Iso.ext
  rfl

/-- The canonical scalar-preservation comparison pastes with the whole geometric chart square. -/
theorem homologyTransferIso_chartChange (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (ModuleCat.restrictScalars (σ).hom.hom).map
        (RelativeNativeChartChange.homologyIso v hv w hw p q).hom ≫
      (homologyTransferIso f p hU n w hw q).hom =
        (homologyTransferIso f p hU n v hv q).hom := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let σ₀ : Γ(Y, W U) ≅ T := σ
  let F := ModuleCat.restrictScalars σ₀.hom.hom
  let : F.PreservesZeroMorphisms := by
    change (ModuleCat.restrictScalars σ₀.hom.hom).PreservesZeroMorphisms
    infer_instance
  let : F.PreservesHomology := by
    change (ModuleCat.restrictScalars σ₀.hom.hom).PreservesHomology
    infer_instance
  let Ev := ModuleComplexNativeCycleClasses.restrictionHomologyIso σ₀.hom.hom (Kv) q
  let Ew := ModuleComplexNativeCycleClasses.restrictionHomologyIso σ₀.hom.hom
    (SchemeRelativeFrobeniusAffineDeRham.complex w hw p) q
  let H := HomologicalComplex.homologyFunctor (ModuleCat Γ(Y, W U)) (ComplexShape.up ℕ) q
  let a := (RelativeNativeChartChange.complexIso v hv w hw p).hom
  let ra := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map a
  have hp : F.map (RelativeNativeChartChange.homologyIso v hv w hw p q).hom ≫ Ew.inv =
      Ev.inv ≫ H.map ra :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat (T)) (ComplexShape.up ℕ) q).map a) (ModuleCat.restrictScalars σ₀.hom.hom)
  have hs := GeometricComplexExchange.homology_chartChange_square f p n hU v hv w hw q
  change F.map (RelativeNativeChartChange.homologyIso v hv w hw p q).hom ≫
    (Ew.inv ≫ (GeometricComplexExchange.homologyIso f p n hU w hw q).hom) =
      Ev.inv ≫ (GeometricComplexExchange.homologyIso f p n hU v hv q).hom
  calc
    _ = (F.map (RelativeNativeChartChange.homologyIso v hv w hw p q).hom ≫ Ew.inv) ≫
        (GeometricComplexExchange.homologyIso f p n hU w hw q).hom := (Category.assoc _ _ _).symm
    _ = (Ev.inv ≫ H.map ra) ≫ (GeometricComplexExchange.homologyIso f p n hU w hw q).hom :=
      congrArg (fun t => t ≫ (GeometricComplexExchange.homologyIso f p n hU w hw q).hom) hp
    _ = Ev.inv ≫ (H.map ra ≫ (GeometricComplexExchange.homologyIso f p n hU w hw q).hom) :=
      Category.assoc _ _ _
    _ = Ev.inv ≫ (GeometricComplexExchange.homologyIso f p n hU v hv q).hom :=
      congrArg (fun t => Ev.inv ≫ t) hs

/-- The same native Cartier map to actual evaluated homology is independent of honest coordinates. -/
theorem nativeInverseCartierIso_chartChange (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    nativeInverseCartierIso f p hU n v hv q = nativeInverseCartierIso f p hU n w hw q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let σ₀ : Γ(Y, W U) ≅ T := σ
  let F := ModuleCat.restrictScalars σ₀.hom.hom
  have hc := (F.map_comp
    (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom
    (RelativeNativeChartChange.homologyIso v hv w hw p q).hom).symm.trans
      (congrArg F.map (RelativeNativeChartChange.inverseCartierIso_chartChange v hv w hw p q))
  have ht := homologyTransferIso_chartChange f p hU n v hv w hw q
  apply Iso.ext
  change F.map (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom ≫
      (homologyTransferIso f p hU n v hv q).hom =
    F.map (RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q).hom ≫
      (homologyTransferIso f p hU n w hw q).hom
  calc
    _ = F.map (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom ≫
        (F.map (RelativeNativeChartChange.homologyIso v hv w hw p q).hom ≫
          (homologyTransferIso f p hU n w hw q).hom) :=
      congrArg (fun t => F.map (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom ≫ t) ht.symm
    _ = (F.map (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom ≫
        F.map (RelativeNativeChartChange.homologyIso v hv w hw p q).hom) ≫
          (homologyTransferIso f p hU n w hw q).hom := (Category.assoc _ _ _).symm
    _ = F.map (RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q).hom ≫
        (homologyTransferIso f p hU n w hw q).hom :=
      congrArg (fun t => t ≫ (homologyTransferIso f p hU n w hw q).hom) hc

/-- The entire local Cartier isomorphism on the actual geometric sheaf sections is coordinate independent. -/
theorem inverseCartierIso_chartChange (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    inverseCartierIso f p hU n v hv q = inverseCartierIso f p hU n w hw q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  have hu := twistedUnitIso_chartChange f p hU n v hv w hw q
  have hc := nativeInverseCartierIso_chartChange f p hU n v hv w hw q
  apply Iso.ext
  change (twistedUnitIso f p hU n v hv q).inv ≫
      ((rawDomainIso f p hU q).hom ≫ (nativeInverseCartierIso f p hU n v hv q).hom) =
    (twistedUnitIso f p hU n w hw q).inv ≫
      ((rawDomainIso f p hU q).hom ≫ (nativeInverseCartierIso f p hU n w hw q).hom)
  exact (congrArg (fun e :
    (CanonicalGeometry.exteriorCotangentPresheaf g q).obj (op (W U)) ≅
      (ΩY q).val.obj (op (W U)) => e.inv ≫
    ((rawDomainIso f p hU q).hom ≫ (nativeInverseCartierIso f p hU n v hv q).hom)) hu).trans
      (congrArg (fun e : nativeDomain f p hU q ≅
        (GeometricComplexExchange.sectionComplex f p n U).homology q => (twistedUnitIso f p hU n w hw q).inv ≫
        ((rawDomainIso f p hU q).hom ≫ e.hom)) hc)

end EnvelopeProperty.Cartier.GeometricLocalCartier
