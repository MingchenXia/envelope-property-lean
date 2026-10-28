import EnvelopeProperty.DI.GeometricLeadingCartier
import EnvelopeProperty.DI.ZeroSourceHomology
import EnvelopeProperty.Cartier.GeometricSheafCartier

/-! # The SAME native exterior xi map retains original geometric Cartier in every degree -/
noncomputable section
namespace EnvelopeProperty.DI.GeometricLeadingCartierExterior
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Cartier Cartier.FrobeniusLiftDifference
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [SmoothOfRelativeDimension n f]
  {U : X.Opens} (hU : IsAffineOpen U)
private abbrev structuralRingMap : k →+* X.presheaf.obj (op U) :=
  ((CanonicalGeometry.schemeConstantPresheafMap f).app (op U)).hom
local notation "T" => RelativeFrobenius.twist (structuralRingMap (U := U) f) p
private abbrev coefficientAlgebra : Algebra k (T) :=
  (RelativeFrobenius.coefficientMap (structuralRingMap (U := U) f) p).hom.toAlgebra
attribute [local instance] coefficientAlgebra
variable {C S : Type u} {R : Type v} [CommRing C] [CommRing R] [CommRing S]
  [Algebra C k] [Algebra C R] [Algebra C S]
private abbrev coefficientCAlgebra : Algebra C (T) :=
  ((RelativeFrobenius.coefficientMap (structuralRingMap (U := U) f) p).hom.comp (algebraMap C k)).toAlgebra
attribute [local instance] coefficientCAlgebra
private instance coefficientTower : IsScalarTower C k (T) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Algebra R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p)] [IsScalarTower C R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p)]
  (c : Reduction p C k) (a : Reduction p R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p)) (b : FlatReduction p S Γ(X,U))
  (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (structuralRingMap (U := U) f) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (structuralRingMap (U := U) f) p) = a.map) (hc : algebraMap C k = c.map)
  [Algebra.FormallySmooth C S]
  (w : Fin n → Γ(X,U)) (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
local notation "Kn" => SchemeRelativeFrobeniusAffineDeRham.complex w hw p
local notation "Kg" => GeometricComplexExchange.sectionComplex f p n U
local notation "σ" => RelativeTwistedAffineCharts.sectionsIso f p U hU
private abbrev scalarRestriction : ModuleCat (T) ⥤
    ModuleCat ((SchemeRelativeFrobenius.twist p f).presheaf.obj (op (RelativeTwistedAffineBasis.twistedOpen f p U))) :=
  ModuleCat.restrictScalars (RelativeTwistedAffineCharts.sectionsIso f p U hU).hom.hom
local notation "RS" => scalarRestriction f p hU
local notation "Krs" => GeometricComplexExchange.nativeSectionComplex f p n hU w hw
local notation "ψ" => GeometricComplexExchange.complexIso f p n hU w hw
local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "WU" => RelativeTwistedAffineBasis.twistedOpen f p U
private abbrev sourceSections (q : ℕ) : ModuleCat ((SchemeRelativeFrobenius.twist p f).presheaf.obj (op WU)) :=
  (CanonicalGeometry.exteriorCotangentSheaf g q).val.obj (op WU)
local notation "M" q => sourceSections (U := U) f p q
private abbrev nativeSource (q : ℕ) : ModuleCat (T) :=
  ModuleCat.of (T) (⋀[T]^q (KaehlerDifferential k (T)))
private def nativeZeroSource : CochainComplex (ModuleCat (T)) ℕ :=
  CochainComplex.of (nativeSource (U := U) f p) (fun _ => 0) (fun _ => by simp)
private theorem nativeZeroSource_d (i j : ℕ) :
    (nativeZeroSource (U := U) f p).d i j = 0 := by
  change CochainComplex.of.d (nativeSource (U := U) f p) (fun _ => 0) i j = 0
  unfold CochainComplex.of.d
  split_ifs <;> simp only [zero_comp]
private def nativePhi :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    nativeZeroSource (U := U) f p ⟶ Kn := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact DeligneIllusieLocalContinuationResidueCartier.cochainMap p c a b F hF ha hc w hw
private abbrev nativeXi (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    nativeSource (U := U) f p q ⟶ (Kn).X q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (nativePhi f p n c a b F hF ha hc w hw).f q
omit [SmoothOfRelativeDimension n f] in
private theorem nativeXi_closed (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; ∀ j, (ComplexShape.up ℕ).Rel q j →
    nativeXi f p n c a b F hF ha hc w hw q ≫ (Kn).d q j = 0 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  intro j _
  exact ((nativePhi f p n c a b F hF ha hc w hw).comm q j).trans
    (by rw [nativeZeroSource_d, zero_comp])
private def nativeCycle (q : ℕ) (ω : nativeSource (U := U) f p q) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    LinearMap.ker ((Kn).sc q).g.hom := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact ((Kn).sc q).moduleCatCyclesIso.hom
    ((Kn).liftCycles (nativeXi f p n c a b F hF ha hc w hw q) (q+1) (by simp)
      (nativeXi_closed f p n c a b F hF ha hc w hw q (q+1) (by simp)) ω)
omit [SmoothOfRelativeDimension n f] in
private theorem nativeCycle_val (q : ℕ) (ω : nativeSource (U := U) f p q) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeCycle f p n c a b F hF ha hc w hw q ω).val =
      nativeXi f p n c a b F hF ha hc w hw q ω := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let y := (Kn).liftCycles (nativeXi f p n c a b F hF ha hc w hw q) (q+1) (by simp)
    (nativeXi_closed f p n c a b F hF ha hc w hw q (q+1) (by simp)) ω
  have hi := ((Kn).sc q).moduleCatCyclesIso_inv_iCycles_apply (((Kn).sc q).moduleCatCyclesIso.hom y)
  rw [Iso.hom_inv_id_apply] at hi
  have hc' := congrArg (fun L : nativeSource (U := U) f p q ⟶ (Kn).X q => L ω)
    ((Kn).liftCycles_i (nativeXi f p n c a b F hF ha hc w hw q) (q+1) (by simp)
      (nativeXi_closed f p n c a b F hF ha hc w hw q (q+1) (by simp)))
  exact hi.symm.trans hc'
omit [SmoothOfRelativeDimension n f] in
private theorem nativeCycle_class (q : ℕ) (ω : nativeSource (U := U) f p q) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ModuleComplexNativeCycleClasses.cycleClass (Kn) q (nativeCycle f p n c a b F hF ha hc w hw q ω) =
      (DeligneIllusieLocalContinuationResidueCartier.classMap p c a b F hF ha hc w hw q).hom ω := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  have h := ZeroSourceHomology.homologyMap_eq_singleClassMap q
    (nativeZeroSource (U := U) f p) (Kn) (nativePhi f p n c a b F hF ha hc w hw)
    (nativeZeroSource_d (U := U) f p)
  change DeligneIllusieLocalContinuationResidueCartier.classMap p c a b F hF ha hc w hw q =
    LeadingCartierCycleTransport.singleClassMap q (nativeSource (U := U) f p q) (Kn)
      (nativeXi f p n c a b F hF ha hc w hw q) _ at h
  have hc' := LeadingCartierCycleTransport.singleClassMap_cycleClass q (nativeSource (U := U) f p q) (Kn)
    (nativeXi f p n c a b F hF ha hc w hw q)
    (nativeXi_closed f p n c a b F hF ha hc w hw q) ω
    (nativeCycle f p n c a b F hF ha hc w hw q ω)
    (nativeCycle_val f p n c a b F hF ha hc w hw q ω).symm
  exact hc'.symm.trans (congrArg (fun L => L.hom ω) h.symm)
private def scalarXi (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (M q) ⟶ (Krs).X q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (GeometricLocalCartier.domainIso f p hU n w hw q).hom ≫
    (RS).map (nativeXi f p n c a b F hF ha hc w hw q)
omit [SmoothOfRelativeDimension n f] in
private theorem scalarXi_closed (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; ∀ j, (ComplexShape.up ℕ).Rel q j →
    scalarXi f p n hU c a b F hF ha hc w hw q ≫ (Krs).d q j = 0 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  intro j hj
  change ((GeometricLocalCartier.domainIso f p hU n w hw q).hom ≫
    (RS).map (nativeXi f p n c a b F hF ha hc w hw q)) ≫ (RS).map ((Kn).d q j) = 0
  rw [Category.assoc, ← Functor.map_comp, nativeXi_closed f p n c a b F hF ha hc w hw q j hj,
    Functor.map_zero, comp_zero]

/-- The actual exterior component of the SAME native xi, with original geometric source/target units. -/
def exteriorSections (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; (M q) ⟶ (Kg).X q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact scalarXi f p n hU c a b F hF ha hc w hw q ≫ (ψ).hom.f q

/-- Every original section retains the exact original exterior target-unit and preimage formula. -/
theorem exteriorSections_apply (q : ℕ) (x : M q) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (exteriorSections f p n hU c a b F hF ha hc w hw q).hom x =
      (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
          (EtaleAffineSectionDifferential.unitEquiv f hU w hw q
            ((DeligneIllusieLocalContinuationResidueCartier.cochainMap p c a b F hF ha hc w hw).f q
              ((GeometricLocalCartier.domainIso f p hU n w hw q).hom.hom x))) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact GeometricComplexExchange.complexIso_hom_f_apply f p n hU w hw q
    (nativeXi f p n c a b F hF ha hc w hw q
      ((GeometricLocalCartier.domainIso f p hU n w hw q).hom.hom x))

/-- On every original source wedge, the same exterior map is the wedge of the SAME native xi values. -/
theorem exteriorSections_sourceWedge (q : ℕ)
    (ω : Fin q → KaehlerDifferential k (T)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (exteriorSections f p n hU c a b F hF ha hc w hw q).hom
      ((GeometricLocalCartier.domainIso f p hU n w hw q).inv.hom
        (exteriorPower.ιMulti (T) q ω)) =
      (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
          (EtaleAffineSectionDifferential.unitEquiv f hU w hw q
            (exteriorPower.ιMulti Γ(X,U) q (fun i =>
              exteriorPower.oneEquiv Γ(X,U) (KaehlerDifferential k Γ(X,U))
                (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc
                  (ω i))))) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  rw [exteriorSections_apply, Iso.inv_hom_id_apply]
  apply congrArg ((CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
    (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op)
  apply congrArg (EtaleAffineSectionDifferential.unitEquiv f hU w hw q)
  exact DeligneIllusieLocalContinuationResidueCartier.formMap_ιMulti p c a b F hF ha hc q ω

/-- Its whole actual single-degree representative, with native closedness derived internally. -/
def exteriorCochain (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (HomologicalComplex.single (ModuleCat Γ(SchemeRelativeFrobenius.twist p f,WU)) (.up ℕ) q).obj
      (M q) ⟶ Kg := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact HomologicalComplex.mkHomFromSingle (scalarXi f p n hU c a b F hF ha hc w hw q)
    (scalarXi_closed f p n hU c a b F hF ha hc w hw q) ≫ (ψ).hom

/-- The entire degree component is the SAME exterior xi sections. -/
theorem exteriorCochain_f (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (exteriorCochain f p n hU c a b F hF ha hc w hw q).f q =
      (HomologicalComplex.singleObjXSelf (.up ℕ) q (M q)).hom ≫
        exteriorSections f p n hU c a b F hF ha hc w hw q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  change (HomologicalComplex.mkHomFromSingle
    (scalarXi f p n hU c a b F hF ha hc w hw q)
    (scalarXi_closed f p n hU c a b F hF ha hc w hw q)).f q ≫ (ψ).hom.f q = _
  rw [HomologicalComplex.mkHomFromSingle_f]
  exact Category.assoc _ _ _

/-- Actual homology of the SAME original exterior representative, in every degree. -/
def exteriorHomologyClass (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; (M q) ⟶ (Kg).homology q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) q (M q)).inv ≫
    HomologicalComplex.homologyMap (exteriorCochain f p n hU c a b F hF ha hc w hw q) q

/-- The SAME actual homology class in sections of the original global homology sheaf. -/
def exteriorClassSections (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; (M q) ⟶
      ((SchemeRelativeFrobeniusBasisDifferential.complex f p n).homology q).val.obj (op WU) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact exteriorHomologyClass f p n hU c a b F hF ha hc w hw q ≫
    (GeometricAffineHomology.geometricHomologySectionsIso f p n hU q).hom
/-- The whole target comparison is the canonical evaluation on the SAME original global complex. -/
theorem exteriorClassSections_eq_canonicalComparison (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    exteriorClassSections f p n hU c a b F hF ha hc w hw q =
      exteriorHomologyClass f p n hU c a b F hF ha hc w hw q ≫
        SchemeSectionHomology.comparison (SchemeRelativeFrobeniusBasisDifferential.complex f p n) WU q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let : ∀ r, ((SchemeRelativeFrobeniusBasisDifferential.complex f p n).X r).IsQuasicoherent :=
    fun r => GeometricRelativeFrobeniusQuasicoherent.complex_term_isQuasicoherent f p n r
  change _ ≫ (GeometricAffineHomology.homologySectionsIso
    (RelativeTwistedAffineBasis.twistedOpen_isAffine f p U hU)
    (SchemeRelativeFrobeniusBasisDifferential.complex f p n) q).hom = _
  rw [GeometricHomologyNaturality.homologySectionsIso_hom_eq]

private theorem exteriorHomologyClass_native (q : ℕ) (x : M q) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (exteriorHomologyClass f p n hU c a b F hF ha hc w hw q).hom x =
      (GeometricLocalCartier.homologyTransferIso f p hU n w hw q).hom.hom
        ((DeligneIllusieLocalContinuationResidueCartier.classMap p c a b F hF ha hc w hw q).hom
          ((GeometricLocalCartier.domainIso f p hU n w hw q).hom.hom x)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let ω : nativeSource (U := U) f p q := (GeometricLocalCartier.domainIso f p hU n w hw q).hom.hom x
  let z := nativeCycle f p n c a b F hF ha hc w hw q ω
  let z' : LinearMap.ker ((Krs).sc q).g.hom := ⟨z.val, z.property⟩
  have hs := LeadingCartierCycleTransport.singleClassMap_cycleClass q (M q) (Krs)
    (scalarXi f p n hU c a b F hF ha hc w hw q)
    (scalarXi_closed f p n hU c a b F hF ha hc w hw q) x z'
      (nativeCycle_val f p n c a b F hF ha hc w hw q ω).symm
  have hm := ModuleComplexNativeCycleClasses.homologyMap_cycleClass (ψ).hom q z'
    (GeometricLocalCartier.imageCycle f p hU n w hw q z) rfl
  have ht := GeometricLocalCartier.homologyTransferIso_cycleClass f p hU n w hw q z
  unfold exteriorHomologyClass exteriorCochain
  rw [HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap (ψ).hom q).hom
    ((LeadingCartierCycleTransport.singleClassMap q (M q) (Krs)
      (scalarXi f p n hU c a b F hF ha hc w hw q)
      (scalarXi_closed f p n hU c a b F hF ha hc w hw q)).hom x) = _
  calc
    _ = (HomologicalComplex.homologyMap (ψ).hom q).hom
        (ModuleComplexNativeCycleClasses.cycleClass (Krs) q z') := congrArg _ hs
    _ = ModuleComplexNativeCycleClasses.cycleClass (Kg) q
        (GeometricLocalCartier.imageCycle f p hU n w hw q z) := hm
    _ = (GeometricLocalCartier.homologyTransferIso f p hU n w hw q).hom.hom
        (ModuleComplexNativeCycleClasses.cycleClass (Kn) q z) := ht.symm
    _ = _ := congrArg _ (nativeCycle_class f p n c a b F hF ha hc w hw q ω)

/-- In EVERY degree the entire original exterior-xi class is the existing original geometric Cartier map. -/
theorem exteriorClassSections_eq_inverseCartier (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    exteriorClassSections f p n hU c a b F hF ha hc w hw q =
      (GeometricAffineHomology.localSheafCartierSectionsIso f p n hU w hw q).hom := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := exteriorHomologyClass_native f p n hU c a b F hF ha hc w hw q x
  rw [DeligneIllusieLocalContinuationResidueCartier.classMap_eq_inverseCartier] at hx
  exact congrArg (GeometricAffineHomology.geometricHomologySectionsIso f p n hU q).hom.hom hx
/-- In every degree the SAME entire exterior-xi class is the original global Cartier component. -/
theorem exteriorClassSections_eq_globalInverseCartier (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    exteriorClassSections f p n hU c a b F hF ha hc w hw q =
      (GeometricSheafCartier.inverseCartierIso f p n q).hom.val.app (op WU) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  rw [exteriorClassSections_eq_inverseCartier]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (GeometricSheafCartier.inverseCartierIso_app_twistedOpen f p n hU w hw q x).symm

end EnvelopeProperty.DI.GeometricLeadingCartierExterior
