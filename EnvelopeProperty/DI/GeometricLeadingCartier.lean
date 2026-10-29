import EnvelopeProperty.DI.LeadingCartierCycleTransport
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationResidueCartier
import EnvelopeProperty.Cartier.GeometricHomologyNaturality

/-!
# The SAME geometric divided one-form induces original geometric Cartier

The actual residue reductions and original lift instantiate the published native
one-form theorem. The original source exterior/cotangent units, scalar restriction,
whole chart complex map, and canonical affine homology comparison carry that SAME
cycle and class to the original global geometric complex. No class/QI conclusion
is an input. The primary scheme has the declared pure relative dimension of the
standard geometric DI input.
-/
noncomputable section
namespace EnvelopeProperty.DI.GeometricLeadingCartier
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Cartier Cartier.FrobeniusLiftDifference
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace NativeClosed
variable {K B C S : Type u} {R : Type v}
  [Field K] [CommRing B] [CommRing C] [CommRing R] [CommRing S]
  [Algebra K B] [Algebra C K] [Algebra C R] [Algebra C S]
  (p : ℕ) [Fact p.Prime] [CharP K p]
private abbrev coefficientAlgebra : Algebra K (RelativeFrobenius.twist (algebraMap K B) p) :=
  (RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.toAlgebra
attribute [local instance] coefficientAlgebra
private abbrev coefficientCAlgebra : Algebra C (RelativeFrobenius.twist (algebraMap K B) p) :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] coefficientCAlgebra
private instance coefficientTower : IsScalarTower C K (RelativeFrobenius.twist (algebraMap K B) p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
  (hc : algebraMap C K = c.map) [Algebra.FormallySmooth C S]
private theorem closed {n : ℕ} (w : Fin n → B)
    (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale) :
    ModuleCat.ofHom
        (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
          (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
        (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1)
        (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc) ≫
      (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).d 1 2 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  change (SchemeRelativeFrobeniusAffineDeRham.differential w hw p 1).hom
    (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω) = 0
  exact DeligneIllusieLocalContinuationResidueCartier.oneFormMap_closed p c a b F hF ha hc w hw ω
end NativeClosed

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
private abbrev sourceSections : ModuleCat ((SchemeRelativeFrobenius.twist p f).presheaf.obj (op WU)) :=
  (CanonicalGeometry.exteriorCotangentSheaf g 1).val.obj (op WU)
local notation "M" => sourceSections (U := U) f p
private abbrev nativeSource : ModuleCat (T) :=
  ModuleCat.of (T) (KaehlerDifferential k (T))
private def nativeXi :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    nativeSource (U := U) f p ⟶ SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := Γ(X,U)) p 1 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact ModuleCat.ofHom (X := nativeSource (U := U) f p)
    (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := Γ(X,U)) p 1)
    (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc)
omit [SmoothOfRelativeDimension n f] in
private theorem nativeXi_closed :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; ∀ j, (ComplexShape.up ℕ).Rel 1 j →
    nativeXi f p c a b F hF ha hc ≫ (Kn).d 1 j = 0 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  intro j hj
  have hj' : 1+1 = j := hj
  subst j
  exact NativeClosed.closed p c a b F hF ha hc w hw
private def nativeCycle (ω : nativeSource (U := U) f p) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    LinearMap.ker ((Kn).sc 1).g.hom := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact ((Kn).sc 1).moduleCatCyclesIso.hom
    ((Kn).liftCycles (nativeXi f p c a b F hF ha hc) 2 (by simp)
      (nativeXi_closed f p n c a b F hF ha hc w hw 2 rfl) ω)
omit [SmoothOfRelativeDimension n f] in
private theorem nativeCycle_val (ω : nativeSource (U := U) f p) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (nativeCycle f p n c a b F hF ha hc w hw ω).val = nativeXi f p c a b F hF ha hc ω := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let y := (Kn).liftCycles (nativeXi f p c a b F hF ha hc) 2 (by simp)
    (nativeXi_closed f p n c a b F hF ha hc w hw 2 rfl) ω
  have hi := ((Kn).sc 1).moduleCatCyclesIso_inv_iCycles_apply (((Kn).sc 1).moduleCatCyclesIso.hom y)
  rw [Iso.hom_inv_id_apply] at hi
  have hc' := congrArg (fun L : nativeSource (U := U) f p ⟶ (Kn).X 1 => L ω)
    ((Kn).liftCycles_i (nativeXi f p c a b F hF ha hc) 2 (by simp)
      (nativeXi_closed f p n c a b F hF ha hc w hw 2 rfl))
  exact hi.symm.trans hc'
omit [SmoothOfRelativeDimension n f] in
private theorem nativeCycle_class (ω : nativeSource (U := U) f p) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ModuleComplexNativeCycleClasses.cycleClass (Kn) 1 (nativeCycle f p n c a b F hF ha hc w hw ω) =
      (DeligneIllusieLocalContinuationResidueCartier.oneFormClassMap p c a b F hF ha hc w hw).hom ω := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  have h := LeadingCartierCycleTransport.singleClassMap_cycleClass 1 (nativeSource (U := U) f p) (Kn)
    (nativeXi f p c a b F hF ha hc) (nativeXi_closed f p n c a b F hF ha hc w hw)
    ω (nativeCycle f p n c a b F hF ha hc w hw ω)
      (nativeCycle_val f p n c a b F hF ha hc w hw ω).symm
  exact h.symm
private def sourceXiMap :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    M ⟶ (RS).obj (nativeSource (U := U) f p) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (GeometricLocalCartier.domainIso f p hU n w hw 1).hom ≫
    (RS).map (ModuleCat.ofHom (exteriorPower.oneEquiv (T) (KaehlerDifferential k (T))).toLinearMap)
private def scalarXi :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    M ⟶ (Krs).X 1 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact sourceXiMap f p n hU w hw ≫ (RS).map (nativeXi f p c a b F hF ha hc)
omit [SmoothOfRelativeDimension n f] in
private theorem scalarXi_closed :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; ∀ j, (ComplexShape.up ℕ).Rel 1 j →
    scalarXi f p n hU c a b F hF ha hc w hw ≫ (Krs).d 1 j = 0 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  intro j hj
  change (sourceXiMap f p n hU w hw ≫ (RS).map (nativeXi f p c a b F hF ha hc)) ≫
    (RS).map ((Kn).d 1 j) = 0
  rw [Category.assoc, ← Functor.map_comp, nativeXi_closed f p n c a b F hF ha hc w hw j hj,
    Functor.map_zero, comp_zero]
private def scalarXiCochain :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (HomologicalComplex.single (ModuleCat Γ(SchemeRelativeFrobenius.twist p f,WU)) (.up ℕ) 1).obj M ⟶ Krs := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact HomologicalComplex.mkHomFromSingle (scalarXi f p n hU c a b F hF ha hc w hw)
      (scalarXi_closed f p n hU c a b F hF ha hc w hw)

/-- The actual original source units, SAME native xi, and original target exterior unit. -/
def xiSections :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    M ⟶ (Kg).X 1 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact scalarXi f p n hU c a b F hF ha hc w hw ≫ (ψ).hom.f 1

/-- Every original source section retains its literal source and target unit formula. -/
theorem xiSections_apply (x : M) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (xiSections f p n hU c a b F hF ha hc w hw).hom x =
      (CanonicalGeometry.exteriorCotangentSheaf f 1).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
          (EtaleAffineSectionDifferential.unitEquiv f hU w hw 1
            (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc
              ((exteriorPower.oneEquiv (T) (KaehlerDifferential k (T)))
                ((GeometricLocalCartier.domainIso f p hU n w hw 1).hom.hom x)))) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact GeometricComplexExchange.complexIso_hom_f_apply f p n hU w hw 1
    (nativeXi f p c a b F hF ha hc ((sourceXiMap f p n hU w hw).hom x))

/-- Closedness is derived for the SAME original section map and actual geometric differential. -/
theorem xiSections_closed :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    xiSections f p n hU c a b F hF ha hc w hw ≫ (Kg).d 1 2 = 0 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  unfold xiSections
  rw [Category.assoc, (ψ).hom.comm 1 2, ← Category.assoc,
    scalarXi_closed f p n hU c a b F hF ha hc w hw 2 rfl, zero_comp]

/-- The genuine original geometric local cochain representative of the SAME xi. -/
def xiCochain :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (HomologicalComplex.single (ModuleCat Γ(SchemeRelativeFrobenius.twist p f,WU)) (.up ℕ) 1).obj M ⟶ Kg := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact scalarXiCochain f p n hU c a b F hF ha hc w hw ≫ (ψ).hom

/-- Its entire original degree-one component is exactly the SAME xi section map. -/
theorem xiCochain_f_one :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (xiCochain f p n hU c a b F hF ha hc w hw).f 1 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 1 M).hom ≫
        xiSections f p n hU c a b F hF ha hc w hw := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  change (HomologicalComplex.mkHomFromSingle
    (scalarXi f p n hU c a b F hF ha hc w hw)
    (scalarXi_closed f p n hU c a b F hF ha hc w hw)).f 1 ≫ (ψ).hom.f 1 = _
  rw [HomologicalComplex.mkHomFromSingle_f]
  exact Category.assoc _ _ _

/-- Actual native homology of the original whole geometric cochain representative. -/
def xiHomologyClass :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    M ⟶ (Kg).homology 1 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 1 M).inv ≫
    HomologicalComplex.homologyMap (xiCochain f p n hU c a b F hF ha hc w hw) 1

/-- The original class lands in sections of the SAME actual global homology sheaf. -/
def xiClassSections :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U; M ⟶
    ((SchemeRelativeFrobeniusBasisDifferential.complex f p n).homology 1).val.obj (op WU) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact xiHomologyClass f p n hU c a b F hF ha hc w hw ≫
      (GeometricAffineHomology.geometricHomologySectionsIso f p n hU 1).hom

/-- The entire target comparison is the canonical original affine evaluation on SAME K. -/
theorem xiClassSections_eq_canonicalComparison :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    xiClassSections f p n hU c a b F hF ha hc w hw =
      xiHomologyClass f p n hU c a b F hF ha hc w hw ≫
        SchemeSectionHomology.comparison (SchemeRelativeFrobeniusBasisDifferential.complex f p n) WU 1 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let : ∀ q, ((SchemeRelativeFrobeniusBasisDifferential.complex f p n).X q).IsQuasicoherent :=
    fun q => GeometricRelativeFrobeniusQuasicoherent.complex_term_isQuasicoherent f p n q
  change _ ≫ (GeometricAffineHomology.homologySectionsIso
    (RelativeTwistedAffineBasis.twistedOpen_isAffine f p U hU)
    (SchemeRelativeFrobeniusBasisDifferential.complex f p n) 1).hom = _
  rw [GeometricHomologyNaturality.homologySectionsIso_hom_eq]

private theorem xiHomologyClass_native (x : M) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    (xiHomologyClass f p n hU c a b F hF ha hc w hw).hom x =
      (GeometricLocalCartier.homologyTransferIso f p hU n w hw 1).hom.hom
        ((DeligneIllusieLocalContinuationResidueCartier.oneFormClassMap p c a b F hF ha hc w hw).hom
          ((sourceXiMap f p n hU w hw).hom x)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let ω : nativeSource (U := U) f p := (sourceXiMap f p n hU w hw).hom x
  let z := nativeCycle f p n c a b F hF ha hc w hw ω
  let z' : LinearMap.ker ((Krs).sc 1).g.hom := ⟨z.val, z.property⟩
  have hs := LeadingCartierCycleTransport.singleClassMap_cycleClass 1 M (Krs)
    (scalarXi f p n hU c a b F hF ha hc w hw)
    (scalarXi_closed f p n hU c a b F hF ha hc w hw) x z'
      (nativeCycle_val f p n c a b F hF ha hc w hw ω).symm
  have hm := ModuleComplexNativeCycleClasses.homologyMap_cycleClass (ψ).hom 1 z'
    (GeometricLocalCartier.imageCycle f p hU n w hw 1 z) rfl
  have ht := GeometricLocalCartier.homologyTransferIso_cycleClass f p hU n w hw 1 z
  unfold xiHomologyClass xiCochain
  rw [HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap (ψ).hom 1).hom
      ((LeadingCartierCycleTransport.singleClassMap 1 M (Krs)
        (scalarXi f p n hU c a b F hF ha hc w hw)
        (scalarXi_closed f p n hU c a b F hF ha hc w hw)).hom x) = _
  calc
    _ = (HomologicalComplex.homologyMap (ψ).hom 1).hom
        (ModuleComplexNativeCycleClasses.cycleClass (Krs) 1 z') := congrArg _ hs
    _ = ModuleComplexNativeCycleClasses.cycleClass (Kg) 1
        (GeometricLocalCartier.imageCycle f p hU n w hw 1 z) := hm
    _ = (GeometricLocalCartier.homologyTransferIso f p hU n w hw 1).hom.hom
        (ModuleComplexNativeCycleClasses.cycleClass (Kn) 1 z) := ht.symm
    _ = _ := congrArg _ (nativeCycle_class f p n c a b F hF ha hc w hw ω)

/-- The ENTIRE actual geometric xi class is the original geometric Cartier morphism. -/
theorem xiClassSections_eq_inverseCartier :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    xiClassSections f p n hU c a b F hF ha hc w hw =
      (GeometricAffineHomology.localSheafCartierSectionsIso f p n hU w hw 1).hom := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := xiHomologyClass_native f p n hU c a b F hF ha hc w hw x
  rw [DeligneIllusieLocalContinuationResidueCartier.oneFormClassMap_eq_inverseCartier] at hx
  have he : (exteriorPower.oneEquiv (T) (KaehlerDifferential k (T))).symm
      ((sourceXiMap f p n hU w hw).hom x) =
      (GeometricLocalCartier.domainIso f p hU n w hw 1).hom.hom x := by
    change (exteriorPower.oneEquiv (T) (KaehlerDifferential k (T))).symm
      ((exteriorPower.oneEquiv (T) (KaehlerDifferential k (T))) _) = _
    exact LinearEquiv.symm_apply_apply _ _
  change (GeometricAffineHomology.geometricHomologySectionsIso f p n hU 1).hom.hom
      ((xiHomologyClass f p n hU c a b F hF ha hc w hw).hom x) =
    (GeometricAffineHomology.geometricHomologySectionsIso f p n hU 1).hom.hom
      ((GeometricLocalCartier.homologyTransferIso f p hU n w hw 1).hom.hom
        ((RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p 1).hom.hom
          ((GeometricLocalCartier.domainIso f p hU n w hw 1).hom.hom x)))
  rw [hx]
  exact congrArg _ (congrArg _ (congrArg _ he))
end EnvelopeProperty.DI.GeometricLeadingCartier
