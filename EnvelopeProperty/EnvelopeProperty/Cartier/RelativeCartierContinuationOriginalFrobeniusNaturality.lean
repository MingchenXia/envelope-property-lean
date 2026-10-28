import EnvelopeProperty.Cartier.RelativeCartierContinuationOriginalFrobeniusBridge
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierAllNaturality
import EnvelopeProperty.Cartier.EtaleAlgebraCartierNaturality

/-! # Actual original Frobenius bridge and corrected Cartier naturality

Only the actual original cochain/native homology map is reused from the older absolute
Cartier namespace. No perfect-field Cartier conclusion or coefficient root is used.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeOriginalFrobeniusNaturality
open CategoryTheory
open scoped Classical
universe u
variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
local notation "EA" => EtaleAlgebraFrobeniusComplex.complex v hv p
local notation "EB" => EtaleAlgebraFrobeniusComplex.complex w hw p
local notation "TA" => RelativeFrobenius.twist (algebraMap k A) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "SA" => (CommRingCat.Hom.hom (RelativeFrobenius.sourceMap (algebraMap k A) p))
local notation "SB" => (CommRingCat.Hom.hom (RelativeFrobenius.sourceMap (algebraMap k B) p))
local notation "τ" => (CommRingCat.Hom.hom
  (RelativeEtaleCartierNaturality.twistMap (k := k) (A := A) (B := B) p))

/-- The original actual all-algebra cochain map internally gives every ACTUAL target cycle,
including zero algebras; no closedness or image-value comparison is an input. -/
def originalImageCycle (q : ℕ) (z : LinearMap.ker ((EA).sc q).g.hom) :
    LinearMap.ker ((EB).sc q).g.hom := by
  let L := ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℕ)).obj EB
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℕ) q).map
    (EtaleAlgebraFrobeniusNaturality.complexMap p v hv w hw)
  let t : LinearMap.ker (L.sc q).g.hom := by
    refine ⟨φ.τ₂ z.val, ?_⟩
    have h := congrArg (fun f : ((EA).sc q).X₂ ⟶ (L.sc q).X₃ => f z.val) φ.comm₂₃
    change (L.sc q).g (φ.τ₂ z.val) = φ.τ₃ (((EA).sc q).g z.val) at h
    exact h.trans ((congrArg φ.τ₃ z.property).trans (φ.τ₃.hom.map_zero))
  exact ⟨t.val, t.property⟩

/-- Every original actual image cycle keeps the ENTIRE original canonical exterior value. -/
theorem originalImageCycle_val (q : ℕ) (z : LinearMap.ker ((EA).sc q).g.hom) :
    (originalImageCycle p v hv w hw q z).val =
      Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q z.val := rfl

/-- The EXISTING actual original native homology map preserves EVERY actual cycle class.
That reused nativeHomologyMap head has no perfection or target-characteristic assumption. -/
theorem originalHomologyMap_cycleClass (q : ℕ) (z : LinearMap.ker ((EA).sc q).g.hom) :
    EtaleAlgebraCartierNaturality.nativeHomologyMap p v hv w hw q
      (ModuleComplexNativeCycleClasses.cycleClass EA q z) =
    ModuleComplexNativeCycleClasses.cycleClass EB q (originalImageCycle p v hv w hw q z) := by
  let L := ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℕ)).obj EB
  let t : LinearMap.ker (L.sc q).g.hom :=
    ⟨(originalImageCycle p v hv w hw q z).val, (originalImageCycle p v hv w hw q z).property⟩
  have h := ModuleComplexNativeCycleClasses.homologyMap_cycleClass
    (EtaleAlgebraFrobeniusNaturality.complexMap p v hv w hw) q z t rfl
  exact (congrArg (ModuleComplexNativeCycleClasses.restrictionHomologyIso
    (algebraMap A B) EB q).hom h).trans
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso_cycleClass (algebraMap A B) EB q
      t (originalImageCycle p v hv w hw q z) rfl)

/-- The entire genuine source-square coefficient equality, derived from the ACTUAL twist map. -/
theorem sourceSquare : (SB).comp (algebraMap A B) = (τ).comp SA :=
  (congrArg CommRingCat.Hom.hom
    (RelativeEtaleCartierNaturality.twistMap_source (k := k) (A := A) (B := B) p)).symm

/-- The GENUINE standard scalar-functor comparison of the original source square on EVERY
native target-twist module, rather than an assumed comparison square. -/
def sourceScalarComparison : ModuleCat.restrictScalars τ ⋙ ModuleCat.restrictScalars SA ≅
    ModuleCat.restrictScalars SB ⋙ ModuleCat.restrictScalars (algebraMap A B) :=
  (ModuleCat.restrictScalarsComp' SA τ ((SB).comp (algebraMap A B))
    (sourceSquare (k := k) (A := A) (B := B) p)).symm ≪≫
      ModuleCat.restrictScalarsComp (algebraMap A B) SB

attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra

/-- Genuine original source-restricted twist exterior maps, INCLUDING zero algebras. -/
def exteriorMap (q : ℕ) : (ModuleCat.restrictScalars SA).obj
    (ModuleCat.of TA (⋀[TA]^q (KaehlerDifferential k TA))) ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((ModuleCat.restrictScalars SB).obj
          (ModuleCat.of TB (⋀[TB]^q (KaehlerDifferential k TB)))) :=
  (ModuleCat.restrictScalars SA).map
    (RelativeEtaleCartierAllNaturality.exteriorMap (k := k) (A := A) (B := B) p q) ≫
      (sourceScalarComparison (k := k) (A := A) (B := B) p).hom.app
        (ModuleCat.of TB (⋀[TB]^q (KaehlerDifferential k TB)))

variable [CharP A p] [CharP B p]
local notation "RA" => RelativeEtaleDeRham.complex v hv p
local notation "RB" => RelativeEtaleDeRham.complex w hw p

/-- The SAME actual original whole restriction maps commute with the ACTUAL full native
relative-to-original bridges and the genuine source-square scalar functor comparison. -/
theorem complexIso_naturality : (RelativeOriginalFrobeniusBridge.complexIso p v hv).hom ≫
    EtaleAlgebraFrobeniusNaturality.complexMap p v hv w hw =
  ((ModuleCat.restrictScalars SA).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (RelativeEtaleCartierNaturality.complexMap p v hv w hw) ≫
    (NatIso.mapHomologicalComplex (sourceScalarComparison (k := k) (A := A) (B := B) p)
      (ComplexShape.up ℕ)).hom.app RB ≫
    ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (RelativeOriginalFrobeniusBridge.complexIso p w hw).hom := by
  ext q a
  rfl

/-- The actual original cycle images commute with the actual relative-to-original bridge. -/
theorem imageCycle_absoluteCycle (q : ℕ) (z : LinearMap.ker ((RA).sc q).g.hom) :
    originalImageCycle p v hv w hw q (RelativeOriginalFrobeniusBridge.absoluteCycle p v hv q z) =
      RelativeOriginalFrobeniusBridge.absoluteCycle p w hw q
        (RelativeEtaleCartierNaturality.imageCycle p v hv w hw q z) := by
  apply Subtype.ext
  rw [originalImageCycle_val, RelativeOriginalFrobeniusBridge.absoluteCycle_val,
    RelativeOriginalFrobeniusBridge.absoluteCycle_val, RelativeEtaleCartierNaturality.imageCycle_val]

/-- The GENUINE actual relative-to-original native Hq bridge is natural on EVERY original
native homology element, with the standard actual source-square scalar comparison. -/
theorem homologyIso_naturality (q : ℕ) : (RelativeOriginalFrobeniusBridge.homologyIso p v hv q).hom ≫
    EtaleAlgebraCartierNaturality.nativeHomologyMap p v hv w hw q =
  (ModuleCat.restrictScalars SA).map (RelativeEtaleCartierNaturality.homologyMap p v hv w hw q) ≫
    (sourceScalarComparison (k := k) (A := A) (B := B) p).hom.app ((RB).homology q) ≫
    (ModuleCat.restrictScalars (algebraMap A B)).map
      (RelativeOriginalFrobeniusBridge.homologyIso p w hw q).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := RelativeEtaleCartierAllNaturality.nativeCycleClass_surjective RA q x
  change EtaleAlgebraCartierNaturality.nativeHomologyMap p v hv w hw q
      ((RelativeOriginalFrobeniusBridge.homologyIso p v hv q).hom
        (ModuleComplexNativeCycleClasses.cycleClass RA q z)) =
    (RelativeOriginalFrobeniusBridge.homologyIso p w hw q).hom
      (RelativeEtaleCartierNaturality.homologyMap p v hv w hw q
        (ModuleComplexNativeCycleClasses.cycleClass RA q z))
  rw [RelativeOriginalFrobeniusBridge.homologyIso_cycleClass, originalHomologyMap_cycleClass,
    RelativeEtaleCartierNaturality.homologyMap_cycleClass, RelativeOriginalFrobeniusBridge.homologyIso_cycleClass]
  exact congrArg (ModuleComplexNativeCycleClasses.cycleClass EB q)
    (imageCycle_absoluteCycle p v hv w hw q z)

/-- The CORRECT original Cartier isomorphisms (source-restricted Ω_T, not Ω_A) are natural
as ENTIRE native original module maps in EVERY degree, including degree zero. -/
theorem correctedCartierIso_naturality (q : ℕ) :
    (RelativeOriginalFrobeniusBridge.correctedCartierIso p v hv q).hom ≫
      EtaleAlgebraCartierNaturality.nativeHomologyMap p v hv w hw q =
    exteriorMap (k := k) (A := A) (B := B) p q ≫
      (ModuleCat.restrictScalars (algebraMap A B)).map
        (RelativeOriginalFrobeniusBridge.correctedCartierIso p w hw q).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change EtaleAlgebraCartierNaturality.nativeHomologyMap p v hv w hw q
      ((RelativeOriginalFrobeniusBridge.homologyIso p v hv q).hom
        ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a)) =
    (RelativeOriginalFrobeniusBridge.homologyIso p w hw q).hom
      ((RelativeEtaleCartierDomain.inverseCartierIso w hw p q).hom
        (RelativeEtaleCartierAllNaturality.exteriorMap (k := k) (A := A) (B := B) p q a))
  have hb := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (homologyIso_naturality p v hv w hw q))
      ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a)
  change EtaleAlgebraCartierNaturality.nativeHomologyMap p v hv w hw q
      ((RelativeOriginalFrobeniusBridge.homologyIso p v hv q).hom
        ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a)) =
    (RelativeOriginalFrobeniusBridge.homologyIso p w hw q).hom
      (RelativeEtaleCartierNaturality.homologyMap p v hv w hw q
        ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a)) at hb
  have hc := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (RelativeEtaleCartierAllNaturality.inverseCartierIso_naturality p v hv w hw q)) a
  change RelativeEtaleCartierNaturality.homologyMap p v hv w hw q
      ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a) =
    (RelativeEtaleCartierDomain.inverseCartierIso w hw p q).hom
      (RelativeEtaleCartierAllNaturality.exteriorMap (k := k) (A := A) (B := B) p q a) at hc
  exact hb.trans (congrArg (RelativeOriginalFrobeniusBridge.homologyIso p w hw q).hom hc)

end EnvelopeProperty.Cartier.RelativeOriginalFrobeniusNaturality
