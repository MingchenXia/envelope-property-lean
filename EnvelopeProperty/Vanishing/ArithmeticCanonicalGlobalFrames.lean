import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalRestriction
import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility

/-! # Constructed global relative canonical lines over arithmetic bases

All affine coordinate maps, localization comparisons and standard-smooth
frames are derived from the original structural morphism. No gluing or
canonical-line model certificate is supplied.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace PrimeSpectrum

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalFrames

open CanonicalGeometry ArithmeticCanonicalGlobal

section Affine

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]

local instance (U : (Spec A).Opensᵒᵖ) : Module ((Spec A).presheaf.obj U)
    ((relativeCotangentPresheaf (affineStructure R A)).obj U) :=
  ((relativeCotangentPresheaf (affineStructure R A)).obj U).isModule

def ordinaryToOpen (U : (Spec A).Opensᵒᵖ) :
    ModuleCat.of A (KaehlerDifferential R A) ⟶
      (ArithmeticCanonicalGlobal.affineCotangentAPresheaf R A).obj U :=
  (ArithmeticCanonicalGlobal.affineCotangentModuleIso R A).inv ≫
    ArithmeticCanonicalGlobal.affineCotangentToOpen R A U

theorem ordinaryToOpen_naturality {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V) :
    ordinaryToOpen R A U ≫
        (ArithmeticCanonicalGlobal.affineCotangentAPresheaf R A).map i =
      ordinaryToOpen R A V := by
  simp only [ordinaryToOpen, Category.assoc,
    ArithmeticCanonicalGlobal.affineCotangentToOpen_naturality]

theorem ordinaryToOpen_isLocalized (r : A) :
    IsLocalizedModule (.powers r) (ordinaryToOpen R A (.op (basicOpen r))).hom := by
  have := ArithmeticCanonicalGlobal.affineCotangentToOpen_isLocalized R A r
  exact IsLocalizedModule.of_linearEquiv_right (.powers r)
    (ArithmeticCanonicalGlobal.affineCotangentToOpen R A (.op (basicOpen r))).hom
    (ArithmeticCanonicalGlobal.affineCotangentModuleIso R A).symm.toLinearEquiv

def ordinarySemilinear (U : (Spec A).Opensᵒᵖ) :
    (KaehlerDifferential R A) →ₛₗ[(affineCoordinateMap A U).hom]
      ((relativeCotangentPresheaf (affineStructure R A)).obj U) where
  toFun x := ordinaryToOpen R A U x
  map_add' := (ordinaryToOpen R A U).hom.map_add
  map_smul' := (ordinaryToOpen R A U).hom.map_smul

def exteriorToOpen (q : ℕ) (U : (Spec A).Opensᵒᵖ) :
    ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A)) ⟶
      (specPresheafToAModules A
        (relativeExteriorPresheaf (affineStructure R A) q)).obj U := by
  let ψ := exteriorSemilinearMap (affineCoordinateMap A U).hom (ordinarySemilinear R A U) q
  exact ModuleCat.ofHom
    (X := ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A)))
    (Y := (specPresheafToAModules A
      (relativeExteriorPresheaf (affineStructure R A) q)).obj U)
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := ψ.map_smulₛₗ }

theorem exteriorToOpen_wedge (q : ℕ) (U : (Spec A).Opensᵒᵖ)
    (m : Fin q → KaehlerDifferential R A) :
    (exteriorToOpen R A q U).hom (exteriorPower.ιMulti A q m) =
      exteriorPower.ιMulti ((Spec A).presheaf.obj U) q ((ordinarySemilinear R A U) ∘ m) := by
  dsimp only [exteriorToOpen]
  exact exteriorSemilinearMap_ιMulti (A := A) (B := (Spec A).presheaf.obj U)
    (M := KaehlerDifferential R A)
    (N := (relativeCotangentPresheaf (affineStructure R A)).obj U)
    (affineCoordinateMap A U).hom (ordinarySemilinear R A U) q m

theorem exteriorToOpen_naturality (q : ℕ) {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V) :
    exteriorToOpen R A q U ≫
        (specPresheafToAModules A
          (relativeExteriorPresheaf (affineStructure R A) q)).map i =
      exteriorToOpen R A q V := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on (exteriorPower.ιMulti_span A q (KaehlerDifferential R A))
  rintro _ ⟨m, rfl⟩
  change (relativeExteriorPresheaf (affineStructure R A) q).map i
      ((exteriorToOpen R A q U).hom (exteriorPower.ιMulti A q m)) =
    (exteriorToOpen R A q V).hom (exteriorPower.ιMulti A q m)
  rw [exteriorToOpen_wedge, exteriorToOpen_wedge]
  erw [exteriorPresheaf_map_mk]
  congr 1
  funext j
  exact congr($(ordinaryToOpen_naturality R A i).hom (m j))

set_option backward.isDefEq.respectTransparency false in
theorem exteriorToOpen_isLocalized {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A)) (q : ℕ) (r : A) :
    IsLocalizedModule (.powers r) (exteriorToOpen R A q (.op (basicOpen r))).hom := by
  have hloc : IsLocalization (.powers r) Γ(Spec A, basicOpen r) := inferInstance
  let U : (Spec A).Opensᵒᵖ := .op (basicOpen r)
  let B := (Spec A).presheaf.obj U
  let P := relativeCotangentPresheaf (affineStructure R A)
  let : Algebra A B := (affineCoordinateMap A U).hom.toAlgebra
  let : Module A (P.obj U) :=
    ((ArithmeticCanonicalGlobal.affineCotangentAPresheaf R A).obj U).isModule
  let : IsScalarTower A B (P.obj U) := .of_algebraMap_smul fun _ _ => rfl
  have : IsLocalization (.powers r) B := by
    convert! hloc using 1
    apply Algebra.algebra_ext
    intro a
    rfl
  let φ : KaehlerDifferential R A →ₗ[A] P.obj U :=
    { toFun := ordinarySemilinear R A U
      map_add' := (ordinarySemilinear R A U).map_add
      map_smul' := (ordinarySemilinear R A U).map_smulₛₗ }
  have : IsLocalizedModule (.powers r) φ := ordinaryToOpen_isLocalized R A r
  exact algebraExteriorLinearMap_isLocalizedModule (B := B) (.powers r) b φ q

/-- The global exterior object on an actual free differential chart has its
derived associated-module model, over the same original arithmetic ring. -/
def affineExteriorSheafIso {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A)) (q : ℕ) :
    relativeExteriorSheaf (affineStructure R A) q ≅
      ArithmeticCanonicalAffine.relativeExteriorModel R A q :=
  affineLocalizedSheafificationIso A
    (relativeExteriorPresheaf (affineStructure R A) q)
    (ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A))) (exteriorToOpen R A q)
    (exteriorToOpen_naturality R A q) (exteriorToOpen_isLocalized R A b q)

/-- The actual top exterior object on a standard-smooth arithmetic chart
has a genuine rank-one sheaf frame, derived from its actual Kähler basis. -/
def affineCanonicalFrame (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    relativeExteriorSheaf (affineStructure R A) n ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
  affineExteriorSheafIso R A (standardSmoothDifferentialBasis R A n) n ≪≫
    affineSheafFrameOfTrivialization (affineCanonicalTrivialization
      (standardSmoothDifferentialBasis R A n))

/-- The newly constructed global exterior object has its actual categorical
field-fibre comparison on every standard-smooth affine arithmetic chart. -/
def affineFieldFiberExteriorIso (k : Type u) [Field k] [Algebra R k]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A] (q : ℕ) :
    (Scheme.Modules.pullback (ArithmeticCanonicalAffine.fiberProjection R k A)).obj
      (relativeExteriorSheaf (affineStructure R A) q) ≅
        exteriorCotangentSheaf (ArithmeticCanonicalAffine.fiberStructure R k A) q :=
  (Scheme.Modules.pullback (ArithmeticCanonicalAffine.fiberProjection R k A)).mapIso
      (affineExteriorSheafIso R A (standardSmoothDifferentialBasis R A n) q) ≪≫
    ArithmeticCanonicalAffine.fiberExteriorIso R k A n q

end Affine

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual global relative canonical object, before any line assertion. -/
def canonicalObject (n : ℕ) : X.Modules := relativeExteriorSheaf f n

/-- Specializing the constructed whole object to a field retains the existing
native canonical sheaf of the same original structural morphism. -/
def canonicalObject_fieldIso {k : Type u} [Field k] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of k)) (n : ℕ) :
    canonicalObject h n ≅ canonicalLineSheaf h n :=
  fieldExteriorIso h n

set_option backward.isDefEq.respectTransparency false in
/-- A genuine standard-smooth arithmetic chart gives an actual frame of the
constructed whole global top exterior object on its actual open site. -/
def chartFrame {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants f).app (.op V)).hom) :
    LocalBundleFrame (canonicalObject f n) V := by
  let A : CommRingCat.{u} := Γ(X, V)
  let φ : CommRingCat.of R ⟶ A := (relativeConstants f).app (.op V)
  letI : Algebra R A := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n R A := hs
  have he : hV.fromSpec ≫ f = affineStructure R A := affineChartStructure f hV
  let E : (Scheme.Modules.restrictFunctor hV.fromSpec).obj (canonicalObject f n) ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
    ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f hV.fromSpec n ≪≫
      eqToIso (congrArg (fun q => relativeExteriorSheaf q n) he) ≪≫
      affineCanonicalFrame R A n
  let EV : (Scheme.Modules.restrictFunctor V.ι).obj (canonicalObject f n) ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).symm.app
      (canonicalObject f n) ≪≫
    (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app
      (canonicalObject f n) ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso E ≪≫
      Scheme.Modules.restrictUnitIso hV.isoSpec.hom
  exact (Scheme.Modules.overEquiv V).unitIso.app ((canonicalObject f n).over V) ≪≫
    (Scheme.Modules.overEquiv V).inverse.mapIso
      ((Scheme.Modules.overFunctorEquiv V).app (canonicalObject f n) ≪≫ EV) ≪≫
    V.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf

/-- The actual fixed-base smooth-chart producer supplies every chart and
its original scalar structure, instead of accepting an atlas certificate. -/
def selectedChart (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    {V : X.Opens // IsAffineOpen V ∧ x ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n
        ((relativeConstants f).app (.op V)).hom} := by
  let h := exists_standardSmoothChart f n x
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

def selectedFrame (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    LocalBundleFrame (canonicalObject f n) (selectedChart f n x).val :=
  chartFrame f (selectedChart f n x).property.1 n (selectedChart f n x).property.2.2

/-- A whole global canonical line atlas is produced from actual arithmetic
smoothness; no gluing datum or model-line certificate is an input. -/
def canonicalAtlas (n : ℕ) [SmoothOfRelativeDimension n f] :
    LineBundleAtlas (canonicalObject f n) where
  I := X
  opens x := (selectedChart f n x).val
  covers x := ⟨x, (selectedChart f n x).property.2.1⟩
  frame x := selectedFrame f n x

/-- The constructed actual global relative canonical object is a native
invertible module over any original arithmetic base ring. -/
theorem canonicalObject_isInvertible (n : ℕ) [SmoothOfRelativeDimension n f] :
    Scheme.Modules.IsInvertible (canonicalObject f n) :=
  (canonicalAtlas f n).isInvertible

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalFrames
