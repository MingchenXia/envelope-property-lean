import EnvelopeProperty.Vanishing.ArithmeticCanonicalAffine

/-! # Actual global relative differential objects over arithmetic bases

The constants and universal derivations use the actual structural morphism
over an arbitrary commutative ring. No global module or comparison certificate
is an input. Field objects are the existing native objects by definition.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobal

open CanonicalGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Actual structural constants on every original open, over any ring. -/
def relativeConstants : constantRingPresheaf R X ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ X.presheaf.map U.unop.leTop.op
  naturality {U V} i := by
    dsimp [constantRingPresheaf]
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp]
    congr 2

/-- The original global relative Kähler presheaf, over any arithmetic ring. -/
def relativeCotangentPresheaf : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' (relativeConstants f)

def relativeDerivation :
    (relativeCotangentPresheaf f).Derivation' (relativeConstants f) :=
  PresheafOfModules.DifferentialsConstruction.derivation' (relativeConstants f)

def relativeUniversal : (relativeDerivation f).Universal :=
  PresheafOfModules.DifferentialsConstruction.isUniversal' (relativeConstants f)

/-- The actual global relative cotangent sheaf is constructed by sheafification. -/
def relativeCotangentSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeCotangentPresheaf f)

def relativeCotangentSheafificationMap :
    relativeCotangentPresheaf f ⟶ (relativeCotangentSheaf f).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- The actual global universal property, rather than a prescribed model object. -/
def relativePresheafHomEquiv (M : X.PresheafOfModules) :
    (relativeCotangentPresheaf f ⟶ M) ≃ M.Derivation' (relativeConstants f) where
  toFun g := (relativeDerivation f).postcomp g
  invFun d := (relativeUniversal f).desc d
  left_inv _g := (relativeUniversal f).postcomp_injective _ _ ((relativeUniversal f).fac _)
  right_inv d := (relativeUniversal f).fac d

def relativeSheafHomEquiv (M : X.Modules) :
    (relativeCotangentSheaf f ⟶ M) ≃ M.val.Derivation' (relativeConstants f) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (relativePresheafHomEquiv f _)

/-- Global relative exterior forms are constructed from the same original
cotangent presheaf and its actual restriction maps. -/
def relativeExteriorPresheaf (q : ℕ) : X.PresheafOfModules :=
  exteriorPresheaf (relativeCotangentPresheaf f) q

def relativeExteriorSheaf (q : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeExteriorPresheaf f q)

/-- Over a field, the construction is definitionally the existing native sheaf. -/
def fieldCotangentIso {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) : relativeCotangentSheaf g ≅ cotangentSheaf g :=
  Iso.refl _

def fieldExteriorIso {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) (q : ℕ) :
    relativeExteriorSheaf g q ≅ exteriorCotangentSheaf g q :=
  Iso.refl _

section Affine

variable (R) (A : CommRingCat.{u}) [Algebra R A]

def affineBaseRingMap : CommRingCat.of R ⟶ A := CommRingCat.ofHom (algebraMap R A)

def affineStructure : Spec A ⟶ Spec (.of R) := Spec.map (affineBaseRingMap R A)

def affineCotangentModule : ModuleCat A :=
  CommRingCat.KaehlerDifferential (affineBaseRingMap R A)

def affineCotangentAPresheaf : TopCat.Presheaf (ModuleCat A) (Spec A) :=
  specPresheafToAModules A (relativeCotangentPresheaf (affineStructure R A))

theorem affineConstantsSquare (U : (Spec A).Opensᵒᵖ) :
    affineBaseRingMap R A ≫ affineCoordinateMap A U =
      (relativeConstants (affineStructure R A)).app U := by
  simp only [relativeConstants, affineStructure, affineCoordinateMap]
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate Kähler map is derived from the actual structural square. -/
def affineCotangentToOpen (U : (Spec A).Opensᵒᵖ) :
    affineCotangentModule R A ⟶ (affineCotangentAPresheaf R A).obj U :=
  CommRingCat.KaehlerDifferential.map
    (f := affineBaseRingMap R A)
    (f' := (relativeConstants (affineStructure R A)).app U)
    (g := 𝟙 (CommRingCat.of R))
    (g' := affineCoordinateMap A U)
    (by simpa using (affineConstantsSquare R A U).symm)

set_option backward.isDefEq.respectTransparency false in
theorem affineCotangentToOpen_d (U : (Spec A).Opensᵒᵖ) (a : A) :
    affineCotangentToOpen R A U (CommRingCat.KaehlerDifferential.d a) =
      (relativeDerivation (affineStructure R A)).d (affineCoordinateMap A U a) :=
  CommRingCat.KaehlerDifferential.map_d _ a

set_option backward.isDefEq.respectTransparency false in
theorem affineCotangentToOpen_naturality {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V) :
    affineCotangentToOpen R A U ≫ (affineCotangentAPresheaf R A).map i =
      affineCotangentToOpen R A V := by
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  change (relativeCotangentPresheaf (affineStructure R A)).map i
      (affineCotangentToOpen R A U (CommRingCat.KaehlerDifferential.d a)) =
    affineCotangentToOpen R A V (CommRingCat.KaehlerDifferential.d a)
  rw [affineCotangentToOpen_d, affineCotangentToOpen_d]
  exact ((relativeDerivation (affineStructure R A)).d_map i
      (affineCoordinateMap A U a)).symm.trans
    (congrArg (relativeDerivation (affineStructure R A)).d
      (congr($(affineCoordinateMap_naturality A i) a)))

set_option backward.isDefEq.respectTransparency false in
/-- On every actual principal open the Kähler map is genuine localization. -/
theorem affineCotangentToOpen_isLocalized (r : A) :
    IsLocalizedModule (.powers r)
      (affineCotangentToOpen R A (.op (PrimeSpectrum.basicOpen r))).hom := by
  have hloc : IsLocalization (.powers r) Γ(Spec A, PrimeSpectrum.basicOpen r) := inferInstance
  let U : (Spec A).Opensᵒᵖ := .op (PrimeSpectrum.basicOpen r)
  let f₀ : CommRingCat.of R ⟶ A := affineBaseRingMap R A
  let f₁ : CommRingCat.of R ⟶ (Spec A).presheaf.obj U :=
    (relativeConstants (affineStructure R A)).app U
  let g₁ := affineCoordinateMap A U
  let : Algebra R A := f₀.hom.toAlgebra
  let : Algebra R ((Spec A).presheaf.obj U) := f₁.hom.toAlgebra
  let : Algebra A ((Spec A).presheaf.obj U) := g₁.hom.toAlgebra
  have : IsScalarTower R A ((Spec A).presheaf.obj U) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      (affineConstantsSquare R A U)).symm
  have : IsLocalization (.powers r) ((Spec A).presheaf.obj U) := by
    convert! hloc using 1
    apply Algebra.algebra_ext
    intro a
    rfl
  change IsLocalizedModule (.powers r)
    (_root_.KaehlerDifferential.map R R A ((Spec A).presheaf.obj U))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
def affineCotangentModuleIso :
    affineCotangentModule R A ≅ ModuleCat.of A (KaehlerDifferential R A) := by
  let F : Algebra R A → ModuleCat A := fun a =>
    letI := a
    ModuleCat.of A (KaehlerDifferential R A)
  exact eqToIso (congrArg F (toAlgebra_algebraMap (R := R) (S := A)))

/-- The whole constructed global sheaf has its actual affine Kähler model. -/
def affineCotangentSheafIso :
    relativeCotangentSheaf (affineStructure R A) ≅
      ArithmeticCanonicalAffine.relativeCotangentModel R A :=
  affineLocalizedSheafificationIso A
      (relativeCotangentPresheaf (affineStructure R A))
      (affineCotangentModule R A) (affineCotangentToOpen R A)
      (fun i => affineCotangentToOpen_naturality R A i)
      (affineCotangentToOpen_isLocalized R A) ≪≫
    (tilde.functor A).mapIso (affineCotangentModuleIso R A)

/-- The global construction on an affine model has the actual categorical
field-fibre comparison, with both original projections retained. -/
def affineFieldFiberCotangentIso (k : Type u) [Field k] [Algebra R k] :
    (Scheme.Modules.pullback
      (ArithmeticCanonicalAffine.fiberProjection R k A)).obj
      (relativeCotangentSheaf (affineStructure R A)) ≅
        cotangentSheaf (ArithmeticCanonicalAffine.fiberStructure R k A) :=
  (Scheme.Modules.pullback (ArithmeticCanonicalAffine.fiberProjection R k A)).mapIso
      (affineCotangentSheafIso R A) ≪≫
    ArithmeticCanonicalAffine.fiberCotangentIso R k A

end Affine

/-- The actual coordinate structure on any affine open is derived from the
original global constant map, without a field or target-point assumption. -/
theorem affineChartStructure {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ f = Spec.map ((relativeConstants f).app (.op V)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV
    (show V ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  congr 1

/-- Fixed-affine-base smoothness yields actual source-local standard
smoothness over the original ring R. It does not force a target open to be top. -/
theorem affineChart_locallyStandardSmooth {V : X.Opens} (hV : IsAffineOpen V)
    (n : ℕ) [SmoothOfRelativeDimension n f] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      ((relativeConstants f).app (.op V)).hom := by
  let φ : CommRingCat.of R ⟶ Γ(X, V) := (relativeConstants f).app (.op V)
  change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ.hom
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n) (φ := φ)).mp
  have he : hV.fromSpec ≫ f = Spec.map φ := affineChartStructure f hV
  have h := AlgebraicGeometry.smoothOfRelativeDimension_comp
    (n := 0) (m := n) hV.fromSpec f
  have h' : SmoothOfRelativeDimension n (hV.fromSpec ≫ f) := by
    simpa only [Nat.zero_add] using h
  exact he ▸ h'

private theorem principalOpen_standardSmooth {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, V)) (n : ℕ)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X, V) (Localization.Away r)).comp
        ((relativeConstants f).app (.op V)).hom)) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants f).app (.op (X.basicOpen r))).hom := by
  let A : CommRingCat.{u} := Γ(X, V)
  let B : CommRingCat.{u} := Γ(X, X.basicOpen r)
  let ρ : A ⟶ B := X.presheaf.map (homOfLE (X.basicOpen_le r)).op
  let : Algebra A B := ρ.hom.toAlgebra
  let : IsLocalization.Away r B := by
    convert! hV.isLocalization_basicOpen r using 1
  let e : Localization.Away r ≃ₐ[A] B :=
    IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) B
  have he₀ : RingHom.IsStandardSmoothOfRelativeDimension 0 e.toRingHom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv e.toRingEquiv
  have he := he₀.comp h
  have hρ : e.toRingHom.comp (algebraMap A (Localization.Away r)) = ρ.hom := by
    ext a
    exact e.commutes a
  have hc : (relativeConstants f).app (.op V) ≫ ρ =
      (relativeConstants f).app (.op (X.basicOpen r)) := by
    have hn := (relativeConstants f).naturality (homOfLE (X.basicOpen_le r)).op
    change 𝟙 _ ≫ (relativeConstants f).app (.op (X.basicOpen r)) =
      (relativeConstants f).app (.op V) ≫ ρ at hn
    exact hn.symm.trans (Category.id_comp _)
  have hm : e.toRingHom.comp
      ((algebraMap A (Localization.Away r)).comp
        ((relativeConstants f).app (.op V)).hom) =
      ((relativeConstants f).app (.op (X.basicOpen r))).hom := by
    rw [← RingHom.comp_assoc, hρ]
    exact congrArg CommRingCat.Hom.hom hc
  have he' : RingHom.IsStandardSmoothOfRelativeDimension n
      (e.toRingHom.comp ((algebraMap A (Localization.Away r)).comp
        ((relativeConstants f).app (.op V)).hom)) := by
    simpa only [Nat.zero_add] using he
  exact hm ▸ he'

/-- Every point on the actual smooth arithmetic family has a genuine affine
chart standard smooth of the prescribed dimension over the original R.
The source-local ring-hom property solves the general-base-open obligation. -/
theorem exists_standardSmoothChart (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      RingHom.IsStandardSmoothOfRelativeDimension n
        ((relativeConstants f).app (.op V)).hom := by
  obtain ⟨_, _, V, hV, hx, _, _⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  obtain ⟨s, hs, h⟩ := affineChart_locallyStandardSmooth f hV n
  have hcover : (⨆ r : s, X.basicOpen r.val) = V := hV.iSup_basicOpen_eq_self_iff.mpr hs
  have hx' : x ∈ ⨆ r : s, X.basicOpen r.val := hcover.symm ▸ hx
  obtain ⟨r, hxr⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  exact ⟨X.basicOpen r.val, hV.basicOpen r.val, hxr,
    principalOpen_standardSmooth f hV r.val n (h r.val r.property)⟩

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobal
