import EnvelopeProperty.ComplexGeometry.Schemes.ProjectiveSectionExtension
import Mathlib.RingTheory.Localization.Integer

/-! # Genuine affine-chart section generators and generic denominator clearing

The affine chart map and the line atlas produce finite local section modules.
The generic coefficients are then cleared over these actual coordinate rings.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace

namespace ComplexSchemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {X : Scheme.{u}} {R : CommRingCat.{u}} {L : X.Modules}

/-- Restriction along a genuine open immersion transports the actual sheaf frame. -/
def LineBundleAtlas.restrictFrame {Y : Scheme.{u}} (a : LineBundleAtlas L)
    (f : Y ⟶ X) [IsOpenImmersion f] (i : a.I) :
    LocalBundleFrame (L.restrict f) (f ⁻¹ᵁ a.opens i) := by
  let U := a.opens i
  let V := f ⁻¹ᵁ U
  let e : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.overFunctorEquiv U).app L).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso (a.frame i) ≪≫
      (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  let e' : (L.restrict f).restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorComp V.ι f).app L).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι f U).symm).app L ≪≫
      (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app L ≪≫
      (Scheme.Modules.restrictFunctor (f ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (f ∣_ U)
  exact (Scheme.Modules.overEquiv V).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv V).app (L.restrict f) ≪≫ e' ≪≫
      (Scheme.Modules.restrictUnitIso V.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv V).app (SheafOfModules.unit Y.ringCatSheaf)).symm)

/-- The actual rank-one atlas pulls back along every genuine open chart map. -/
def LineBundleAtlas.restrict {Y : Scheme.{u}} (a : LineBundleAtlas L)
    (f : Y ⟶ X) [IsOpenImmersion f] : LineBundleAtlas (L.restrict f) where
  I := a.I
  opens i := f ⁻¹ᵁ a.opens i
  covers x := a.covers (f x)
  frame i := a.restrictFrame f i

/-- Principal opens in a true affine chart whose images refine the genuine atlas. -/
def LineBundleAtlas.chartFrameFunctions (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] : Set R :=
  {g | ∃ i, f ''ᵁ PrimeSpectrum.basicOpen g ≤ a.opens i}

/-- The actual pulled-back frame cover gives the unit ideal of the actual affine chart ring. -/
theorem LineBundleAtlas.chartFrameFunctions_span (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] :
    Ideal.span (a.chartFrameFunctions f) = ⊤ := by
  rw [← Subtype.range_val (s := a.chartFrameFunctions f)]
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := a.covers (f x)
  have hx : x ∈ f ⁻¹ᵁ a.opens i := hi
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hgi⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx (f ⁻¹ᵁ a.opens i).isOpen
  refine Opens.mem_iSup.mpr ⟨⟨g, i, ?_⟩, hxg⟩
  exact (f.image_mono hgi).trans (f.image_preimage_le (a.opens i))

/-- A genuine image frame gives actual coefficients in the actual affine-chart section ring. -/
def LineBundleAtlas.chartFrameSectionsEquiv (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] (g : a.chartFrameFunctions f) :
    Γ(L.restrict f, PrimeSpectrum.basicOpen g.val) ≃ₗ[Γ(Spec R, PrimeSpectrum.basicOpen g.val)]
      Γ(Spec R, PrimeSpectrum.basicOpen g.val) := by
  let i := g.property.choose
  let c := localFrameCoefficientsOn (a.frame i) (homOfLE g.property.choose_spec)
  let e := (f.appIso (PrimeSpectrum.basicOpen g.val)).commRingCatIsoToRingEquiv
  refine { c.toAddEquiv.trans e.toAddEquiv with map_smul' := ?_ }
  intro r s
  change e (c ((f.appIso (PrimeSpectrum.basicOpen g.val)).inv r •
    (show bundleSections L (f ''ᵁ PrimeSpectrum.basicOpen g.val) from s))) = r * e (c s)
  rw [c.map_smul]
  change e (e.symm r * c s) = r * e (c s)
  rw [map_mul, e.apply_symm_apply]

/-- Real local chart frames produce finite local section modules over the real regular rings. -/
theorem LineBundleAtlas.chartFrameSections_finite (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] (g : a.chartFrameFunctions f) :
    Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen g.val)
      Γ(L.restrict f, PrimeSpectrum.basicOpen g.val) :=
  Module.Finite.equiv (a.chartFrameSectionsEquiv f g).symm

/-- Every genuine affine chart has finitely generated actual line-sheaf sections.
Both quasicoherence and the local finite modules are derived from the actual atlas. -/
theorem LineBundleAtlas.chartGlobalSections_finite (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] : Module.Finite R Γ(L.restrict f, ⊤) := by
  let := a.isQuasicoherent
  let : ∀ g : a.chartFrameFunctions f,
      IsLocalizedModule.Away g.val (affineSectionRestriction (L.restrict f) g.val) :=
    fun g => affineSectionRestriction_isLocalized (L.restrict f) g.val
  exact Module.Finite.of_localizationSpan' (a.chartFrameFunctions f)
    (a.chartFrameFunctions_span f)
    (Mₚ := fun g => Γ(L.restrict f, PrimeSpectrum.basicOpen g.val))
    (Rₚ := fun g => Γ(Spec R, PrimeSpectrum.basicOpen g.val))
    (fun g => affineSectionRestriction (L.restrict f) g.val) (a.chartFrameSections_finite f)

/-- Genuine affine chart sections of all actual tensor powers are finite modules. -/
theorem LineBundleAtlas.chartPowerGlobalSections_finite (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] (n : ℕ) :
    Module.Finite R Γ((bundleTensorPower L n).restrict f, ⊤) :=
  (a.tensorPower n).chartGlobalSections_finite f

/-- The actual chart scalar transport, using only the chart and its native section-ring isomorphisms. -/
def affineOpenChartScalars {U : X.Opens} (hU : IsAffineOpen U) : Γ(X, U) →+* Γ(X, U) :=
  let h : hU.fromSpec ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  (X.presheaf.map (eqToHom h.symm).op).hom.comp
    ((hU.fromSpec.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso Γ(X, U)).inv.hom)

/-- Actual chart sections transport to the actual original affine-open sections. -/
def affineOpenSectionsFromChart {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(L.restrict hU.fromSpec, ⊤) →ₛₗ[affineOpenChartScalars hU] Γ(L, U) := by
  let h : hU.fromSpec ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  refine {
    toFun := L.presheaf.map (eqToHom h.symm).op
    map_add' := (L.presheaf.map (eqToHom h.symm).op).hom.map_add
    map_smul' := ?_ }
  intro r s
  change L.presheaf.map (eqToHom h.symm).op
    ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv r) •
      (show bundleSections L (hU.fromSpec ''ᵁ ⊤) from s)) = _
  rw [L.map_smul]
  rfl

/-- Genuine affine-open section transport is bijective, from the actual equality of the chart image. -/
theorem affineOpenSectionsFromChart_bijective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (affineOpenSectionsFromChart (L := L) hU) :=
  ConcreteCategory.bijective_of_isIso (L.presheaf.map
    (eqToHom (hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec).symm).op)

/-- Actual sections over every genuine affine open are finite over its own actual regular ring. -/
theorem LineBundleAtlas.affineOpenSections_finite (a : LineBundleAtlas L)
    {U : X.Opens} (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(L, U) := by
  let := a.chartGlobalSections_finite hU.fromSpec
  exact Module.Finite.of_surjective (affineOpenSectionsFromChart hU)
    (affineOpenSectionsFromChart_bijective hU).surjective

/-- Every actual tensor-power affine-open section module is finite over the true regular ring. -/
theorem LineBundleAtlas.affineOpenPowerSections_finite (a : LineBundleAtlas L)
    {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ) :
    Module.Finite Γ(X, U) Γ(bundleTensorPower L n, U) :=
  (a.tensorPower n).affineOpenSections_finite hU

section GenericCoefficients

variable [IsDomain R]

/-- The genuine generic frame coefficient is linear over the actual affine coordinate ring. -/
def affineGlobalSectionToFunctionField {M : (Spec R).Modules}
    {U : (Spec R).Opens} [Nonempty U] (e : LocalBundleFrame M U) :
    Γ(M, ⊤) →ₗ[R] (Spec R).functionField where
  toFun := globalSectionToFunctionField e
  map_add' := (globalSectionToFunctionField e).map_add
  map_smul' r s := by
    change globalSectionToFunctionField e ((Scheme.ΓSpecIso R).inv r • s) = _
    rw [(globalSectionToFunctionField e).map_smul]
    rfl

/-- The actual affine generic coefficient representation is faithful from the genuine atlas. -/
theorem affineGlobalSectionToFunctionField_injective {M : (Spec R).Modules}
    (a : LineBundleAtlas M) {U : (Spec R).Opens} [Nonempty U]
    (e : LocalBundleFrame M U) : Function.Injective (affineGlobalSectionToFunctionField e) :=
  globalSectionToFunctionField_injective a e

/-- A genuine affine chart supplies its actual generic coefficient map from its pulled-back atlas. -/
def LineBundleAtlas.chartGenericEvaluation (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] :
    Γ(L.restrict f, ⊤) →ₗ[R] (Spec R).functionField :=
  affineGlobalSectionToFunctionField ((a.restrict f).frame (a.restrict f).genericIndex)

/-- Faithfulness of the actual chart coefficient map is derived from the transported atlas. -/
theorem LineBundleAtlas.chartGenericEvaluation_injective (a : LineBundleAtlas L)
    (f : Spec R ⟶ X) [IsOpenImmersion f] : Function.Injective (a.chartGenericEvaluation f) :=
  affineGlobalSectionToFunctionField_injective (a.restrict f)
    ((a.restrict f).frame (a.restrict f).genericIndex)

end GenericCoefficients

section UniformGenericDenominator

variable {A F M : Type u} [CommRing A] [IsDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] [AddCommGroup M] [Module A M] [Module.Finite A M]

omit [IsDomain A] in
/-- Finite generators clear a single genuine nonzero denominator for the entire coefficient module. -/
theorem finiteModule_clearGenericDenominator (q : M →ₗ[A] F) :
    ∃ b : nonZeroDivisors A, ∀ m : M, ∃ r : A,
      algebraMap A F r = (b.val : A) • q m := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) s q
  let P : Submodule A F := (Algebra.linearMap A F).range
  let bq : M →ₗ[A] F := b.val • q
  have hspan : Submodule.span A (s : Set M) ≤ P.comap bq := by
    apply Submodule.span_le.mpr
    intro m hm
    obtain ⟨r, hr⟩ := hb m hm
    exact LinearMap.mem_range.mpr ⟨r, hr⟩
  refine ⟨b, fun m => ?_⟩
  have hm : m ∈ Submodule.span A (s : Set M) := by rw [hs]; trivial
  exact LinearMap.mem_range.mp (hspan hm)

/-- Actual finite affine-chart generators yield one true denominator for all actual generic coefficients. -/
theorem LineBundleAtlas.chartGenericEvaluation_clearDenominator [IsDomain R]
    (a : LineBundleAtlas L) (f : Spec R ⟶ X) [IsOpenImmersion f] :
    ∃ b : nonZeroDivisors R, ∀ s : Γ(L.restrict f, ⊤), ∃ r : R,
      algebraMap R (Spec R).functionField r = b.val • a.chartGenericEvaluation f s := by
  let := a.chartGlobalSections_finite f
  exact finiteModule_clearGenericDenominator (a.chartGenericEvaluation f)

end UniformGenericDenominator

section SameGenericFrame

variable [IsIntegral X] {W : X.Opens} [Nonempty W]

/-- Actual local sections evaluated in one fixed genuine generic fiber frame.
The frame is the same on every affine chart, so these coefficients agree on overlaps. -/
def fixedFrameGenericCoefficients (e : LocalBundleFrame L W) (U : X.Opens) [Nonempty U] :
    Γ(L, U) →ₗ[Γ(X, U)] X.functionField where
  toFun s := genericBundleFiberFrame e (bundleGenericGerm L U s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' r s := by
    rw [(bundleGenericGerm L U).map_smulₛₗ, (genericBundleFiberFrame e).map_smul]
    rfl

/-- The coefficients in the fixed actual generic frame commute with genuine restrictions. -/
theorem fixedFrameGenericCoefficients_restrict (e : LocalBundleFrame L W)
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(L, U)) :
    fixedFrameGenericCoefficients e V (L.presheaf.map i.op s) =
      fixedFrameGenericCoefficients e U s := by
  apply congrArg (genericBundleFiberFrame e)
  exact L.presheaf.germ_res_apply i (genericPoint X) (genericPoint_mem_nonempty_open V) s

/-- Actual finite affine section generators clear one genuine denominator in the same fixed generic frame. -/
theorem LineBundleAtlas.affineOpenFixedFrame_clearDenominator (a : LineBundleAtlas L)
    (e : LocalBundleFrame L W) {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U) :
    ∃ b : nonZeroDivisors Γ(X, U), ∀ s : Γ(L, U), ∃ r : Γ(X, U),
      algebraMap Γ(X, U) X.functionField r = b.val • fixedFrameGenericCoefficients e U s := by
  let := a.affineOpenSections_finite hU
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  exact finiteModule_clearGenericDenominator (fixedFrameGenericCoefficients e U)

end SameGenericFrame

section PolynomialProjectiveGeometry

variable {K I : Type u} [Field K] [Nonempty I]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual zero homogeneous prime is the genuine generic point of polynomial Proj. -/
theorem homogeneousPolynomialZeroPrime_isGenericPoint :
    IsGenericPoint (homogeneousPolynomialZeroPrime (K := K) (I := I)) Set.univ := by
  rw [isGenericPoint_def]
  apply Set.eq_univ_iff_forall.mpr
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure _ _ x).mp
  change (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K)) ≤ x.asHomogeneousIdeal
  exact bot_le

/-- Polynomial Proj is irreducible from its actual dense zero-prime point. -/
instance homogeneousPolynomialProjIrreducible :
    IrreducibleSpace (Proj (MvPolynomial.homogeneousSubmodule I K)) :=
  (irreducibleSpace_def _).mpr homogeneousPolynomialZeroPrime_isGenericPoint.isIrreducible

/-- Every actual prime-localized fraction fiber of polynomial Proj is a domain. -/
instance homogeneousPolynomialTwistingFiberDomain
    (x : Proj (MvPolynomial.homogeneousSubmodule I K)) :
    IsDomain (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ x.asHomogeneousIdeal.toIdeal.primeCompl_le_nonZeroDivisors

/-- The actual regular section rings are reduced because their actual fraction-function inclusion is faithful. -/
instance homogeneousPolynomialProjReduced :
    AlgebraicGeometry.IsReduced (Proj (MvPolynomial.homogeneousSubmodule I K)) := by
  constructor
  intro U
  apply isReduced_of_injective
    (projectiveRegularToTwistingFunctions (MvPolynomial.homogeneousSubmodule I K) U)
  intro r s h
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  exact congrArg (fun t => t x) h

/-- Polynomial projective space is an actual integral scheme, derived from its native rings and topology. -/
instance homogeneousPolynomialProjIntegral :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule I K)) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The native scheme generic point is exactly the constructed actual zero homogeneous prime. -/
theorem homogeneousPolynomialProj_genericPoint_eq_zero :
    genericPoint (Proj (MvPolynomial.homogeneousSubmodule I K)) =
      homogeneousPolynomialZeroPrime (K := K) (I := I) :=
  (genericPoint_spec _).eq homogeneousPolynomialZeroPrime_isGenericPoint

end PolynomialProjectiveGeometry

end

end ComplexSchemes
