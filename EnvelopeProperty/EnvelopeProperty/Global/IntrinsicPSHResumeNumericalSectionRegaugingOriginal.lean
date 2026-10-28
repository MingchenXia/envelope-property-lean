import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalSectionRegauging
import EnvelopeProperty.Global.IntrinsicPSHResumeLinearProductTransport
import EnvelopeProperty.Berkovich.CartierRatioGenericMetric
import EnvelopeProperty.AlgGeom.CartierCanonicalTensorPullback
import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationNativePowerUnitSections
import EnvelopeProperty.Local.PLNormalizedOriginalModelConvexity

/-! # Actual local sections behind the original Cartier-ratio family -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped Classical NNReal ENNReal
universe u
namespace EnvelopeProperty.NumericalSectionRegaugingOriginal
open Berkovich Berkovich.RelativeSchemeValuedPoint NumericalSectionRegauging
open Scheme.Modules SchemeLineSectionEvaluation ClosedProjectiveGlobalSections

/-- An actual original local line section pulled to the SAME original
residue fibre through its true support-open factor. -/
def supportSectionAt {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj M) (x : X) (hx : x ∈ V) :
    Γ((pullback (X.fromSpecResidueField x)).obj M, ⊤) :=
  sectionAtOne (pullbackSectionHom (supportResidueFactor x V hx) δ ≫
    (frameFactorIso (supportResidueFactor x V hx) V.ι (X.fromSpecResidueField x)
      (supportResidueFactor_comp x V hx) M).hom)

private theorem factorSection_frame {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (p : A ⟶ C) (hp : g ≫ b = p)
    (M : C.Modules) (e : (pullback b).obj M ≅ unitObj B) :
    sectionAtOne (pullbackSectionHom g e.inv ≫ (frameFactorIso g b p hp M).hom) =
      ((frameViaFactor g b p hp e).inv.val.app (op ⊤)).hom
        (1 : Γ(A, ⊤)) := by
  rfl

private theorem supportSectionAt_frame {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (e : (pullback V.ι).obj M ≅ unitObj V.toScheme) (x : X) (hx : x ∈ V) :
    supportSectionAt M V e.inv x hx =
      ((frameViaFactor (supportResidueFactor x V hx) V.ι (X.fromSpecResidueField x)
        (supportResidueFactor_comp x V hx) e).inv.val.app (op ⊤)).hom
          (1 : Γ(Spec (CommRingCat.of (X.residueField x)), ⊤)) :=
  factorSection_frame (supportResidueFactor x V hx) V.ι (X.fromSpecResidueField x)
    (supportResidueFactor_comp x V hx) M e

private theorem supportSectionAt_global {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : RelativeSchemeValuedPoint v f) (M : X.Modules) (V : X.Opens)
    (hy : y.1.point ∈ V) (α : unitObj X ⟶ M) :
    supportSectionAt M V (pullbackSectionHom V.ι α) y.1.point hy = fibreSection y α := by
  exact congrArg sectionAtOne
    (SchemeLineSectionFactorization.pullbackSectionHom_factor
      (supportResidueFactor y.1.point V hy) V.ι (X.fromSpecResidueField y.1.point)
      (supportResidueFactor_comp y.1.point V hy) α)

private theorem idealUnit_supportSectionAt
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (I : X.IdealSheafData) (hI : I.IsInvertible) (V : X.Opens)
    (hV : V ≤ I.support.compl) (hy : y.1.point ∈ V) :
    ∃ hn : modelIdealNorm I hb y ≠ 0,
      genericIdealUnitSection hb y I hI hn =
        supportSectionAt I.toModules V (I.pullbackModuleIsoOfLeComplSupport V hV).inv y.1.point hy := by
  obtain ⟨hn, he⟩ := genericIdealUnitSection_eq_supportFrame hb y I hI V hV hy
  exact ⟨hn, he.trans (supportSectionAt_frame I.toModules V
    (I.pullbackModuleIsoOfLeComplSupport V hV) y.1.point hy).symm⟩

private theorem tensorComp_inverse {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (M N : C.Modules) :
    (pullback g).map (canonicalTensorPullbackIso b M N).inv ≫
        (pullbackComp g b).hom.app (tensorObj M N) =
      (canonicalTensorPullbackIso g ((pullback b).obj M) ((pullback b).obj N)).hom ≫
        (tensorObjCongr ((pullbackComp g b).app M) ((pullbackComp g b).app N)).hom ≫
          (canonicalTensorPullbackIso (g ≫ b) M N).inv := by
  have hc := congrArg Iso.hom (canonicalTensorPullbackIso_comp g b M N)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hc
  have he := congrArg
    (fun q => (pullback g).map (canonicalTensorPullbackIso b M N).inv ≫ q ≫
      (canonicalTensorPullbackIso (g ≫ b) M N).inv) hc
  have hi := (pullback g).map_id
    (tensorObj ((pullback b).obj M) ((pullback b).obj N))
  simpa only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    hi, Category.id_comp, Iso.hom_inv_id, Category.comp_id] using he.symm

private def factorWholeSection {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (p : A ⟶ C) (hp : g ≫ b = p)
    (M : C.Modules) (s : Γ((pullback b).obj M, ⊤)) :
    Γ((pullback p).obj M, ⊤) :=
  (frameFactorIso g b p hp M).hom.val.app (op ⊤)
    (wholePullbackSection g ((pullback b).obj M) s)

private theorem factorWholeSection_tensor {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (p : A ⟶ C) (hp : g ≫ b = p)
    (M N : C.Modules) (s : Γ((pullback b).obj M, ⊤))
    (t : Γ((pullback b).obj N, ⊤)) :
    factorWholeSection g b p hp (tensorObj M N)
        ((canonicalTensorPullbackIso b M N).inv.val.app (op ⊤)
          (CanonicalGeometry.tensorSection ((pullback b).obj M) ((pullback b).obj N) ⊤ s t)) =
      (canonicalTensorPullbackIso p M N).inv.val.app (op ⊤)
        (CanonicalGeometry.tensorSection ((pullback p).obj M) ((pullback p).obj N) ⊤
          (factorWholeSection g b p hp M s) (factorWholeSection g b p hp N t)) := by
  subst p
  let z := wholePullbackSection g
    (tensorObj ((pullback b).obj M) ((pullback b).obj N))
      (CanonicalGeometry.tensorSection ((pullback b).obj M) ((pullback b).obj N) ⊤ s t)
  have hm := wholePullbackSection_map g (canonicalTensorPullbackIso b M N).inv
    (CanonicalGeometry.tensorSection ((pullback b).obj M) ((pullback b).obj N) ⊤ s t)
  have hc := congrArg (fun q => q.val.app (op ⊤) z) (tensorComp_inverse g b M N)
  change ((pullbackComp g b).hom.app (tensorObj M N)).val.app (op ⊤)
      (((pullback g).map (canonicalTensorPullbackIso b M N).inv).val.app (op ⊤) z) =
    (canonicalTensorPullbackIso (g ≫ b) M N).inv.val.app (op ⊤)
      ((tensorObjCongr ((pullbackComp g b).app M) ((pullbackComp g b).app N)).hom.val.app (op ⊤)
        ((canonicalTensorPullbackIso g ((pullback b).obj M) ((pullback b).obj N)).hom.val.app
          (op ⊤) z)) at hc
  have ht := canonicalTensorPullbackIso_wholePullbackSection g
    ((pullback b).obj M) ((pullback b).obj N) s t
  have he := TestConfigurationSectionTransport.bundleTensorIso_tensorSection
    ((pullbackComp g b).app M) ((pullbackComp g b).app N) ⊤
    (wholePullbackSection g ((pullback b).obj M) s)
    (wholePullbackSection g ((pullback b).obj N) t)
  have hleft := congrArg
    (fun a => ((pullbackComp g b).hom.app (tensorObj M N)).val.app (op ⊤) a) hm.symm
  have hright := congrArg
    (fun a => (canonicalTensorPullbackIso (g ≫ b) M N).inv.val.app (op ⊤) a)
    ((congrArg
      (fun a => (tensorObjCongr ((pullbackComp g b).app M)
        ((pullbackComp g b).app N)).hom.val.app (op ⊤) a) ht).trans he)
  exact hleft.trans (hc.trans hright)

private theorem topSectionHom_atOne {X : Scheme.{u}} (M : X.Modules)
    (δ : unitObj X ⟶ M) : topSectionHom M (sectionAtOne δ) = δ := by
  have h1 := topSectionHom_app_top_apply_one (unitObj X) (1 : Γ(X, ⊤))
  have hone : topSectionHom (unitObj X) (1 : Γ(X, ⊤)) = 𝟙 (unitObj X) :=
    (unitHom_eq_globalScalar _).trans
      ((congrArg ModularCurves.unitEndomorphismOfTopSection h1).trans
        ModularCurves.unitEndomorphismOfTopSection_one)
  have h := ModularCurves.topSectionHom_comp (M := unitObj X) (N := M)
    (show Γ(unitObj X, ⊤) from (1 : Γ(X, ⊤))) δ
  rw [hone, Category.id_comp] at h
  exact h.symm

private theorem wholePullbackSection_atOne {A B : Scheme.{u}} (g : A ⟶ B)
    (M : B.Modules) (δ : unitObj B ⟶ M) :
    wholePullbackSection g M (sectionAtOne δ) = sectionAtOne (pullbackSectionHom g δ) := by
  have h := wholePullbackSection_eq_sectionAtOne g M (sectionAtOne δ)
  rw [topSectionHom_atOne] at h
  exact h

private theorem factorWholeSection_atOne {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (p : A ⟶ C) (hp : g ≫ b = p)
    (M : C.Modules) (δ : unitObj B ⟶ (pullback b).obj M) :
    factorWholeSection g b p hp M (sectionAtOne δ) =
      sectionAtOne (pullbackSectionHom g δ ≫ (frameFactorIso g b p hp M).hom) :=
  congrArg (fun s => (frameFactorIso g b p hp M).hom.val.app (op ⊤) s)
    (wholePullbackSection_atOne g ((pullback b).obj M) δ)

private theorem supportSectionAt_eq_factorWhole {X : Scheme.{u}}
    (M : X.Modules) (V : X.Opens) (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj M)
    (x : X) (hx : x ∈ V) :
    supportSectionAt M V δ x hx =
      factorWholeSection (supportResidueFactor x V hx) V.ι (X.fromSpecResidueField x)
        (supportResidueFactor_comp x V hx) M (sectionAtOne δ) :=
  (factorWholeSection_atOne (supportResidueFactor x V hx) V.ι (X.fromSpecResidueField x)
    (supportResidueFactor_comp x V hx) M δ).symm

private theorem isoSection_inv {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (s : Γ(M, ⊤)) (t : Γ(N, ⊤))
    (h : e.hom.val.app (op ⊤) s = t) : s = e.inv.val.app (op ⊤) t := by
  have hi := congrArg (fun q => q.val.app (op ⊤) s) e.hom_inv_id
  change e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s at hi
  exact hi.symm.trans (congrArg (fun a => e.inv.val.app (op ⊤) a) h)

private theorem genericTensorSection_inv
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : RelativeSchemeValuedPoint v f) (M N : X.Modules)
    (s : Γ(genericLineModule y M, ⊤)) (t : Γ(genericLineModule y N, ⊤)) :
    genericTensorSection y s t =
      (canonicalTensorPullbackIso (X.fromSpecResidueField y.1.point) M N).inv.val.app (op ⊤)
        (CanonicalGeometry.tensorSection (genericLineModule y M) (genericLineModule y N) ⊤ s t) :=
  isoSection_inv _ _ _
    (TestConfigurationLaurentExpansionContinuation.originalCanonicalPullback_genericTensorSection y s t)

private def localTensorHom {X : Scheme.{u}} (M N : X.Modules) (V : X.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj M)
    (ε : unitObj V.toScheme ⟶ (pullback V.ι).obj N) :
    unitObj V.toScheme ⟶ (pullback V.ι).obj (tensorObj M N) :=
  topSectionHom _ ((canonicalTensorPullbackIso V.ι M N).inv.val.app (op ⊤)
    (CanonicalGeometry.tensorSection ((pullback V.ι).obj M) ((pullback V.ι).obj N) ⊤
      (sectionAtOne δ) (sectionAtOne ε)))

private theorem supportSectionAt_tensor
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : RelativeSchemeValuedPoint v f) (M N : X.Modules) (V : X.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj M)
    (ε : unitObj V.toScheme ⟶ (pullback V.ι).obj N) (hy : y.1.point ∈ V) :
    supportSectionAt (tensorObj M N) V (localTensorHom M N V δ ε) y.1.point hy =
      genericTensorSection y (supportSectionAt M V δ y.1.point hy)
        (supportSectionAt N V ε y.1.point hy) := by
  let g := supportResidueFactor y.1.point V hy
  let p := X.fromSpecResidueField y.1.point
  let hp := supportResidueFactor_comp y.1.point V hy
  have h1 := supportSectionAt_eq_factorWhole (tensorObj M N) V
    (localTensorHom M N V δ ε) y.1.point hy
  have h2 := congrArg (factorWholeSection g V.ι p hp (tensorObj M N))
    (topSectionHom_app_top_apply_one _
      ((canonicalTensorPullbackIso V.ι M N).inv.val.app (op ⊤)
        (CanonicalGeometry.tensorSection ((pullback V.ι).obj M) ((pullback V.ι).obj N) ⊤
          (sectionAtOne δ) (sectionAtOne ε))))
  have h3 := factorWholeSection_tensor g V.ι p hp M N (sectionAtOne δ) (sectionAtOne ε)
  have h4 := congrArg₂
    (fun s t => (canonicalTensorPullbackIso p M N).inv.val.app (op ⊤)
      (CanonicalGeometry.tensorSection ((pullback p).obj M) ((pullback p).obj N) ⊤ s t))
    (supportSectionAt_eq_factorWhole M V δ y.1.point hy).symm
    (supportSectionAt_eq_factorWhole N V ε y.1.point hy).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans
    (genericTensorSection_inv y M N _ _).symm)))

/-- The entire actual canonical Cartier-ratio family is the residue
pullback of ONE internally constructed actual original local section. -/
theorem exists_cartierRatio_localSection
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (V : X.Opens)
    (hV : V ≤ I.support.compl) :
    ∃ δ : unitObj V.toScheme ⟶ (pullback V.ι).obj (I.ratioModule J),
      ∀ (y : RelativeSchemeValuedPoint v f) (hy : y.1.point ∈ V),
        ∃ hn : modelIdealNorm I hb y ≠ 0,
          genericCartierRatioSection hb y I J hI hJ hn =
            supportSectionAt (I.ratioModule J) V δ y.1.point hy := by
  let α := hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion
  let δ := localTensorHom I.toModules (dualObj J.toModules) V
    (I.pullbackModuleIsoOfLeComplSupport V hV).inv (pullbackSectionHom V.ι α)
  refine ⟨δ, ?_⟩
  intro y hy
  obtain ⟨hn, hA⟩ := idealUnit_supportSectionAt hb y I hI V hV hy
  refine ⟨hn, ?_⟩
  have hB := supportSectionAt_global y (dualObj J.toModules) V hy α
  exact (congrArg₂ (genericTensorSection y) hA hB.symm).trans
    (supportSectionAt_tensor y I.toModules (dualObj J.toModules) V
      (I.pullbackModuleIsoOfLeComplSupport V hV).inv (pullbackSectionHom V.ι α) hy).symm

private theorem factorWholeSection_map {A B C : Scheme.{u}}
    (g : A ⟶ B) (b : B ⟶ C) (p : A ⟶ C) (hp : g ≫ b = p)
    {M N : C.Modules} (a : M ⟶ N) (s : Γ((pullback b).obj M, ⊤)) :
    factorWholeSection g b p hp N (((pullback b).map a).val.app (op ⊤) s) =
      ((pullback p).map a).val.app (op ⊤) (factorWholeSection g b p hp M s) := by
  let c := (pullbackComp g b) ≪≫ pullbackCongr hp
  have hn := c.hom.naturality a
  simp only [Functor.comp_map] at hn
  have hc := congrArg
    (fun q => q.val.app (op ⊤) (wholePullbackSection g ((pullback b).obj M) s)) hn
  change (c.hom.app N).val.app (op ⊤)
      (((pullback g).map ((pullback b).map a)).val.app (op ⊤)
        (wholePullbackSection g ((pullback b).obj M) s)) =
    ((pullback p).map a).val.app (op ⊤)
      ((c.hom.app M).val.app (op ⊤) (wholePullbackSection g ((pullback b).obj M) s)) at hc
  exact (congrArg (fun t => (c.hom.app N).val.app (op ⊤) t)
    (wholePullbackSection_map g ((pullback b).map a) s)).symm.trans hc

private theorem supportSectionAt_map {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) (V : X.Opens) (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj M)
    (x : X) (hx : x ∈ V) :
    supportSectionAt N V (δ ≫ (pullback V.ι).map a) x hx =
      ((pullback (X.fromSpecResidueField x)).map a).val.app (op ⊤)
        (supportSectionAt M V δ x hx) := by
  have h1 := supportSectionAt_eq_factorWhole N V (δ ≫ (pullback V.ι).map a) x hx
  have h2 := factorWholeSection_map (supportResidueFactor x V hx) V.ι
    (X.fromSpecResidueField x) (supportResidueFactor_comp x V hx) a (sectionAtOne δ)
  have h3 := congrArg
    (fun t => ((pullback (X.fromSpecResidueField x)).map a).val.app (op ⊤) t)
    (supportSectionAt_eq_factorWhole M V δ x hx).symm
  exact h1.trans (h2.trans h3)

section Original
open ProjBerk IntegralSchemeNormalization
variable {k : Type u} [Field k] [PerfectField k] {n : ℕ} (X : ProjSubvariety k n)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The SAME original polarized family is ONE actual local section on
its TRUE support-open, for EVERY homogeneous form including its zeros. -/
theorem exists_originalPolarized_localSection (j : Fin (n+1)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d)
    (V : (X.normalizedSimultaneousIdealBlowup I J hfin).Opens)
    (hV : V ≤ (((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin)).support).compl) :
    ∃ δ : unitObj V.toScheme ⟶ (pullback V.ι).obj
      (X.normalizedSimultaneousTwistedRatioLine I J hfin j d),
      ∀ (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) (hy : y.1.point ∈ V),
        ∃ hnI : modelIdealLog I gaussModelCoefficient_le_one
          (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥,
          X.normalizedSimultaneousOriginalRatioSectionAt I J hfin y hnI j d F hF =
            supportSectionAt (X.normalizedSimultaneousTwistedRatioLine I J hfin j d)
              V δ y.1.point hy := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv
      (hfin X.triv).1 (hfin X.triv).2
  let : IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin
  let A := (I.comap (X.simultaneousIdealBlowupProjection I J)).comap
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin)
  let B := (J.comap (X.simultaneousIdealBlowupProjection I J)).comap
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin)
  let hA : A.IsInvertible := cartier_comap (X.simultaneousIdealBlowup I J)
    (X.simultaneousIdealBlowup_isInvertible I J).1
  let hB : B.IsInvertible := cartier_comap (X.simultaneousIdealBlowup I J)
    (X.simultaneousIdealBlowup_isInvertible I J).2
  let H := (pullback (X.normalizedSimultaneousPolynomialProjection I J hfin)).obj
    (MvPolynomial.coordinateHyperplanePoleSheafPower (R := Polynomial k) j d)
  let α : unitObj (X.normalizedSimultaneousIdealBlowup I J hfin) ⟶ H :=
    pullbackSectionHom (X.normalizedSimultaneousPolynomialProjection I J hfin)
      (ProjectiveHomogeneousSections.sectionHom j d
        (MvPolynomial.map (Polynomial.C : k →+* Polynomial k) F) (hF.map (Polynomial.C : k →+* Polynomial k)))
  obtain ⟨δR, hR⟩ := exists_cartierRatio_localSection
    (R := Polynomial k) (v := gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
    (f := X.normalizedSimultaneousIdealBlowupStructure I J hfin)
    (gaussModelCoefficient_le_one (k := k)) A B hA hB V hV
  let e := X.normalizedSimultaneousPolynomialRatioLineIso I J hfin j d
  let δP := localTensorHom H (A.ratioModule B) V (pullbackSectionHom V.ι α) δR
  let δ := δP ≫ (pullback V.ι).map e.hom
  refine ⟨δ, ?_⟩
  intro y hy
  obtain ⟨hnA, hRy⟩ := hR y hy
  have hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥ := by
    intro hz
    apply hnA
    exact ENNReal.log_eq_bot_iff.mp
      ((X.modelIdealLog_normalizedSimultaneous_comap I J hfin I y).trans hz)
  refine ⟨hnI, ?_⟩
  have hH := supportSectionAt_global y H V hy α
  have hP := (congrArg₂ (genericTensorSection y) hH.symm hRy).trans
    (supportSectionAt_tensor y H (A.ratioModule B) V
      (pullbackSectionHom V.ι α) δR hy).symm
  exact (congrArg
    (fun s => ((pullback ((X.normalizedSimultaneousIdealBlowup I J hfin).fromSpecResidueField
      y.1.point)).map e.hom).val.app (op ⊤) s) hP).trans
    (supportSectionAt_map e.hom V δP y.1.point hy).symm
end Original

end EnvelopeProperty.NumericalSectionRegaugingOriginal
