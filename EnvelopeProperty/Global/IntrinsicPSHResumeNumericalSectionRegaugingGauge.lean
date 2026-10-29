import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalSectionRegaugingOriginal
import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.AlgGeom.Canonical.NativeLineSectionRatios
import EnvelopeProperty.Berkovich.SchemeGenericLineNormConvexityPullback
import EnvelopeProperty.Berkovich.SchemeUnitLogPSH

/-! # Actual original rational-section gauges on true support opens -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped Classical NNReal ENNReal
universe u
namespace EnvelopeProperty.NumericalSectionRegaugingGauge
open Berkovich Berkovich.RelativeSchemeValuedPoint ProjBerk
open Scheme.Modules SchemeLineSectionEvaluation NumericalSectionRegauging
open NumericalSectionRegaugingOriginal

private theorem modelIdealLog_ne_top {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    [IsProper f] (hb : ∀ r, v r ≤ 1) (K : X.IdealSheafData)
    (y : RelativeSchemeValuedPoint v f) : modelIdealLog K hb y ≠ ⊤ := by
  intro h
  have he := ENNReal.log_eq_top_iff.mp h
  exact (ne_of_lt (lt_of_le_of_lt (modelIdealNorm_le_one K hb y) (by simp))) he

private theorem exists_sectionFrame_at_fieldPoint {K : CommRingCat.{u}} [IsLocalRing K]
    (hK : IsField K)
    {Y : Scheme.{u}} {M : Y.Modules} (hM : IsInvertible M)
    (α : unitObj Y ⟶ M) (r : Spec K ⟶ Y)
    (hs : sectionAtOne (pullbackSectionHom r α) ≠ 0) :
    ∃ W : Y.Opens, r (IsLocalRing.closedPoint K) ∈ W ∧
      IsIso (pullbackSectionHom W.ι α) := by
  obtain ⟨ι,U,hU,hframe⟩ := hM
  have hx : r (IsLocalRing.closedPoint K) ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨e⟩ := hframe i
  obtain ⟨q,hq⟩ := Scheme.exists_lift_open_of_closedPoint_mem r (U i) hi
  let s := pullbackSectionHom (U i).ι α
  let c := SchemeLineSectionUnitFrames.frameScalar e s
  let E := frameViaFactor q (U i).ι r hq e
  have hc : q.appTop.hom c ≠ 0 := by
    intro hz
    apply hs
    have h := frameViaFactor_sectionHom_scalar_apply q (U i).ι r hq e α c
      (SchemeLineSectionUnitFrames.frameScalar_identity e s)
    have he : E.hom.val.app (op ⊤) (sectionAtOne (pullbackSectionHom r α)) =
        E.hom.val.app (op ⊤) 0 := by
      exact h.trans (hz.trans (map_zero _).symm)
    have hinv := congrArg (fun a => a.val.app (op ⊤)
      (sectionAtOne (pullbackSectionHom r α))) E.hom_inv_id
    change E.inv.val.app (op ⊤)
      (E.hom.val.app (op ⊤) (sectionAtOne (pullbackSectionHom r α))) =
        sectionAtOne (pullbackSectionHom r α) at hinv
    exact hinv.symm.trans (by rw [he]; simp only [map_zero]; rfl)
  have hcK : (Scheme.ΓSpecIso K).hom.hom (q.appTop.hom c) ≠ 0 := by
    intro hz
    exact hc ((ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso K).hom).1 (hz.trans (map_zero _).symm))
  have hu : IsUnit (q.appTop.hom c) := by
    have huK : IsUnit ((Scheme.ΓSpecIso K).hom.hom (q.appTop.hom c)) :=
      isUnit_iff_exists_inv.mpr (hK.mul_inv_cancel hcK)
    have h := huK.map (Scheme.ΓSpecIso K).inv.hom
    change IsUnit (((Scheme.ΓSpecIso K).hom ≫
      (Scheme.ΓSpecIso K).inv).hom (q.appTop.hom c)) at h
    rw [Iso.hom_inv_id] at h
    exact h
  let B := (U i).toScheme.basicOpen c
  have hB : (⊤ : (Spec K).Opens) ≤ q ⁻¹ᵁ B := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
  have hqB : q (IsLocalRing.closedPoint K) ∈ B := hB trivial
  let b := B.ι ≫ (U i).ι
  let W := b.opensRange
  have hrW : r (IsLocalRing.closedPoint K) ∈ W := by
    refine ⟨⟨q (IsLocalRing.closedPoint K), hqB⟩, ?_⟩
    exact congrArg (fun f : Spec K ⟶ Y => f (IsLocalRing.closedPoint K)) hq
  have hb : IsIso (pullbackSectionHom b α) := by
    let : IsIso (pullbackSectionHom B.ι s) :=
      SchemeLineSectionUnitFrames.basicOpenSection_isIso e s
    rw [← SchemeLineSectionFactorization.pullbackSectionHom_factor B.ι (U i).ι b rfl α]
    infer_instance
  let eW := IsOpenImmersion.isoOfRangeEq b W.ι (by rw [W.range_ι]; rfl)
  exact ⟨W,hrW,SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
    eW.inv b W.ι (IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _) α hb⟩

private def genericResidueEquiv (Y : Scheme.{u}) [IsIntegral Y] :
    Y.functionField ≃+* Y.residueField (genericPoint Y) :=
  RingEquiv.ofBijective (Y.residue (genericPoint Y)).hom
    ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective (genericPoint Y)⟩

/-- Every nonzero actual generic residue scalar has an internally chosen
genuine affine local unit with EXACT original residue evaluation. -/
theorem exists_genericResidue_localUnit (Y : Scheme.{u}) [IsIntegral Y]
    (c : Y.residueField (genericPoint Y)) (hc : c ≠ 0) :
    ∃ (V : Y.Opens) (_hV : V ∈ Y.affineOpens) (hη : genericPoint Y ∈ V)
      (a : Γ(Y,V)ˣ), Y.evaluation V (genericPoint Y) hη (a : Γ(Y,V)) = c := by
  let e := genericResidueEquiv Y
  have hf : e.symm c ≠ 0 := by
    intro h
    exact hc (e.symm.injective (h.trans e.symm.map_zero.symm))
  obtain ⟨V,hV,a,hne,hg,ha⟩ := AlgebraicGeometry.exists_isUnit_germ_eq Y (e.symm c) hf
  let : Nonempty V := hne
  refine ⟨V,hV,CanonicalGeometry.genericPoint_mem_nonempty_open V,ha.unit,?_⟩
  change (Y.residue (genericPoint Y)).hom (Y.germToFunctionField V (ha.unit : Γ(Y,V))) = c
  rw [ha.unit_spec,hg]
  exact e.apply_symm_apply c

private theorem openTopSection_eq_appLE {Y : Scheme.{u}} (V : Y.Opens) (c : Γ(Y,V)) :
    openTopSection V c = (V.ι.appLE V ⊤ V.ι_preimage_self.ge).hom c := by
  rw [openTopSection, Scheme.Opens.ι_appIso, Scheme.Opens.ι_appLE]
  change (Y.presheaf.map (eqToHom V.ι_image_top).op).hom c = _
  apply ConcreteCategory.congr_hom
  apply Y.presheaf.congr_map
  exact Subsingleton.elim _ _

/-- The true support factor evaluates the SAME original open scalar in
the SAME original residue field, without any model-center hypothesis. -/
theorem supportResidueFactor_openTopSection {Y : Scheme.{u}}
    (x : Y) (V : Y.Opens) (hx : x ∈ V) (c : Γ(Y,V)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField x))).hom.hom
      ((supportResidueFactor x V hx).appTop.hom (openTopSection V c)) =
        Y.evaluation V x hx c := by
  rw [openTopSection_eq_appLE]
  let g := supportResidueFactor x V hx
  have htop : ⊤ ≤ g ⁻¹ᵁ (⊤ : V.toScheme.Opens) := le_top
  have he := Scheme.Hom.appLE_comp_appLE g V.ι V ⊤ ⊤ V.ι_preimage_self.ge htop
  have ht : g.appLE ⊤ ⊤ htop = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ (Spec (CommRingCat.of (Y.residueField x))).presheaf.map
      (𝟙 (op (⊤ : (Spec (CommRingCat.of (Y.residueField x))).Opens))) = g.appTop
    rw [(Spec (CommRingCat.of (Y.residueField x))).presheaf.map_id, Category.comp_id]
  have hfun : ∀ h : ⊤ ≤ (g ≫ V.ι) ⁻¹ᵁ V,
      (g ≫ V.ι).appLE V ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField x))).hom = Y.evaluation V x hx := by
    dsimp only [g]
    rw [supportResidueFactor_comp]
    intro h
    exact SchemeValuedPoint.fromSpecResidueField_appLE_top _ _ _ _
  have hcomp : V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫ g.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField x))).hom = Y.evaluation V x hx := by
    rw [← ht, ← Category.assoc, he]
    exact hfun _
  exact congrArg (fun q : Γ(Y,V) ⟶ Y.residueField x => q.hom c) hcomp

-- Elementary native pullback associativity, retained privately: the existing
-- frame API proves the same categorical calculation privately for frames.
private theorem factorIso_comp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    (w : A ⟶ D) (hi : i ≫ f = w) (M : D.Modules) :
    (pullback i).map (frameFactorIso g b f hg M).hom ≫ (frameFactorIso i f w hi M).hom =
      (pullbackComp i g).hom.app ((pullback b).obj M) ≫
        (frameFactorIso (i ≫ g) b w (by rw [Category.assoc,hg]; exact hi) M).hom := by
  subst f
  have h := pullbackComp_three_congr_trans_app i g b (i ≫ g) rfl w
    (Category.assoc i g b).symm ((Category.assoc i g b).trans hi) M
  change (pullback i).map ((pullbackComp g b).hom.app M) ≫
      (pullbackComp i (g ≫ b)).hom.app M ≫ (pullbackCongr hi).hom.app M =
    (pullbackComp i g).hom.app ((pullback b).obj M) ≫
      (pullbackComp (i ≫ g) b).hom.app M ≫
        (pullbackCongr ((Category.assoc i g b).trans hi)).hom.app M
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
    show (pullbackCongr (rfl : i ≫ g = i ≫ g)).hom.app ((pullback b).obj M) = 𝟙 _ from rfl,
    Category.comp_id, Category.id_comp] using h

private theorem factorSection_comp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    (w : A ⟶ D) (hi : i ≫ f = w) {M : D.Modules}
    (δ : unitObj C ⟶ (pullback b).obj M) :
    pullbackSectionHom i (pullbackSectionHom g δ ≫ (frameFactorIso g b f hg M).hom) ≫
      (frameFactorIso i f w hi M).hom =
    pullbackSectionHom (i ≫ g) δ ≫
      (frameFactorIso (i ≫ g) b w (by rw [Category.assoc,hg]; exact hi) M).hom := by
  have hc := factorIso_comp i g b f hg w hi M
  have hs := SchemeLineSectionFactorization.pullbackSectionHom_factor i g (i ≫ g) rfl δ
  calc
    _ = pullbackSectionHom i (pullbackSectionHom g δ) ≫
        ((pullback i).map (frameFactorIso g b f hg M).hom ≫
          (frameFactorIso i f w hi M).hom) := by
      simp only [pullbackSectionHom, Functor.map_comp, Category.assoc]
    _ = pullbackSectionHom i (pullbackSectionHom g δ) ≫
        ((pullbackComp i g).hom.app ((pullback b).obj M) ≫
          (frameFactorIso (i ≫ g) b w (by rw [Category.assoc,hg]; exact hi) M).hom) := by rw [hc]
    _ = _ := by
      rw [← Category.assoc]
      exact congrArg (fun a => a ≫ (frameFactorIso (i ≫ g) b w
        (by rw [Category.assoc,hg]; exact hi) M).hom) hs

private theorem factorSection_congr {A B C : Scheme.{u}}
    (g g' : A ⟶ B) (hg : g = g') (b : B ⟶ C) (p : A ⟶ C)
    (hp : g ≫ b = p) (hp' : g' ≫ b = p) {M : C.Modules}
    (δ : unitObj B ⟶ (pullback b).obj M) :
    pullbackSectionHom g δ ≫ (frameFactorIso g b p hp M).hom =
      pullbackSectionHom g' δ ≫ (frameFactorIso g' b p hp' M).hom := by
  subst g'
  rfl

private theorem factorAtOne_comp {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    (w : A ⟶ D) (hi : i ≫ f = w) (g' : A ⟶ C) (hig : i ≫ g = g')
    (hg' : g' ≫ b = w) {M : D.Modules} (δ : unitObj C ⟶ (pullback b).obj M) :
    sectionAtOne (pullbackSectionHom i
      (pullbackSectionHom g δ ≫ (frameFactorIso g b f hg M).hom) ≫
        (frameFactorIso i f w hi M).hom) =
      sectionAtOne (pullbackSectionHom g' δ ≫ (frameFactorIso g' b w hg' M).hom) :=
  congrArg sectionAtOne ((factorSection_comp i g b f hg w hi δ).trans
    (factorSection_congr (i ≫ g) g' hig b w
      (by rw [Category.assoc,hg]; exact hi) hg' δ))

private theorem factorMap_eq {A B C D : Scheme.{u}}
    (i : A ⟶ B) (g : B ⟶ C) (b : C ⟶ D) [Mono b]
    (f : B ⟶ D) (hg : g ≫ b = f) (p : A ⟶ D) (hi : i ≫ f = p)
    (g' : A ⟶ C) (hg' : g' ≫ b = p) : i ≫ g = g' := by
  apply (cancel_mono b).mp
  exact ((Category.assoc i g b).trans (congrArg (fun a => i ≫ a) hg)).trans
    (hi.trans hg'.symm)

/-- Genuine local section restriction using the SAME original module and
the actual native open-inclusion/factor comparison. -/
def restrictLocalSection {Y : Scheme.{u}} (M : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (V : Y.Opens) (hVU : V ≤ U) : unitObj V.toScheme ⟶ (pullback V.ι).obj M :=
  pullbackSectionHom (Y.homOfLE hVU) δ ≫
    (frameFactorIso (Y.homOfLE hVU) U.ι V.ι (Y.homOfLE_ι hVU) M).hom

/-- Actual local-section restriction preserves EVERY original support
residue-fibre value, by internally derived literal factor triangles. -/
theorem supportSectionAt_restrict {Y : Scheme.{u}} (M : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (V : Y.Opens) (hVU : V ≤ U) (x : Y) (hx : x ∈ V) :
    supportSectionAt M V (restrictLocalSection M U δ V hVU) x hx =
      supportSectionAt M U δ x (hVU hx) :=
  factorAtOne_comp (supportResidueFactor x V hx) (Y.homOfLE hVU) U.ι V.ι
    (Y.homOfLE_ι hVU) (Y.fromSpecResidueField x) (supportResidueFactor_comp x V hx)
    (supportResidueFactor x U (hVU hx))
    (factorMap_eq (supportResidueFactor x V hx) (Y.homOfLE hVU) U.ι V.ι
      (Y.homOfLE_ι hVU) (Y.fromSpecResidueField x) (supportResidueFactor_comp x V hx)
      (supportResidueFactor x U (hVU hx)) (supportResidueFactor_comp x U (hVU hx)))
    (supportResidueFactor_comp x U (hVU hx)) δ

private theorem factorAtOne_ne_zero {A B C : Scheme.{u}} (g : A ⟶ B) (b : B ⟶ C)
    (p : A ⟶ C) (hp : g ≫ b = p) {M : C.Modules}
    (δ : unitObj B ⟶ (pullback b).obj M)
    (hs : sectionAtOne (pullbackSectionHom g δ ≫ (frameFactorIso g b p hp M).hom) ≠ 0) :
    sectionAtOne (pullbackSectionHom g δ) ≠ 0 := by
  intro hz
  apply hs
  change (frameFactorIso g b p hp M).hom.val.app (op ⊤)
    (sectionAtOne (pullbackSectionHom g δ)) = 0
  exact (congrArg (fun a => (frameFactorIso g b p hp M).hom.val.app (op ⊤) a) hz).trans
    (map_zero _)

private theorem restrictLocalSection_image_isIso {Y : Scheme.{u}} (M : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (W : U.toScheme.Opens) (hW : IsIso (pullbackSectionHom W.ι δ)) :
    IsIso (restrictLocalSection M U δ (U.ι ''ᵁ W) (U.ι_image_le W)) := by
  let V := U.ι ''ᵁ W
  let hVU : V ≤ U := U.ι_image_le W
  have hi : (U.ι.isoImage W).inv ≫ W.ι = Y.homOfLE hVU := U.isoImage_ι_inv_ι W
  let hδ : IsIso (pullbackSectionHom (Y.homOfLE hVU) δ) :=
    SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
      (U.ι.isoImage W).inv W.ι (Y.homOfLE hVU) hi δ hW
  change IsIso (pullbackSectionHom (Y.homOfLE hVU) δ ≫
    (frameFactorIso (Y.homOfLE hVU) U.ι V.ι (Y.homOfLE_ι hVU) M).hom)
  infer_instance

private theorem mem_open_image_of_factor {K : CommRingCat.{u}} [IsLocalRing K]
    {Y : Scheme.{u}} (U : Y.Opens) (r : Spec K ⟶ U.toScheme)
    (p : Spec K ⟶ Y) (hp : r ≫ U.ι = p)
    (x : Y) (hx : p (IsLocalRing.closedPoint K) = x)
    (W : U.toScheme.Opens) (hrW : r (IsLocalRing.closedPoint K) ∈ W) : x ∈ U.ι ''ᵁ W :=
  ⟨r (IsLocalRing.closedPoint K),hrW,
    (congrArg (fun f : Spec K ⟶ Y => f (IsLocalRing.closedPoint K)) hp).trans hx⟩

private theorem exists_localSection_iso_at_fieldPoint {K : CommRingCat.{u}} [IsLocalRing K]
    (hK : IsField K)
    {Y : Scheme.{u}} (M : Y.Modules) (hM : IsInvertible M)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (r : Spec K ⟶ U.toScheme) (p : Spec K ⟶ Y)
    (hp : r ≫ U.ι = p)
    (hs : sectionAtOne (pullbackSectionHom r δ ≫ (frameFactorIso r U.ι p hp M).hom) ≠ 0) :
    ∃ (V : Y.Opens) (hVU : V ≤ U), p (IsLocalRing.closedPoint K) ∈ V ∧
      IsIso (restrictLocalSection M U δ V hVU) := by
  have hr := factorAtOne_ne_zero r U.ι p hp δ hs
  obtain ⟨W,hrW,hW⟩ := exists_sectionFrame_at_fieldPoint hK (hM.pullback U.ι) δ r hr
  exact ⟨U.ι ''ᵁ W,U.ι_image_le W,
    mem_open_image_of_factor U r p hp (p (IsLocalRing.closedPoint K)) rfl W hrW,
    restrictLocalSection_image_isIso M U δ W hW⟩

private theorem propFamily_transport {T : Type u} (P : T → Prop) {x y : T}
    (h : x = y) (hx : P x) : P y := h ▸ hx

private theorem actualResidue_isField (Y : Scheme.{u}) (x : Y) : IsField (Y.residueField x) :=
  (Ideal.Quotient.maximal_ideal_iff_isField_quotient
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))).mp inferInstance

private theorem exists_localSection_iso {Y : Scheme.{u}} (M : Y.Modules) (hM : IsInvertible M)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (x : Y) (hx : x ∈ U) (hs : supportSectionAt M U δ x hx ≠ 0) :
    ∃ (V : Y.Opens) (hVU : V ≤ U), x ∈ V ∧ IsIso (restrictLocalSection M U δ V hVU) :=
  propFamily_transport
    (fun z : Y => ∃ (V : Y.Opens) (hVU : V ≤ U), z ∈ V ∧
      IsIso (restrictLocalSection M U δ V hVU))
    (Y.fromSpecResidueField_apply x _)
    (exists_localSection_iso_at_fieldPoint (K := CommRingCat.of (Y.residueField x))
      (actualResidue_isField Y x) M hM U δ
      (supportResidueFactor x U hx) (Y.fromSpecResidueField x) (supportResidueFactor_comp x U hx) hs)

section Original
variable {k : Type u} [Field k] [PerfectField k] {n : ℕ} (X : ProjSubvariety k n)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfinAll : ∀ z : RelativeSchemeValuedPoint
    (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
  modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥)

private theorem exists_coordinate_modelSection_ne_zero (j : Fin (n+1)) (d : ℕ)
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J
        (fun w => hfinAll (X.nativeProductGaussPoint w)))) :
    ∃ l : Fin (n+1), ∃ hF : ((MvPolynomial.X l : MvPolynomial (Fin (n+1)) k)^d).IsHomogeneous d,
      (X.normalizedSimultaneousBaseRestrictionAt I J _ y).1.1.val ((MvPolynomial.X l)^d) = 1 ∧
      (MvPolynomial.X l : MvPolynomial (Fin (n+1)) k)^d ∉ X.ideal ∧
      X.normalizedSimultaneousOriginalRatioSectionAt I J
        (fun w => hfinAll (X.nativeProductGaussPoint w)) y
        (hfinAll (X.normalizedSimultaneousProductPointAt I J _ y)).1 j d
        ((MvPolynomial.X l)^d) hF ≠ 0 := by
  let hfin := fun w => hfinAll (X.nativeProductGaussPoint w)
  let w := X.normalizedSimultaneousBaseRestrictionAt I J hfin y
  obtain ⟨l,hl⟩ := ProjBerk.exists_val_X_eq_one w.1
  have hF : ((MvPolynomial.X l : MvPolynomial (Fin (n+1)) k)^d).IsHomogeneous d := by
    simpa only [one_mul] using (MvPolynomial.isHomogeneous_X (R := k) l).pow d
  have hv : w.1.1.val ((MvPolynomial.X l)^d) = 1 := by
    rw [map_pow, hl, one_pow]
  have hFI : (MvPolynomial.X l : MvPolynomial (Fin (n+1)) k)^d ∉ X.ideal :=
    X.notMem_ideal_of_val_ne_zero (v := w) (by rw [hv]; exact one_ne_zero)
  refine ⟨l,hF,hv,hFI,?_⟩
  let z := X.normalizedSimultaneousProductPointAt I J hfin y
  let a := modelIdealLog I gaussModelCoefficient_le_one z
  let b := modelIdealLog J gaussModelCoefficient_le_one z
  have ha : (a.toReal : EReal) = a := EReal.coe_toReal
    (modelIdealLog_ne_top gaussModelCoefficient_le_one I z) (hfinAll z).1
  have hb : (b.toReal : EReal) = b := EReal.coe_toReal
    (modelIdealLog_ne_top gaussModelCoefficient_le_one J z) (hfinAll z).2
  have hlog : ProjBerk.logAbs ((MvPolynomial.X l)^d) w.1 = 0 := by
    change ENNReal.log (w.1.1.val ((MvPolynomial.X l)^d) : ℝ≥0∞) = 0
    rw [hv]
    exact ENNReal.log_one
  have hw := X.normalizedSimultaneousOriginalRatioWeightAt_eq I J hfin y
    (hfinAll z).1 j d ((MvPolynomial.X l)^d) hF
  rw [X.normalizedSimultaneousPolynomialRatioWeightAt_eq,
    X.normalizedSimultaneousRatioWeightAt_eq, hlog, sub_zero] at hw
  have he : X.normalizedSimultaneousOriginalRatioWeightAt I J hfin y
      (hfinAll z).1 j d ((MvPolynomial.X l)^d) hF = ((a.toReal-b.toReal : ℝ) : EReal) := by
    exact hw.trans (by rw [EReal.coe_sub, ha, hb])
  intro hs
  let : IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin
  have hn := (modelLineNorm_eq_zero_iff gaussModelCoefficient_le_one y
    (X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d) _).mpr hs
  unfold ProjSubvariety.normalizedSimultaneousOriginalRatioWeightAt at he
  rw [hn, ENNReal.coe_zero, ENNReal.log_zero, EReal.neg_bot] at he
  exact EReal.coe_ne_top (a.toReal-b.toReal) he.symm

/-- At EVERY original native point, an internally chosen coordinate power
gives ONE genuine support-open local frame of the SAME original line.
Every original sigma_F fibre section there is this actual frame section. -/
theorem exists_originalPolarized_supportFrame (j : Fin (n+1)) (d : ℕ)
    (y₀ : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J
        (fun w => hfinAll (X.nativeProductGaussPoint w)))) :
    ∃ (l : Fin (n+1)) (hF : ((MvPolynomial.X l : MvPolynomial (Fin (n+1)) k)^d).IsHomogeneous d),
      (X.normalizedSimultaneousBaseRestrictionAt I J _ y₀).1.1.val ((MvPolynomial.X l)^d) = 1 ∧
      (MvPolynomial.X l : MvPolynomial (Fin (n+1)) k)^d ∉ X.ideal ∧
      ∃ (V : (X.normalizedSimultaneousIdealBlowup I J
          (fun w => hfinAll (X.nativeProductGaussPoint w))).Opens)
        (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj
          (X.normalizedSimultaneousTwistedRatioLine I J
            (fun w => hfinAll (X.nativeProductGaussPoint w)) j d)),
        y₀.1.point ∈ V ∧ IsIso δ ∧
        ∀ (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
          (X.normalizedSimultaneousIdealBlowupStructure I J
            (fun w => hfinAll (X.nativeProductGaussPoint w)))) (hy : y.1.point ∈ V),
          ∃ hnI : modelIdealLog I gaussModelCoefficient_le_one
              (X.normalizedSimultaneousProductPointAt I J _ y) ≠ ⊥,
            X.normalizedSimultaneousOriginalRatioSectionAt I J _ y hnI j d
              ((MvPolynomial.X l)^d) hF =
                supportSectionAt (X.normalizedSimultaneousTwistedRatioLine I J
                  (fun w => hfinAll (X.nativeProductGaussPoint w)) j d) V δ y.1.point hy := by
  let hfin := fun w => hfinAll (X.nativeProductGaussPoint w)
  let : IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin
  obtain ⟨l,hF,hval,hFI,hσ⟩ := exists_coordinate_modelSection_ne_zero X I J hfinAll j d y₀
  let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
  let A := (I.comap (X.simultaneousIdealBlowupProjection I J)).comap
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin)
  let U := A.support.compl
  have hyU : y₀.1.point ∈ U := by
    intro hy
    apply (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y₀)).1
    exact (X.modelIdealLog_normalizedSimultaneous_comap I J hfin I y₀).symm.trans
      ((modelIdealLog_eq_bot_iff A gaussModelCoefficient_le_one y₀).mpr hy)
  obtain ⟨δ,hδ⟩ := exists_originalPolarized_localSection X I J hfin j d
    ((MvPolynomial.X l)^d) hF U le_rfl
  obtain ⟨hn₀,hδ₀⟩ := hδ y₀ hyU
  have hs : supportSectionAt M U δ y₀.1.point hyU ≠ 0 := by
    rw [← hδ₀]
    exact hσ
  obtain ⟨V,hVU,hyV,hiso⟩ := exists_localSection_iso M
    (X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d) U δ y₀.1.point hyU hs
  refine ⟨l,hF,hval,hFI,V,restrictLocalSection M U δ V hVU,hyV,hiso,?_⟩
  intro y hy
  obtain ⟨hn,he⟩ := hδ y (hVU hy)
  exact ⟨hn,he.trans (supportSectionAt_restrict M U δ V hVU y.1.point hy).symm⟩
end Original

end EnvelopeProperty.NumericalSectionRegaugingGauge
