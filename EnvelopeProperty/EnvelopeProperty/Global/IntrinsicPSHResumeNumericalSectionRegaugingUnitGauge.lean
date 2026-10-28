import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalSectionRegaugingGauge

/-! # Actual regular-unit representatives of original rational line sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped Classical NNReal ENNReal
universe u
namespace EnvelopeProperty.NumericalSectionRegaugingUnitGauge
open Scheme.Modules SchemeLineSectionEvaluation
open NumericalSectionRegauging NumericalSectionRegaugingOriginal NumericalSectionRegaugingGauge
open Berkovich Berkovich.RelativeSchemeValuedPoint

private theorem unitScalar_atOne {B : Scheme.{u}} (r : Γ(B, ⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
  rw [sectionAtOne, ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id, one_mul]
  erw [CategoryTheory.Functor.map_id]
  rfl

private theorem iso_app_injective {B : Scheme.{u}} {M N : B.Modules} (E : M ≅ N) :
    Function.Injective (E.hom.val.app (op ⊤)) := by
  have hleft : Function.LeftInverse (E.inv.val.app (op ⊤)) (E.hom.val.app (op ⊤)) := by
    intro a
    have h := congrArg (fun f => f.val.app (op ⊤) a) E.hom_inv_id
    exact h
  exact hleft.injective

private theorem iso_app_ne_zero {B : Scheme.{u}} {M N : B.Modules} (E : M ≅ N)
    (ρ : Γ(M, ⊤)) (hρ : ρ ≠ 0) : E.hom.val.app (op ⊤) ρ ≠ 0 := by
  intro hz
  exact hρ ((iso_app_injective E) (hz.trans (map_zero _).symm))

private theorem specScalar_ne_zero (K : CommRingCat.{u}) (r : Γ(Spec K, ⊤)) (hr : r ≠ 0) :
    (Scheme.ΓSpecIso K).hom.hom r ≠ 0 := by
  intro hz
  exact hr ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso K).hom).1
    (hz.trans (map_zero _).symm))

private theorem frame_coefficient {B : Scheme.{u}} {M : B.Modules}
    (E : M ≅ unitObj B) (σ : Γ(M, ⊤))
    (hσ : E.hom.val.app (op ⊤) σ = (1 : Γ(B, ⊤))) (ρ : Γ(M, ⊤)) :
    (show Γ(B, ⊤) from E.hom.val.app (op ⊤) ρ) • σ = ρ := by
  let r : Γ(B, ⊤) := E.hom.val.app (op ⊤) ρ
  let t : Γ(B, ⊤) := E.hom.val.app (op ⊤) σ
  apply iso_app_injective E
  have h := (E.hom.val.app (op ⊤)).hom.map_smul r σ
  change E.hom.val.app (op ⊤) (r • σ) = r * t at h
  have ht : t = 1 := hσ
  exact h.trans (by rw [ht,mul_one])

private theorem evaluation_restrict {Y : Scheme.{u}} (U V : Y.Opens) (hVU : V ≤ U)
    (x : Y) (hx : x ∈ V) (r : Γ(Y,U)) :
    Y.evaluation V x hx (Y.presheaf.map (homOfLE hVU).op r) =
      Y.evaluation U x (hVU hx) r := by
  change (Y.residue x).hom (Y.presheaf.germ V x hx
    (Y.presheaf.map (homOfLE hVU).op r)) = _
  rw [Y.presheaf.germ_res_apply]
  rfl

private theorem exists_genericUnit_on_subopen (Y : Scheme.{u}) [IsIntegral Y]
    (U : Y.Opens) (hηU : genericPoint Y ∈ U)
    (c : Y.residueField (genericPoint Y)) (hc : c ≠ 0) :
    ∃ (V : Y.Opens) (_hV : V ∈ Y.affineOpens) (_hVU : V ≤ U)
      (hηV : genericPoint Y ∈ V) (a : Γ(Y,V)ˣ),
      Y.evaluation V (genericPoint Y) hηV (a : Γ(Y,V)) = c := by
  obtain ⟨W,hW,hηW,a,ha⟩ := exists_genericResidue_localUnit Y c hc
  obtain ⟨_,⟨V,hV,rfl⟩,hηV,hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint Y ∈ W ⊓ U from ⟨hηW,hηU⟩) (W ⊓ U).isOpen
  have hVW : V ≤ W := fun _ hx => (hVU hx).1
  let aV := Units.map (Y.presheaf.map (homOfLE hVW).op).hom.toMonoidHom a
  refine ⟨V,hV,(fun _ hx => (hVU hx).2),hηV,aV,?_⟩
  change Y.evaluation V (genericPoint Y) hηV
    (Y.presheaf.map (homOfLE hVW).op (a : Γ(Y,W))) = c
  rw [evaluation_restrict]
  exact ha

private def originalFibreModule {X : Scheme.{u}} (M : X.Modules) (x : X) :
    (Spec (CommRingCat.of (X.residueField x))).Modules :=
  (pullback (X.fromSpecResidueField x)).obj M

private theorem originalFibreModule_eq_generic
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0} {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} (y : RelativeSchemeValuedPoint v f) (M : X.Modules) :
    originalFibreModule M y.1.point = genericLineModule y M := by
  rfl

private def supportHomAt {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M) (x : Y) (hx : x ∈ U) :
    unitObj (Spec (CommRingCat.of (Y.residueField x))) ⟶
      originalFibreModule M x :=
  pullbackSectionHom (supportResidueFactor x U hx) δ ≫
    (frameFactorIso (supportResidueFactor x U hx) U.ι (Y.fromSpecResidueField x)
      (supportResidueFactor_comp x U hx) M).hom

private def pulledLocalHomAt {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (x : X) (hx : g x ∈ U) :
    unitObj (Spec (CommRingCat.of (X.residueField x))) ⟶
      originalFibreModule ((pullback g).obj M) x :=
  SchemeValuedPoint.pullbackResidueSectionHom g x (supportHomAt M U δ (g x) hx)

private def openScalarAt {X : Scheme.{u}} (V : X.Opens) (a : Γ(X,V))
    (x : X) (hx : x ∈ V) : Γ(Spec (CommRingCat.of (X.residueField x)), ⊤) :=
  (supportResidueFactor x V hx).appTop.hom (openTopSection V a)

private theorem targetSupport {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (hVU : V ≤ g ⁻¹ᵁ U) (x : X) (hx : x ∈ V) : g x ∈ U :=
  hVU hx

/-- The canonical actual original fibre family: original target local Hom,
its genuine residue-field pullback, and the actual source regular-unit scalar.
It is indexed by original scheme points and uses no valuation choices. -/
def unitPullbackSectionValue {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (V : X.Opens) (hVU : V ≤ g ⁻¹ᵁ U) (a : Γ(X,V)ˣ) (x : X) (hx : x ∈ V) :
    Γ(originalFibreModule ((pullback g).obj M) x, ⊤) :=
  openScalarAt V (a : Γ(X,V)) x hx •
    sectionAtOne (pulledLocalHomAt g M U δ x (targetSupport g U V hVU x hx))

private theorem pullbackSectionHom_isIso {B C : Scheme.{u}} (g : B ⟶ C)
    {M : C.Modules} (δ : unitObj C ⟶ M) [IsIso δ] : IsIso (pullbackSectionHom g δ) := by
  dsimp only [pullbackSectionHom]
  infer_instance

private theorem supportHomAt_isIso {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M) [IsIso δ] (x : Y) (hx : x ∈ U) :
    IsIso (supportHomAt M U δ x hx) := by
  exact IsIso.comp_isIso' (pullbackSectionHom_isIso (supportResidueFactor x U hx) δ)
    (frameFactorIso (supportResidueFactor x U hx) U.ι (Y.fromSpecResidueField x)
      (supportResidueFactor_comp x U hx) M).isIso_hom

private theorem pulledLocalHomAt_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M) [IsIso δ]
    (x : X) (hx : g x ∈ U) : IsIso (pulledLocalHomAt g M U δ x hx) := by
  let : IsIso (supportHomAt M U δ (g x) hx) := supportHomAt_isIso M U δ (g x) hx
  exact IsIso.comp_isIso'
    (pullbackSectionHom_isIso (Spec.map (g.residueFieldMap x)) (supportHomAt M U δ (g x) hx))
    (SchemeValuedPoint.residueModulePullbackIso g x M).isIso_hom

private def isoSectionCoefficient {B : Scheme.{u}} (M : B.Modules)
    (β : unitObj B ⟶ M) [IsIso β] (ρ : Γ(M, ⊤)) : Γ(B, ⊤) :=
  (inv β).val.app (op ⊤) ρ

private theorem isoSectionCoefficient_apply {B : Scheme.{u}} (M : B.Modules)
    (β : unitObj B ⟶ M) [IsIso β] (ρ : Γ(M, ⊤)) :
    isoSectionCoefficient M β ρ • sectionAtOne β = ρ := by
  have h := congrArg (fun f : unitObj B ⟶ unitObj B => f.val.app (op ⊤)
    (1 : Γ(B, ⊤))) (asIso β).hom_inv_id
  change (inv β).val.app (op ⊤) (sectionAtOne β) = (1 : Γ(B, ⊤)) at h
  exact frame_coefficient (asIso β).symm (sectionAtOne β) h ρ

private theorem isoSectionCoefficient_ne_zero {B : Scheme.{u}} (M : B.Modules)
    (β : unitObj B ⟶ M) [IsIso β] (ρ : Γ(M, ⊤)) (hρ : ρ ≠ 0) :
    isoSectionCoefficient M β ρ ≠ 0 :=
  iso_app_ne_zero (asIso β).symm ρ hρ

private theorem exists_unit_at_generic_point (X : Scheme.{u}) [IsIntegral X]
    (x : X) (hx : x = genericPoint X) (W : X.Opens) (hxW : x ∈ W)
    (c : X.residueField x) (hc : c ≠ 0) :
    ∃ (V : X.Opens) (_hV : V ∈ X.affineOpens) (_hVW : V ≤ W)
      (hxV : x ∈ V) (a : Γ(X,V)ˣ), X.evaluation V x hxV (a : Γ(X,V)) = c := by
  subst x
  exact exists_genericUnit_on_subopen X W hxW c hc

private theorem pointFamily_eq_transport {T : Type*} {F : T → Type*} {U : Set T}
    (s : ∀ x, x ∈ U → F x) (x₀ : T) (hx₀ : x₀ ∈ U) (ρ : F x₀)
    (hρ : s x₀ hx₀ = ρ) (x : T) (hx : x ∈ U) (he : x = x₀) :
    s x hx = he.symm ▸ ρ := by
  subst x
  exact hρ

private theorem exists_nativeUnit_gauge {X Y : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M) [IsIso δ]
    (x₀ : X) (hx₀ : x₀ = genericPoint X) (hxU : g x₀ ∈ U)
    (ρ : Γ(originalFibreModule ((pullback g).obj M) x₀, ⊤))
    (hρ : ρ ≠ 0) :
    ∃ (V : X.Opens) (_hV : V ∈ X.affineOpens) (hVU : V ≤ g ⁻¹ᵁ U)
      (hxV : x₀ ∈ V) (a : Γ(X,V)ˣ),
      unitPullbackSectionValue g M U δ V hVU a x₀ hxV = ρ ∧
      ∀ (x : X) (hx : x ∈ V) (he : x = x₀),
        unitPullbackSectionValue g M U δ V hVU a x hx = he.symm ▸ ρ := by
  let β := pulledLocalHomAt g M U δ x₀ hxU
  let : IsIso β := pulledLocalHomAt_isIso g M U δ x₀ hxU
  let r : Γ(Spec (CommRingCat.of (X.residueField x₀)), ⊤) :=
    isoSectionCoefficient _ β ρ
  have hr : r ≠ 0 := isoSectionCoefficient_ne_zero _ β ρ hρ
  let c := (Scheme.ΓSpecIso (CommRingCat.of (X.residueField x₀))).hom.hom r
  have hc : c ≠ 0 := specScalar_ne_zero (CommRingCat.of (X.residueField x₀)) r hr
  obtain ⟨V,hV,hVU,hxV,a,ha⟩ :=
    exists_unit_at_generic_point X x₀ hx₀ (g ⁻¹ᵁ U) hxU c hc
  have hs : openScalarAt V (a : Γ(X,V)) x₀ hxV = r := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (X.residueField x₀))).hom).1
    exact (supportResidueFactor_openTopSection x₀ V hxV _).trans ha
  have hval : unitPullbackSectionValue g M U δ V hVU a x₀ hxV = ρ := by
    change openScalarAt V (a : Γ(X,V)) x₀ hxV • sectionAtOne β = ρ
    rw [hs]
    exact isoSectionCoefficient_apply _ β ρ
  refine ⟨V,hV,hVU,hxV,a,hval,?_⟩
  intro x hx he
  exact pointFamily_eq_transport (fun x hx => unitPullbackSectionValue g M U δ V hVU a x hx)
    x₀ hxV ρ hval x hx he

private theorem unitPullbackSectionValue_norm
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0} {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
    [IsProper fX] [IsProper fY] (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)))
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fX)
    (M : Y.Modules) (hM : IsInvertible M) (U : Y.Opens)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (V : X.Opens) (hVU : V ≤ g ⁻¹ᵁ U) (a : Γ(X,V)ˣ) (hy : y.1.point ∈ V) :
    modelLineNorm hb y (hM.pullback g)
      (unitPullbackSectionValue g M U δ V hVU a y.1.point hy) =
      SchemeValuedPoint.eval y.1 V hy (a : Γ(X,V)) *
        modelLineNorm hb (mapOverBase (RingHom.id R) (fun _ => rfl) g hg y) hM
          (sectionAtOne (supportHomAt M U δ (g y.1.point)
            (targetSupport g U V hVU y.1.point hy))) := by
  let ht : g y.1.point ∈ U := targetSupport g U V hVU y.1.point hy
  let β := supportHomAt M U δ (g y.1.point) ht
  have hmul := modelLineNorm_smul hb y (hM.pullback g)
    (openScalarAt V (a : Γ(X,V)) y.1.point hy)
    (sectionAtOne (SchemeValuedPoint.pullbackResidueSectionHom g y.1.point β))
  have heval : y.1.residueVal
      ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
        (openScalarAt V (a : Γ(X,V)) y.1.point hy)) =
      SchemeValuedPoint.eval y.1 V hy (a : Γ(X,V)) := by
    dsimp only [openScalarAt]
    rw [supportResidueFactor_openTopSection]
    rfl
  have hn := modelLineNorm_pullbackResidueSectionHom_eq_overBase (RingHom.id R)
    (fun _ => rfl) g hg hb hb y hM β
  exact hmul.trans (congrArg₂ (fun b c : ℝ≥0 => b*c) heval hn)

private theorem supportHomAt_value {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M) (x : Y) (hx : x ∈ U) :
    sectionAtOne (supportHomAt M U δ x hx) = supportSectionAt M U δ x hx := by
  rfl

private theorem unitPullbackSectionValue_weight
    {R : Type u} [CommRing R] {v : Valuation R ℝ≥0} {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
    [IsProper fX] [IsProper fY] (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)))
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fX)
    (M : Y.Modules) (hM : IsInvertible M) (U : Y.Opens)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M)
    (V : X.Opens) (hVU : V ≤ g ⁻¹ᵁ U) (a : Γ(X,V)ˣ) (hy : y.1.point ∈ V) :
    -ENNReal.log (modelLineNorm hb y (hM.pullback g)
      (unitPullbackSectionValue g M U δ V hVU a y.1.point hy) : ℝ≥0∞) =
      -ENNReal.log (modelLineNorm hb (mapOverBase (RingHom.id R) (fun _ => rfl) g hg y) hM
        (supportSectionAt M U δ (g y.1.point) (targetSupport g U V hVU y.1.point hy)) : ℝ≥0∞) -
        SchemeValuedPoint.sectionLogAbs V (a : Γ(X,V)) y.1 := by
  have hn : modelLineNorm hb y (hM.pullback g)
      (unitPullbackSectionValue g M U δ V hVU a y.1.point hy) =
      SchemeValuedPoint.eval y.1 V hy (a : Γ(X,V)) *
        modelLineNorm hb (mapOverBase (RingHom.id R) (fun _ => rfl) g hg y) hM
          (supportSectionAt M U δ (g y.1.point) (targetSupport g U V hVU y.1.point hy)) :=
    unitPullbackSectionValue_norm g hg hb y M hM U δ V hVU a hy
  rw [hn,ENNReal.coe_mul,ENNReal.log_mul_add,
    SchemeValuedPoint.sectionLogAbs_of_mem V _ y.1 hy]
  have hnotop (b : ℝ≥0) : ENNReal.log (b : ℝ≥0∞) ≠ ⊤ :=
    fun h => ENNReal.coe_ne_top (ENNReal.log_eq_top_iff.mp h)
  exact (EReal.neg_add (Or.inr (hnotop _)) (Or.inl (hnotop _))).trans (add_comm _ _)

open ProjBerk

/-- The fixed ORIGINAL normalized line produces a canonical native gauge
for ANY original nonzero generic section, with ALL generic-support values
equal to that section and ALL actual model weights internally computed. -/
theorem exists_originalPolarized_nativeGauge {k : Type u} [Field k] [PerfectField k]
    {n : ℕ} (X : ProjSubvariety k n) (I J : X.NativeProductModel.IdealSheafData)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥) :
    let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
    ∀ (j : Fin (n+1)) (d : ℕ),
      let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
      ∀ (Z : Scheme.{u}) (fZ : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
        [IsProper fZ] [IsIntegral Z]
        (g : Z ⟶ X.normalizedSimultaneousIdealBlowup I J hfin)
        (hg : g ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
          fZ ≫ Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))))
        (y₀ : RelativeSchemeValuedPoint
          (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
        (hη : y₀.1.point = genericPoint Z)
        (ρ : Γ(genericLineModule y₀ ((pullback g).obj M), ⊤)), ρ ≠ 0 →
        ∃ (l : Fin (n+1)) (hF : (MvPolynomial.X l ^ d : MvPolynomial (Fin (n+1)) k).IsHomogeneous d),
          (X.normalizedSimultaneousBaseRestrictionAt I J hfin
            (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y₀)).1.1.val
              (MvPolynomial.X l ^ d) = 1 ∧ MvPolynomial.X l ^ d ∉ X.ideal ∧
          ∃ (U : (X.normalizedSimultaneousIdealBlowup I J hfin).Opens)
            (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M), IsIso δ ∧
            ∃ (V : Z.Opens) (_hV : V ∈ Z.affineOpens) (hVU : V ≤ g ⁻¹ᵁ U) (a : Γ(Z,V)ˣ),
              y₀.1.point ∈ V ∧
              (∀ (y : RelativeSchemeValuedPoint
                  (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
                (hyη : y.1.point = genericPoint Z), ∃ hyV : y.1.point ∈ V,
                  unitPullbackSectionValue g M U δ V hVU a y.1.point hyV =
                    (hyη.trans hη.symm).symm ▸ ρ) ∧
              ∀ (y : RelativeSchemeValuedPoint
                  (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
                (hyV : y.1.point ∈ V),
                -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
                  ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
                  (unitPullbackSectionValue g M U δ V hVU a y.1.point hyV) : ℝ≥0∞) =
                  X.normalizedSimultaneousOriginalRatioWeightAt I J hfin
                    (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y)
                    (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin
                      (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y))).1
                    j d (MvPolynomial.X l ^ d) hF -
                    SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1 := by
  intro hfin j d M Z fZ hProper hIntegral g hg y₀ hη ρ hρ
  let hM := X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d
  let : IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin
  let q : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ →
      RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg
  obtain ⟨l,hF,hval,hFI,U,δ,hyU,hδ,hsections⟩ :=
    exists_originalPolarized_supportFrame X I J hfinAll j d (q y₀)
  let : IsIso δ := hδ
  obtain ⟨V,hV,hVU,hyV,a,hrho,hgeneric⟩ :=
    exists_nativeUnit_gauge g M U δ y₀.1.point hη hyU ρ hρ
  refine ⟨l,hF,hval,hFI,U,δ,hδ,V,hV,hVU,a,hyV,?_,?_⟩
  · intro y hyη
    let he := hyη.trans hη.symm
    have hy : y.1.point ∈ V := he.symm ▸ hyV
    exact ⟨hy,hgeneric y.1.point hy he⟩
  · intro y hy
    have ht : (q y).1.point ∈ U := targetSupport g U V hVU y.1.point hy
    obtain ⟨hnI,he⟩ := hsections (q y) ht
    have hw := unitPullbackSectionValue_weight g hg gaussModelCoefficient_le_one y M hM U δ V hVU a hy
    have hnorm := congrArg (fun s =>
      -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one (q y) hM s : ℝ≥0∞)) he.symm
    exact hw.trans (congrArg (fun t : EReal => t - SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1) hnorm)


/-- ORIGINAL local convexity internally constructs the fixed prescribed class
and genuine canonical gauges for EVERY original nonzero generic section.
The native fibre family equals the same section at ALL generic supports,
and its TRUE original model weight is intrinsically convex near the original point. -/
theorem exists_prescribedClass_nativeRationalGauges
    {k : Type u} [Field k] [PerfectField k] {n : ℕ}
    (X : ProjSubvariety k n) (hX : X.IsProjNormal)
    {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (_hd : 0 < d), (d : ℚ) = r*a ∧
      ∃ (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
        (hfinAll : ∀ z : RelativeSchemeValuedPoint
            (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
          modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
          modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥),
        let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
        (∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
            (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
          (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
            X.normalizedSimultaneousRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal)) ∧
        ∀ (j : Fin (n+1)),
      let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
      ∀ (Z : Scheme.{u}) (fZ : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
        [IsProper fZ] [IsIntegral Z]
        (g : Z ⟶ X.normalizedSimultaneousIdealBlowup I J hfin)
        (hg : g ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
          fZ ≫ Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))))
        (y₀ : RelativeSchemeValuedPoint
          (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
        (hη : y₀.1.point = genericPoint Z)
        (ρ : Γ(genericLineModule y₀ ((pullback g).obj M), ⊤)), ρ ≠ 0 →
        ∃ (l : Fin (n+1)) (hF : (MvPolynomial.X l ^ d : MvPolynomial (Fin (n+1)) k).IsHomogeneous d),
          (X.normalizedSimultaneousBaseRestrictionAt I J hfin
            (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y₀)).1.1.val
              (MvPolynomial.X l ^ d) = 1 ∧ MvPolynomial.X l ^ d ∉ X.ideal ∧
          ∃ (U : (X.normalizedSimultaneousIdealBlowup I J hfin).Opens)
            (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M), IsIso δ ∧
            ∃ (V : Z.Opens) (_hV : V ∈ Z.affineOpens) (hVU : V ≤ g ⁻¹ᵁ U) (a : Γ(Z,V)ˣ),
              y₀.1.point ∈ V ∧
              (∀ (y : RelativeSchemeValuedPoint
                  (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
                (hyη : y.1.point = genericPoint Z), ∃ hyV : y.1.point ∈ V,
                  unitPullbackSectionValue g M U δ V hVU a y.1.point hyV =
                    (hyη.trans hη.symm).symm ▸ ρ) ∧
              (∀ (y : RelativeSchemeValuedPoint
                  (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
                (hyV : y.1.point ∈ V),
                -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
                  ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
                  (unitPullbackSectionValue g M U δ V hVU a y.1.point hyV) : ℝ≥0∞) =
                  X.normalizedSimultaneousOriginalRatioWeightAt I J hfin
                    (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y)
                    (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin
                      (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y))).1
                    j d (MvPolynomial.X l ^ d) hF -
                    SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1) ∧
              y₀ ∈ ((mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg ⁻¹'
                X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin (MvPolynomial.X l ^ d)) ∩
                  {y : RelativeSchemeValuedPoint
                    (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ | y.1.point ∈ V}) ∧
              Berkovich.RelativeSchemeValuedPoint.IsConvexPLOn
                ((mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg ⁻¹'
                  X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin (MvPolynomial.X l ^ d)) ∩
                    {y : RelativeSchemeValuedPoint
                    (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ | y.1.point ∈ V})
                (fun (y : RelativeSchemeValuedPoint
                    (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ) => if hy : y.1.point ∈ V then
                  -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
                    ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
                    (unitPullbackSectionValue g M U δ V hVU a y.1.point hy) : ℝ≥0∞)
                  else ⊤) := by
  obtain ⟨r,d,hr,hd,hda,C,I,J,hfinAll,heq,hweights⟩ :=
    hconv.exists_prescribedClass_intrinsicConvex_originalModelMetric X hX ha
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  refine ⟨r,d,hr,hd,hda,C,I,J,hfinAll,heq,?_⟩
  intro j M Z fZ hProper hIntegral g hg y₀ hη ρ hρ
  obtain ⟨l,hF,hval,hFI,U,δ,hδ,V,hV,hVU,a,hyV,hgeneric,hnorm⟩ :=
    exists_originalPolarized_nativeGauge X I J hfinAll j d Z fZ g hg y₀ hη ρ hρ
  let q : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ →
      RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg
  have hc := Berkovich.RelativeSchemeValuedPoint.IsConvexPLOn.comp_mapOverBase (RingHom.id (Polynomial k))
    (fun _ => rfl) g hg (hweights j (MvPolynomial.X l ^ d) hF hFI)
  have hc' := hc.add_smul_sectionLogAbs V a (-1)
  refine ⟨l,hF,hval,hFI,U,δ,hδ,V,hV,hVU,a,hyV,hgeneric,hnorm,?_,?_⟩
  · refine ⟨?_,hyV⟩
    exact (X.mem_normalizedSimultaneousAdmissibleAnalyticLocus I J hfin _ (q y₀)).mpr
      (by rw [hval]; exact one_ne_zero)
  · apply hc'.congr
    intro y hy
    have hyV : y.1.point ∈ V := hy.2
    let w : EReal := X.normalizedSimultaneousOriginalRatioWeightAt I J hfin
      (q y) (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin (q y))).1
      j d (MvPolynomial.X l ^ d) hF
    have hadj : w + (((-1 : ℚ) : ℝ) : EReal) *
        SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1 =
        w - SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1 := by
      exact congrArg (fun t : EReal => w + t)
        (by simp only [Rat.cast_neg,Rat.cast_one,EReal.coe_neg,EReal.coe_one,neg_one_mul])
    have hcond :
        (if hx : y.1.point ∈ V then
          -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
            ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
            (unitPullbackSectionValue g M U δ V hVU a y.1.point hx) : ℝ≥0∞)
          else ⊤) =
        -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
          ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
          (unitPullbackSectionValue g M U δ V hVU a y.1.point hyV) : ℝ≥0∞) :=
      dif_pos hyV
    exact hadj.trans ((hnorm y hyV).symm.trans hcond.symm)

end EnvelopeProperty.NumericalSectionRegaugingUnitGauge
