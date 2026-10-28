import EnvelopeProperty.Local.PLGaussCommonVerticalPoints
import EnvelopeProperty.AlgGeom.CentralGenericLineSectionLift

/-! # The prescribed central generic section has norm one at the SAME true vertex -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
open scoped Classical NNReal
universe u
namespace EnvelopeProperty.GaussCentralLineNormalization
open Berkovich Berkovich.RelativeSchemeValuedPoint SchemeLineSectionEvaluation

private def originalFibreModule {Y : Scheme.{u}} (L : Y.Modules) (p : Y) :
    (Spec (CommRingCat.of (Y.residueField p))).Modules :=
  (pullback (Y.fromSpecResidueField p)).obj L

private theorem originalFibreModule_eq_generic {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)}
    (y : RelativeSchemeValuedPoint v f) (L : Y.Modules) :
    originalFibreModule L y.1.point = genericLineModule y L := rfl

private def rawSectionToOriginal {Y : Scheme.{u}} (L : Y.Modules) (p : Y)
    (s : Γ((pullback (Y.fromSpecResidueField p)).obj L, ⊤)) :
    Γ(originalFibreModule L p, ⊤) := s

/-- Equality transport retains the prescribed raw section in the actual point-indexed fibre. -/
def genericSectionAt {Y : Scheme.{u}} [IsIntegral Y] (L : Y.Modules)
    (p : Y) (hp : p = genericPoint Y)
    (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)) :
    Γ(originalFibreModule L p, ⊤) := by
  subst p
  exact rawSectionToOriginal L (genericPoint Y) ρ

private def pointOpenFactor {Y : Scheme.{u}} (p : Y) (V : Y.Opens) (hp : p ∈ V) :
    Spec (CommRingCat.of (Y.residueField p)) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (Y.fromSpecResidueField p) (by
    rw [V.range_ι]
    rintro _ ⟨z,rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact hp)

private theorem pointOpenFactor_comp {Y : Scheme.{u}} (p : Y)
    (V : Y.Opens) (hp : p ∈ V) :
    pointOpenFactor p V hp ≫ V.ι = Y.fromSpecResidueField p :=
  IsOpenImmersion.lift_fac _ _ _

private def localHomAt {Y : Scheme.{u}} (L : Y.Modules) (V : Y.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) (p : Y) (hp : p ∈ V) :
    unitObj (Spec (CommRingCat.of (Y.residueField p))) ⟶ originalFibreModule L p :=
  pullbackSectionHom (pointOpenFactor p V hp) δ ≫
    (frameFactorIso (pointOpenFactor p V hp) V.ι (Y.fromSpecResidueField p)
      (pointOpenFactor_comp p V hp) L).hom

/-- The SAME local Hom gives the actual section of the actual point-indexed fibre. -/
def localSectionAt {Y : Scheme.{u}} (L : Y.Modules) (V : Y.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) (p : Y) (hp : p ∈ V) :
    Γ(originalFibreModule L p, ⊤) := sectionAtOne (localHomAt L V δ p hp)

private theorem factorSection_congr {Y : Scheme.{u}} (L : Y.Modules) (V : Y.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) (p : Y)
    (g h : Spec (CommRingCat.of (Y.residueField p)) ⟶ V.toScheme)
    (hg : g ≫ V.ι = Y.fromSpecResidueField p)
    (hh : h ≫ V.ι = Y.fromSpecResidueField p) (he : g = h) :
    sectionAtOne (pullbackSectionHom g δ ≫ (frameFactorIso g V.ι
      (Y.fromSpecResidueField p) hg L).hom) =
    sectionAtOne (pullbackSectionHom h δ ≫ (frameFactorIso h V.ι
      (Y.fromSpecResidueField p) hh L).hom) := by
  cases he
  rfl

private theorem genericSectionAt_localSectionAt {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (V : Y.Opens) [Nonempty V]
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L)
    (p : Y) (hp : p = genericPoint Y) (hV : p ∈ V) :
    genericSectionAt L p hp (CentralGenericLineSectionLift.genericSection L V δ) =
      localSectionAt L V δ p hV := by
  subst p
  rfl

private theorem factorSection_frame_one {B C D : Scheme.{u}}
    (g : B ⟶ C) (b : C ⟶ D) (f : B ⟶ D) (hg : g ≫ b = f)
    {L : D.Modules} (δ : unitObj C ⟶ (pullback b).obj L) [IsIso δ] :
    ((frameViaFactor g b f hg (asIso δ).symm).hom.val.app (op ⊤)).hom
      (sectionAtOne (pullbackSectionHom g δ ≫ (frameFactorIso g b f hg L).hom)) =
        (show Γ(B, ⊤) from 1) := by
  let E := (pullbackUnitIso g).symm ≪≫ (pullback g).mapIso (asIso δ) ≪≫
    frameFactorIso g b f hg L
  change (E.inv.val.app (op ⊤)).hom
    ((E.hom.val.app (op ⊤)).hom (show Γ(B, ⊤) from 1)) = _
  exact Scheme.Modules.iso_hom_inv_app_applyT E (op ⊤) _

private theorem pointSectionAt_frame_one {Y : Scheme.{u}}
    (L : Y.Modules) (V : Y.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ]
    (p : Y) (hp : p ∈ V)
    (g : Spec (CommRingCat.of (Y.residueField p)) ⟶ V.toScheme)
    (hg : g ≫ V.ι = Y.fromSpecResidueField p) :
    ((frameViaFactor g V.ι (Y.fromSpecResidueField p) hg (asIso δ).symm).hom.val.app (op ⊤)).hom
      (localSectionAt L V δ p hp) =
        (show Γ(Spec (CommRingCat.of (Y.residueField p)), ⊤) from 1) := by
  have heq : pointOpenFactor p V hp = g := by
    apply (cancel_mono V.ι).mp
    exact (pointOpenFactor_comp p V hp).trans hg.symm
  have hs := factorSection_congr L V δ p _ g (pointOpenFactor_comp p V hp) hg heq
  have he := congrArg (fun t : Γ((pullback (Y.fromSpecResidueField p)).obj L, ⊤) =>
    ((frameViaFactor g V.ι (Y.fromSpecResidueField p) hg (asIso δ).symm).hom.val.app (op ⊤)).hom t) hs
  exact he.trans (factorSection_frame_one g V.ι (Y.fromSpecResidueField p) hg δ)

private theorem localSectionAt_frame_one {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}}
    {f : Y ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (L : Y.Modules) (V : Y.Opens) (hc : center hb y ∈ V)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ] :
    ((localFrameGenericIso hb y V hc (asIso δ).symm).hom.val.app (op ⊤)).hom
      (localSectionAt L V δ y.1.point (support_mem_of_center_mem hb y V hc)) =
        (show Γ(Spec (CommRingCat.of (Y.residueField y.1.point)), ⊤) from 1) := by

  exact pointSectionAt_frame_one L V δ y.1.point (support_mem_of_center_mem hb y V hc)
    (localGenericFactor hb y V hc) (localGenericFactor_comp hb y V hc)

private theorem pointSectionAt_scalar_one {Y : Scheme.{u}}
    (L : Y.Modules) (V : Y.Opens)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ]
    (p : Y) (hp : p ∈ V)
    (g : Spec (CommRingCat.of (Y.residueField p)) ⟶ V.toScheme)
    (hg : g ≫ V.ι = Y.fromSpecResidueField p) :
    (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField p))).hom.hom
      (((frameViaFactor g V.ι (Y.fromSpecResidueField p) hg (asIso δ).symm).hom.val.app
        (op ⊤)).hom (localSectionAt L V δ p hp)) = 1 := by
  exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField p))).hom.hom
    (pointSectionAt_frame_one L V δ p hp g hg)).trans (map_one _)

private theorem localSectionAt_scalar_one {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}}
    {f : Y ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (L : Y.Modules) (V : Y.Opens) (hc : center hb y ∈ V)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ] :
    (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y.1.point))).hom.hom
      (((localFrameGenericIso hb y V hc (asIso δ).symm).hom.val.app (op ⊤)).hom
        (localSectionAt L V δ y.1.point (support_mem_of_center_mem hb y V hc))) = 1 :=
  pointSectionAt_scalar_one L V δ y.1.point (support_mem_of_center_mem hb y V hc)
    (localGenericFactor hb y V hc) (localGenericFactor_comp hb y V hc)

private theorem modelLineNorm_one_of_localScalar {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}}
    {f : Y ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (L : Y.Modules) (hL : IsInvertible L) (V : Y.Opens) (hc : center hb y ∈ V)
    (e : (pullback V.ι).obj L ≅ unitObj V.toScheme)
    (s : Γ(genericLineModule y L, ⊤))
    (hs : (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y.1.point))).hom.hom
      (((localFrameGenericIso hb y V hc e).hom.val.app (op ⊤)).hom s) = 1) :
    modelLineNorm hb y hL s = 1 :=
  (modelLineNorm_eq_localFrame hb y hL V hc e s).trans
    ((congrArg y.1.residueVal hs).trans (map_one _))

/-- A true center-neighborhood generator has genuine model norm one. -/
theorem modelLineNorm_localGenerator {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}}
    {f : Y ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (L : Y.Modules) (hL : IsInvertible L) (V : Y.Opens)
    (hc : center hb y ∈ V)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ] :
    modelLineNorm hb y hL
      (localSectionAt L V δ y.1.point (support_mem_of_center_mem hb y V hc)) = 1 := by
  exact modelLineNorm_one_of_localScalar hb y L hL V hc (asIso δ).symm
    (localSectionAt L V δ y.1.point (support_mem_of_center_mem hb y V hc))
    (localSectionAt_scalar_one hb y L V hc δ)

/-- Prescribed central σ gives an internally lifted SAME generic ρ of norm1 at ANY actual same-center point. -/
theorem exists_prescribed_section_unit_norm_at {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}} [IsIntegral Y]
    {f : Y ⟶ Spec (CommRingCat.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (hy : y.1.point = genericPoint Y)
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i]
    (hc : center hb y = i (genericPoint C))
    (L : Y.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj ((pullback i).obj L), ⊤))
    (hσ : σ ≠ 0) :
    ∃ (V : Y.Opens) (hηV : i (genericPoint C) ∈ V)
      (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L),
      IsIso δ ∧ CentralGenericLineSectionLift.closedGenericSection i L V hηV δ = σ ∧
      ∃ (hV : Nonempty V)
        (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)),
        ρ = @CentralGenericLineSectionLift.genericSection Y _ L V hV δ ∧ ρ ≠ 0 ∧
        modelLineNorm hb y hL (genericSectionAt L y.1.point hy ρ) = 1 := by
  obtain ⟨V,hηV,δ,hδ,hcentral,hV,ρ,hρ,hρne⟩ :=
    CentralGenericLineSectionLift.exists_generic_section_lift i L hL σ hσ
  let : IsIso δ := hδ
  let : Nonempty V := hV
  have hcV : center hb y ∈ V := hc.symm ▸ hηV
  let hpV := support_mem_of_center_mem hb y V hcV
  have htransport : genericSectionAt L y.1.point hy ρ = localSectionAt L V δ y.1.point hpV :=
    (congrArg (genericSectionAt L y.1.point hy) hρ).trans
      (genericSectionAt_localSectionAt L V δ y.1.point hy hpV)
  refine ⟨V,hηV,δ,hδ,hcentral,hV,ρ,hρ,hρne,?_⟩
  exact (congrArg (fun t : Γ(originalFibreModule L y.1.point, ⊤) =>
    modelLineNorm hb y hL t) htransport).trans
      (modelLineNorm_localGenerator hb y L hL V hcV δ)

/-- SAME original common q_C and given central σ internally produce SAME ambient ρ with genuine norm1. -/
theorem exists_prescribed_section_unit_norm {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper f] [IsDominant f]
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i]
    (x₀ : C) [IsNoetherianRing (Y.presheaf.stalk (i x₀))]
    (π₀ : Y.presheaf.stalk (i x₀)) (hπ₀ : Prime π₀)
    (hker₀ : RingHom.ker (i.stalkMap x₀).hom = Ideal.span {π₀})
    (hη : Polynomial.X ∈ (f (i (genericPoint C))).asIdeal)
    (L : Y.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj ((pullback i).obj L), ⊤))
    (hσ : σ ≠ 0) :
    ∃ y : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f,
      ∃ hy : y.1.point = genericPoint Y,
        center ProjBerk.gaussModelCoefficient_le_one y = i (genericPoint C) ∧
        ∃ (V : Y.Opens) (hηV : i (genericPoint C) ∈ V)
          (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L),
          IsIso δ ∧ CentralGenericLineSectionLift.closedGenericSection i L V hηV δ = σ ∧
          ∃ (hV : Nonempty V)
            (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)),
            ρ = @CentralGenericLineSectionLift.genericSection Y _ L V hV δ ∧ ρ ≠ 0 ∧
            modelLineNorm ProjBerk.gaussModelCoefficient_le_one y hL
              (genericSectionAt L y.1.point hy ρ) = 1 := by
  obtain ⟨y,hy,hcenter,_Hlocal⟩ :=
    GaussCommonVerticalPoints.exists_commonVerticalPoint (f := f) i x₀ π₀ hπ₀ hker₀ hη
  exact ⟨y,hy,hcenter,exists_prescribed_section_unit_norm_at
    ProjBerk.gaussModelCoefficient_le_one y hy i hcenter L hL σ hσ⟩

end EnvelopeProperty.GaussCentralLineNormalization
