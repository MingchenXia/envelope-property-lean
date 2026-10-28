import EnvelopeProperty.Char0.RoundedCanonicalTargetOpen
import EnvelopeProperty.Char0.RoundedCanonicalKernelBaseChange
import EnvelopeProperty.Char0.AffineOpenChartMaps
import EnvelopeProperty.AlgGeom.PullbackUnitSectionKernel

/-! # The whole original geometric pushed kernel on actual principal source charts

The original source ring may be reducible. Actual flat H0 base change,
source-open quotient transport and target-open exterior differential
invariance compare the same categorical pulled model and original rounded
quotient, with every original coefficient retained.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Char0
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SourceOpenPushedKernel
variable {k : Type u} [Field k] (A S : CommRingCat.{u})
  [Algebra k A] [Algebra k S] [Algebra A S] [IsScalarTower k A S]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S)))]

/-- Actual original coordinates restrict to actual etale coordinates on the SAME open base. -/
theorem etale_coordinates {n : ℕ} (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) (fun i => algebraMap A S (z i))).toRingHom.Etale := by
  apply etale_aeval_algebraMap z hz
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap A S))).mp inferInstance

omit [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S)))] in
/-- The literal original coefficient triangle is retained by the actual open base. -/
theorem structuralMap :
    Spec.map (CommRingCat.ofHom (algebraMap A S)) ≫ affineStructuralMap k A =
      affineStructuralMap k S := by
  unfold affineStructuralMap
  rw [← Spec.map_comp]
  congr 2
  ext c
  exact (IsScalarTower.algebraMap_apply k A S c).symm

variable {Y : Scheme.{u}} (g : Y ⟶ Spec A)

/-- Actual pure smoothness on the SAME categorical pulled original model. -/
theorem model_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)] :
    SmoothOfRelativeDimension n
      (FlatGlobalSections.structureMap (S := S) g ≫ affineStructuralMap k S) := by
  rw [← structuralMap A S, ← Category.assoc, ← pullback.condition, Category.assoc]
  exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp
    (f := FlatGlobalSections.firstProjection (S := S) g) (n := 0) (m := n)
      (g ≫ affineStructuralMap k A))

omit [Algebra k S] [IsScalarTower k A S] in
/-- SNC is derived for the literal pulled original ideal, without a matching certificate. -/
theorem model_snc [CharZero k] (n : ℕ)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    (J.comap (FlatGlobalSections.firstProjection (S := S) g)).IsIdealOfSncDivisor := by
  let : Smooth (g ≫ affineStructuralMap k A) := SmoothOfRelativeDimension.smooth n _
  exact hJ.comap_of_smooth (g ≫ affineStructuralMap k A)
    (FlatGlobalSections.firstProjection (S := S) g)

end SourceOpenPushedKernel

namespace RoundedCanonicalModule

private theorem pulledSectionKernel_mem_iff
    (S : CommRingCat.{u}) {Y W : Scheme.{u}} (g : W ⟶ Spec S) (c : W ⟶ Y)
    (Q : Y.Modules) (δ : Scheme.Modules.unitObj Y ⟶ Q) (s : S) :
    s ∈ FlatSectionKernel.sectionKernel g ((Scheme.Modules.pullback c).obj Q)
      (Scheme.Modules.affinePullbackUnitTop c Q
        (δ.val.app (.op ⊤) (1 : Γ(Y, ⊤)))) ↔
      ((Scheme.Modules.pullbackUnitIso c).inv ≫ (Scheme.Modules.pullback c).map δ).val.app
        (.op ⊤) (ProperBirationalSections.coefficientMap g s) = 0 := by
  rw [FlatSectionKernel.mem_sectionKernel_iff,
    PullbackUnitSectionKernel.affinePullbackUnitTop_sectionAtOne c δ]
  let α := (Scheme.Modules.pullbackUnitIso c).inv ≫ (Scheme.Modules.pullback c).map δ
  have h := (α.val.app (.op ⊤)).hom.map_smul
    (ProperBirationalSections.coefficientMap g s) (1 : Γ(W, ⊤))
  simpa only [smul_eq_mul, mul_one] using
    (Iff.of_eq (congrArg (fun v => v = 0) h)).symm

private theorem pulledQuotient_apply_eq_zero_iff_openSquare
    {k : Type u} [Field k] [CharZero k] {X X' Y W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of k))
    (e : X' ⟶ X) [IsOpenImmersion e] (g : Y ⟶ X)
    (g' : W ⟶ X') (c : W ⟶ Y) [IsOpenImmersion c]
    (hstruct : e ≫ f = f') (htriangle : c ≫ g = g' ≫ e)
    (n : ℕ) [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n f']
    [SmoothOfRelativeDimension n (g ≫ f)] [SmoothOfRelativeDimension n (g' ≫ f')]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    letI : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
    ∀ b : Γ(W, ⊤),
      (AffineOpenGlobalRoundedKernel.pulledQuotientDifferentialSection
        f g n c J hJ q).val.app (.op ⊤) b = 0 ↔
      (quotientDifferentialSection f' g' n (J.comap c)
        (hJ.comap_of_smooth (g ≫ f) c) q).val.app (.op ⊤) b = 0 := by
  subst f'
  let : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
  let : SmoothOfRelativeDimension n ((c ≫ g) ≫ f) := by
    rw [Category.assoc]
    exact (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp
      (f := c) (n := 0) (m := n) (g ≫ f))
  let : SmoothOfRelativeDimension n ((g' ≫ e) ≫ f) := htriangle ▸ inferInstance
  let JC := J.comap c
  let hJC := hJ.comap_of_smooth (g ≫ f) c
  intro b
  have hSource :
      (quotientDifferentialSection f (c ≫ g) n JC hJC q).val.app (.op ⊤) b = 0 ↔
      (quotientDifferentialSection f (g' ≫ e) n JC hJC q).val.app (.op ⊤) b = 0 :=
    Iff.of_eq (congrArg (fun r =>
      (quotientDifferentialSection f r n JC hJC q).val.app (.op ⊤) b = 0) htriangle)
  exact (AffineOpenGlobalRoundedKernel.pulledQuotientDifferentialSection_apply_eq_zero_iff_openComposite
    f g n c J hJ q b).trans (hSource.trans
      (quotientDifferentialSection_apply_eq_zero_iff_targetOpen f e g' n JC hJC q b))

private theorem pulledQuotient_sectionKernel_eq_openSquare
    {k : Type u} [Field k] [CharZero k] (S : CommRingCat.{u}) [Algebra k S]
    {X Y W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ X)
    (g' : W ⟶ Spec S) (c : W ⟶ Y) [IsOpenImmersion c]
    (e : Spec S ⟶ X) [IsOpenImmersion e]
    (hstruct : e ≫ f = affineStructuralMap k S) (htriangle : c ≫ g = g' ≫ e)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension n (g ≫ f)]
    [SmoothOfRelativeDimension n (g' ≫ affineStructuralMap k S)]
    (z : Fin n → S) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    letI : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
    let Q := quotient f g n J hJ q
    let δ := quotientDifferentialSection f g n J hJ q
    FlatSectionKernel.sectionKernel g' ((Scheme.Modules.pullback c).obj Q)
      (Scheme.Modules.affinePullbackUnitTop c Q
        (δ.val.app (.op ⊤) (1 : Γ(Y, ⊤)))) =
      specPushedQuotientKernel S g' z hz (J.comap c)
        (hJ.comap_of_smooth (g ≫ f) c) q := by
  let : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n (g ≫ f)
  intro Q δ
  let : SmoothOfRelativeDimension n (affineStructuralMap k S) :=
    smoothOfRelativeDimension_of_etale_coordinates z hz
  have hgeom := pulledQuotient_apply_eq_zero_iff_openSquare f (affineStructuralMap k S)
    e g g' c hstruct htriangle n J hJ q
  ext s
  exact (pulledSectionKernel_mem_iff S g' c Q δ s).trans
    ((hgeom (ProperBirationalSections.coefficientMap g' s)).trans
      (mem_specPushedQuotientKernel_iff S g' z hz (J.comap c)
        (hJ.comap_of_smooth (g ≫ f) c) q s).symm)

/-- The WHOLE original pushed quotient-kernel extension equals the intrinsic
kernel on the SAME actual pulled model over an actual flat open affine base.
The original coefficient ring and its open may be reducible. -/
theorem specPushedQuotientKernel_openBase
    {k : Type u} [Field k] [CharZero k] (A S : CommRingCat.{u})
    [Algebra k A] [Algebra k S] [Algebra A S] [IsScalarTower k A S]
    [Module.Flat A S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S)))]
    {Y : Scheme.{u}} (g : Y ⟶ Spec A) [CompactSpace Y] [Y.IsSeparated] {n : ℕ}
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (specPushedQuotientKernel A g z hz J hJ q).map (algebraMap A S) =
      specPushedQuotientKernel S (FlatGlobalSections.structureMap (S := S) g)
        (fun i => algebraMap A S (z i)) (SourceOpenPushedKernel.etale_coordinates A S z hz)
        (J.comap (FlatGlobalSections.firstProjection (S := S) g))
        (SourceOpenPushedKernel.model_snc (k := k) A S g n J hJ) q := by
  let f := affineStructuralMap k A
  let fS := affineStructuralMap k S
  let e := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let p := FlatGlobalSections.firstProjection (S := S) g
  let gS := FlatGlobalSections.structureMap (S := S) g
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : SmoothOfRelativeDimension n (gS ≫ fS) :=
    SourceOpenPushedKernel.model_smoothOfRelativeDimension A S g n
  let : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth n _
  exact (map_specPushedQuotientKernel_eq (S := S) A g z hz J hJ q).trans
    (pulledQuotient_sectionKernel_eq_openSquare S f g gS p e
      (SourceOpenPushedKernel.structuralMap A S) pullback.condition n
      (fun i => algebraMap A S (z i)) (SourceOpenPushedKernel.etale_coordinates A S z hz)
      J hJ q)

/-- Every literal principal localization has the whole original geometric
kernel restriction formula on the SAME actual categorical pulled model. -/
theorem specPushedQuotientKernel_away
    {k : Type u} [Field k] [CharZero k] (A : CommRingCat.{u}) [Algebra k A]
    {Y : Scheme.{u}} (g : Y ⟶ Spec A) [CompactSpace Y] [Y.IsSeparated] {n : ℕ}
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : A) :
    (specPushedQuotientKernel A g z hz J hJ q).map (algebraMap A (Localization.Away a)) =
      specPushedQuotientKernel (.of (Localization.Away a))
        (FlatGlobalSections.structureMap (S := Localization.Away a) g)
        (fun i => algebraMap A (Localization.Away a) (z i))
        (SourceOpenPushedKernel.etale_coordinates A (.of (Localization.Away a)) z hz)
        (J.comap (FlatGlobalSections.firstProjection (S := Localization.Away a) g))
        (SourceOpenPushedKernel.model_snc (k := k) A (.of (Localization.Away a)) g n J hJ) q :=
  specPushedQuotientKernel_openBase A (.of (Localization.Away a)) g z hz J hJ q

end RoundedCanonicalModule
end EnvelopeProperty.Char0
