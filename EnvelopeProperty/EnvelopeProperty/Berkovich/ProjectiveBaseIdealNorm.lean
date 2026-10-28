import EnvelopeProperty.AlgGeom.InvertibleBaseIdealFrameCoefficients
import EnvelopeProperty.Berkovich.SchemeModelIdeals
import EnvelopeProperty.Berkovich.SchemeLineLocalSectionEvaluation
import EnvelopeProperty.AlgGeom.IntegralLineImageModules

/-! # A single actual global family computes the whole base-ideal model norm -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
open Scheme.Modules InvertibleSheafBaseIdeal InvertibleBaseIdealFrameCoefficients

private theorem frameCoefficient_eq_local {X : Scheme.{u}} (L : X.Modules)
    (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (s : Γ(L, ⊤)) :
    frameCoefficient L U e s = ModularCurves.localTrivializationCoefficient L U
      (ModularCurves.restrictTrivializationOfOverIso L U.1 e) s := by
  have h := ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso
    L U (ModularCurves.restrictTrivializationOfOverIso L U.1 e) s
  rw [ModularCurves.overTrivializationOfRestrictTrivializationOfOverIso] at h
  have he : frameCoefficient L U e s =
      ModularCurves.overTrivializationCoefficient L U.1 e s := by
    change e.hom.val.app (.op (Over.mk (𝟙 U.1)))
        ((1 : Γ(X, U)) • (show Γ(L, U.1) from
          L.presheaf.map (.op (homOfLE le_top)) s)) = _
    rw [one_smul]
    rfl
  exact he.trans h

/-- The TRUE model norm of the SAME original global section is its actual
original affine-frame coefficient evaluation. The whole local scalar equation
is DERIVED from the native section map and native frame equivalences. -/
theorem modelLineNorm_fibreSection_eq_frameCoefficient {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (L : X.Modules) (hL : IsInvertible L) (U : X.affineOpens)
    (hc : center hb y ∈ U.1)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) (s : Γ(L, ⊤)) :
    modelLineNorm hb y hL (fibreSection y (SchemeModuleGlobalSections.sectionHom L s)) =
      SchemeValuedPoint.eval y.1 U.1 (support_mem_of_center_mem hb y U.1 hc)
        (frameCoefficient L U e s) := by
  let E := ModularCurves.restrictTrivializationOfOverIso L U.1 e
  have hr := SchemeLineSectionEvaluation.sectionHom_localScalar L U E s
  have h := modelLineNorm_fibreSection_eq_localEval hb y hL U.1 hc
    (pullbackIsoOfRestrictIso L U.1 E) (SchemeModuleGlobalSections.sectionHom L s)
    (ModularCurves.localTrivializationCoefficient L U E s) hr
  exact h.trans (congrArg
    (SchemeValuedPoint.eval y.1 U.1 (support_mem_of_center_mem hb y U.1 hc))
      (frameCoefficient_eq_local L U e s).symm)

/-- ONE finite family of actual original global sections computes the genuine
intrinsic whole base-ideal norm on EVERY original point and EVERY original
center frame. Projectivity derives properness and the true center internally. -/
theorem exists_baseIdeal_norm_global_coefficients {R : Type u} [CommRing R]
    [IsNoetherianRing R] {v : Valuation R ℝ≥0} {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) (hb : ∀ r, v r ≤ 1) :
    have : IsProper f := hf.isProper
    ∃ G : Finset Γ(L, ⊤), ∀ (y : RelativeSchemeValuedPoint v f)
      (U : X.affineOpens) (hc : center hb y ∈ U.1)
      (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)),
      modelIdealNorm (baseIdeal hL) hb y =
        ((G.sup fun s => SchemeValuedPoint.eval y.1 U.1
          (support_mem_of_center_mem hb y U.1 hc) (frameCoefficient L U e s) : ℝ≥0) :
          ℝ≥0∞) := by
  have : IsProper f := hf.isProper
  classical
  obtain ⟨G, hG⟩ := exists_finite_global_frame_coefficients f hf L hL
  refine ⟨G, fun y U hc e => ?_⟩
  let c := frameCoefficient L U e
  have hS : (baseIdeal hL).ideal U = Ideal.span (↑(G.image c) : Set Γ(X, U)) := by
    simpa only [Finset.coe_image] using hG U e
  have hn := modelIdealNorm_eq_generators (baseIdeal hL) hb y U hc (G.image c) hS
  have hi : (G.image c).sup (fun a => SchemeValuedPoint.eval y.1 U.1
      (support_mem_of_center_mem hb y U.1 hc) a) =
    G.sup (fun s => SchemeValuedPoint.eval y.1 U.1
      (support_mem_of_center_mem hb y U.1 hc) (c s)) := Finset.sup_image G c (fun a => SchemeValuedPoint.eval y.1 U.1
      (support_mem_of_center_mem hb y U.1 hc) a)
  exact hn.trans (congrArg (fun q : ℝ≥0 => (q : ℝ≥0∞)) hi)

/-- ONE original finite global family computes the intrinsic whole base-ideal
norm as the maximum of TRUE original generic-fibre section norms, at EVERY
original point. No frame, chosen generators or norm equality is a premise. -/
theorem exists_baseIdeal_norm_global_sections {R : Type u} [CommRing R]
    [IsNoetherianRing R] {v : Valuation R ℝ≥0} {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) (hb : ∀ r, v r ≤ 1) :
    have : IsProper f := hf.isProper
    ∃ G : Finset Γ(L, ⊤), ∀ y : RelativeSchemeValuedPoint v f,
      modelIdealNorm (baseIdeal hL) hb y =
        ((G.sup fun s => modelLineNorm hb y hL
          (fibreSection y (SchemeModuleGlobalSections.sectionHom L s)) : ℝ≥0) : ℝ≥0∞) := by
  have : IsProper f := hf.isProper
  obtain ⟨G, hG⟩ := exists_baseIdeal_norm_global_coefficients hf L hL hb
  refine ⟨G, fun y => ?_⟩
  obtain ⟨U, hc, ⟨e⟩⟩ := IntegralLineImageModules.exists_affine_frame L hL (center hb y)
  have h := hG y U hc e
  have he : G.sup (fun s => SchemeValuedPoint.eval y.1 U.1
      (support_mem_of_center_mem hb y U.1 hc) (frameCoefficient L U e s)) =
    G.sup (fun s => modelLineNorm hb y hL
      (fibreSection y (SchemeModuleGlobalSections.sectionHom L s))) := by
    apply Finset.sup_congr rfl
    intro s _
    exact (modelLineNorm_fibreSection_eq_frameCoefficient hb y L hL U hc e s).symm
  exact h.trans (congrArg (fun q : ℝ≥0 => (q : ℝ≥0∞)) he)

/-- EVERY actual original global section is bounded by the intrinsic norm of
its WHOLE actual base ideal, at every original point of a proper model. -/
theorem globalSection_norm_le_baseIdealNorm {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)
    (L : X.Modules) (hL : IsInvertible L) (s : Γ(L, ⊤)) :
    (modelLineNorm hb y hL (fibreSection y (SchemeModuleGlobalSections.sectionHom L s)) :
      ℝ≥0∞) ≤ modelIdealNorm (baseIdeal hL) hb y := by
  obtain ⟨U, hc, ⟨e⟩⟩ := IntegralLineImageModules.exists_affine_frame L hL (center hb y)
  have hm : frameCoefficient L U e s ∈ (baseIdeal hL).ideal U := by
    rw [baseIdeal_ideal_of_frame hL U e]
    exact Ideal.mem_iSup_of_mem (R := Γ(X, U)) s
      (Ideal.mem_span_singleton_self (frameCoefficient L U e s))
  have hv := Spectrum.val_le_idealNorm ((baseIdeal hL).ideal U)
    (sectionSpectrum y U.1 (support_mem_of_center_mem hb y U.1 hc)).1 hm
  have hn := modelIdealNorm_eq_affine (baseIdeal hL) hb y U hc
  have he := congrArg (fun q : ℝ≥0 => (q : ℝ≥0∞))
    (modelLineNorm_fibreSection_eq_frameCoefficient hb y L hL U hc e s)
  exact he.le.trans (hv.trans_eq hn.symm)

/-- The WHOLE original all-global-section base ideal has intrinsic norm EXACTLY
the supremum of the TRUE model norms of ALL original global sections. -/
theorem baseIdeal_norm_eq_iSup_global_sections {R : Type u} [CommRing R]
    [IsNoetherianRing R] {v : Valuation R ℝ≥0} {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) (hb : ∀ r, v r ≤ 1) :
    have : IsProper f := hf.isProper
    ∀ y : RelativeSchemeValuedPoint v f, modelIdealNorm (baseIdeal hL) hb y =
      ⨆ s : Γ(L, ⊤), (modelLineNorm hb y hL
        (fibreSection y (SchemeModuleGlobalSections.sectionHom L s)) : ℝ≥0∞) := by
  have : IsProper f := hf.isProper
  dsimp only
  intro y
  apply le_antisymm
  · obtain ⟨G, hG⟩ := exists_baseIdeal_norm_global_sections hf L hL hb
    rw [hG y, ENNReal.coe_finset_sup]
    exact Finset.sup_le fun s _ => le_iSup (fun t : Γ(L, ⊤) =>
      (modelLineNorm hb y hL (fibreSection y (SchemeModuleGlobalSections.sectionHom L t)) :
        ℝ≥0∞)) s
  · exact iSup_le fun s => globalSection_norm_le_baseIdealNorm hb y L hL s

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
