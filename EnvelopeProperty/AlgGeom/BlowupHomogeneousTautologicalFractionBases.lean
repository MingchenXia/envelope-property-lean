import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalLocalBasis
import EnvelopeProperty.Alterations.Geometry.BlowupCartier

/-! # Actual specified-generator fraction charts for the original blowup

The specified original generators themselves give a native fraction-chart
open cover. Zero generators are removed because their actual Proj basic opens
are empty, including when the entire ideal is zero.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Algebra.ReesPresentation

universe u

namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine

variable {A : Type u} [CommRing A] {m : ℕ}

private theorem specifiedDegreeOne_adjoin (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) :
    Algebra.adjoin A (Set.range fun a => reesDegreeOne I (g a)
      (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan a)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  change (reesPolynomialEval I g
    (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan)).range = ⊤
  rw [AlgHom.range_eq_top]
  exact reesPolynomialMap_surjective I g
    (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan) hspan

private theorem specifiedAdjoin_zero {Q B : Type u} [CommRing Q] [CommRing B]
    [Algebra A B] [Algebra Q B] (s : Set B)
    (hgen : Algebra.adjoin A s = ⊤)
    (hcoeff : ∀ a : A, algebraMap A B a ∈ Algebra.adjoin Q s) :
    Algebra.adjoin Q s = ⊤ := by
  apply top_unique
  intro b htop
  clear htop
  have hb : b ∈ Algebra.adjoin A s := by rw [hgen]; trivial
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact Algebra.subset_adjoin hb
  | algebraMap a => exact hcoeff a
  | add b c _ _ hb hc => exact (Algebra.adjoin Q s).add_mem hb hc
  | mul b c _ _ hb hc => exact (Algebra.adjoin Q s).mul_mem hb hc

/-- The SAME original finite generator family covers its actual original Rees
Proj by its OWN actual degree-one basic opens. -/
theorem iSup_specifiedGeneratorChartOpen (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) :
    (⨆ a : Fin (m+1), affineBlowupChartOpen I (g a)
      (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan a)) = ⊤ := by
  let hmem : ∀ a : Fin (m+1), g a ∈ I :=
    Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan
  have hzero : Algebra.adjoin (reesGrading I 0)
      (Set.range fun a => reesDegreeOne I (g a) (hmem a)) = ⊤ :=
    specifiedAdjoin_zero (A := A) (Q := reesGrading I 0) (B := reesAlgebra I)
      (Set.range fun a => reesDegreeOne I (g a) (hmem a))
      (specifiedDegreeOne_adjoin I g hspan)
      (fun a => (Algebra.adjoin (reesGrading I 0)
        (Set.range fun b => reesDegreeOne I (g b) (hmem b))).algebraMap_mem (reesConstants I a))
  exact Proj.iSup_basicOpen_eq_top' (reesGrading I)
    (fun a => reesDegreeOne I (g a) (hmem a))
    (fun a => ⟨1, reesDegreeOne_mem I (g a) (hmem a)⟩) hzero

/-- The actual specified original NONZERO generators still cover. No nonzero
ideal hypothesis is needed: the zero-ideal blowup itself is empty. -/
theorem iSup_specifiedNonzeroGeneratorChartOpen (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) :
    (⨆ a : {a : Fin (m+1) // g a ≠ 0}, affineBlowupChartOpen I (g a.val)
      (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan a.val)) = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp ((iSup_specifiedGeneratorChartOpen I g hspan).ge hx)
  have ha0 : g a ≠ 0 := by
    intro h
    have hz : reesDegreeOne I (g a)
        (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan a) = 0 := by
      apply Subtype.ext
      simp [reesDegreeOne, h]
    change x ∈ Proj.basicOpen (reesGrading I) (reesDegreeOne I (g a)
      (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan a)) at ha
    rw [hz, Proj.basicOpen_zero] at ha
    exact ha
  exact Opens.mem_iSup.mpr ⟨⟨a, ha0⟩, ha⟩

variable [IsDomain A]

/-- The SAME specified original generator family yields a genuine scheme open
cover by its actual native fraction-chart immersions. -/
def specifiedGeneratorFractionOpenCover (I : Ideal A) (g : Fin (m+1) → A)
    (hspan : Ideal.span (Set.range g) = I) : (affineBlowup I).OpenCover.{0} :=
  Scheme.Cover.mkOfCovers
    {a : Fin (m+1) // g a ≠ 0}
    (fun a => Spec (CommRingCat.of (affineBlowupFractionChart I (g a.val))))
    (fun a => affineBlowupChartInclusion I (g a.val)
      (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan a.val) a.property)
    (by
      intro x
      have hx : x ∈ (⊤ : (affineBlowup I).Opens) := trivial
      rw [← iSup_specifiedNonzeroGeneratorChartOpen I g hspan] at hx
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
      rw [← affineBlowupFractionChartInclusion_opensRange I (g a.val)
        (Alterations.Geometry.BlowupProjectiveEmbedding.generator_mem I g hspan a.val)
        a.property] at ha
      exact ⟨a, ha⟩)

/-- The ENTIRE original ideal on the actual native fraction chart is the
principal ideal generated by the original denominator, with no ideal-matching
certificate supplied. -/
theorem originalFractionChart_comap {X : Scheme.{u}} (D : X.IdealSheafData)
    (U : X.affineOpens) [IsDomain Γ(X, U)] (g : Γ(X, U))
    (hg : g ∈ D.ideal U) (hg0 : g ≠ 0) :
    D.comap ((affineBlowupChartInclusion (D.ideal U) g hg hg0 ≫
        affineBlowupStructure (D.ideal U)) ≫ U.2.fromSpec) =
      Alterations.Geometry.SpecIdealSheaf.specIdealSheaf
        (affineBlowupFractionChart (D.ideal U) g)
        (Ideal.span {algebraMap Γ(X, U) (affineBlowupFractionChart (D.ideal U) g) g}) := by
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    Alterations.Geometry.BlowupCartier.comap_fromSpec]
  exact affineBlowupExceptionalIdeal_comap_chart (D.ideal U) g hg hg0

private theorem pulledForm_specMap_fromSpec
    {R S : Type u} [CommRing R] [CommRing S] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n) (U : X.affineOpens)
    (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ Alterations.Geometry.ProjectiveIdeal.nativeCoordinateOpen i)
    (φ : Γ(X, U) →+* S) (F : MvPolynomial (Fin (n+1)) R)
    (h : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤
      ((Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) ≫ j) ⁻¹ᵁ
        Alterations.Geometry.ProjectiveIdeal.nativeCoordinateOpen i) :
    Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm
        ((Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) ≫ j)
        ⟨⊤, isAffineOpen_top _⟩ i h F =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
        (φ (Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm j U i hi F)) := by
  let v := Spec.map (CommRingCat.ofHom φ)
  let f := v ≫ U.2.fromSpec
  let V := Alterations.Geometry.ProjectiveIdeal.nativeCoordinateOpen (R := R) i
  have hp : (⊤ : (Spec Γ(X, U)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by
    rw [U.2.fromSpec_preimage_self]
  have hf : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ f ⁻¹ᵁ U.1 := by
    dsimp only [f]
    rw [Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
    exact le_rfl
  have ha : U.2.fromSpec.appLE U.1 ⊤ hp = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, U.2.fromSpec_app_self]
    simp only [Category.assoc, ← Functor.map_comp]
    simp
  have hv : v.appLE ⊤ ⊤ (by simp) = v.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  have hφ : f.appLE U.1 ⊤ hf = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ v.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE v U.2.fromSpec U.1 ⊤ ⊤ hp (by simp), ha, hv]
  have hc := Scheme.Hom.appLE_comp_appLE f j V U.1 ⊤ hi hf
  change ((f ≫ j).appLE V ⊤ h).hom
      (Alterations.Geometry.ProjectiveIdeal.nativeFormSection i F) = _
  rw [← hc]
  change (f.appLE U.1 ⊤ hf).hom
      (Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm j U i hi F) = _
  rw [hφ]
  exact congrArg (fun q : Γ(X, U) ⟶ Γ(Spec (CommRingCat.of S), ⊤) =>
    q.hom (Alterations.Geometry.BlowupProjectiveEmbedding.pulledForm j U i hi F))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm

open Alterations.Geometry.ProjectiveIdeal
open Alterations.Geometry.BlowupProjectiveEmbedding
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem pulledForm_mem_originalIdeal
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : MvPolynomial (Fin (n+1)) R) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) :
    pulledForm j U i hi F ∈
      ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).ideal U := by
  let v : J.toIdeal → MvPolynomial (Fin (n+1)) R := Subtype.val
  have hspan : Ideal.span (Set.range v) = J.toIdeal := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact a.property
    · intro a ha
      exact Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩
  have hm : pulledForm j U i hi F ∈
      Ideal.span (Set.range (fun a : J.toIdeal => pulledForm j U i hi (v a))) :=
    Ideal.subset_span ⟨⟨F, hFJ⟩, rfl⟩
  rwa [pulledForm_span j U J v hspan i hi] at hm

private theorem isIso_of_pullbackSectionHom_along_iso {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsIso f] {M : X.Modules}
    (β : Scheme.Modules.unitObj X ⟶ M)
    (hβ : IsIso (SchemeLineSectionEvaluation.pullbackSectionHom f β)) : IsIso β := by
  let P := Scheme.Modules.pullback f
  let Q := Scheme.Modules.pullback (inv f)
  have hP : IsIso (P.map β) := by
    have h : IsIso ((Scheme.Modules.pullbackUnitIso f).inv ≫ P.map β) := hβ
    let := h
    exact IsIso.of_isIso_comp_left (Scheme.Modules.pullbackUnitIso f).inv (P.map β)
  let := hP
  let E : P ⋙ Q ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp (inv f) f ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId X
  have hn : Q.map (P.map β) ≫ E.hom.app M =
      E.hom.app (Scheme.Modules.unitObj X) ≫ β := E.hom.naturality β
  have heq : β = E.inv.app (Scheme.Modules.unitObj X) ≫ Q.map (P.map β) ≫ E.hom.app M := by
    calc
      β = (E.inv.app (Scheme.Modules.unitObj X) ≫ E.hom.app (Scheme.Modules.unitObj X)) ≫ β := by
        rw [Iso.inv_hom_id_app, Category.id_comp]
      _ = E.inv.app (Scheme.Modules.unitObj X) ≫ (E.hom.app (Scheme.Modules.unitObj X) ≫ β) :=
        Category.assoc _ _ _
      _ = E.inv.app (Scheme.Modules.unitObj X) ≫ (Q.map (P.map β) ≫ E.hom.app M) :=
        congrArg (fun k => E.inv.app (Scheme.Modules.unitObj X) ≫ k) hn.symm
  rw [heq]
  infer_instance

private theorem pulledForm_congr {R : Type u} [CommRing R] {n : ℕ} {Z : Scheme.{u}}
    (f g : Z ⟶ Alterations.projectiveSpace R n) (hfg : f = g)
    (T : Z.affineOpens) (i : Fin (n+1))
    (hf : T.1 ≤ f ⁻¹ᵁ nativeCoordinateOpen i) (hg : T.1 ≤ g ⁻¹ᵁ nativeCoordinateOpen i)
    (F : MvPolynomial (Fin (n+1)) R) :
    pulledForm f T i hf F = pulledForm g T i hg F := by
  cases hfg
  rfl

private theorem spectrumPrincipalIdeal_top (S : Type u) [CommRing S] (t : S) :
    (Alterations.Geometry.SpecIdealSheaf.specIdealSheaf S (Ideal.span {t})).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t} := by
  rw [Alterations.Geometry.SpecIdealSheaf.specIdealSheaf_ideal_top,
    Ideal.map_span, Set.image_singleton]

private theorem spectrumFractionGenerator_regular {C : Type u} [CommRing C] [IsDomain C]
    (I : Ideal C) (g : C) (hg0 : g ≠ 0) :
    (Scheme.ΓSpecIso (CommRingCat.of (affineBlowupFractionChart I g))).inv.hom
        (algebraMap C (affineBlowupFractionChart I g) g) ∈
      nonZeroDivisors Γ(Spec (CommRingCat.of (affineBlowupFractionChart I g)), ⊤) :=
  isRegular_iff_mem_nonZeroDivisors.mp
    (Alterations.Geometry.CartierLocality.isRegular_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of (affineBlowupFractionChart I g))).symm.commRingCatIsoToRingEquiv
      (affineBlowupFractionChart_generator_isRegular I g hg0))

private theorem originalFractionChart_regular_principal
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : MvPolynomial (Fin (n+1)) R) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) [IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi F ≠ 0) :
    let D := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g := pulledForm j U i hi F
    let hg : g ∈ D.ideal U := pulledForm_mem_originalIdeal j J F hFJ U i hi
    let S := affineBlowupFractionChart (D.ideal U) g
    let f := (affineBlowupChartInclusion (D.ideal U) g hg hg0 ≫ affineBlowupStructure (D.ideal U)) ≫
      U.2.fromSpec
    let T : (Spec (CommRingCat.of S)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
    ∃ hcoord : T.1 ≤ (f ≫ j) ⁻¹ᵁ nativeCoordinateOpen i,
      pulledForm (f ≫ j) T i hcoord F ∈ nonZeroDivisors Γ(Spec (CommRingCat.of S), ⊤) ∧
      (D.comap f).ideal T = Ideal.span {pulledForm (f ≫ j) T i hcoord F} := by
  let D := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g := pulledForm j U i hi F
  let hg : g ∈ D.ideal U := pulledForm_mem_originalIdeal j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let hU : IsAffineOpen U.1 := U.2
  let b : Spec Γ(X, U) ⟶ X := hU.fromSpec
  let f : Spec (CommRingCat.of S) ⟶ X :=
    (affineBlowupChartInclusion (D.ideal U) g hg hg0 ≫ affineBlowupStructure (D.ideal U)) ≫
      b
  let T : (Spec (CommRingCat.of S)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  change ∃ hcoord : T.1 ≤ (f ≫ j) ⁻¹ᵁ nativeCoordinateOpen i,
    pulledForm (f ≫ j) T i hcoord F ∈ nonZeroDivisors Γ(Spec (CommRingCat.of S), ⊤) ∧
    (D.comap f).ideal T = Ideal.span {pulledForm (f ≫ j) T i hcoord F}
  have hf : f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫ b := by
    dsimp only [f]
    rw [affineBlowupChartInclusion_structure]
  have hfU : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ f ⁻¹ᵁ U.1 := by
    rw [hf, Scheme.Hom.comp_preimage]
    dsimp only [b]
    rw [hU.fromSpec_preimage_self]
    exact le_rfl
  have hcoord : T.1 ≤ (f ≫ j) ⁻¹ᵁ nativeCoordinateOpen i := by
    change (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ f ⁻¹ᵁ j ⁻¹ᵁ nativeCoordinateOpen i
    exact hfU.trans (f.preimage_mono hi)
  have hcoord' : T.1 ≤
      ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫ b) ≫ j) ⁻¹ᵁ nativeCoordinateOpen i := by
    rw [← hf]
    exact hcoord
  have hcoeff : pulledForm (f ≫ j) T i hcoord F =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap Γ(X, U) S g) := by
    exact (pulledForm_congr (f ≫ j) _ (congrArg (fun k => k ≫ j) hf) T i hcoord hcoord' F).trans
      (pulledForm_specMap_fromSpec j U i hi (algebraMap Γ(X, U) S) F hcoord')
  have hKnative := originalFractionChart_comap D U g hg hg0
  change D.comap f = _ at hKnative
  have hK : (D.comap f).ideal T =
      Ideal.span {pulledForm (f ≫ j) T i hcoord F} := by
    exact (congrArg (fun K : (Spec (CommRingCat.of S)).IdealSheafData => K.ideal T) hKnative).trans
      ((spectrumPrincipalIdeal_top S (algebraMap Γ(X, U) S g)).trans
        (congrArg (fun c : Γ(Spec (CommRingCat.of S), ⊤) => Ideal.span {c}) hcoeff.symm))
  have hregular : pulledForm (f ≫ j) T i hcoord F ∈ nonZeroDivisors Γ(Spec (CommRingCat.of S), ⊤) := by
    exact Eq.mpr (congrArg
      (fun c : Γ(Spec (CommRingCat.of S), ⊤) => c ∈ nonZeroDivisors Γ(Spec (CommRingCat.of S), ⊤))
      hcoeff) (spectrumFractionGenerator_regular (D.ideal U) g hg0)
  exact ⟨hcoord, hregular, hK⟩

/-- On the ACTUAL native fraction chart of the original pulled form, that
SAME original lifted form is a genuine basis. The original chart construction
internally supplies both the regular coefficient and the full principal ideal;
neither old `hg` nor old `hK` is an incoming certificate. -/
theorem liftedFormSection_isIso_on_originalFractionChart
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) [IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi F ≠ 0) :
    let D := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g := pulledForm j U i hi F
    let hg : g ∈ D.ideal U := pulledForm_mem_originalIdeal j J F hFJ U i hi
    IsIso (liftedFormSection
      ((affineBlowupChartInclusion (D.ideal U) g hg hg0 ≫ affineBlowupStructure (D.ideal U)) ≫
        U.2.fromSpec) j J d F hF hFJ) := by
  let D := (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g := pulledForm j U i hi F
  let hg : g ∈ D.ideal U := pulledForm_mem_originalIdeal j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let f : Spec (CommRingCat.of S) ⟶ X :=
    (affineBlowupChartInclusion (D.ideal U) g hg hg0 ≫ affineBlowupStructure (D.ideal U)) ≫ U.2.fromSpec
  let T : (Spec (CommRingCat.of S)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  change IsIso (liftedFormSection f j J d F hF hFJ)
  obtain ⟨hcoord, hregular, hK⟩ := originalFractionChart_regular_principal j J F hFJ U i hi hg0
  have hb := liftedFormSection_isIso_of_regular_coefficient f j J d F hF hFJ T i hcoord hregular hK
  let hT : IsAffineOpen T.1 := T.2
  let σ := hT.fromSpec
  let : IsIso σ := by
    dsimp only [σ, hT, T]
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  exact isIso_of_pullbackSectionHom_along_iso σ (liftedFormSection f j J d F hF hFJ) hb

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
