/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.GlobalReesCover
import Hironaka.Resolution.Algebraic.Kol07.IsoRestrict
import Hironaka.Scheme.BlowUpSequence.ConcatPullback

/-!
# Nonempty isomorphism opens in actual blowup sequences

These lemmas transport actual isomorphisms over nonempty opens through the
chart pullbacks used to construct finite Rees trees.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {X Y Z : Scheme.{u}}

/-- An actual inverse over a nonempty open produces an actual source point. -/
theorem nonempty_of_isIso_restrict (f : X ⟶ Y) (U : Y.Opens)
    (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] : Nonempty X := by
  obtain ⟨y, hy⟩ := hU
  exact ⟨((inv (f ∣_ U)) ⟨y, hy⟩).1⟩

/-- Cancel the actual isomorphism on the right after restricting a composite. -/
theorem isIso_restrict_cancel_right (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    [IsIso (g ∣_ U)] [IsIso ((f ≫ g) ∣_ U)] : IsIso (f ∣_ g ⁻¹ᵁ U) := by
  have h : IsIso ((f ∣_ g ⁻¹ᵁ U) ≫ (g ∣_ U)) := by
    have hcomp : IsIso ((f ≫ g) ∣_ U) := inferInstance
    rw [morphismRestrict_comp] at hcomp
    exact hcomp
  exact IsIso.of_isIso_comp_right (f ∣_ g ⁻¹ᵁ U) (g ∣_ U)

/-- An actual cartesian square transports an isomorphism open by inverse image. -/
theorem isIso_restrict_of_isPullback {P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {h : Y ⟶ Z} (p : IsPullback a b f h) (U : Z.Opens)
    [IsIso (f ∣_ U)] : IsIso (b ∣_ h ⁻¹ᵁ U) := by
  have outer : IsPullback ((b ⁻¹ᵁ h ⁻¹ᵁ U).ι ≫ a) (b ∣_ h ⁻¹ᵁ U)
      f ((h ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact (isPullback_morphismRestrict b (h ⁻¹ᵁ U)).flip.paste_horiz p
  exact property_of_isPullback (MorphismProperty.isomorphisms Scheme)
    (IsPullback.of_right' outer (isPullback_morphismRestrict f U).flip).flip inferInstance

/-- An injective map of rings induces an actual spectrum map with dense image. -/
theorem denseRange_specMap_of_injective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    DenseRange (Spec.map (CommRingCat.ofHom f)) := by
  change DenseRange (PrimeSpectrum.comap f)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
  intro x hx
  have hx0 : x = 0 := hf (hx.trans (map_zero f).symm)
  simpa only [hx0] using (Ideal.zero_mem (nilradical R))

/-- The actual last-stage lift is the cartesian base change of the actual composite. -/
theorem isPullback_pullbackLastHom (S : Scheme.BlowUpSequence X) (h : Y ⟶ X) [Flat h] :
    IsPullback (S.pullbackLastHom h) (S.pullback h).composite S.composite h := by
  have hstage : ∀ {i j : Fin ((S.pullback h).length + 1)} (e : i = j),
      eqToHom (congrArg (S.pullback h).stage e) ≫ (S.pullback h).stageMap j =
        (S.pullback h).stageMap i := by
    intro i j e
    subst j
    simp
  apply (isPullback_pullbackStageHom S h (Fin.last _)).of_iso'
    (eqToIso (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom]
    rfl
  · simpa only [eqToIso.hom, Iso.refl_hom, Category.comp_id,
      Scheme.BlowUpSequence.composite] using
      hstage (pullbackStageIdx_last S h).symm
  · simp [Scheme.BlowUpSequence.composite]
  · simp

/-- A flat pullback sequence inherits every actual isomorphism open of its composite. -/
theorem isIso_pullback_composite_restrict (S : Scheme.BlowUpSequence X) (h : Y ⟶ X)
    [Flat h] (U : X.Opens) [IsIso (S.composite ∣_ U)] :
    IsIso ((S.pullback h).composite ∣_ h ⁻¹ᵁ U) :=
  isIso_restrict_of_isPullback (isPullback_pullbackLastHom S h) U

/-- Final-stage lifts of actual sequences preserve open immersions. -/
theorem isOpenImmersion_pullbackLastHom (S : Scheme.BlowUpSequence X) (h : Y ⟶ X)
    [IsOpenImmersion h] : IsOpenImmersion (S.pullbackLastHom h) :=
  property_of_isPullback _ (isPullback_pullbackLastHom S h) inferInstance

/-- The image of the final-stage lift is exactly the inverse image of the base chart. -/
theorem range_pullbackLastHom (S : Scheme.BlowUpSequence X) (h : Y ⟶ X) [Flat h] :
    Set.range (S.pullbackLastHom h) = S.composite ⁻¹' Set.range h :=
  range_fst_of_isPullback (isPullback_pullbackLastHom S h)

/-- The scheme-theoretic support of the normalized affine ideal is its actual vanishing set. -/
theorem support_specIdealSheaf {R : Type u} [CommRing R] (I : Ideal R) :
    ((specIdealSheaf I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus I := by
  change (Spec (.of R)).zeroLocus (U := ⊤)
    ((I.map (Scheme.ΓSpecIso (.of R)).inv.hom : Ideal _) : Set _) = _
  rw [Spec_zeroLocus, ← Ideal.coe_comap,
    Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)]

/-- A generator's basic open lies outside the actual affine centre. -/
theorem basicOpen_le_compl_support {R : Type u} [CommRing R]
    (J : (Spec (.of R)).IdealSheafData) {a : R} (ha : a ∈ idealOfSpecSheaf J) :
    PrimeSpectrum.basicOpen a ≤ J.support.compl := by
  intro x hx
  change x ∉ J.support
  rw [← specIdealSheaf_idealOfSpecSheaf J]
  change x ∉ ((specIdealSheaf (idealOfSpecSheaf J)).support : Set (Spec (.of R)))
  rw [support_specIdealSheaf]
  intro hzero
  exact hx (hzero ha)

/-- The actual first blowup is an isomorphism on each generator's basic open. -/
theorem isIso_blowUpπ_restrict_basicOpen {R : Type u} [CommRing R]
    (J : (Spec (.of R)).IdealSheafData) {a : R} (ha : a ∈ idealOfSpecSheaf J) :
    IsIso (J.blowUpπ ∣_ PrimeSpectrum.basicOpen a) := by
  have := Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support J
  exact Hironaka.Sequence.isIso_restrict_of_le _ (basicOpen_le_compl_support J ha)

variable {B K : Type u} [CommRing B] [Field K] [Algebra B K]

/-- Every nonempty root open has a point in each actual ratio-chart spectrum. -/
theorem nonempty_reesTreeChart_preimage (C : Subalgebra B K) {n : ℕ}
    (g : Fin n → C) (i : Fin n) (U : (Spec (.of C)).Opens)
    (hU : (U : Set (Spec (.of C))).Nonempty) :
    ((Spec.map (CommRingCat.ofHom (reesTreeChartIncl C g i).toRingHom) ⁻¹ᵁ U) :
      Set (Spec (.of (reesTreeChart C g i)))).Nonempty := by
  apply DenseRange.exists_mem_open
    (denseRange_specMap_of_injective (reesTreeChartIncl C g i).toRingHom ?_) U.2 hU
  intro x y h
  exact Subtype.ext (congrArg (fun z : reesTreeChart C g i => (z : K)) h)

/-- In a domain, shrinking a nonempty open by a nonzero denominator stays nonempty. -/
theorem nonempty_inf_basicOpen (C : Subalgebra B K) (U : (Spec (.of C)).Opens)
    (hU : (U : Set (Spec (.of C))).Nonempty) {a : C} (ha : a ≠ 0) :
    ((U ⊓ PrimeSpectrum.basicOpen a : (Spec (.of C)).Opens) :
      Set (Spec (.of C))).Nonempty := by
  apply nonempty_preirreducible_inter U.2 (PrimeSpectrum.basicOpen a).2 hU
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  exact ha

/-- The actual restricted tail on each nonzero ratio chart has a nonempty isomorphism open. -/
theorem exists_nonempty_isIso_restrict_rees_tail (C : Subalgebra B K)
    (J : (Spec (.of C)).IdealSheafData) (rest : Scheme.BlowUpSequence J.blowUp)
    (U : (Spec (.of C)).Opens) (hU : (U : Set (Spec (.of C))).Nonempty)
    [IsIso ((Scheme.BlowUpSequence.cons _ J rest).composite ∣_ U)]
    {n : ℕ} (g : Fin n → C) (hg : Ideal.span (Set.range g) = idealOfSpecSheaf J)
    (i : Fin n) (hi : g i ≠ 0) :
    ∃ V : (Spec (.of (reesTreeChart C g i))).Opens,
      (V : Set (Spec (.of (reesTreeChart C g i)))).Nonempty ∧
      IsIso ((rest.pullback (globalReesBlowUpChart C J g hg i hi)).composite ∣_ V) := by
  let W := U ⊓ PrimeSpectrum.basicOpen (g i)
  have hW : (W : Set (Spec (.of C))).Nonempty := nonempty_inf_basicOpen C U hU hi
  have hgi : g i ∈ idealOfSpecSheaf J := by
    rw [← hg]
    exact Ideal.subset_span ⟨i, rfl⟩
  have := isIso_blowUpπ_restrict_basicOpen J hgi
  have : IsIso (J.blowUpπ ∣_ W) :=
    Hironaka.Sequence.isIso_restrict_of_le _ (show W ≤ _ from inf_le_right)
  have : IsIso ((rest.composite ≫ J.blowUpπ) ∣_ W) :=
    Hironaka.Sequence.isIso_restrict_of_le
      (Scheme.BlowUpSequence.cons _ J rest).composite (show W ≤ U from inf_le_left)
  have := isIso_restrict_cancel_right rest.composite J.blowUpπ W
  refine ⟨globalReesBlowUpChart C J g hg i hi ⁻¹ᵁ J.blowUpπ ⁻¹ᵁ W, ?_,
    isIso_pullback_composite_restrict rest _ (J.blowUpπ ⁻¹ᵁ W)⟩
  rw [← Scheme.Hom.comp_preimage, globalReesBlowUpChart_π]
  exact nonempty_reesTreeChart_preimage C g i W hW

end EnvelopeProperty.Char0
