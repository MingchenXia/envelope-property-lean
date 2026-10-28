import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosed
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRestriction

/-! # Actual partial morphisms extend their central embedding near zero -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPartial
open ProjectiveCentralFiberSectionLifting ProjectiveCentralFiberEmbeddingNeighborhood
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedRestriction

/-- The SAME partially defined map is proper after an actual base restriction
whose whole original inverse image belongs to its domain. Properness is over
that actual base open, not falsely attributed to the open inclusion into S. -/
theorem isProper_partial_restrict {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper p]
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k))) [IsSeparated q]
    (U : Y.Opens) (f : U.toScheme ⟶ Z) (hf : f ≫ q = U.ι ≫ p)
    (B : (Spec (CommRingCat.of (Polynomial k))).Opens) (hB : p ⁻¹ᵁ B ≤ U) :
    IsProper (f ∣_ (q ⁻¹ᵁ B)) := by
  let V := q ⁻¹ᵁ B
  let W := f ⁻¹ᵁ V
  let i : W.toScheme ⟶ Y := W.ι ≫ U.ι
  let r : W.toScheme ⟶ B.toScheme := (f ∣_ V) ≫ (q ∣_ B)
  have hcomm : i ≫ p = r ≫ B.ι := by
    calc
      i ≫ p = W.ι ≫ (U.ι ≫ p) := by dsimp only [i]; rw [Category.assoc]
      _ = W.ι ≫ (f ≫ q) := by rw [hf]
      _ = ((f ∣_ V) ≫ V.ι) ≫ q := by rw [morphismRestrict_ι, Category.assoc]
      _ = r ≫ B.ι := by
        dsimp only [r, V]
        simpa only [Category.assoc] using
          congrArg (fun a => (f ∣_ (q ⁻¹ᵁ B)) ≫ a) (morphismRestrict_ι q B).symm
  have hrange : p ⁻¹ᵁ B.ι.opensRange = i.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    ext y
    change p y ∈ B ↔ y ∈ Set.range i
    constructor
    · intro hy
      let x : U.toScheme := ⟨y, hB hy⟩
      have hx : f x ∈ V := by
        change q (f x) ∈ B
        have he : q (f x) = p (U.ι x) := congrArg (fun a => a x) hf
        rw [he]
        exact hy
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      have he : q (f x.1) = p (U.ι x.1) := congrArg (fun a => a x.1) hf
      exact he ▸ x.2
  have hs : IsPullback r i B.ι p :=
    IsOpenImmersion.isPullback r i B.ι p hcomm hrange
  have : IsProper r := IsZariskiLocalAtTarget.of_isPullback hs.flip inferInstance
  have : IsSeparated (q ∣_ B) := IsZariskiLocalAtTarget.restrict
    (P := @IsSeparated) (inferInstance : IsSeparated q) B
  exact IsProper.of_comp (f ∣_ V) (q ∣_ B)

private theorem central_range_subset_image {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (U : Y.Opens)
    (hU : Set.range (zeroInclusion p) ⊆ (U : Set Y))
    (T : U.toScheme.Opens)
    (hT : Set.range (zeroInclusion (U.ι ≫ p)) ⊆ (T : Set U.toScheme)) :
    Set.range (zeroInclusion p) ⊆ (U.ι ''ᵁ T : Set Y) := by
  let : IsIso (centralMap (U.ι ≫ p) p U.ι rfl) := centralMap_open_isIso p U hU
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := (centralMap (U.ι ≫ p) p U.ι rfl).surjective y
  refine ⟨zeroInclusion (U.ι ≫ p) x, hT ⟨x, rfl⟩, ?_⟩
  have he : zeroInclusion p (centralMap (U.ι ≫ p) p U.ι rfl x) =
      U.ι (zeroInclusion (U.ι ≫ p) x) :=
    congrArg (fun a => a x) (centralMap_inclusion (U.ι ≫ p) p U.ι rfl)
  exact he.symm.trans (congrArg (fun a => zeroInclusion p a) hx)

/-- A map defined only on an original open containing the whole centre is
internally finite after shrinking the ORIGINAL proper base family. -/
theorem exists_finite_neighborhood_partial {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper p]
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k))) [IsSeparated q]
    (U : Y.Opens) (hU : Set.range (zeroInclusion p) ⊆ (U : Set Y))
    (f : U.toScheme ⟶ Z) (hf : f ≫ q = U.ι ≫ p)
    [IsClosedImmersion (centralMap (U.ι ≫ p) q f hf)] :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      p ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤ U ∧
      IsFinite (f ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen g)) := by
  have : LocallyOfFiniteType (f ≫ q) := hf.symm ▸ inferInstance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f q
  have hcentral := central_range_subset_quasiFiniteLocus (U.ι ≫ p) q f hf
    (centralMap (U.ι ≫ p) q f hf).isEmbedding.injective
  let T := U.ι ''ᵁ f.quasiFiniteLocus
  have hT : Set.range (zeroInclusion p) ⊆ (T : Set Y) :=
    central_range_subset_image p U hU f.quasiFiniteLocus hcentral
  obtain ⟨g, hg, hsubset⟩ :=
    ProjectiveCentralFiberGeneratorNeighborhood.exists_principal_neighborhood_of_fiber_subset p T hT
  let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
  let V := q ⁻¹ᵁ B
  have hBU : p ⁻¹ᵁ B ≤ U := by
    intro y hy
    obtain ⟨x, _hx, hxy⟩ := hsubset hy
    exact hxy ▸ x.2
  refine ⟨g, hg, hBU, ?_⟩
  have : IsProper (f ∣_ V) := isProper_partial_restrict p q U f hf B hBU
  have hgood : f ⁻¹ᵁ V ≤ f.quasiFiniteLocus := by
    intro x hx
    change q (f x) ∈ B at hx
    have he : q (f x) = p (U.ι x) := congrArg (fun a => a x) hf
    have hxB : p (U.ι x) ∈ B := he ▸ hx
    have hxT : U.ι x ∈ T := hsubset hxB
    obtain ⟨z, hz, hzx⟩ := hxT
    have hzx' : z = x := U.ι.isEmbedding.injective hzx
    exact hzx' ▸ hz
  have : LocallyQuasiFinite (f ∣_ V) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    ext x
    have hx : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := hgood x.2
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff] at hx
    simpa using hx
  exact IsFinite.of_isProper_of_locallyQuasiFinite (f ∣_ V)

private theorem closed_restrict_of_le {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (V T : Z.Opens) (hVT : V ≤ T) (hT : IsClosedImmersion (f ∣_ T)) :
    IsClosedImmersion (f ∣_ V) := by
  have h := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) hT (T.ι ⁻¹ᵁ V)
  have h' := (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictRestrict f T (T.ι ⁻¹ᵁ V))).mp h
  have he : T.ι ''ᵁ (T.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVT]
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictEq f he)).mp h'

/-- The SAME actual map, defined only on an original neighbourhood of the
whole source centre, is internally a closed immersion near zero. -/
theorem exists_closedImmersion_neighborhood_partial {k : Type u} [Field k]
    {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper p]
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper q]
    (U : Y.Opens) (hU : Set.range (zeroInclusion p) ⊆ (U : Set Y))
    (f : U.toScheme ⟶ Z) (hf : f ≫ q = U.ι ≫ p)
    [IsClosedImmersion (centralMap (U.ι ≫ p) q f hf)] :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      p ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤ U ∧
      IsClosedImmersion (f ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen g)) := by
  obtain ⟨a, ha, haU, hfinite⟩ := exists_finite_neighborhood_partial p q U hU f hf
  let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen a
  let V := q ⁻¹ᵁ B
  let W := f ⁻¹ᵁ V
  let p' := W.ι ≫ (U.ι ≫ p)
  let q' := V.ι ≫ q
  let f' := f ∣_ V
  have hf' : f' ≫ q' = p' := by
    dsimp only [f', q', p', W]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf]
  let : IsFinite f' := hfinite
  have hV : Set.range (zeroInclusion q) ⊆ (V : Set Z) :=
    central_range_subset_basicOpen q a ha
  let : IsClosedImmersion (centralMap p' q' f' hf') :=
    centralMap_restrict_closedImmersion (U.ι ≫ p) q f hf V hV
  obtain ⟨T', hT', hclosed⟩ :=
    ProjectiveCentralFiberEmbeddingNeighborhoodClosed.exists_closed_target_neighborhood p' q' f' hf'
  let T := V.ι ''ᵁ T'
  have hT : Set.range (zeroInclusion q) ⊆ (T : Set Z) :=
    central_range_subset_image q V hV T' hT'
  have hclosedT : IsClosedImmersion (f ∣_ T) :=
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (morphismRestrictRestrict f V T')).mp hclosed
  obtain ⟨b, hb, hbT⟩ :=
    ProjectiveCentralFiberGeneratorNeighborhood.exists_principal_neighborhood_of_fiber_subset q T hT
  refine ⟨a * b, ?_, ?_, ?_⟩
  · rw [Polynomial.eval_mul]
    exact mul_ne_zero ha hb
  · intro y hy
    apply haU
    change p y ∈ PrimeSpectrum.basicOpen a
    change p y ∈ PrimeSpectrum.basicOpen (a * b) at hy
    exact PrimeSpectrum.basicOpen_mul_le_left a b hy
  · apply closed_restrict_of_le f _ T ?_ hclosedT
    intro z hz
    apply hbT
    change q z ∈ PrimeSpectrum.basicOpen b
    change q z ∈ PrimeSpectrum.basicOpen (a * b) at hz
    exact PrimeSpectrum.basicOpen_mul_le_right a b hz

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedPartial
