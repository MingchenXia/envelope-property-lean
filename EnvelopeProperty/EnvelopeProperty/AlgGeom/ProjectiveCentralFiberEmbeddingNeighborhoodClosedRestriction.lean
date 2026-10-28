import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhood

/-! # The actual central fibre survives every neighbourhood of the whole centre -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRestriction
open ProjectiveCentralFiberSectionLifting ProjectiveCentralFiberEmbeddingNeighborhood

/-- The actual original central map of an open restriction is its genuine
cartesian base change, retaining the two original zero-fibre inclusions. -/
theorem isPullback_centralMap_open {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (U : Y.Opens) :
    IsPullback (centralMap (U.ι ≫ p) p U.ι rfl)
      (zeroInclusion (U.ι ≫ p)) (zeroInclusion p) U.ι := by
  have houter : IsPullback
      (centralMap (U.ι ≫ p) p U.ι rfl ≫ pullback.snd p (zeroMap k))
      (zeroInclusion (U.ι ≫ p)) (zeroMap k) (U.ι ≫ p) := by
    simpa only [centralMap, pullback.lift_snd] using
      (IsPullback.of_hasPullback (U.ι ≫ p) (zeroMap k)).flip
  exact houter.of_right (centralMap_inclusion (U.ι ≫ p) p U.ι rfl)
    (IsPullback.of_hasPullback p (zeroMap k)).flip

private theorem centralMap_open_isOpenImmersion {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (U : Y.Opens) :
    IsOpenImmersion (centralMap (U.ι ≫ p) p U.ι rfl) := by
  let h := isPullback_centralMap_open p U
  have hcomp : IsOpenImmersion (h.isoPullback.hom ≫ pullback.fst (zeroInclusion p) U.ι) :=
    inferInstance
  simpa only [h.isoPullback_hom_fst] using hcomp

/-- An open containing the ENTIRE original centre induces an isomorphism of
the SAME actual zero fibres, without an incoming base-change comparison. -/
theorem centralMap_open_isIso {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (U : Y.Opens)
    (hU : Set.range (zeroInclusion p) ⊆ (U : Set Y)) :
    IsIso (centralMap (U.ι ≫ p) p U.ι rfl) := by
  let h := isPullback_centralMap_open p U
  let : IsOpenImmersion (centralMap (U.ι ≫ p) p U.ι rfl) := centralMap_open_isOpenImmersion p U
  have hs : Function.Surjective (centralMap (U.ι ≫ p) p U.ι rfl) := by
    intro y
    have hy : y ∈ Set.range (pullback.fst (zeroInclusion p) U.ι) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨⟨zeroInclusion p y, hU ⟨y, rfl⟩⟩, rfl⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨h.isoPullback.inv z, ?_⟩
    have hh := congrArg (fun r => r z) h.isoPullback_inv_fst
    exact hh.trans hz
  let : Surjective (centralMap (U.ι ≫ p) p U.ι rfl) := ⟨hs⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

/-- The actual central closed immersion is retained by the SAME original
target restriction containing the whole central target. -/
theorem centralMap_restrict_closedImmersion {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) (hf : f ≫ q = p)
    [IsClosedImmersion (centralMap p q f hf)] (V : Z.Opens)
    (hV : Set.range (zeroInclusion q) ⊆ (V : Set Z)) :
    IsClosedImmersion
      (centralMap ((f ⁻¹ᵁ V).ι ≫ p) (V.ι ≫ q) (f ∣_ V)
        (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf])) := by
  let W := f ⁻¹ᵁ V
  let p' := W.ι ≫ p
  let q' := V.ι ≫ q
  let f' := f ∣_ V
  have hf' : f' ≫ q' = p' := by
    dsimp only [f', q', p', W]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf]
  have hW : Set.range (zeroInclusion p) ⊆ (W : Set Y) := by
    rintro _ ⟨y, rfl⟩
    change f (zeroInclusion p y) ∈ V
    have hh : zeroInclusion q (centralMap p q f hf y) = f (zeroInclusion p y) :=
      congrArg (fun r => r y) (centralMap_inclusion p q f hf)
    rw [← hh]
    exact hV ⟨centralMap p q f hf y, rfl⟩
  let : IsIso (centralMap p' p W.ι rfl) := centralMap_open_isIso p W hW
  let : IsIso (centralMap q' q V.ι rfl) := centralMap_open_isIso q V hV
  have hc : centralMap p' q' f' hf' ≫ centralMap q' q V.ι rfl =
      centralMap p' p W.ι rfl ≫ centralMap p q f hf := by
    apply (cancel_mono (zeroInclusion q)).mp
    calc
      (centralMap p' q' f' hf' ≫ centralMap q' q V.ι rfl) ≫ zeroInclusion q =
          centralMap p' q' f' hf' ≫ (zeroInclusion q' ≫ V.ι) := by
            rw [Category.assoc, centralMap_inclusion]
      _ = (zeroInclusion p' ≫ f') ≫ V.ι := by
        rw [← Category.assoc, centralMap_inclusion]
      _ = zeroInclusion p' ≫ (W.ι ≫ f) := by
        rw [Category.assoc, morphismRestrict_ι]
      _ = (centralMap p' p W.ι rfl ≫ zeroInclusion p) ≫ f := by
        rw [centralMap_inclusion, Category.assoc]
      _ = (centralMap p' p W.ι rfl ≫ centralMap p q f hf) ≫ zeroInclusion q := by
        rw [Category.assoc, Category.assoc, centralMap_inclusion]
  have hclosed : IsClosedImmersion
      (centralMap p' q' f' hf' ≫ centralMap q' q V.ι rfl) := by
    rw [hc]
    infer_instance
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)
    (centralMap p' q' f' hf') (centralMap q' q V.ι rfl)).mp hclosed

/-- Every original polynomial nonzero at zero gives an actual target open
containing the whole original scheme-theoretic central fibre. -/
theorem central_range_subset_basicOpen {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) (a : Polynomial k)
    (ha : Polynomial.eval 0 a ≠ 0) :
    Set.range (zeroInclusion p) ⊆ (p ⁻¹ᵁ PrimeSpectrum.basicOpen a : Set Y) := by
  rintro _ ⟨y, rfl⟩
  let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen a
  change p (zeroInclusion p y) ∈ B
  have hh : p (zeroInclusion p y) = zeroMap k (pullback.snd p (zeroMap k) y) :=
    congrArg (fun r => r y) (pullback.condition (f := p) (g := zeroMap k))
  rw [hh]
  change Polynomial.eval 0 a ∉ (pullback.snd p (zeroMap k) y).asIdeal
  intro hmem
  have hmul := (pullback.snd p (zeroMap k) y).asIdeal.mul_mem_left
    (Polynomial.eval 0 a)⁻¹ hmem
  have hone : (1 : k) ∈ (pullback.snd p (zeroMap k) y).asIdeal := by
    simpa only [inv_mul_cancel₀ ha] using hmul
  exact (pullback.snd p (zeroMap k) y).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRestriction
