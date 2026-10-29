import EnvelopeProperty.Vanishing.SpecializationDerivedChainHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-! # Actual reversal of an integer cochain complex and tensor homology

The native embedding sends a natural chain degree q to the original integer
cochain degree N-q. All maps and scalar extensions are retained.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedReversal

open SpecializationDerivedReplacementStep SpecializationDerivedFiniteApproximation

variable {R : Type u} [CommRing R]

/-- Scalar extension of an actual original short-complex isomorphism. -/
def baseChangeIso {U V : ShortComplex (ModuleCat.{u} R)} (e : U ≅ V)
    (T : Type u) [CommRing T] [Algebra R T] :
    baseChangeComplex U T ≅ baseChangeComplex V T :=
  ShortComplex.isoMk
    (((ShortComplex.π₁.mapIso e).toLinearEquiv).baseChange R T _ _).toModuleIso
    (((ShortComplex.π₂.mapIso e).toLinearEquiv).baseChange R T _ _).toModuleIso
    (((ShortComplex.π₃.mapIso e).toLinearEquiv).baseChange R T _ _).toModuleIso
    (by
      apply ModuleCat.hom_ext
      change V.f.hom.baseChange T ∘ₗ e.hom.τ₁.hom.baseChange T =
        e.hom.τ₂.hom.baseChange T ∘ₗ U.f.hom.baseChange T
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      exact ModuleCat.hom_ext_iff.mp e.hom.comm₁₂)
    (by
      apply ModuleCat.hom_ext
      change V.g.hom.baseChange T ∘ₗ e.hom.τ₂.hom.baseChange T =
        e.hom.τ₃.hom.baseChange T ∘ₗ U.g.hom.baseChange T
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      exact ModuleCat.hom_ext_iff.mp e.hom.comm₂₃)

/-- The native reversed complex, using the actual embedding q ↦ N-q. -/
def reverse (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℤ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  K.restriction (ComplexShape.embeddingUpIntLE N)

/-- The actual original three cochain terms in the reversed degree. -/
def originalSegment (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℤ) (q : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  K.sc' (N - q - 1) (N - q) (N - q + 1)

/-- Actual original segments at equal indices are canonically isomorphic. -/
def reindexSegmentIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {i j k i' j' k' : ℤ} (hi : i = i') (hj : j = j') (hk : k = k') :
    K.sc' i j k ≅ K.sc' i' j' k' := by
  subst i' j' k'
  exact Iso.refl _

/-- In positive chain degree the actual neighboring terms and maps are retained. -/
def reverseSegmentIsoSucc (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℤ) (q : ℕ) :
    segment (reverse K N) (q + 1) ≅ originalSegment K N (q + 1) := by
  have hi : N - ((q + 2 : ℕ) : ℤ) = N - ((q + 1 : ℕ) : ℤ) - 1 := by omega
  have hk : N - (q : ℤ) = N - ((q + 1 : ℕ) : ℤ) + 1 := by omega
  exact reindexSegmentIso K hi rfl hk

/-- The actual original native cochain homology is the original segment homology. -/
def originalSegmentIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℤ) (q : ℕ) :
    K.sc (N - q) ≅ originalSegment K N q :=
  K.isoSc' _ _ _ (CochainComplex.prev ℤ _) (CochainComplex.next ℤ _)

/-- The literal top reversed terms are normalized using only original index equalities. -/
def reverseTopNormalizeIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℤ) :
    segment (reverse K N) 0 ≅ K.sc' (N - 1) N N :=
  reindexSegmentIso K (by simp) (by simp) (by simp)

/-- The original top cochain segment is normalized using only original index equalities. -/
def originalTopNormalizeIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℤ) :
    originalSegment K N 0 ≅ K.sc' (N - 1) N (N + 1) :=
  reindexSegmentIso K (by simp) (by simp) (by simp)

/-- The normalized top reversed comparison fixes the actual incoming and middle terms. -/
def reverseTopComparison (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℤ)
    (hnext : IsZero (K.X (N + 1))) :
    K.sc' (N - 1) N N ⟶ K.sc' (N - 1) N (N + 1) where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 0
  comm₁₂ := by
    change 𝟙 _ ≫ K.d (N - 1) N = K.d (N - 1) N ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  comm₂₃ := by
    have hg : K.d N (N + 1) = 0 := hnext.eq_of_tgt _ _
    change 𝟙 _ ≫ K.d N (N + 1) = K.d N N ≫ 0
    rw [hg, comp_zero, comp_zero]

/-- Top native homology is retained after every algebra extension because the
actual original next term is zero. -/
def reverseTopNormalizedBaseChangeHomologyIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : ℤ) (hnext : IsZero (K.X (N + 1)))
    (T : Type u) [CommRing T] [Algebra R T] :
    (baseChangeComplex (K.sc' (N - 1) N N) T).homology ≅
      (baseChangeComplex (K.sc' (N - 1) N (N + 1)) T).homology := by
  let φ := baseChangeComparison (reverseTopComparison K N hnext) T
  have hz : K.d N N = 0 := K.shape N N (by change ¬ N + 1 = N; omega)
  have hc : IsIso (ShortComplex.cyclesMap φ) := by
    apply cyclesMap_isIso_of_relations
    · intro x y _ _ hxy
      change (LinearMap.id : K.X N →ₗ[R] K.X N).baseChange T x =
        (LinearMap.id : K.X N →ₗ[R] K.X N).baseChange T y at hxy
      rw [LinearMap.baseChange_id] at hxy
      exact hxy
    · intro y _
      refine ⟨y, ?_, ?_⟩
      · change (K.d N N).hom.baseChange T y = 0
        rw [hz]
        change (0 : K.X N →ₗ[R] K.X N).baseChange T y = 0
        rw [LinearMap.baseChange_zero]
        rfl
      · change (LinearMap.id : K.X N →ₗ[R] K.X N).baseChange T y = y
        rw [LinearMap.baseChange_id]
        rfl
  let := hc
  have hfirst : IsIso φ.τ₁ := by
    change IsIso (ModuleCat.ofHom
      ((LinearMap.id : K.X (N - 1) →ₗ[R] K.X (N - 1)).baseChange T))
    rw [LinearMap.baseChange_id]
    change IsIso (𝟙 (ModuleCat.of T (T ⊗[R] K.X (N - 1))))
    infer_instance
  let := hfirst
  let : IsIso (ShortComplex.homologyMap φ) :=
    ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap φ)

/-- The actual top reversed tensor complex has the original native top homology. -/
def reverseTopBaseChangeHomologyIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : ℤ) (hnext : IsZero (K.X (N + 1)))
    (T : Type u) [CommRing T] [Algebra R T] :
    (baseChangeComplex (segment (reverse K N) 0) T).homology ≅
      (baseChangeComplex (originalSegment K N 0) T).homology :=
  ShortComplex.homologyMapIso (baseChangeIso (reverseTopNormalizeIso K N) T) ≪≫
    reverseTopNormalizedBaseChangeHomologyIso K N hnext T ≪≫
      ShortComplex.homologyMapIso (baseChangeIso (originalTopNormalizeIso K N).symm T)

/-- Every original reversed degree retains actual scalar-extended native homology. -/
def reverseBaseChangeHomologyIso (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : ℤ) (hnext : IsZero (K.X (N + 1))) (q : ℕ)
    (T : Type u) [CommRing T] [Algebra R T] :
    (baseChangeComplex (segment (reverse K N) q) T).homology ≅
      (baseChangeComplex (originalSegment K N q) T).homology := by
  cases q with
  | zero => exact reverseTopBaseChangeHomologyIso K N hnext T
  | succ q =>
    exact ShortComplex.homologyMapIso
      (baseChangeIso (reverseSegmentIsoSucc K N q) T)

/-- The actual reversed terms remain flat over the same original ring. -/
theorem reverse_X_flat (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Flat R (K.X i)] (N : ℤ) (q : ℕ) :
    Module.Flat R ((reverse K N).X q) :=
  inferInstanceAs (Module.Flat R (K.X ((ComplexShape.embeddingUpIntLE N).f q)))

/-- The reversed native homology is independently finite by its constructed
comparison with the original finite native cochain homology. -/
theorem reverse_homology_finite (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Finite R (K.homology i)] (N : ℤ)
    (hnext : IsZero (K.X (N + 1))) (q : ℕ) :
    Module.Finite R ((reverse K N).homology q) := by
  let e : (reverse K N).homology q ≅ K.homology (N - q) :=
    ShortComplex.homologyMapIso (segmentIso (reverse K N) q) ≪≫
      (ShortComplex.homologyMapIso (selfBaseChangeIso
        (segment (reverse K N) q))).symm ≪≫
      reverseBaseChangeHomologyIso K N hnext q R ≪≫
      ShortComplex.homologyMapIso (selfBaseChangeIso (originalSegment K N q)) ≪≫
      (ShortComplex.homologyMapIso (originalSegmentIso K N q)).symm
  exact Module.Finite.equiv e.symm.toLinearEquiv

variable [IsNoetherianRing R]

/-- Zero actual residue homology of the original cochain complex persists on
a constructed principal open, with every other comparison produced internally. -/
theorem exists_cochain_homology_zero_neighborhood
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Finite R (K.homology i)]
    (N : ℤ) (hnext : IsZero (K.X (N + 1))) (p : Ideal R) [p.IsMaximal] (q : ℕ)
    (hzero : IsZero (baseChangeComplex (originalSegment K N q) p.ResidueField).homology) :
    ∃ r : R, r ∉ p ∧ ∀ (F : Type u) [Field F] [Algebra R F],
      algebraMap R F r ≠ 0 →
        IsZero (baseChangeComplex (originalSegment K N q) F).homology := by
  let C := reverse K N
  let : ∀ q, Module.Flat R (C.X q) := fun q => reverse_X_flat K N q
  let : ∀ q, Module.Finite R (C.homology q) := fun q => reverse_homology_finite K N hnext q
  have hreverse : IsZero (baseChangeComplex (segment C q) p.ResidueField).homology :=
    hzero.of_iso (reverseBaseChangeHomologyIso K N hnext q p.ResidueField)
  obtain ⟨r, hr, hfield⟩ := exists_chain_homology_zero_neighborhood C p q hreverse
  exact ⟨r, hr, fun F _ _ hF =>
    (hfield F hF).of_iso (reverseBaseChangeHomologyIso K N hnext q F).symm⟩

/-- Original closed-fibre native cochain homology vanishing reaches the original
fraction field, without a supplied free model or generic comparison. -/
theorem generic_cochain_homology_isZero_of_closed_fibre [IsDomain R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Finite R (K.homology i)]
    (N : ℤ) (hnext : IsZero (K.X (N + 1))) (p : Ideal R) [p.IsMaximal] (q : ℕ)
    (hzero : IsZero (baseChangeComplex (originalSegment K N q) p.ResidueField).homology)
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    IsZero (baseChangeComplex (originalSegment K N q) F).homology := by
  obtain ⟨r, hr, hfield⟩ := exists_cochain_homology_zero_neighborhood K N hnext p q hzero
  apply hfield F
  intro h
  have hrzero : r = 0 :=
    IsFractionRing.injective R F (h.trans (map_zero (algebraMap R F)).symm)
  exact hr (hrzero ▸ p.zero_mem)

end EnvelopeProperty.Vanishing.SpecializationDerivedReversal
