import EnvelopeProperty.Cartier.GeometricSheafCartier
import EnvelopeProperty.Cartier.DeligneIllusieCechGoodTruncation
import EnvelopeProperty.Cartier.DeligneIllusieGradedSourceHomology

/-!
# Finite Source Assembly

The actual zero summand and the original finite-source good truncation.
Positive DI summands and the final quasi-isomorphism are separate constructions.
-/

noncomputable section
namespace EnvelopeProperty.DI.FiniteSourceAssembly

open AlgebraicGeometry CategoryTheory Category Limits HomologicalComplex

universe u v

section Geometry
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
  (n : ℕ) [SmoothOfRelativeDimension n f]

local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
private abbrev twistStructure :
    (Cartier.SchemeRelativeFrobenius.twist p f) ⟶ Spec (.of k) :=
  pullback.snd f (Cartier.SchemeRelativeFrobenius.baseMap (k := k) p)

local notation "g" => twistStructure f p
local notation "K" => Cartier.SchemeRelativeFrobeniusBasisDifferential.complex f p n
local notation "M" => CanonicalGeometry.exteriorCotangentSheaf g 0

private def inverseCartierZero : M ⟶ (K).homology 0 :=
  (Cartier.GeometricSheafCartier.inverseCartierIso f p n 0).hom

/-- The actual original inverse Cartier map, lifted through the canonical zero cycles. -/
def zeroComponent : M ⟶ (K).X 0 :=
  inverseCartierZero f p n ≫
    (K).isoHomologyπ₀.inv ≫ (K).iCycles 0

/-- The original degree-zero representative is closed in the original complex. -/
theorem zeroComponent_closed : zeroComponent f p n ≫ (K).d 0 1 = 0 := by
  simp only [zeroComponent, assoc, iCycles_d, comp_zero]

/-- A genuine cochain map from the original single zero-form sheaf. -/
def zeroCochainMap : (single (Y).Modules (ComplexShape.up ℕ) 0).obj M ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K M).symm
    ⟨zeroComponent f p n, zeroComponent_closed f p n⟩

/-- The complete zero component is the original single-object identification and representative. -/
theorem zeroCochainMap_f_zero :
    (zeroCochainMap f p n).f 0 =
      (singleObjXSelf (ComplexShape.up ℕ) 0 M).hom ≫ zeroComponent f p n := by
  simp only [zeroCochainMap, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  rfl

/-- The entire actual homology map is precisely the already constructed global Cartier map. -/
theorem zeroCochainMap_class :
    (singleObjHomologySelfIso (ComplexShape.up ℕ) 0 M).inv ≫
      homologyMap (zeroCochainMap f p n) 0 =
        (Cartier.GeometricSheafCartier.inverseCartierIso f p n 0).hom := by
  change _ = inverseCartierZero f p n
  have hc : cyclesMap (zeroCochainMap f p n) 0 =
      (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 M).hom ≫
        inverseCartierZero f p n ≫
          (K).isoHomologyπ₀.inv := by
    apply (cancel_mono ((K).iCycles 0)).mp
    rw [cyclesMap_i, zeroCochainMap_f_zero]
    simp only [zeroComponent, singleObjCyclesSelfIso_hom]
    simp only [assoc]
  apply (cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 M).hom).mp
  rw [← assoc, singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv,
    homologyπ_naturality, hc]
  change (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 M).hom ≫
    (inverseCartierZero f p n ≫
      (K).isoHomologyπ₀.inv) ≫ (K).isoHomologyπ₀.hom = _
  simp only [assoc, Iso.inv_hom_id, comp_id]

/-- The original zero cochain followed by the original native total augmentation. -/
def zeroTotalMap {ι : Type u} (U : ι → (Cartier.SchemeRelativeFrobenius.twist p f).Opens) :
    (single (Y).Modules (ComplexShape.up ℕ) 0).obj M ⟶
      Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation.totalComplex U K :=
  zeroCochainMap f p n ≫
    Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation.totalAugmentation U K

end Geometry

section FiniteSource
variable {C : Type u} [Category.{v} C] [Abelian C] {p : ℕ} (M : Fin p → C)

local notation "S" => Cartier.DeligneIllusieGradedSourceHomology.gradedSource
  (ComplexShape.up ℕ) Fin.val M

/-- The actual extended finite source has no term above its original cutoff. -/
theorem source_extend_isStrictlyLE :
    CochainComplex.IsStrictlyLE ((S).extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  cases i with
  | ofNat q =>
    simp only [Int.ofNat_eq_natCast] at hi
    have hpq : p ≤ q := by omega
    have hzero : IsZero ((S).X q) :=
      Cartier.DeligneIllusieGradedSourceHomology.gradedSource_X_isZero_of_not_mem
        (ComplexShape.up ℕ) Fin.val M q (by
          intro j hj
          have hqp : q < p := by simpa only [← hj] using j.isLt
          exact Nat.not_lt_of_ge hpq hqp)
    exact hzero.of_iso ((S).extendXIso ComplexShape.embeddingUpNat (i := q) rfl)
  | negSucc q => omega

/-- The original good-truncation inclusion is invertible, including the empty finite source. -/
def sourceTruncationIso :
    CochainComplex.truncLE ((S).extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1) ≅
      (S).extend ComplexShape.embeddingUpNat := by
  letI := source_extend_isStrictlyLE M
  exact asIso (CochainComplex.ιTruncLE ((S).extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1))

/-- Canonical factorization of the actual finite-source map through the genuine outgoing kernel. -/
def truncatedMap {T : CochainComplex C ℕ} (a : S ⟶ T) :
    (S).extend ComplexShape.embeddingUpNat ⟶
      CochainComplex.truncLE (T.extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1) :=
  (sourceTruncationIso M).inv ≫
    CochainComplex.truncLEMap (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
      ((p : ℤ) - 1)

/-- Its entire untruncated map is exactly the original map, with no additional hypothesis. -/
theorem truncatedMap_inclusion {T : CochainComplex C ℕ} (a : S ⟶ T) :
    truncatedMap M a ≫
      CochainComplex.ιTruncLE (T.extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1) =
        HomologicalComplex.extendMap a ComplexShape.embeddingUpNat := by
  rw [truncatedMap, assoc, CochainComplex.ιTruncLE_naturality]
  change (sourceTruncationIso M).inv ≫ (sourceTruncationIso M).hom ≫ _ = _
  simp only [Iso.inv_hom_id_assoc]

end FiniteSource
end EnvelopeProperty.DI.FiniteSourceAssembly
