import EnvelopeProperty.AlgGeom.SchemeProjectiveSectionOpenBasis

/-! # Actual positive-power section opens refine original affine opens

The original closed projective embedding and the native homogeneous
Proj basis internally construct positive-degree original line sections.
Actual original homogeneous basic opens, not supplied open-matching data,
control pointwise and finite affine refinements of original opens.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open MvPolynomial Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeProjectiveSectionPositiveBasis
open CanonicalGeometry SchemeLineSectionEvaluation SchemeModuleCechLineSectionLocalization
open SchemeProjectiveSectionOpenBasis
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable instance basisPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullback f).Monoidal := pullbackMonoidal f
variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
local notation "P" => Proj (homogeneousSubmodule (Fin (n + 1)) R)
local notation "O₁" => coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (1 : ℤ)

/-- The SAME actual original O(1) pulled along the original embedding. -/
abbrev embeddingLine (j : X ⟶ P) : X.Modules := (pullback j).obj O₁

theorem embeddingLine_isInvertible (j : X ⟶ P) : IsInvertible (embeddingLine j) :=
  (coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (n + 1)) (1 : ℤ)).pullback j

/-- Actual pullback of the original homogeneous-form section, transported
by the genuine native original tensor-power comparison into SAME H^d. -/
def pulledHomogeneousPowerSection (j : X ⟶ P) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    unitObj X ⟶ bundleTensorPower (embeddingLine j) d :=
  pullbackSectionHom j (homogeneousPowerSection (0 : Fin (n + 1)) d F hF) ≫
    (BundleTensorPowerPullback.pullbackIso j O₁ d).hom

/-- The SAME actual original homogeneous section open pulls back literally
along the original map, with all native power/line comparisons internal. -/
theorem pulledHomogeneousPowerSection_open (j : X ⟶ P) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    sectionOpen (bundleTensorPower (embeddingLine j) d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible (embeddingLine_isInvertible j) d)
      (pulledHomogeneousPowerSection j d F hF) =
      j ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) F := by
  let hO := coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (n + 1)) (1 : ℤ)
  have h₁ := sectionOpen_postcompose_iso
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hO d).pullback j)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible (embeddingLine_isInvertible j) d)
    (pullbackSectionHom j (homogeneousPowerSection (0 : Fin (n + 1)) d F hF))
    (BundleTensorPowerPullback.pullbackIso j O₁ d)
  have h₂ := sectionOpen_pullback (bundleTensorPower O₁ d)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hO d)
    (homogeneousPowerSection (0 : Fin (n + 1)) d F hF) j
  exact h₁.trans (h₂.trans (congrArg (fun W => j ⁻¹ᵁ W)
    (homogeneousPowerSection_open (0 : Fin (n + 1)) d F hF)))

/-- The original projective embedding internally supplies a positive-power
section affine open around every original point inside every original open.
No chosen homogeneous numerator, cover, frame or open matching is input. -/
theorem exists_positive_sectionOpen_le (j : X ⟶ P) [IsClosedImmersion j]
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ (d : ℕ), 0 < d ∧ ∃ s : unitObj X ⟶ bundleTensorPower (embeddingLine j) d,
      x ∈ sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (embeddingLine_isInvertible j) d) s ∧
      IsAffineOpen (sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (embeddingLine_isInvertible j) d) s) ∧
      sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (embeddingLine_isInvertible j) d) s ≤ U := by
  classical
  obtain ⟨V, hV, hUV⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp U.isOpen
  let V₀ : (P).Opens := ⟨V, hV⟩
  have hjx : j x ∈ V₀ := by
    change x ∈ j ⁻¹' V
    rw [hUV]
    exact hx
  obtain ⟨B, hB, hxB, hBV⟩ := Opens.isBasis_iff_nbhd.mp
    (Proj.isBasis_basicOpen (homogeneousSubmodule (Fin (n + 1)) R)) hjx
  obtain ⟨f, rfl⟩ := hB
  have hxp : j x ∈ ⨆ d : ℕ, Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R)
      (GradedRing.proj (homogeneousSubmodule (Fin (n + 1)) R) d f) := by
    rw [← Proj.basicOpen_eq_iSup_proj]
    exact hxB
  obtain ⟨d, hxd⟩ := Opens.mem_iSup.mp hxp
  let F := GradedRing.proj (homogeneousSubmodule (Fin (n + 1)) R) d f
  have hF : F.IsHomogeneous d := by
    change GradedRing.proj (homogeneousSubmodule (Fin (n + 1)) R) d f ∈
      homogeneousSubmodule (Fin (n + 1)) R d
    exact (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) R) f d).property
  have hcoord : j x ∈ ⨆ i : Fin (n + 1), coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hcoord
  let G := F * MvPolynomial.X i
  have hG : G.IsHomogeneous (d + 1) := hF.mul (MvPolynomial.isHomogeneous_X R i)
  have hxG : j x ∈ Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) G := by
    rw [Proj.basicOpen_mul]
    exact ⟨hxd, hxi⟩
  have hFd : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) F ≤
      Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) f := by
    rw [Proj.basicOpen_eq_iSup_proj _ f]
    exact le_iSup (fun k => Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R)
      (GradedRing.proj (homogeneousSubmodule (Fin (n + 1)) R) k f)) d
  have hGV : Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) G ≤ V₀ := by
    rw [Proj.basicOpen_mul]
    exact inf_le_left.trans (hFd.trans hBV)
  let s := pulledHomogeneousPowerSection j (d + 1) G hG
  let W := sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
    (embeddingLine_isInvertible j) (d + 1)) s
  have hW : W = j ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) G :=
    pulledHomogeneousPowerSection_open j (d + 1) G hG
  refine ⟨d + 1, Nat.succ_pos d, s, ?_, ?_, ?_⟩
  · change x ∈ W
    rw [hW]
    exact hxG
  · change IsAffineOpen W
    rw [hW]
    exact (Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin (n + 1)) R)
      G hG (Nat.succ_pos d)).preimage j
  · change W ≤ U
    rw [hW]
    intro z hz
    have hzV := hGV hz
    change z ∈ (U : Set X)
    rw [← hUV]
    exact hzV

/-- Original affine compactness internally makes a finite affine refinement
of the ORIGINAL affine U by literal positive-power opens of SAME H=j*O(1).
All actual sections and exact cover/subset/affineness statements are produced. -/
theorem exists_finite_positive_sectionOpen_refinement (j : X ⟶ P) [IsClosedImmersion j]
    (U : X.affineOpens) :
    ∃ (I : Type u) (_ : Finite I) (d : I → ℕ) (s : ∀ i, unitObj X ⟶ bundleTensorPower (embeddingLine j) (d i)),
      (∀ i, 0 < d i) ∧
      (∀ i, IsAffineOpen (sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (embeddingLine_isInvertible j) (d i)) (s i))) ∧
      (∀ i, sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (embeddingLine_isInvertible j) (d i)) (s i) ≤ U.1) ∧
      (⨆ i, sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (embeddingLine_isInvertible j) (d i)) (s i)) = U.1 := by
  classical
  choose d hd s hs hAff hSub using fun x : U.1 => exists_positive_sectionOpen_le j U.1 x.1 x.2
  let W (x : U.1) := sectionOpen _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible
    (embeddingLine_isInvertible j) (d x)) (s x)
  have hcover : (U.1 : Set X) ⊆ ⋃ x : U.1, (W x : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hs ⟨x, hx⟩⟩
  obtain ⟨a, ha⟩ := U.2.isCompact.elim_finite_subcover
    (fun x : U.1 => (W x : Set X)) (fun x => (W x).isOpen) hcover
  refine ⟨a, inferInstance, fun i => d i.1, fun i => s i.1,
    fun i => hd i.1, fun i => hAff i.1, fun i => hSub i.1, ?_⟩
  apply le_antisymm
  · exact iSup_le (fun i => hSub i.1)
  · intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ha hx)
    obtain ⟨hya, hxy⟩ := Set.mem_iUnion.mp hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hya⟩, hxy⟩

end EnvelopeProperty.SchemeProjectiveSectionPositiveBasis
