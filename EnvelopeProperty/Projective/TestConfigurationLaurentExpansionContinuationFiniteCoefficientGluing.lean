import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationOverlapMatching
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sets.OpenCover

/-! # Genuine finite gluing of original Laurent coefficients

Original sections on the actual inverse images of affine opens produce
their local coefficients. Their proved matching gives native original
sheaf gluing. Finiteness of the actual cover derives finite whole support.
No decomposition, coefficient family, or matching proof is an input.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of R[T;T⁻¹])) (g : Y ⟶ X)
  (H : IsPullback g q f (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))))
  (M : X.Modules) [M.IsQuasicoherent] {ι : Type u}
  (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hUU : ∀ i j, IsAffineOpen (U i ⊓ U j)) (hCover : TopologicalSpace.IsOpenCover U)
  (s : (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj (op ⊤))

include hUU hCover

/-- Native original sheaf gluing produces the unique whole coefficient
at each integer, from the SAME original whole section and actual cover. -/
theorem exists_unique_original_whole_laurent_coefficient (n : ℤ) :
    ∃! t : (originalBaseOpenPresheaf f M).obj (op ⊤), ∀ i,
      M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op t =
        (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
          ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
            (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)) n := by
  let sf (i : ι) : Γ(M, U i) :=
    (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
      ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
        (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)) n
  have hcpt : ∀ i j,
      M.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (sf i) =
        M.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (sf j) := by
    intro i j
    have hleft : TopologicalSpace.Opens.infLELeft (U i) (U j) =
        homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := Subsingleton.elim _ _
    have hright : TopologicalSpace.Opens.infLERight (U i) (U j) =
        homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := Subsingleton.elim _ _
    rw [hleft, hright]
    exact originalAffineOpenLaurentCoefficients_match_global f q g H M s
      (U i) (U j) (hU i) (hU j) (hUU i j) n
  exact TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) (le_of_eq hCover.iSup_eq_top.symm) sf hcpt

/-- The actual original whole coefficient is produced by the preceding
derived native unique gluing, without a gluing or coefficient input. -/
def originalWholeLaurentCoefficient (n : ℤ) :
    (originalBaseOpenPresheaf f M).obj (op ⊤) :=
  Classical.choose
    (exists_unique_original_whole_laurent_coefficient f q g H M U hU hUU hCover s n).exists

/-- Every actual original restriction of the produced whole coefficient
is exactly the derived local coefficient of the original section. -/
theorem originalWholeLaurentCoefficient_restrict (n : ℤ) (i : ι) :
    M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
        (originalWholeLaurentCoefficient f q g H M U hU hUU hCover s n) =
      (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
        ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
          (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)) n :=
  Classical.choose_spec
    (exists_unique_original_whole_laurent_coefficient f q g H M U hU hUU hCover s n).exists i

/-- The finite union of the ACTUAL local supports bounds the produced
whole coefficients, by original sheaf uniqueness against the zero section. -/
theorem originalWholeLaurentCoefficient_eq_zero_outside_support [Fintype ι] (n : ℤ)
    (hn : n ∉ Finset.univ.biUnion (fun i =>
      (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
        ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
          (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)).support)) :
    originalWholeLaurentCoefficient f q g H M U hU hUU hCover s n = 0 := by
  classical
  have hlocal (i : ι) :
      (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
        ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
          (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)) n = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hi
    exact hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hzero : ∀ i, M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
      (0 : (originalBaseOpenPresheaf f M).obj (op ⊤)) =
        (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
          ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
            (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)) n := by
    intro i
    rw [map_zero, hlocal]
  exact (exists_unique_original_whole_laurent_coefficient f q g H M U hU hUU hCover s n).unique
    (originalWholeLaurentCoefficient_restrict f q g H M U hU hUU hCover s n) hzero

/-- Finiteness is DERIVED from the original finite affine cover. The
produced original whole Finsupp is unique with its exact original restrictions. -/
theorem exists_unique_original_whole_laurent_finite_coefficients [Fintype ι] :
    ∃! c : ℤ →₀ (originalBaseOpenPresheaf f M).obj (op ⊤), ∀ i n,
      M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (c n) =
        (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
          ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
            (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)) n := by
  classical
  let F : Finset ℤ := Finset.univ.biUnion (fun i =>
    (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
      ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
        (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)).support)
  let c (n : ℤ) := originalWholeLaurentCoefficient f q g H M U hU hUU hCover s n
  have hc : ∀ n, c n ≠ 0 → n ∈ F := by
    intro n hcn
    by_contra hn
    exact hcn (originalWholeLaurentCoefficient_eq_zero_outside_support
      f q g H M U hU hUU hCover s n hn)
  let C : ℤ →₀ (originalBaseOpenPresheaf f M).obj (op ⊤) := Finsupp.onFinset F c hc
  have hC : ∀ i n, M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (C n) =
      (originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
        ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
          (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s)) n := by
    intro i n
    exact originalWholeLaurentCoefficient_restrict f q g H M U hU hUU hCover s n i
  refine ⟨C, hC, ?_⟩
  intro D hD
  ext n
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) (le_of_eq hCover.iSup_eq_top.symm)
  intro i
  exact (hD i n).trans (hC i n).symm

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
