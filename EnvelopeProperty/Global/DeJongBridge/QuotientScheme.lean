import EnvelopeProperty.Global.DeJongBridge.ProjChart
import EnvelopeProperty.Global.DeJongModel
import EnvelopeProperty.Alterations.Theorem
import EnvelopeProperty.Alterations.Composition
import EnvelopeProperty.Alterations.Geometry.ProjectiveIdealQuotient
import EnvelopeProperty.Alterations.Geometry.ProjIntegral
import EnvelopeProperty.Alterations.Geometry.ProjStructureMap

/-!
# The projective variety `Proj(k[x] / I)` of a `ProjSubvariety`

Step 1 of the bridge. For a projective subvariety
`X = V(I) ⊆ ℙ^N` in the sense of this library (`EnvelopeProperty.ProjSubvariety k N`: a
homogeneous prime `I ⊆ k[x_0, …, x_N]` not containing all `x_i`), the scheme
`X^s = Proj(k[x] / I)` (`DeJongEPBridge.Subvariety.scheme`), with the grading of the quotient by
the images of the homogeneous components
(`Alterations.Geometry.ProjectiveIdeal.GradedQuotient`), is

* a closed subscheme of projective space `ℙ^N = Proj k[x]` (`Subvariety.ι`,
  `quotientSchemeMap`), compatibly with the structure morphisms (`Subvariety.ι_comp`);
* integral (`ProjIntegral.isIntegral_proj`: `k[x] / I` is a domain with a nonzero
  element of degree `1`), with generic point the zero ideal (`genericPoint_asHomogeneousIdeal`);
* a variety over `k` in de Jong's sense, `Alterations.IsVariety` (2.9), being proper over
  `k` (`Subvariety.isVariety`).

The degree-`1` generators `x̄_i` of `k[x] / I` and of `k[x]` (`Subvariety.coord`, `X`) satisfy the
hypotheses of `ProjChart.range_pullGerm_eq_adjoin`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open Alterations Alterations.Geometry.ProjectiveIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DeJongEPBridge

universe u

/-! ### Projective space -/

section ProjectiveSpace

variable (k : Type u) [Field k] (n : ℕ)

/-- The structure morphism of `ℙ^n` is the structure morphism `Proj k[x] → Spec k` of
`ProjChart`. -/
theorem projectiveSpaceStructure_eq :
    projectiveSpaceStructure k n = ProjChart.structureMap (projectiveSpaceGrading k n) := by
  rw [projectiveSpaceStructure, ProjChart.structureMap]
  congr 2

theorem X_mem_projectiveSpaceGrading (i : Fin (n + 1)) :
    (X i : MvPolynomial (Fin (n + 1)) k) ∈ projectiveSpaceGrading k n 1 :=
  isHomogeneous_X k i

theorem adjoin_range_X_eq_top :
    Algebra.adjoin k (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)) = ⊤ :=
  MvPolynomial.adjoin_range_X

theorem exists_algebraMap_eq_of_mem_projectiveSpaceGrading_zero
    (a : MvPolynomial (Fin (n + 1)) k) (ha : a ∈ projectiveSpaceGrading k n 0) :
    ∃ c : k, algebraMap k _ c = a := by
  obtain ⟨c, hc⟩ := (projectiveSpaceConstants_bijective k n).2 ⟨a, ha⟩
  exact ⟨c, congrArg Subtype.val hc⟩

end ProjectiveSpace

/-! ### The quotient scheme -/

namespace Subvariety

variable {k : Type u} [Field k] {N : ℕ} (X : EnvelopeProperty.ProjSubvariety k N)

/-- The homogeneous ideal `I` of `X` as a `HomogeneousIdeal`. -/
def homIdeal : HomogeneousIdeal (projectiveSpaceGrading k N) :=
  ⟨X.ideal, (EnvelopeProperty.isHomogeneousIdeal_iff_isHomogeneous _).1 X.isHomogeneousIdeal⟩

/-- The homogeneous coordinate ring `k[x] / I`. -/
abbrev Ring : Type u :=
  MvPolynomial (Fin (N + 1)) k ⧸ (homIdeal X).toIdeal

/-- The grading of `k[x] / I` by the images of the homogeneous components. -/
abbrev grading : ℕ → Submodule k (Ring X) :=
  GradedQuotient.grading (projectiveSpaceGrading k N) (homIdeal X).toIdeal

instance : (homIdeal X).toIdeal.IsPrime :=
  X.isPrime

/-- The scheme `X^s = Proj(k[x] / I)`. -/
abbrev scheme : Scheme.{u} :=
  Proj (grading X)

/-- The closed immersion `X^s → ℙ^N`. -/
def ι : scheme X ⟶ projectiveSpace k N :=
  GradedQuotient.quotientSchemeMap (projectiveSpaceGrading k N) (homIdeal X)

instance : IsClosedImmersion (ι X) :=
  GradedQuotient.instIsClosedImmersion_quotientSchemeMap _ _

/-- The structure morphism `X^s → Spec k`. -/
abbrev p : scheme X ⟶ Spec (.of k) :=
  ProjChart.structureMap (grading X)

theorem ι_comp : ι X ≫ projectiveSpaceStructure k N = p X :=
  Geometry.ProjStructureMap.map_toSpec_base _ _ (projectiveSpaceConstants k N)
    (ProjChart.zeroConst _) (by ext c; rfl)

instance : IsProper (p X) := by
  rw [← ι_comp]
  infer_instance

/-- The coordinate `x̄_i ∈ k[x] / I`. -/
abbrev coord (i : Fin (N + 1)) : Ring X :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem coord_mem (i : Fin (N + 1)) : coord X i ∈ grading X 1 :=
  Submodule.mem_map.2 ⟨_, X_mem_projectiveSpaceGrading k N i, rfl⟩

theorem adjoin_range_coord : Algebra.adjoin k (Set.range (coord X)) = ⊤ := by
  have h := congrArg (Subalgebra.map (Ideal.Quotient.mkₐ k (homIdeal X).toIdeal))
    (adjoin_range_X_eq_top k N)
  rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
    (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective k _)] at h
  exact h

theorem exists_algebraMap_eq_of_mem_grading_zero (a : Ring X) (ha : a ∈ grading X 0) :
    ∃ c : k, algebraMap k _ c = a := by
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 ha
  obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_mem_projectiveSpaceGrading_zero k N b hb
  exact ⟨c, rfl⟩

theorem coord_ne_zero_iff (i : Fin (N + 1)) :
    coord X i ≠ 0 ↔ (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∉ X.ideal := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem irrelevant_ne_bot : HomogeneousIdeal.irrelevant (grading X) ≠ ⊥ := by
  obtain ⟨i, hi⟩ := X.exists_X_notMem
  intro h
  have hmem := HomogeneousIdeal.mem_irrelevant_of_mem (grading X) one_pos (coord_mem X i)
  rw [h] at hmem
  exact (coord_ne_zero_iff X i).2 hi hmem

instance : IsIntegral (scheme X) :=
  Geometry.ProjIntegral.isIntegral_proj (grading X) (irrelevant_ne_bot X)

/-- `X^s` is a variety over `k` (de Jong 2.9). -/
instance isVariety : IsVariety (p X) where

/-- The generic point of `X^s` is the zero ideal. -/
theorem genericPoint_asHomogeneousIdeal :
    (genericPoint (scheme X)).asHomogeneousIdeal = ⊥ := by
  have h := (Geometry.ProjIntegral.isGenericPoint_of_asHomogeneousIdeal_eq_bot (grading X)
    (Geometry.ProjIntegral.zeroPoint (grading X) (irrelevant_ne_bot X)) rfl).eq
      (genericPoint_spec _)
  rw [← h]
  rfl

end Subvariety

end DeJongEPBridge
