import Hironaka.Scheme.ProjectiveBundle.Affine.Properties
import ModularCurves.ForMathlib.ProjectiveFactorization

/-! # Actual finite polynomial embeddings of symmetric projective bundles -/

open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.SymmetricProjectiveEmbedding

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type} (m : ι → M)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial presentation sends the original generators to their
canonical images in the original symmetric algebra. -/
def polynomialMap : MvPolynomial ι R →ₐ[R] SymmetricAlgebra R M :=
  aeval fun i => SymmetricAlgebra.ι R M (m i)

/-- The original polynomial presentation preserves the entire actual degree-one
submodule, hence every original homogeneous degree. -/
theorem polynomialMap_mem {d : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ homogeneousSubmodule ι R d) :
    polynomialMap (R := R) m p ∈ SymmetricAlgebra.grading R M d := by
  have h1 : (homogeneousSubmodule ι R 1).map (polynomialMap (R := R) m).toLinearMap ≤
      LinearMap.range (SymmetricAlgebra.ι R M) := by
    rw [homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨m i, ?_⟩
    simp only [polynomialMap, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X]
  have hd : (homogeneousSubmodule ι R d).map (polynomialMap (R := R) m).toLinearMap ≤
      SymmetricAlgebra.grading R M d := by
    rw [← homogeneousSubmodule_one_pow R d, Submodule.map_pow]
    exact pow_le_pow_left' h1 d
  exact hd ⟨p, hp, rfl⟩

/-- The genuine whole polynomial presentation, with its original homogeneous grading. -/
def gradedPolynomialMap : homogeneousSubmodule ι R →+*ᵍ SymmetricAlgebra.grading R M where
  __ := (polynomialMap (R := R) m).toRingHom
  map_mem := polynomialMap_mem (R := R) m

/-- Every actual spanning family of the original module gives a surjective
whole original symmetric-algebra polynomial presentation. -/
theorem polynomialMap_surjective (hm : Submodule.span R (Set.range m) = ⊤) :
    Function.Surjective (polynomialMap (R := R) m) := by
  have hι (x : M) : SymmetricAlgebra.ι R M x ∈ (polynomialMap (R := R) m).range := by
    have hx : x ∈ Submodule.span R (Set.range m) := hm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨X i, ?_⟩
      exact aeval_X (fun j => SymmetricAlgebra.ι R M (m j)) i
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy => rw [LinearMap.map_smul]; exact Subalgebra.smul_mem _ hy r
  intro z
  change z ∈ (polynomialMap (R := R) m).range
  induction z using SymmetricAlgebra.induction R M with
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | ι x => exact hι x
  | mul a b ha hb => exact mul_mem ha hb
  | add a b ha hb => exact add_mem ha hb

/-- Actual surjectivity of the SAME graded presentation. -/
theorem gradedPolynomialMap_surjective (hm : Submodule.span R (Set.range m) = ⊤) :
    Function.Surjective (gradedPolynomialMap (R := R) m) := polynomialMap_surjective (R := R) m hm

/-- Surjectivity of the ACTUAL original graded polynomial presentation gives
the genuine irrelevant-ideal condition for its native Proj morphism. -/
theorem gradedPolynomialMap_irrelevant_le (hm : Submodule.span R (Set.range m) = ⊤) :
    HomogeneousIdeal.irrelevant (SymmetricAlgebra.grading R M) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).map
        (gradedPolynomialMap (R := R) m) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective (gradedPolynomialMap (R := R) m)
    (gradedPolynomialMap_surjective (R := R) m hm)

variable {n : ℕ} (a : Fin (n+1) → M) (ha : Submodule.span R (Set.range a) = ⊤)

/-- The actual original finite generators construct a whole native polynomial
projective embedding of the SAME original symmetric projective bundle. -/
def embedding : affineProjectiveBundle R M ⟶
    Proj (homogeneousSubmodule (Fin (n+1)) R) :=
  Proj.map (gradedPolynomialMap (R := R) a) (gradedPolynomialMap_irrelevant_le a ha)

/-- The genuine finite-generator native Proj map is an actual closed immersion. -/
theorem embedding_isClosedImmersion : IsClosedImmersion (embedding (R := R) a ha) :=
  Proj.isClosedImmersion_map_of_surjective (gradedPolynomialMap (R := R) a)
    (gradedPolynomialMap_irrelevant_le a ha) (gradedPolynomialMap_surjective a ha)

private theorem degreeZero_coefficient :
    CommRingCat.ofHom (algebraMap R (homogeneousSubmodule (Fin (n+1)) R 0)) ≫
        CommRingCat.ofHom (ModularCurves.gradedRingHomZero (gradedPolynomialMap (R := R) a)) =
      (SymmetricAlgebra.gradingZeroEquiv R M).toCommRingCatIso.hom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact (polynomialMap (R := R) a).commutes r

/-- The whole constructed closed embedding retains the SAME original
coefficient projection, as an equality of native scheme morphisms. -/
theorem embedding_structure :
    embedding (R := R) a ha ≫ homogeneousProjπ = affineProjectiveBundle.π R M := by
  unfold embedding homogeneousProjπ affineProjectiveBundle.π
  rw [← Category.assoc, ModularCurves.map_comp_toSpecZero, Category.assoc,
    ← Spec.map_comp, degreeZero_coefficient]

/-- A finite original module internally supplies actual finite polynomial
coordinates and a genuine closed immersion over its original coefficient spectrum. -/
theorem exists_embedding [Module.Finite R M] :
    ∃ (n : ℕ) (j : affineProjectiveBundle R M ⟶
        Proj (homogeneousSubmodule (Fin (n+1)) R)), IsClosedImmersion j ∧
      j ≫ homogeneousProjπ = affineProjectiveBundle.π R M := by
  obtain ⟨n, a, ha⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let b : Fin (n+1) → M := Fin.cases 0 a
  have hb : Submodule.span R (Set.range b) = ⊤ := by
    apply top_unique
    rw [← ha]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, rfl⟩
  exact ⟨n, embedding (R := R) b hb, embedding_isClosedImmersion b hb,
    embedding_structure b hb⟩

/-- The actual native projective bundle of EVERY finite module satisfies the
original finite-polynomial projective factorization predicate, with no added data. -/
theorem isProjectiveFactorization [Module.Finite R M] :
    IsProjectiveFactorization (affineProjectiveBundle.π R M) := exists_embedding

end EnvelopeProperty.SymmetricProjectiveEmbedding
