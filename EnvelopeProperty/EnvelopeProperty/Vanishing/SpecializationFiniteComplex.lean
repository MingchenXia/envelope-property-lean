import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Actual finite-free-complex specialization by a lifted contraction

The determinant of a lifted contracting endomorphism will define the
principal neighborhood where the original finite matrix complex is exact.
-/

open Function

noncomputable section
universe u v w z

namespace EnvelopeProperty.Vanishing.SpecializationFiniteComplex

section Linear

variable {K : Type u} [Field K]
    {A : Type v} [AddCommGroup A] [Module K A]
    {B : Type w} [AddCommGroup B] [Module K B]
    {C : Type z} [AddCommGroup C] [Module K C]

/-- An actual exact complex of vector spaces has a contracting identity
at its middle object; no finite-dimensionality is required here. -/
theorem exists_contraction (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (hex : Exact f g) :
    ∃ (a : B →ₗ[K] A) (b : C →ₗ[K] B), f.comp a + b.comp g = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g.rangeRestrict
    (LinearMap.id : g.range →ₗ[K] g.range) (by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩)
  let b : C →ₗ[K] B := s.comp g.range.subtype.leftInverse
  have hgbg (x : B) : g (b (g x)) = g x := by
    let y : g.range := ⟨g x, ⟨x, rfl⟩⟩
    have hi : g.range.subtype.leftInverse (g x) = y :=
      LinearMap.leftInverse_apply_of_inj g.range.ker_subtype y
    change g (s (g.range.subtype.leftInverse (g x))) = g x
    rw [hi]
    exact congrArg Subtype.val (LinearMap.congr_fun hs y)
  let h : B →ₗ[K] B := LinearMap.id - b.comp g
  have hh (x : B) : h x ∈ f.range := by
    rw [← LinearMap.exact_iff.mp hex]
    change g (x - b (g x)) = 0
    rw [map_sub, hgbg, sub_self]
  obtain ⟨t, ht⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.id : f.range →ₗ[K] f.range) (by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩)
  let a : B →ₗ[K] A := t.comp (h.codRestrict f.range hh)
  refine ⟨a, b, ?_⟩
  ext x
  have hx := congrArg Subtype.val (LinearMap.congr_fun ht ((h.codRestrict f.range hh) x))
  change f (a x) = h x at hx
  change f (a x) + b (g x) = x
  rw [hx]
  exact sub_add_cancel x (b (g x))

/-- A surjective contracting endomorphism forces exactness of the actual
finite-dimensional complex, without a supplied homology comparison. -/
theorem exact_of_surjective_contraction [FiniteDimensional K B]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (hgf : g.comp f = 0)
    (a : B →ₗ[K] A) (b : C →ₗ[K] B)
    (hsurj : Surjective (f.comp a + b.comp g)) : Exact f g := by
  let h : B →ₗ[K] B := f.comp a + b.comp g
  have hstable : f.range ≤ f.range.comap h := by
    rintro _ ⟨x, rfl⟩
    refine ⟨a (f x), ?_⟩
    have hx : g (f x) = 0 := LinearMap.congr_fun hgf x
    change f (a (f x)) = f (a (f x)) + b (g (f x))
    rw [hx, map_zero, add_zero]
  let hQ : (B ⧸ f.range) →ₗ[K] (B ⧸ f.range) := f.range.mapQ f.range h hstable
  have hQsurj : Surjective hQ := by
    intro y
    obtain ⟨y, rfl⟩ := f.range.mkQ_surjective y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨f.range.mkQ x, ?_⟩
    change f.range.mkQ (h x) = f.range.mkQ y
    rw [hx]
  have hQinj : Injective hQ := LinearMap.injective_iff_surjective.mpr hQsurj
  apply LinearMap.exact_of_comp_of_mem_range hgf
  intro x hx
  have hz : hQ (f.range.mkQ x) = 0 := by
    change f.range.mkQ (f (a x) + b (g x)) = 0
    rw [hx, map_zero, add_zero]
    exact (Submodule.Quotient.mk_eq_zero f.range).mpr ⟨a x, rfl⟩
  have hxQ : f.range.mkQ x = 0 := hQinj (by simpa only [map_zero] using hz)
  exact (Submodule.Quotient.mk_eq_zero f.range).mp hxQ

end Linear

section Matrices

variable {R : Type u} [CommRing R] {k : Type v} [Field k]

/-- A surjective coefficient map lifts each entry of the original matrix. -/
theorem exists_matrix_lift (π : R →+* k) (hπ : Surjective π)
    {m : Type w} {n : Type z} (A : Matrix m n k) :
    ∃ B : Matrix m n R, B.map π = A := by
  classical
  choose b hb using fun i j => hπ (A i j)
  exact ⟨b, funext fun i => funext fun j => hb i j⟩

/-- Exactness at a closed field-valued fibre of an original finite matrix
complex persists over every field point in one actual principal open.
The scalar defining that open and all its coefficient maps are constructed. -/
theorem exists_field_exactness_neighborhood
    {α β γ : Type w} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (π : R →+* k) (hπ : Surjective π)
    (F : Matrix β α R) (G : Matrix γ β R) (hGF : G * F = 0)
    (hex : Exact (Matrix.toLin' (F.map π)) (Matrix.toLin' (G.map π))) :
    ∃ r : R, π r = 1 ∧ ∀ (K : Type z) [Field K] (φ : R →+* K), φ r ≠ 0 →
      Exact (Matrix.toLin' (F.map φ)) (Matrix.toLin' (G.map φ)) := by
  classical
  obtain ⟨s, t, hst⟩ := exists_contraction (Matrix.toLin' (F.map π))
    (Matrix.toLin' (G.map π)) hex
  have hstM : F.map π * LinearMap.toMatrix' s +
      LinearMap.toMatrix' t * G.map π = 1 := by
    have h := congrArg LinearMap.toMatrix' hst
    simpa only [map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using h
  obtain ⟨S, hS⟩ := exists_matrix_lift π hπ (LinearMap.toMatrix' s)
  obtain ⟨T, hT⟩ := exists_matrix_lift π hπ (LinearMap.toMatrix' t)
  let H : Matrix β β R := F * S + T * G
  have hHπ : H.map π = 1 := by
    change π.mapMatrix (F * S + T * G) = 1
    rw [map_add]
    change (F * S).map π + (T * G).map π = 1
    rw [Matrix.map_mul, Matrix.map_mul, hS, hT]
    exact hstM
  have hdet : π H.det = 1 := by
    rw [RingHom.map_det]
    change (H.map π).det = 1
    rw [hHπ, Matrix.det_one]
  refine ⟨H.det, hdet, ?_⟩
  intro K _ φ hφ
  have hHunit : IsUnit (H.map φ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    change (φ.mapMatrix H).det ≠ 0
    rw [← RingHom.map_det]
    exact hφ
  have hsurj : Surjective (Matrix.toLin' (H.map φ)) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hHunit
  have hGφF : G.map φ * F.map φ = 0 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    exact map_zero φ
  apply exact_of_surjective_contraction (Matrix.toLin' (F.map φ))
    (Matrix.toLin' (G.map φ))
    (by rw [← Matrix.toLin'_mul, hGφF, map_zero])
    (Matrix.toLin' (S.map φ)) (Matrix.toLin' (T.map φ))
  have hHφ : H.map φ = F.map φ * S.map φ + T.map φ * G.map φ := by
    change φ.mapMatrix (F * S + T * G) = _
    rw [map_add]
    change (F * S).map φ + (T * G).map φ = _
    rw [Matrix.map_mul, Matrix.map_mul]
  rw [hHφ] at hsurj
  simpa only [map_add, Matrix.toLin'_mul] using hsurj

/-- A finite family of original three-term free complexes admits one
principal open on which all field fibres are exact simultaneously. -/
theorem exists_uniform_field_exactness_neighborhood
    {ι : Type w} [Fintype ι] (a b c : ι → ℕ)
    (π : R →+* k) (hπ : Surjective π)
    (F : ∀ i, Matrix (Fin (b i)) (Fin (a i)) R)
    (G : ∀ i, Matrix (Fin (c i)) (Fin (b i)) R)
    (hGF : ∀ i, G i * F i = 0)
    (hex : ∀ i, Exact (Matrix.toLin' ((F i).map π)) (Matrix.toLin' ((G i).map π))) :
    ∃ r : R, π r = 1 ∧ ∀ (K : Type z) [Field K] (φ : R →+* K), φ r ≠ 0 →
      ∀ i, Exact (Matrix.toLin' ((F i).map φ)) (Matrix.toLin' ((G i).map φ)) := by
  classical
  choose r hr hExact using fun i =>
    exists_field_exactness_neighborhood π hπ (F i) (G i) (hGF i) (hex i)
  refine ⟨∏ i, r i, ?_, ?_⟩
  · simp only [map_prod, hr, Finset.prod_const_one]
  · intro K _ φ hφ i
    have hi : φ (r i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hφ)) i (Finset.mem_univ i)
    exact hExact i K φ hi

/-- The original generic matrix complex is exact if its original residue
complex is exact. The only coefficient map used at the generic point is
the canonical map to the supplied fraction field. -/
theorem generic_exact_of_residue_exact [IsDomain R]
    {α β γ : Type w} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (π : R →+* k) (hπ : Surjective π)
    (F : Matrix β α R) (G : Matrix γ β R) (hGF : G * F = 0)
    (hex : Exact (Matrix.toLin' (F.map π)) (Matrix.toLin' (G.map π)))
    (K : Type z) [Field K] [Algebra R K] [IsFractionRing R K] :
    Exact (Matrix.toLin' (F.map (algebraMap R K)))
      (Matrix.toLin' (G.map (algebraMap R K))) := by
  obtain ⟨r, hr, hExact⟩ := exists_field_exactness_neighborhood π hπ F G hGF hex
  apply hExact K (algebraMap R K)
  intro h
  have hrzero : r = 0 :=
    IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm)
  have hz : (0 : k) = 1 := by simpa only [hrzero, map_zero] using hr
  exact zero_ne_one hz

end Matrices

end EnvelopeProperty.Vanishing.SpecializationFiniteComplex
