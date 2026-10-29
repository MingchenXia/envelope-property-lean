/-
Mathlib-only proof port. Original source: EnvelopeProperty/ComplexGeometry/Schemes/SmoothCanonicalCharts.lean
Upstream SHA256: 90474089f62774ff67c662d58c9787fc1cd34a5232009957d7bdbba0503b03dc
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalModule
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Data.Fintype.EquivFin

/-! # Canonical frames from actual standard-smooth charts

The differential basis is derived from the actual polynomial presentation and
its invertible evaluated Jacobian. No differential basis or canonical line is
assumed. Scheme smoothness supplies genuine affine chart neighborhoods; the
comparison with a sheaf on those neighborhoods is a separate construction.
-/

open Module Algebra AlgebraicGeometry

namespace EnvelopeProperty.CanonicalGeometry

variable {K A I J : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- The complement of the selected Jacobian coordinates has cardinality equal
to the dimension of the actual finite presentation. -/
noncomputable def submersiveFreeIndexEquiv [Finite I] [Finite J]
    (P : SubmersivePresentation K A I J) :
    ((Set.range P.map)ᶜ : Set I) ≃ Fin P.dimension := by
  classical
  letI := Fintype.ofFinite I
  letI := Fintype.ofFinite J
  apply Fintype.equivFinOfCardEq
  simp only [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj,
    Presentation.dimension, Nat.card_eq_fintype_card]

/-- The actual Jacobian-unit presentation produces a differential basis of its
relative dimension, using precisely the unselected coordinate differentials. -/
noncomputable def submersiveDifferentialBasis [Finite I] [Finite J]
    (P : SubmersivePresentation K A I J) :
    Basis (Fin P.dimension) A (KaehlerDifferential K A) :=
  P.basisKaehler.reindex (submersiveFreeIndexEquiv P)

@[simp]
theorem submersiveDifferentialBasis_apply [Finite I] [Finite J]
    (P : SubmersivePresentation K A I J) (i : Fin P.dimension) :
    submersiveDifferentialBasis P i =
      KaehlerDifferential.D K A (P.val ((submersiveFreeIndexEquiv P).symm i)) := by
  simp [submersiveDifferentialBasis]

/-- Freeness and finite generation are consequences of the Jacobian construction. -/
theorem submersiveDifferentials_finite_free [Finite I] [Finite J]
    (P : SubmersivePresentation K A I J) :
    Module.Finite A (KaehlerDifferential K A) ∧ Module.Free A (KaehlerDifferential K A) :=
  ⟨Module.Finite.of_basis (submersiveDifferentialBasis P),
    Module.Free.of_basis (submersiveDifferentialBasis P)⟩

/-- The actual differential module has the presentation's relative dimension. -/
theorem submersiveDifferentials_finrank [Nontrivial A] [Finite I] [Finite J]
    (P : SubmersivePresentation K A I J) :
    Module.finrank A (KaehlerDifferential K A) = P.dimension := by
  simpa using Module.finrank_eq_card_basis (submersiveDifferentialBasis P)

/-- A genuine presentation with `n+r` variables and `r` equations has dimension `n`. -/
theorem jacobianPresentation_dimension {n r : ℕ}
    (P : PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) :
    P.dimension = n := by
  simp [Presentation.dimension]

/-- The actual evaluated Jacobian determinant, rather than a basis premise,
produces the rank-`n` Kähler basis. -/
noncomputable def jacobianDifferentialBasis {n r : ℕ}
    (P : PreSubmersivePresentation K A (Fin (n + r)) (Fin r))
    (hJ : IsUnit P.jacobian) : Basis (Fin n) A (KaehlerDifferential K A) :=
  (submersiveDifferentialBasis
    ({ toPreSubmersivePresentation := P, jacobian_isUnit := hJ } :
      SubmersivePresentation K A (Fin (n + r)) (Fin r))).reindex
    (finCongr (jacobianPresentation_dimension P))

/-- Every derived Jacobian basis vector is the differential of an actual
unselected presentation coordinate. -/
theorem jacobianDifferentialBasis_is_coordinate {n r : ℕ}
    (P : PreSubmersivePresentation K A (Fin (n + r)) (Fin r))
    (hJ : IsUnit P.jacobian) (i : Fin n) :
    ∃ j : Fin (n + r), j ∉ Set.range P.map ∧
      jacobianDifferentialBasis P hJ i = KaehlerDifferential.D K A (P.val j) := by
  let Q : SubmersivePresentation K A (Fin (n + r)) (Fin r) :=
    { toPreSubmersivePresentation := P, jacobian_isUnit := hJ }
  let j := (submersiveFreeIndexEquiv Q).symm
    ((finCongr (jacobianPresentation_dimension P)).symm i)
  refine ⟨j.val, j.property, ?_⟩
  dsimp only [jacobianDifferentialBasis]
  rw [Basis.reindex_apply, submersiveDifferentialBasis_apply]

/-- The actual top differential wedge has a concrete frame from Jacobian data. -/
noncomputable def jacobianCanonicalFrame {n r : ℕ}
    (P : PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hJ : IsUnit P.jacobian) :
    affineCanonicalModule K A n ≃ₗ[A] A :=
  affineCanonicalTrivialization (jacobianDifferentialBasis P hJ)

/-- Its actual linear dual has the evaluation frame from the same Jacobian data. -/
noncomputable def jacobianAnticanonicalFrame {n r : ℕ}
    (P : PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hJ : IsUnit P.jacobian) :
    affineAnticanonicalModule K A n ≃ₗ[A] A :=
  affineAnticanonicalTrivialization (jacobianDifferentialBasis P hJ)

/-- An invertible actual Jacobian derives finite free rank-one top-wedge and dual modules. -/
theorem jacobian_canonical_anticanonical [Nontrivial A] {n r : ℕ}
    (P : PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hJ : IsUnit P.jacobian) :
    (Module.Finite A (affineCanonicalModule K A n) ∧
      Module.Free A (affineCanonicalModule K A n)) ∧
    (Module.Finite A (affineAnticanonicalModule K A n) ∧
      Module.Free A (affineAnticanonicalModule K A n)) ∧
    Module.finrank A (affineCanonicalModule K A n) = 1 ∧
    Module.finrank A (affineAnticanonicalModule K A n) = 1 :=
  ⟨affineCanonical_finite_free (jacobianDifferentialBasis P hJ),
    affineAnticanonical_finite_free (jacobianDifferentialBasis P hJ),
    affineCanonical_finrank (jacobianDifferentialBasis P hJ),
    affineAnticanonical_finrank (jacobianDifferentialBasis P hJ)⟩

/-- The determinant transition between actual smooth coordinate bases is a unit. -/
theorem jacobian_canonical_transition_det_isUnit {n r s : ℕ}
    (P : PreSubmersivePresentation K A (Fin (n + r)) (Fin r)) (hP : IsUnit P.jacobian)
    (Q : PreSubmersivePresentation K A (Fin (n + s)) (Fin s)) (hQ : IsUnit Q.jacobian) :
    IsUnit ((Matrix.of fun i j =>
      (jacobianDifferentialBasis P hP).coord j (jacobianDifferentialBasis Q hQ i)).det) :=
  affineCanonical_transition_det_isUnit (jacobianDifferentialBasis P hP)
    (jacobianDifferentialBasis Q hQ)

variable (K A)

/-- The actual standard-smooth presentation produces a rank-indexed differential basis. -/
theorem exists_standardSmoothDifferentialBasis (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    Nonempty (Basis (Fin n) A (KaehlerDifferential K A)) := by
  obtain ⟨I, J, hJ, hI, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := K) (S := A)
  let := hI
  let := hJ
  exact ⟨(submersiveDifferentialBasis P).reindex (finCongr hP)⟩

/-- Select the actual basis derived from the standard-smooth presentation. -/
noncomputable def standardSmoothDifferentialBasis (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    Basis (Fin n) A (KaehlerDifferential K A) :=
  Classical.choice (exists_standardSmoothDifferentialBasis K A n)

/-- The actual relative differential module on a standard-smooth chart is finite free. -/
theorem standardSmoothDifferentials_finite_free (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    Module.Finite A (KaehlerDifferential K A) ∧ Module.Free A (KaehlerDifferential K A) :=
  ⟨Module.Finite.of_basis (standardSmoothDifferentialBasis K A n),
    Module.Free.of_basis (standardSmoothDifferentialBasis K A n)⟩

/-- The derived basis gives the actual chart differential rank. -/
theorem standardSmoothDifferentials_finrank [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    Module.finrank A (KaehlerDifferential K A) = n := by
  simpa using Module.finrank_eq_card_basis (standardSmoothDifferentialBasis K A n)

/-- A canonical frame is derived on the actual standard-smooth coordinate ring. -/
noncomputable def standardSmoothCanonicalFrame (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    affineCanonicalModule K A n ≃ₗ[A] A :=
  affineCanonicalTrivialization (standardSmoothDifferentialBasis K A n)

/-- The corresponding anticanonical frame is an actual linear-dual frame. -/
noncomputable def standardSmoothAnticanonicalFrame (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    affineAnticanonicalModule K A n ≃ₗ[A] A :=
  affineAnticanonicalTrivialization (standardSmoothDifferentialBasis K A n)

/-- Standard smoothness derives finite free rank-one canonical and dual modules. -/
theorem standardSmooth_canonical_anticanonical [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    (Module.Finite A (affineCanonicalModule K A n) ∧
      Module.Free A (affineCanonicalModule K A n)) ∧
    (Module.Finite A (affineAnticanonicalModule K A n) ∧
      Module.Free A (affineAnticanonicalModule K A n)) ∧
    Module.finrank A (affineCanonicalModule K A n) = 1 ∧
    Module.finrank A (affineAnticanonicalModule K A n) = 1 :=
  ⟨affineCanonical_finite_free (standardSmoothDifferentialBasis K A n),
    affineAnticanonical_finite_free (standardSmoothDifferentialBasis K A n),
    affineCanonical_finrank (standardSmoothDifferentialBasis K A n),
    affineAnticanonical_finrank (standardSmoothDifferentialBasis K A n)⟩

section SchemeCharts

open CategoryTheory

variable {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)

/-- Smoothness of relative dimension `n` produces actual affine chart neighborhoods
with a derived differential basis and actual canonical and anticanonical frames. -/
theorem smoothRelativeDimension_chart_frames [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      letI := (f.appLE U V e).hom.toAlgebra
      Nonempty (Basis (Fin n) Γ(X, V) (KaehlerDifferential Γ(Y, U) Γ(X, V))) ∧
      Nonempty (affineCanonicalModule Γ(Y, U) Γ(X, V) n ≃ₗ[Γ(X, V)] Γ(X, V)) ∧
      Nonempty (affineAnticanonicalModule Γ(Y, U) Γ(X, V) n ≃ₗ[Γ(X, V)] Γ(X, V)) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  let := (f.appLE U V e).hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) Γ(X, V) := hf
  exact ⟨⟨standardSmoothDifferentialBasis Γ(Y, U) Γ(X, V) n⟩,
    ⟨standardSmoothCanonicalFrame Γ(Y, U) Γ(X, V) n⟩,
    ⟨standardSmoothAnticanonicalFrame Γ(Y, U) Γ(X, V) n⟩⟩

/-- The nonempty affine source charts have differential rank `n` and actual finite free
rank-one canonical and dual modules. These are coordinate-ring claims, before sheaf gluing. -/
theorem smoothRelativeDimension_chart_basis_and_ranks [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
      (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      letI := (f.appLE U V e).hom.toAlgebra
      Nonempty (Basis (Fin n) Γ(X, V) (KaehlerDifferential Γ(Y, U) Γ(X, V))) ∧
      Module.finrank Γ(X, V) (KaehlerDifferential Γ(Y, U) Γ(X, V)) = n ∧
      (Module.Finite Γ(X, V) (affineCanonicalModule Γ(Y, U) Γ(X, V) n) ∧
        Module.Free Γ(X, V) (affineCanonicalModule Γ(Y, U) Γ(X, V) n)) ∧
      (Module.Finite Γ(X, V) (affineAnticanonicalModule Γ(Y, U) Γ(X, V) n) ∧
        Module.Free Γ(X, V) (affineAnticanonicalModule Γ(Y, U) Γ(X, V) n)) ∧
      Module.finrank Γ(X, V) (affineCanonicalModule Γ(Y, U) Γ(X, V) n) = 1 ∧
      Module.finrank Γ(X, V) (affineAnticanonicalModule Γ(Y, U) Γ(X, V) n) = 1 := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  let := (f.appLE U V e).hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) Γ(X, V) := hf
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  exact ⟨⟨standardSmoothDifferentialBasis Γ(Y, U) Γ(X, V) n⟩,
    standardSmoothDifferentials_finrank Γ(Y, U) Γ(X, V) n,
    standardSmooth_canonical_anticanonical Γ(Y, U) Γ(X, V) n⟩

end SchemeCharts

end EnvelopeProperty.CanonicalGeometry
