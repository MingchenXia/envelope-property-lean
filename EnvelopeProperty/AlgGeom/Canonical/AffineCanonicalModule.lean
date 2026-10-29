/-
Mathlib-only proof port. Original source: EnvelopeProperty/ComplexGeometry/Schemes/AffineCanonicalModule.lean
Upstream SHA256: ed9e5ef593d0addec679c5eb0cfed0a18e9290a55c9083c1bdceb3874aca0606
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Local canonical and anticanonical modules

The canonical module here is the actual top exterior power of the relative
Kähler differentials. Its anticanonical module is its actual linear dual.
A finite differential basis produces their one-element bases. The polynomial
model supplies that differential basis from Mathlib, without an extra premise.
Global gluing, ampleness and intersection degree are separate constructions.
-/

open Module

namespace EnvelopeProperty.CanonicalGeometry

variable (K A : Type*) [CommRing K] [CommRing A] [Algebra K A]

/-- The relative canonical module on an affine chart of differential rank `n`. -/
noncomputable abbrev affineCanonicalModule (n : ℕ) := ⋀[A]^n (KaehlerDifferential K A)

/-- The anticanonical module is the actual dual of the top differential wedge. -/
abbrev affineAnticanonicalModule (n : ℕ) := Module.Dual A (affineCanonicalModule K A n)

variable {K A}

/-- The full set is the unique cardinal-`n` subset of `Fin n`, also for `n = 0`. -/
def topExteriorIndexEquiv (n : ℕ) : Set.powersetCard (Fin n) n ≃ Unit where
  toFun _ := Unit.unit
  invFun _ := ⟨Finset.univ, by simp [Set.powersetCard.mem_iff]⟩
  left_inv s := by
    apply Subtype.ext
    exact (Finset.eq_univ_of_card s.val (s.property.trans (Fintype.card_fin n).symm)).symm
  right_inv _ := rfl

/-- The ordered enumeration of the full exterior index is the identity. -/
theorem topExteriorIndexEquiv_symm_orderEmb (n : ℕ) :
    Set.powersetCard.ofFinEmbEquiv.symm ((topExteriorIndexEquiv n).symm Unit.unit) =
      OrderEmbedding.id (Fin n) := by
  exact (Finset.orderEmbOfFin_unique' (by simp) (fun i : Fin n => Finset.mem_univ i)).symm

/-- The actual top exterior basis has just the full differential wedge. -/
noncomputable def affineCanonicalBasis {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Basis Unit A (affineCanonicalModule K A n) :=
  (b.exteriorPower n).reindex (topExteriorIndexEquiv n)

/-- The distinguished generator of the actual canonical module. -/
noncomputable def affineCanonicalGenerator {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) : affineCanonicalModule K A n :=
  affineCanonicalBasis b Unit.unit

/-- The produced canonical generator is the actual ordered top wedge of the basis. -/
theorem affineCanonicalGenerator_eq_wedge {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    affineCanonicalGenerator b = exteriorPower.ιMulti A n b := by
  simp [affineCanonicalGenerator, affineCanonicalBasis, Basis.reindex_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    topExteriorIndexEquiv_symm_orderEmb]

/-- The canonical module is explicitly trivialized by its top-wedge coordinate. -/
noncomputable def affineCanonicalTrivialization {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    affineCanonicalModule K A n ≃ₗ[A] A :=
  (affineCanonicalBasis b).repr.trans (Finsupp.uniqueLinearEquiv A A Unit.unit)

/-- Top-wedge coordinates are the determinant of the actual differential coordinates. -/
theorem affineCanonicalTrivialization_apply_wedge {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A))
    (v : Fin n → KaehlerDifferential K A) :
    affineCanonicalTrivialization b (exteriorPower.ιMulti A n v) =
      (Matrix.of fun i j => b.coord j (v i)).det := by
  simp [affineCanonicalTrivialization, affineCanonicalBasis,
    exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti, topExteriorIndexEquiv_symm_orderEmb]

/-- The actual dual basis trivializes the anticanonical module. -/
noncomputable def affineAnticanonicalBasis {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Basis Unit A (affineAnticanonicalModule K A n) :=
  (affineCanonicalBasis b).dualBasis

/-- The normalized functional dual to the top differential wedge. -/
noncomputable def affineAnticanonicalGenerator {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) : affineAnticanonicalModule K A n :=
  affineAnticanonicalBasis b Unit.unit

/-- The anticanonical module is explicitly trivialized by evaluation on the top wedge. -/
noncomputable def affineAnticanonicalTrivialization {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    affineAnticanonicalModule K A n ≃ₗ[A] A :=
  (affineAnticanonicalBasis b).repr.trans (Finsupp.uniqueLinearEquiv A A Unit.unit)

@[simp]
theorem affineCanonicalTrivialization_generator {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    affineCanonicalTrivialization b (affineCanonicalGenerator b) = 1 := by
  simp [affineCanonicalTrivialization, affineCanonicalGenerator]

@[simp]
theorem affineAnticanonicalGenerator_apply_generator {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    affineAnticanonicalGenerator b (affineCanonicalGenerator b) = 1 := by
  simp [affineAnticanonicalGenerator, affineAnticanonicalBasis,
    affineCanonicalGenerator]

@[simp]
theorem affineAnticanonicalTrivialization_apply {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A))
    (f : affineAnticanonicalModule K A n) :
    affineAnticanonicalTrivialization b f = f (affineCanonicalGenerator b) := by
  simp [affineAnticanonicalTrivialization, affineAnticanonicalBasis,
    affineCanonicalGenerator]

/-- Every top differential wedge is the unique scalar multiple of the produced generator. -/
theorem affineCanonical_eq_smul_generator {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) (x : affineCanonicalModule K A n) :
    x = affineCanonicalTrivialization b x • affineCanonicalGenerator b := by
  simpa [affineCanonicalTrivialization, affineCanonicalGenerator] using
    ((affineCanonicalBasis b).sum_repr x).symm

/-- Every actual anticanonical functional is determined by its value on the top wedge. -/
theorem affineAnticanonical_eq_smul_generator {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) (f : affineAnticanonicalModule K A n) :
    f = f (affineCanonicalGenerator b) • affineAnticanonicalGenerator b := by
  simpa [affineAnticanonicalGenerator, affineAnticanonicalBasis,
    affineCanonicalGenerator] using ((affineAnticanonicalBasis b).sum_repr f).symm

/-- The scalar changing two actual canonical generators is a unit.
This is a local transition prerequisite, obtained from the actual bases. -/
theorem affineCanonical_transition_isUnit {n : ℕ}
    (b b' : Basis (Fin n) A (KaehlerDifferential K A)) :
    IsUnit (affineCanonicalTrivialization b (affineCanonicalGenerator b')) := by
  have h := affineCanonical_eq_smul_generator b' (affineCanonicalGenerator b)
  rw [affineCanonical_eq_smul_generator b (affineCanonicalGenerator b')] at h
  have hc := congrArg (affineCanonicalTrivialization b) h
  simp only [affineCanonicalTrivialization_generator, map_smul, smul_eq_mul] at hc
  exact IsUnit.of_mul_eq_one
    (affineCanonicalTrivialization b' (affineCanonicalGenerator b))
    (by simpa only [one_mul, mul_comm] using hc.symm)

/-- The determinant transition computed from actual differential bases is invertible. -/
theorem affineCanonical_transition_det_isUnit {n : ℕ}
    (b b' : Basis (Fin n) A (KaehlerDifferential K A)) :
    IsUnit ((Matrix.of fun i j => b.coord j (b' i)).det) := by
  simpa only [affineCanonicalGenerator_eq_wedge, affineCanonicalTrivialization_apply_wedge]
    using affineCanonical_transition_isUnit b b'

/-- An actual finite differential basis produces a finite free canonical module. -/
theorem affineCanonical_finite_free {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Module.Finite A (affineCanonicalModule K A n) ∧
      Module.Free A (affineCanonicalModule K A n) :=
  ⟨Module.Finite.of_basis (affineCanonicalBasis b),
    Module.Free.of_basis (affineCanonicalBasis b)⟩

/-- The actual dual top-wedge module is finite free. -/
theorem affineAnticanonical_finite_free {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Module.Finite A (affineAnticanonicalModule K A n) ∧
      Module.Free A (affineAnticanonicalModule K A n) :=
  ⟨Module.Finite.of_basis (affineAnticanonicalBasis b),
    Module.Free.of_basis (affineAnticanonicalBasis b)⟩

/-- Its produced one-element basis gives canonical rank one. -/
theorem affineCanonical_finrank [Nontrivial A] {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Module.finrank A (affineCanonicalModule K A n) = 1 := by
  simpa using Module.finrank_eq_card_basis (affineCanonicalBasis b)

/-- Its produced dual basis gives anticanonical rank one. -/
theorem affineAnticanonical_finrank [Nontrivial A] {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Module.finrank A (affineAnticanonicalModule K A n) = 1 := by
  simpa using Module.finrank_eq_card_basis (affineAnticanonicalBasis b)

section BaseChange

variable {B : Type*} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

/-- An actual differential basis transports through the actual formally étale differential
base-change isomorphism. -/
noncomputable def affineDifferentialBasisOfFormallyEtale [Algebra.FormallyEtale A B]
    {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Basis (Fin n) B (KaehlerDifferential K B) :=
  (b.baseChange B).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A B)

@[simp]
theorem affineDifferentialBasisOfFormallyEtale_apply [Algebra.FormallyEtale A B]
    {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential K A)) (i : Fin n) :
    affineDifferentialBasisOfFormallyEtale b i = KaehlerDifferential.map K K A B (b i) := by
  simp [affineDifferentialBasisOfFormallyEtale, KaehlerDifferential.mapBaseChange_tmul]

/-- Localizing the actual differential module produces its actual localized basis. -/
noncomputable def affineDifferentialBasisOfLocalization (S : Submonoid A) [IsLocalization S B]
    {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential K A)) :
    Basis (Fin n) B (KaehlerDifferential K B) := by
  letI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  exact affineDifferentialBasisOfFormallyEtale b

end BaseChange

variable (K)

/-- Polynomial affine space supplies an actual differential basis `dXᵢ`. -/
noncomputable def polynomialCanonicalBasis (n : ℕ) :
    Basis Unit (MvPolynomial (Fin n) K)
      (affineCanonicalModule K (MvPolynomial (Fin n) K) n) :=
  affineCanonicalBasis (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- The canonical generator of polynomial affine space. -/
noncomputable def polynomialCanonicalGenerator (n : ℕ) :
    affineCanonicalModule K (MvPolynomial (Fin n) K) n :=
  affineCanonicalGenerator (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- The polynomial canonical generator is literally `dX₀ ∧... ∧ dXₙ₋₁`. -/
theorem polynomialCanonicalGenerator_eq_wedge (n : ℕ) :
    polynomialCanonicalGenerator K n =
      exteriorPower.ιMulti (MvPolynomial (Fin n) K) n
        (fun i => KaehlerDifferential.D K (MvPolynomial (Fin n) K) (MvPolynomial.X i)) := by
  rw [polynomialCanonicalGenerator, affineCanonicalGenerator_eq_wedge]
  congr 1
  funext i
  exact KaehlerDifferential.mvPolynomialBasis_apply K (Fin n) i

/-- The actual dual basis of the polynomial top differential wedge. -/
noncomputable def polynomialAnticanonicalBasis (n : ℕ) :
    Basis Unit (MvPolynomial (Fin n) K)
      (affineAnticanonicalModule K (MvPolynomial (Fin n) K) n) :=
  affineAnticanonicalBasis (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- The normalized anticanonical generator for polynomial affine space. -/
noncomputable def polynomialAnticanonicalGenerator (n : ℕ) :
    affineAnticanonicalModule K (MvPolynomial (Fin n) K) n :=
  affineAnticanonicalGenerator (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- Polynomial affine space has an actual finite free canonical module. -/
theorem polynomialCanonical_finite_free (n : ℕ) :
    Module.Finite (MvPolynomial (Fin n) K)
      (affineCanonicalModule K (MvPolynomial (Fin n) K) n) ∧
    Module.Free (MvPolynomial (Fin n) K)
      (affineCanonicalModule K (MvPolynomial (Fin n) K) n) :=
  affineCanonical_finite_free (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- Polynomial affine space has an actual finite free anticanonical module. -/
theorem polynomialAnticanonical_finite_free (n : ℕ) :
    Module.Finite (MvPolynomial (Fin n) K)
      (affineAnticanonicalModule K (MvPolynomial (Fin n) K) n) ∧
    Module.Free (MvPolynomial (Fin n) K)
      (affineAnticanonicalModule K (MvPolynomial (Fin n) K) n) :=
  affineAnticanonical_finite_free (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- Canonical rank one is derived for polynomial affine space. -/
theorem polynomialCanonical_finrank [Nontrivial K] (n : ℕ) :
    Module.finrank (MvPolynomial (Fin n) K)
      (affineCanonicalModule K (MvPolynomial (Fin n) K) n) = 1 :=
  affineCanonical_finrank (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- Anticanonical rank one is derived for polynomial affine space. -/
theorem polynomialAnticanonical_finrank [Nontrivial K] (n : ℕ) :
    Module.finrank (MvPolynomial (Fin n) K)
      (affineAnticanonicalModule K (MvPolynomial (Fin n) K) n) = 1 :=
  affineAnticanonical_finrank (KaehlerDifferential.mvPolynomialBasis K (Fin n))

@[simp]
theorem polynomialAnticanonicalGenerator_apply_generator (n : ℕ) :
    polynomialAnticanonicalGenerator K n (polynomialCanonicalGenerator K n) = 1 :=
  affineAnticanonicalGenerator_apply_generator (KaehlerDifferential.mvPolynomialBasis K (Fin n))

section PolynomialCharts

variable (B : Type*) [CommRing B] [Algebra K B]

/-- An actual formally étale chart over polynomial affine space supplies the differential
basis; it is not an assumed canonical line. -/
noncomputable def polynomialEtaleDifferentialBasis (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) B]
    [IsScalarTower K (MvPolynomial (Fin n) K) B]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) K) B] :
    Basis (Fin n) B (KaehlerDifferential K B) :=
  affineDifferentialBasisOfFormallyEtale (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- The étale chart basis is the actual differential of its coordinate functions. -/
theorem polynomialEtaleDifferentialBasis_apply (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) B]
    [IsScalarTower K (MvPolynomial (Fin n) K) B]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) K) B] (i : Fin n) :
    polynomialEtaleDifferentialBasis K B n i =
      KaehlerDifferential.D K B (algebraMap (MvPolynomial (Fin n) K) B (MvPolynomial.X i)) := by
  simp [polynomialEtaleDifferentialBasis, KaehlerDifferential.map_D]

/-- Actual étale polynomial coordinates produce finite free canonical and anticanonical
modules of rank one. -/
theorem polynomialEtale_canonical_anticanonical [Nontrivial B] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) B]
    [IsScalarTower K (MvPolynomial (Fin n) K) B]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) K) B] :
    (Module.Finite B (affineCanonicalModule K B n) ∧
      Module.Free B (affineCanonicalModule K B n)) ∧
    (Module.Finite B (affineAnticanonicalModule K B n) ∧
      Module.Free B (affineAnticanonicalModule K B n)) ∧
    Module.finrank B (affineCanonicalModule K B n) = 1 ∧
    Module.finrank B (affineAnticanonicalModule K B n) = 1 :=
  ⟨affineCanonical_finite_free (polynomialEtaleDifferentialBasis K B n),
    affineAnticanonical_finite_free (polynomialEtaleDifferentialBasis K B n),
    affineCanonical_finrank (polynomialEtaleDifferentialBasis K B n),
    affineAnticanonical_finrank (polynomialEtaleDifferentialBasis K B n)⟩

/-- Localization of polynomial affine space supplies an actual differential basis. -/
noncomputable def polynomialLocalizationDifferentialBasis (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) B]
    [IsScalarTower K (MvPolynomial (Fin n) K) B]
    (S : Submonoid (MvPolynomial (Fin n) K)) [IsLocalization S B] :
    Basis (Fin n) B (KaehlerDifferential K B) :=
  affineDifferentialBasisOfLocalization S (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- Actual polynomial localization charts produce finite free canonical and anticanonical
modules of rank one. -/
theorem polynomialLocalization_canonical_anticanonical [Nontrivial B] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) B]
    [IsScalarTower K (MvPolynomial (Fin n) K) B]
    (S : Submonoid (MvPolynomial (Fin n) K)) [IsLocalization S B] :
    (Module.Finite B (affineCanonicalModule K B n) ∧
      Module.Free B (affineCanonicalModule K B n)) ∧
    (Module.Finite B (affineAnticanonicalModule K B n) ∧
      Module.Free B (affineAnticanonicalModule K B n)) ∧
    Module.finrank B (affineCanonicalModule K B n) = 1 ∧
    Module.finrank B (affineAnticanonicalModule K B n) = 1 :=
  ⟨affineCanonical_finite_free (polynomialLocalizationDifferentialBasis K B n S),
    affineAnticanonical_finite_free (polynomialLocalizationDifferentialBasis K B n S),
    affineCanonical_finrank (polynomialLocalizationDifferentialBasis K B n S),
    affineAnticanonical_finrank (polynomialLocalizationDifferentialBasis K B n S)⟩

end PolynomialCharts

end EnvelopeProperty.CanonicalGeometry
