import EnvelopeProperty.Cartier.SmoothEtaleAffineCover
import EnvelopeProperty.Cartier.EtaleSchemeSectionDifferential
import EnvelopeProperty.Char0.AffineOpenChartMaps

/-! # Genuine original smooth etale coordinate affine opens form a whole topological basis -/
noncomputable section
namespace EnvelopeProperty.Cartier.SmoothEtaleAffineBasis
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The SAME original restriction to an actual affine principal open is genuinely etale. -/
theorem basicOpen_restriction_etale {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.Etale := by
  let : Algebra Γ(X, V) Γ(X, X.basicOpen a) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsLocalization.Away a Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
  exact Algebra.Etale.of_isLocalizationAway a

/-- SAME original coordinates restricted through actual principal restriction stay etale. -/
theorem etale_coordinates_basicOpen {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V))
    {n : ℕ} (v : Fin n → Γ(X, V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f (X.basicOpen a)
    (MvPolynomial.aeval (R := k)
      (fun j => X.presheaf.map (homOfLE (X.basicOpen_le a)).op (v j))).toRingHom.Etale := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f (X.basicOpen a)
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f
    (homOfLE (X.basicOpen_le a))).toAlgebra
  let : IsScalarTower k Γ(X, V) Γ(X, X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq fun b =>
      ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f
        (homOfLE (X.basicOpen_le a))).commutes b).symm
  exact Char0.etale_aeval_algebraMap v hv (basicOpen_restriction_etale hV a)

/-- The ACTUAL original affine-coordinate opens, with SAME structural coefficient action. -/
def coordinateOpens (n : ℕ) : Set X.Opens :=
  {V | IsAffineOpen V ∧ letI := CanonicalGeometry.cotangentOpenAlgebra f V
    ∃ v : Fin n → Γ(X, V), (MvPolynomial.aeval (R := k) v).toRingHom.Etale}

variable (n : ℕ) [SmoothOfRelativeDimension n f]

/-- EVERY original neighborhood has a genuine original etale coordinate subchart. -/
theorem exists_subchart {W : X.Opens} (x : X) (hx : x ∈ W) :
    ∃ V ∈ coordinateOpens f n, x ∈ V ∧ V ≤ W := by
  obtain ⟨V, hV, hxV, v, hv⟩ := SmoothEtaleAffineCover.exists_affine_etale_chart f n x
  obtain ⟨a, ha, hxa⟩ := hV.exists_basicOpen_le (⟨x, hx⟩ : W) hxV
  exact ⟨X.basicOpen a, ⟨hV.basicOpen a, _, etale_coordinates_basicOpen f hV a v hv⟩, hxa, ha⟩

/-- GENUINE whole original smooth coordinate-open basis, empty schemes included internally. -/
theorem isBasis_coordinateOpens : Opens.IsBasis (coordinateOpens f n) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  exact exists_subchart f n x hx

end EnvelopeProperty.Cartier.SmoothEtaleAffineBasis
