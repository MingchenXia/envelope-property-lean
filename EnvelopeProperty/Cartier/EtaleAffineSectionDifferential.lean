import EnvelopeProperty.Cartier.EtaleSchemeSectionDifferential
import EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusComplex
import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionSheafUnits

/-! # Intrinsic differential on SAME entire original affine exterior sheaf sections -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleAffineSectionDifferential
open AlgebraicGeometry CategoryTheory Opposite
universe u
private def conjugate {R A₀ A₁ B₀ B₁ : Type u} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup B₀] [AddCommGroup B₁]
    [Module R A₀] [Module R A₁] [Module R B₀] [Module R B₁]
    (e₀ : A₀ ≃ₗ[R] B₀) (e₁ : A₁ ≃ₗ[R] B₁) (d : A₀ →+ A₁) : B₀ →+ B₁ where
  toFun b := e₁ (d (e₀.symm b))
  map_zero' := by rw [map_zero, map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add, map_add]

private theorem conjugate_square {R A₀ A₁ A₂ B₀ B₁ B₂ : Type u} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂]
    [Module R B₀] [Module R B₁] [Module R B₂]
    (e₀ : A₀ ≃ₗ[R] B₀) (e₁ : A₁ ≃ₗ[R] B₁) (e₂ : A₂ ≃ₗ[R] B₂)
    (d₀ : A₀ →+ A₁) (d₁ : A₁ →+ A₂) (h : ∀ a, d₁ (d₀ a) = 0) (b : B₀) :
    conjugate e₁ e₂ d₁ (conjugate e₀ e₁ d₀ b) = 0 := by
  change e₂ (d₁ (e₁.symm (e₁ (d₀ (e₀.symm b))))) = 0
  rw [LinearEquiv.symm_apply_apply, h, map_zero]

private theorem conjugate_pow_smul {R A₀ A₁ B₀ B₁ : Type u} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup B₀] [AddCommGroup B₁]
    [Module R A₀] [Module R A₁] [Module R B₀] [Module R B₁]
    (e₀ : A₀ ≃ₗ[R] B₀) (e₁ : A₁ ≃ₗ[R] B₁) (d : A₀ →+ A₁) (p : ℕ)
    (h : ∀ (a : R) (w : A₀), d (a^p • w) = a^p • d w) (a : R) (b : B₀) :
    conjugate e₀ e₁ d (a^p • b) = a^p • conjugate e₀ e₁ d b := by
  change e₁ (d (e₀.symm (a^p • b))) = a^p • e₁ (d (e₀.symm b))
  rw [map_smul, h, map_smul]

private theorem transfer_naturality {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : Type u}
    (e₀ : A₀ → B₀) (e₁ : A₁ → B₁) (f₀ : C₀ → D₀) (f₁ : C₁ → D₁)
    (he : Function.Surjective e₀) (d : A₀ → A₁) (d' : C₀ → C₁)
    (D : B₀ → B₁) (D' : D₀ → D₁)
    (r₀ : A₀ → C₀) (r₁ : A₁ → C₁) (s₀ : B₀ → D₀) (s₁ : B₁ → D₁)
    (hD : ∀ a, D (e₀ a) = e₁ (d a)) (hD' : ∀ a, D' (f₀ a) = f₁ (d' a))
    (h₀ : ∀ a, s₀ (e₀ a) = f₀ (r₀ a)) (h₁ : ∀ a, s₁ (e₁ a) = f₁ (r₁ a))
    (hd : ∀ a, d' (r₀ a) = r₁ (d a)) (b : B₀) : D' (s₀ b) = s₁ (D b) := by
  obtain ⟨a, rfl⟩ := he b
  rw [h₀, hD', hd, ← h₁, ← hD]

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} (v : Fin n → Γ(X, V))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

@[instance_reducible]
private def originalExteriorSectionModule (q : ℕ) :
    Module Γ(X, V) ((CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :=
  ((CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)).isModule

attribute [local instance] originalExteriorSectionModule

/-- SAME actual original whole affine sheafification unit, with BOTH actual linear inverses. -/
def unitEquiv (q : ℕ) :
    (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V) ≃ₗ[Γ(X, V)]
      Γ(CanonicalGeometry.exteriorCotangentSheaf f q, V) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  exact LinearEquiv.ofBijective
    ((CanonicalGeometry.exteriorSheafificationMap
      (CanonicalGeometry.cotangentPresheaf f) q).app (op V)).hom
    (CanonicalGeometry.affineChartExteriorSheafificationMap_bijective f hV
      (Char0.etaleDifferentialBasis v hv) q)

/-- EVERY original form retains EXACTLY its original sheafification unit image. -/
theorem unitEquiv_apply (q : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    unitEquiv f hV v hv q a =
      (CanonicalGeometry.exteriorSheafificationMap
        (CanonicalGeometry.cotangentPresheaf f) q).app (op V) a := rfl

/-- SAME intrinsic original raw differential on original actual exterior sections. -/
def rawDifferential (q : ℕ) :
    (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V) →+
      (CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).obj (op V) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  exact EtaleDeRham.differential v hv q

/-- Actual additive differential on SAME entire original affine sheaf-section groups. -/
def differential (q : ℕ) :
    Γ(CanonicalGeometry.exteriorCotangentSheaf f q, V) →+
      Γ(CanonicalGeometry.exteriorCotangentSheaf f (q+1), V) :=
  conjugate (unitEquiv f hV v hv q) (unitEquiv f hV v hv (q+1))
    (rawDifferential f v hv q)

/-- EVERY original raw form recovers its SAME actual original differential under the unit. -/
theorem differential_unit (q : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    differential f hV v hv q (unitEquiv f hV v hv q a) =
      unitEquiv f hV v hv (q+1) (rawDifferential f v hv q a) := by
  change unitEquiv f hV v hv (q+1)
    (rawDifferential f v hv q ((unitEquiv f hV v hv q).symm (unitEquiv f hV v hv q a))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The SAME actual entire affine sheaf-section differential has true square zero. -/
theorem differential_square (q : ℕ) (a : Γ(CanonicalGeometry.exteriorCotangentSheaf f q, V)) :
    differential f hV v hv (q+1) (differential f hV v hv q a) = 0 := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  exact conjugate_square (unitEquiv f hV v hv q) (unitEquiv f hV v hv (q+1))
    (unitEquiv f hV v hv (q+1+1)) (rawDifferential f v hv q)
    (rawDifferential f v hv (q+1)) (fun x => EtaleDeRham.differential_square v hv q x) a

/-- Genuine Frobenius power linearity for EVERY SAME original affine sheaf section. -/
theorem differential_pow_smul (p : ℕ) [Fact p.Prime] [CharP k p]
    (q : ℕ) (a : Γ(X, V)) (s : Γ(CanonicalGeometry.exteriorCotangentSheaf f q, V)) :
    differential f hV v hv q (a^p • s) = a^p • differential f hV v hv q s := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  exact conjugate_pow_smul (unitEquiv f hV v hv q) (unitEquiv f hV v hv (q+1))
    (rawDifferential f v hv q) p
    (fun a w => EtaleAlgebraFrobeniusComplex.differential_pow_smul v hv p q a w) a s

variable {U : X.Opens} (hU : IsAffineOpen U) (i : U ⟶ V)
variable {m : ℕ} (w : Fin m → Γ(X, U))
variable (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) w).toRingHom.Etale)

/-- Every original actual unit commutes with SAME original raw and sheaf restrictions. -/
theorem unitEquiv_restrict (q : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map i.op
      (unitEquiv f hV v hv q a) =
      unitEquiv f hU w hw q ((CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op a) :=
  (PresheafOfModules.naturality_apply
    (CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf f) q)
    i.op a).symm

/-- ENTIRE genuine original affine sheaf-section differential commutes with restriction. -/
theorem differential_restrict (q : ℕ)
    (s : Γ(CanonicalGeometry.exteriorCotangentSheaf f q, V)) :
    differential f hU w hw q
      ((CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map i.op s) =
      (CanonicalGeometry.exteriorCotangentSheaf f (q+1)).presheaf.map i.op
        (differential f hV v hv q s) := by
  exact transfer_naturality (unitEquiv f hV v hv q) (unitEquiv f hV v hv (q+1))
    (unitEquiv f hU w hw q) (unitEquiv f hU w hw (q+1))
    (unitEquiv f hV v hv q).surjective
    (rawDifferential f v hv q) (rawDifferential f w hw q)
    (differential f hV v hv q) (differential f hU w hw q)
    ((CanonicalGeometry.exteriorCotangentPresheaf f q).map i.op)
    ((CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).map i.op)
    ((CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map i.op)
    ((CanonicalGeometry.exteriorCotangentSheaf f (q+1)).presheaf.map i.op)
    (differential_unit f hV v hv q) (differential_unit f hU w hw q)
    (unitEquiv_restrict f hV v hv hU i w hw q)
    (unitEquiv_restrict f hV v hv hU i w hw (q+1))
    (EtaleSchemeSectionDifferential.differential_restrict f i v hv w hw q) s

end EnvelopeProperty.Cartier.EtaleAffineSectionDifferential
