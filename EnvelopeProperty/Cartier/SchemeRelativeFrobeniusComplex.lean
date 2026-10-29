import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineSectionLinearity
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineSections

/-! # The actual global relative-Frobenius-pushed exterior modules

The target is the genuine twist, and every original section and scalar action
is retained. The original intrinsic differential is linear on twisted opens.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusDeRham
open AlgebraicGeometry CategoryTheory Opposite
universe u
private theorem conjugate_smul {R A₀ A₁ B₀ B₁ : Type u} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup B₀] [AddCommGroup B₁]
    [Module R A₀] [Module R A₁] [Module R B₀] [Module R B₁]
    (e₀ : A₀ ≃ₗ[R] B₀) (e₁ : A₁ ≃ₗ[R] B₁) (d : A₀ → A₁) (a : R)
    (h : ∀ w, d (a • w) = a • d w) (s : B₀) :
    e₁ (d (e₀.symm (a • s))) = a • e₁ (d (e₀.symm s)) := by
  rw [map_smul, h, map_smul]

private theorem raw_smul_of_D_zero {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] {n : ℕ} (v : Fin n → B)
    (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale) (q : ℕ) (a : B)
    (ha : KaehlerDifferential.D R B a = 0)
    (w : ⋀[B]^q (KaehlerDifferential R B)) :
    EtaleDeRham.differential v hv q (a • w) =
      a • EtaleDeRham.differential v hv q w := by
  rw [EtaleDifferentialLeibniz.differential_smul, ha]
  change (EtaleDifferentialLeibniz.leftWedgeLinear q 0) w + _ = _
  simp only [map_zero, LinearMap.zero_apply, zero_add]

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f

/-- The ORIGINAL globally pushed exterior sheaf with its actual twist-module action. -/
def formModule (q : ℕ) : (Y).Modules :=
  (Scheme.Modules.pushforward (Fr)).obj (CanonicalGeometry.exteriorCotangentSheaf f q)

/-- EVERY original open and section has exactly its original geometric pullback scalar action. -/
theorem formModule_smul (q : ℕ) (W : (Y).Opens) (a : Γ(Y, W))
    (s : Γ(formModule f p q, W)) :
    (a • s : Γ(formModule f p q, W)) =
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f q, (Fr) ⁻¹ᵁ W) from
        ((Fr).app W).hom a •
          (show Γ(CanonicalGeometry.exteriorCotangentSheaf f q, (Fr) ⁻¹ᵁ W) from s)) := rfl

variable {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (v : Fin n → Γ(X, U))
variable (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
  (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- ALL original whole affine sections have the true geometric twisted-open scalar linearity. -/
theorem differential_relativeSectionMap_smul (q : ℕ)
    (a : Γ(Y, RelativeTwistedAffineBasis.twistedOpen f p U))
    (s : Γ(CanonicalGeometry.exteriorCotangentSheaf f q, U)) :
    EtaleAffineSectionDifferential.differential f hU v hv q
        ((RelativeTwistedAffineSections.relativeSectionMap f p U).hom a • s) =
      (RelativeTwistedAffineSections.relativeSectionMap f p U).hom a •
        EtaleAffineSectionDifferential.differential f hU v hv q s := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f U
  let _ : Module Γ(X, U) ((CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U)) :=
    ((CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U)).isModule
  let _ : Module Γ(X, U) ((CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).obj (op U)) :=
    ((CanonicalGeometry.exteriorCotangentPresheaf f (q+1)).obj (op U)).isModule
  let σ : Γ(Y, RelativeTwistedAffineBasis.twistedOpen f p U) ≅
      RelativeFrobenius.twist (algebraMap k Γ(X, U)) p :=
    RelativeTwistedAffineCharts.sectionsIso f p U hU
  let β := SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k Γ(X, U)) p
  have hμ : (RelativeTwistedAffineSections.relativeSectionMap f p U).hom a =
      β.hom (σ.hom.hom a) := congrArg
    (fun z : Γ(Y, RelativeTwistedAffineBasis.twistedOpen f p U) ⟶ Γ(X, U) => z.hom a)
    (RelativeTwistedAffineSections.relativeSectionMap_eq f p U hU)
  have hD : KaehlerDifferential.D k Γ(X, U)
      ((RelativeTwistedAffineSections.relativeSectionMap f p U).hom a) = 0 := by
    rw [hμ, SchemeRelativeFrobeniusAffineMap.D_ringMap_eq_zero]
  let e₀ := EtaleAffineSectionDifferential.unitEquiv f hU v hv q
  let e₁ := EtaleAffineSectionDifferential.unitEquiv f hU v hv (q+1)
  change e₁ (EtaleDeRham.differential v hv q
      (e₀.symm ((RelativeTwistedAffineSections.relativeSectionMap f p U).hom a • s))) =
    (RelativeTwistedAffineSections.relativeSectionMap f p U).hom a •
      e₁ (EtaleDeRham.differential v hv q (e₀.symm s))
  exact conjugate_smul e₀ e₁ (EtaleAffineSectionDifferential.rawDifferential f v hv q)
    ((RelativeTwistedAffineSections.relativeSectionMap f p U).hom a)
    (fun w => raw_smul_of_D_zero v hv q _ hD w) s


set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
#check @conjugate_smul
#print axioms conjugate_smul
#check @raw_smul_of_D_zero
#print axioms raw_smul_of_D_zero
#check @formModule
#print axioms formModule
#check @formModule_smul
#print axioms formModule_smul
#check @differential_relativeSectionMap_smul
#print axioms differential_relativeSectionMap_smul
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusDeRham
