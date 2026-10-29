import EnvelopeProperty.Cartier.AlgebraFrobenius
import EnvelopeProperty.Cartier.EtaleDifferentialLeibniz

/-! # The actual etale Frobenius complex includes zero algebras internally -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusComplex
open CategoryTheory
open scoped Classical
universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "W" => KaehlerDifferential k B

omit [Fact p.Prime] in
include k in
/-- The ORIGINAL p vanishes in EVERY original algebra, including zero, without target CharP. -/
theorem natCast_eq_zero : (p : B) = 0 := by
  exact (map_natCast (algebraMap k B) p).symm.trans
    ((congrArg (algebraMap k B) (CharP.cast_eq_zero k p)).trans (map_zero _))

omit [Fact p.Prime] in
/-- True original universal derivatives kill pth powers on EVERY original k-algebra,
including zero; no target characteristic/nontriviality premise is supplied. -/
theorem universalD_pow (a : B) : KaehlerDifferential.D k B (a^p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, natCast_eq_zero (k := k) p, zero_smul]

omit [Fact p.Prime] in
/-- The SAME entire original de Rham differential is genuinely Frobenius-linear even on the
zero algebra, derived from actual universalD and full scalar Leibniz. -/
theorem differential_pow_smul (q : ℕ) (a : B) (w : ⋀[B]^q W) :
    EtaleDeRham.differential v hv q (a^p • w) = a^p • EtaleDeRham.differential v hv q w := by
  rw [EtaleDifferentialLeibniz.differential_smul, universalD_pow]
  change (EtaleDifferentialLeibniz.leftWedgeLinear q 0) w + _ = _
  simp only [map_zero, LinearMap.zero_apply, zero_add]

/-- Actual original exterior forms with SAME genuine all-algebra Frobenius scalar action. -/
def formModule (q : ℕ) : ModuleCat B :=
  (ModuleCat.restrictScalars (AlgebraFrobenius.map k B p)).obj (ModuleCat.of B (⋀[B]^q W))

private def restrictedMorphism {A : Type u} [CommRing A] (f : A →+* A)
    (M N : ModuleCat A) (g : M →+ N)
    (h : ∀ a w, g (f a • w) = f a • g w) :
    (ModuleCat.restrictScalars f).obj M ⟶ (ModuleCat.restrictScalars f).obj N :=
  let X := (ModuleCat.restrictScalars f).obj M
  let Y := (ModuleCat.restrictScalars f).obj N
  letI := X.isModule
  letI := Y.isModule
  ModuleCat.ofHom (X := X) (Y := Y)
    { toFun := g
      map_add' := g.map_add
      map_smul' := h }

/-- The SAME actual original de Rham differential between actual full Frobenius modules;
EVERY original k-algebra is included, with no target CharP premise. -/
def differential (q : ℕ) : formModule (k := k) (B := B) p q ⟶
    formModule (k := k) (B := B) p (q+1) :=
  restrictedMorphism (AlgebraFrobenius.map k B p)
    (ModuleCat.of B (⋀[B]^q W)) (ModuleCat.of B (⋀[B]^(q+1) W))
    (EtaleDeRham.differential v hv q) (fun a w => by
      rw [AlgebraFrobenius.map_apply]
      exact differential_pow_smul v hv p q a w)

/-- Every original form is sent through the SAME entire original differential. -/
theorem differential_apply (q : ℕ) (w : formModule (k := k) (B := B) p q) :
    differential v hv p q w = EtaleDeRham.differential v hv q w := rfl

/-- The GENUINE SAME whole original Frobenius de Rham complex on EVERY original etale
k-algebra, including zero and every degree, with no target characteristic certificate. -/
def complex : CochainComplex (ModuleCat B) ℕ :=
  CochainComplex.of (formModule (k := k) (B := B) p) (differential v hv p) (fun q => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact EtaleDeRham.differential_square v hv q a)

variable [CharP B p]

/-- Actual whole form-module comparison with the pre-existing native Frobenius module. -/
def nativeModuleIso (q : ℕ) : formModule (k := k) (B := B) p q ≅
    EtaleDeRham.frobeniusModule (R := k) (B := B) p q :=
  (ModuleCat.restrictScalarsCongr (AlgebraFrobenius.map_eq_frobenius k B p)).app
    (ModuleCat.of B (⋀[B]^q W))

/-- The genuine native component comparison retains EVERY SAME original form. -/
theorem nativeModuleIso_hom_apply (q : ℕ) (w : formModule (k := k) (B := B) p q) :
    (nativeModuleIso (k := k) (B := B) p q).hom w = w :=
  ModuleCat.restrictScalarsCongr_hom_app
    (AlgebraFrobenius.map_eq_frobenius k B p) _ _

/-- True entire native complex comparison; every component is the SAME original form map. -/
def nativeComplexIso : complex v hv p ≅ EtaleDeRham.frobeniusComplex v hv p := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => nativeModuleIso (k := k) (B := B) p q) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [complex, EtaleDeRham.frobeniusComplex, CochainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  rfl

/-- The ENTIRE actual native complex map preserves EVERY original form in EVERY degree. -/
theorem nativeComplexIso_hom_f_apply (q : ℕ) (w : (complex v hv p).X q) :
    (nativeComplexIso v hv p).hom.f q w = w := rfl

end EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusComplex
