import EnvelopeProperty.Cartier.CartierAdditivePrimitive
import EnvelopeProperty.Cartier.EtaleDifferentialLeibniz
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The actual canonical Cartier one-form derivation in native cohomology -/
noncomputable section
namespace EnvelopeProperty.Cartier.IntrinsicCartierOne
open CategoryTheory
open scoped Classical
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP B p]

/-- The SAME actual original degree-zero/one/two Frobenius de Rham short complex. -/
def shortComplex : ShortComplex (ModuleCat B) :=
  ShortComplex.mk (EtaleDeRham.frobeniusDifferential v hv p 0)
    (EtaleDeRham.frobeniusDifferential v hv p 1) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact EtaleDeRham.differential_square v hv 0 a)

private def shortCycleClass {A : Type u} [CommRing A] (S : ShortComplex (ModuleCat A)) :
    LinearMap.ker S.g.hom →ₗ[A] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (LinearMap.range S.moduleCatToCycles).mkQ

private theorem shortCycleClass_boundary {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (a : S.X₁) :
    shortCycleClass S (S.moduleCatToCycles a) = 0 := by
  change S.moduleCatHomologyIso.inv (Submodule.Quotient.mk (S.moduleCatToCycles a)) = 0
  rw [show (Submodule.Quotient.mk (S.moduleCatToCycles a) :
    LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ a)]
  exact S.moduleCatHomologyIso.inv.hom.map_zero

/-- The actual original closed one-form a^(p-1) da, before Frobenius restriction. -/
def generatorForm (a : B) : ⋀[B]^1 (KaehlerDifferential R B) :=
  a^(p-1) • (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm
    (KaehlerDifferential.D R B a)

/-- Its closedness is DERIVED in the SAME original complex. -/
def generatorCycle (a : B) : LinearMap.ker (shortComplex v hv p).g.hom :=
  ⟨generatorForm (R := R) p a, EtaleDifferentialLeibniz.differential_power_universalD v hv a (p-1)⟩

/-- The actual original native cycle-class linear map on the ENTIRE original cycle module. -/
def cycleClass : LinearMap.ker (shortComplex v hv p).g.hom →ₗ[B]
    (shortComplex v hv p).homology := shortCycleClass (shortComplex v hv p)

/-- Its WHOLE original formula is the actual native homology projection of the SAME cycle. -/
theorem cycleClass_eq (z : LinearMap.ker (shortComplex v hv p).g.hom) :
    cycleClass v hv p z = (shortComplex v hv p).homologyπ
      ((shortComplex v hv p).moduleCatCyclesIso.inv z) := by
  exact (ShortComplex.moduleCatCyclesIso_inv_π_apply (shortComplex v hv p) z).symm

/-- The genuine original native cohomology class of a^(p-1) da. -/
def generatorClass (a : B) : (shortComplex v hv p).homology :=
  cycleClass v hv p (generatorCycle v hv p a)

/-- The actual additive discrepancy is the boundary of the ACTUAL integral polynomial
primitive evaluated at the SAME two original functions. -/
theorem generatorCycle_add_difference (a b : B) :
    generatorCycle v hv p (a+b) - generatorCycle v hv p a - generatorCycle v hv p b =
      (shortComplex v hv p).moduleCatToCycles
        ((exteriorPower.zeroEquiv B (KaehlerDifferential R B)).symm
          (CartierAdditivePrimitive.primitive p a b)) := by
  apply Subtype.ext
  change generatorForm (R := R) p (a+b) - generatorForm (R := R) p a -
    generatorForm (R := R) p b = EtaleDeRham.differential v hv 0 _
  apply (exteriorPower.oneEquiv B (KaehlerDifferential R B)).injective
  simp only [generatorForm, map_sub, map_smul, LinearEquiv.apply_symm_apply,
    EtaleDeRham.differential_zero]
  rw [CartierAdditivePrimitive.universalD_primitive]
  rw [map_add, smul_add, sub_smul, sub_smul]
  abel

/-- Additivity holds in the WHOLE genuine native original cohomology, not merely after
selecting coordinates or projecting selected coefficients. -/
theorem generatorClass_add (a b : B) :
    generatorClass v hv p (a+b) = generatorClass v hv p a + generatorClass v hv p b := by
  have h := congrArg (shortCycleClass (shortComplex v hv p))
    (generatorCycle_add_difference v hv p a b)
  have hz := h.trans (shortCycleClass_boundary (shortComplex v hv p)
    (show (shortComplex v hv p).X₁ from
      (exteriorPower.zeroEquiv B (KaehlerDifferential R B)).symm
        (CartierAdditivePrimitive.primitive p a b)))
  simp only [map_sub] at hz
  change generatorClass v hv p (a+b) - generatorClass v hv p a -
    generatorClass v hv p b = 0 at hz
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)


private theorem power_mul_coefficient (p : ℕ) (hp : 0 < p) (a b : B) :
    (a*b)^(p-1)*a = a^p*b^(p-1) := by
  rw [mul_pow]
  calc
    (a^(p-1)*b^(p-1))*a = (a^(p-1)*a)*b^(p-1) := by ring
    _ = a^p*b^(p-1) := by rw [← pow_succ, Nat.sub_add_cancel hp]

/-- The SAME actual cycles obey the true Frobenius Leibniz identity. -/
theorem generatorCycle_mul (a b : B) :
    generatorCycle v hv p (a*b) =
      a • generatorCycle v hv p b + b • generatorCycle v hv p a := by
  apply Subtype.ext
  change generatorForm (R := R) p (a*b) =
    a^p • generatorForm (R := R) p b + b^p • generatorForm (R := R) p a
  apply (exteriorPower.oneEquiv B (KaehlerDifferential R B)).injective
  simp only [generatorForm, map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
    power_mul_coefficient p (Fact.out : p.Prime).pos,
    show (a*b)^(p-1)*b = b^p*a^(p-1) from by
      rw [mul_comm a b]; exact power_mul_coefficient p (Fact.out : p.Prime).pos b a]

/-- Frobenius Leibniz holds in the WHOLE genuine native original cohomology. -/
theorem generatorClass_mul (a b : B) :
    generatorClass v hv p (a*b) =
      a • generatorClass v hv p b + b • generatorClass v hv p a := by
  exact (congrArg (shortCycleClass (shortComplex v hv p))
    (generatorCycle_mul v hv p a b)).trans (by rw [map_add, map_smul, map_smul]; rfl)

/-- Every original base-ring coefficient has ZERO actual Cartier generator class. -/
theorem generatorClass_algebraMap (r : R) :
    generatorClass v hv p (algebraMap R B r) = 0 := by
  have hz : generatorCycle v hv p (algebraMap R B r) = 0 := by
    apply Subtype.ext
    change generatorForm (R := R) p (algebraMap R B r) = 0
    simp only [generatorForm, Derivation.map_algebraMap, map_zero, smul_zero]
  exact (congrArg (shortCycleClass (shortComplex v hv p)) hz).trans
    (shortCycleClass (shortComplex v hv p)).map_zero


/-- The SAME original generator classes form an ACTUAL relative derivation for the
original Frobenius coefficient action, with no additivity/Leibniz certificate. -/
def derivation :
    letI : Module R (shortComplex v hv p).homology :=
      Module.compHom (shortComplex v hv p).homology (algebraMap R B)
    Derivation R B (shortComplex v hv p).homology := by
  let : Module R (shortComplex v hv p).homology :=
    Module.compHom (shortComplex v hv p).homology (algebraMap R B)
  exact
    { toFun := generatorClass v hv p
      map_add' := generatorClass_add v hv p
      map_smul' := fun r a => by
        rw [Algebra.smul_def]
        change generatorClass v hv p ((algebraMap R B r)*a) =
          (algebraMap R B r) • generatorClass v hv p a
        rw [generatorClass_mul, generatorClass_algebraMap, smul_zero, add_zero]
      map_one_eq_zero' := by
        change generatorClass v hv p (1 : B) = 0
        simpa only [map_one] using generatorClass_algebraMap v hv p (1 : R)
      leibniz' := generatorClass_mul v hv p }

/-- The actual inverse Cartier ONE-form map is determined by the SAME original universal
Kaehler differential and genuine native cohomology, without a chosen-coordinate formula. -/
def inverseCartier :
    KaehlerDifferential R B →ₗ[B] (shortComplex v hv p).homology := by
  let : Module R (shortComplex v hv p).homology :=
    Module.compHom (shortComplex v hv p).homology (algebraMap R B)
  let : IsScalarTower R B (shortComplex v hv p).homology :=
    IsScalarTower.of_compHom R B (shortComplex v hv p).homology
  exact (derivation v hv p).liftKaehlerDifferential

/-- EVERY original function retains the actual original Cartier cycle class. -/
theorem inverseCartier_D (a : B) :
    inverseCartier v hv p (KaehlerDifferential.D R B a) = generatorClass v hv p a := by
  let : Module R (shortComplex v hv p).homology :=
    Module.compHom (shortComplex v hv p).homology (algebraMap R B)
  let : IsScalarTower R B (shortComplex v hv p).homology :=
    IsScalarTower.of_compHom R B (shortComplex v hv p).homology
  exact Derivation.liftKaehlerDifferential_comp_D (derivation v hv p) a

/-- The WHOLE original linear map is uniquely determined by its actual universal
Cartier generators, not merely by any selected coordinate basis. -/
theorem inverseCartier_unique
    (F : KaehlerDifferential R B →ₗ[B] (shortComplex v hv p).homology)
    (hF : ∀ a : B, F (KaehlerDifferential.D R B a) = generatorClass v hv p a) :
    F = inverseCartier v hv p := by
  let : Module R (shortComplex v hv p).homology :=
    Module.compHom (shortComplex v hv p).homology (algebraMap R B)
  let : IsScalarTower R B (shortComplex v hv p).homology :=
    IsScalarTower.of_compHom R B (shortComplex v hv p).homology
  apply Derivation.liftKaehlerDifferential_unique F (inverseCartier v hv p)
  apply Derivation.ext
  intro a
  exact (hF a).trans (inverseCartier_D v hv p a).symm

end EnvelopeProperty.Cartier.IntrinsicCartierOne
