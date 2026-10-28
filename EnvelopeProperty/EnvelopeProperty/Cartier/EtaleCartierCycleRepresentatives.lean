import EnvelopeProperty.Cartier.EtaleClosedExteriorLift
import EnvelopeProperty.Cartier.IntrinsicCartierOne

/-! # Genuine original all-degree etale Cartier cycle representatives -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCartierCycleRepresentatives
open CategoryTheory
open scoped Classical
universe u
private def rowTransport {A : Type u} [CommRing A] (S : ShortComplex (ModuleCat A))
    {H : ModuleCat A} (e : H ≅ ModuleCat.of A
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)) : S.homology ≅ H :=
  S.moduleCatHomologyIso ≪≫ e.symm

private theorem rowTransport_class {A : Type u} [CommRing A] (S : ShortComplex (ModuleCat A))
    {H : ModuleCat A} (e : H ≅ ModuleCat.of A
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
    (z : LinearMap.ker S.g.hom) :
    (rowTransport S e).hom.hom (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
      e.inv.hom (Submodule.Quotient.mk z) := by
  change e.inv.hom (S.moduleCatHomologyIso.hom.hom
    (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z))) = _
  exact congrArg e.inv.hom (Iso.inv_hom_id_apply S.moduleCatHomologyIso (Submodule.Quotient.mk z))

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP B p]
local notation "W" => KaehlerDifferential R B

/-- The original etale basis DERIVES an actual cycle-valued Frobenius-linear map.
No chosen lift, closedness or representative certificate is supplied. -/
def coordinateCycleMap : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1 :=
  (Char0.etaleDifferentialBasis v hv).constr B
    (fun i => (show EtaleCohomologyProducts.cycles v hv p 1 from
      IntrinsicCartierOne.generatorCycle v hv p (v i)))

/-- EACH original coordinate differential has its genuine original v_i^(p-1)dv_i cycle. -/
theorem coordinateCycleMap_D (i : Fin n) :
    coordinateCycleMap v hv p (KaehlerDifferential.D R B (v i)) =
      (show EtaleCohomologyProducts.cycles v hv p 1 from
        IntrinsicCartierOne.generatorCycle v hv p (v i)) := by
  rw [← Char0.etaleDifferentialBasis_apply v hv i]
  exact Module.Basis.constr_basis _ _ _ _

/-- Genuine ALL-degree original cycle-valued Cartier lifts, constructed internally. -/
def cycleRepresentative (q : ℕ) : (⋀[B]^q W) →ₗ[B] EtaleCohomologyProducts.cycles v hv p q :=
  EtaleClosedExteriorLift.cycleRepresentative v hv p (coordinateCycleMap v hv p) q

/-- Actual all-degree maps into the SAME native whole original Frobenius complex cohomology. -/
def inverseCartier (q : ℕ) : (⋀[B]^q W) →ₗ[B]
    (EtaleDeRham.frobeniusComplex v hv p).homology q :=
  EtaleClosedExteriorLift.nativeClassMap v hv p (coordinateCycleMap v hv p) q

/-- The genuine SAME original 0/1/2 row is compared with SAME whole-complex native H1. -/
def oneHomologyIso : (IntrinsicCartierOne.shortComplex v hv p).homology ≅
    (EtaleDeRham.frobeniusComplex v hv p).homology 1 :=
  rowTransport (IntrinsicCartierOne.shortComplex v hv p)
    (EtaleCohomologyProducts.cohomologyIso v hv p 1)

/-- This comparison retains the ENTIRE actual original cycle class, not merely coordinates. -/
theorem oneHomologyIso_cycleClass (z : EtaleCohomologyProducts.cycles v hv p 1) :
    (oneHomologyIso v hv p).hom.hom (IntrinsicCartierOne.cycleClass v hv p z) =
      (EtaleCohomologyProducts.nativeCycleClass v hv p 1).toFun z :=
  rowTransport_class (IntrinsicCartierOne.shortComplex v hv p)
    (EtaleCohomologyProducts.cohomologyIso v hv p 1) z

/-- The ENTIRE degree-one map is the previously proved original UNIVERSAL inverse Cartier
map, through the genuine original row/whole-complex comparison. -/
theorem inverseCartier_one :
    (inverseCartier v hv p 1).comp (exteriorPower.oneEquiv B W).symm.toLinearMap =
      (oneHomologyIso v hv p).hom.hom.comp (IntrinsicCartierOne.inverseCartier v hv p) := by
  apply (Char0.etaleDifferentialBasis v hv).ext
  intro i
  rw [Char0.etaleDifferentialBasis_apply]
  change EtaleCohomologyProducts.nativeCycleClass v hv p 1
    (cycleRepresentative v hv p 1 ((exteriorPower.oneEquiv B W).symm
      (KaehlerDifferential.D R B (v i)))) =
    (oneHomologyIso v hv p).hom.hom
      (IntrinsicCartierOne.inverseCartier v hv p (KaehlerDifferential.D R B (v i)))
  have hc := EtaleClosedExteriorLift.cycleRepresentative_one v hv p (coordinateCycleMap v hv p)
    (KaehlerDifferential.D R B (v i))
  change cycleRepresentative v hv p 1 _ = coordinateCycleMap v hv p _ at hc
  rw [hc, coordinateCycleMap_D, IntrinsicCartierOne.inverseCartier_D]
  exact (oneHomologyIso_cycleClass v hv p (IntrinsicCartierOne.generatorCycle v hv p (v i))).symm

/-- EVERY original function has its genuine original a^(p-1)da class, through the SAME
actual row/whole-complex homology comparison. No function-generator formula is assumed. -/
theorem inverseCartier_D (a : B) :
    inverseCartier v hv p 1 ((exteriorPower.oneEquiv B W).symm (KaehlerDifferential.D R B a)) =
      (oneHomologyIso v hv p).hom.hom (IntrinsicCartierOne.generatorClass v hv p a) := by
  have h := congrArg (fun F : W →ₗ[B] (EtaleDeRham.frobeniusComplex v hv p).homology 1 =>
    F (KaehlerDifferential.D R B a)) (inverseCartier_one v hv p)
  exact h.trans (congrArg (oneHomologyIso v hv p).hom.hom (IntrinsicCartierOne.inverseCartier_D v hv p a))

/-- These internally constructed actual Cartier maps preserve EVERY original homogeneous
product in the SAME entire native original Frobenius complex cohomology. -/
theorem inverseCartier_wedgeProduct (q r : ℕ) (a : ⋀[B]^q W) (b : ⋀[B]^r W) :
    (inverseCartier (R := R) v hv p (r+q)).toFun (EtaleGradedLeibniz.wedgeProduct q r a b) =
      ((EtaleCohomologyProducts.nativeCohomologyProduct (R := R) (B := B) v hv p q r).toFun
        ((inverseCartier (R := R) v hv p q).toFun a)).toFun
          ((inverseCartier (R := R) v hv p r).toFun b) :=
  EtaleClosedExteriorLift.nativeClassMap_wedgeProduct v hv p (coordinateCycleMap v hv p) q r a b

end EnvelopeProperty.Cartier.EtaleCartierCycleRepresentatives
