import EnvelopeProperty.Cartier.EtaleClosedExteriorLift
import EnvelopeProperty.Cartier.IntrinsicCartierOne

/-! # Cycle representatives of the inverse Cartier map in all degrees, for étale coordinates -/
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

/-- The `B`-linear map from the Kähler differentials to the degree-one cycles of the Frobenius
complex sending `dvᵢ` to `vᵢ^(p-1) dvᵢ`, defined on the basis `(dvᵢ)` of étale coordinates. -/
def coordinateCycleMap : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1 :=
  (Char0.etaleDifferentialBasis v hv).constr B
    (fun i => (show EtaleCohomologyProducts.cycles v hv p 1 from
      IntrinsicCartierOne.generatorCycle v hv p (v i)))

/-- `coordinateCycleMap` sends `dvᵢ` to the cycle `vᵢ^(p-1) dvᵢ`. -/
theorem coordinateCycleMap_D (i : Fin n) :
    coordinateCycleMap v hv p (KaehlerDifferential.D R B (v i)) =
      (show EtaleCohomologyProducts.cycles v hv p 1 from
        IntrinsicCartierOne.generatorCycle v hv p (v i)) := by
  rw [← Char0.etaleDifferentialBasis_apply v hv i]
  exact Module.Basis.constr_basis _ _ _ _

/-- The cycle representatives of the inverse Cartier map in degree `q`. -/
def cycleRepresentative (q : ℕ) : (⋀[B]^q W) →ₗ[B] EtaleCohomologyProducts.cycles v hv p q :=
  EtaleClosedExteriorLift.cycleRepresentative v hv p (coordinateCycleMap v hv p) q

/-- The inverse Cartier map `⋀^q Ω ⟶ H^q` of the Frobenius complex in degree `q`. -/
def inverseCartier (q : ℕ) : (⋀[B]^q W) →ₗ[B]
    (EtaleDeRham.frobeniusComplex v hv p).homology q :=
  EtaleClosedExteriorLift.nativeClassMap v hv p (coordinateCycleMap v hv p) q

/-- The homology of the short complex in degrees `0, 1, 2` is the first homology of the
Frobenius complex. -/
def oneHomologyIso : (IntrinsicCartierOne.shortComplex v hv p).homology ≅
    (EtaleDeRham.frobeniusComplex v hv p).homology 1 :=
  rowTransport (IntrinsicCartierOne.shortComplex v hv p)
    (EtaleCohomologyProducts.cohomologyIso v hv p 1)

/-- `oneHomologyIso` sends the class of a cycle to its class in the Frobenius complex. -/
theorem oneHomologyIso_cycleClass (z : EtaleCohomologyProducts.cycles v hv p 1) :
    (oneHomologyIso v hv p).hom.hom (IntrinsicCartierOne.cycleClass v hv p z) =
      (EtaleCohomologyProducts.nativeCycleClass v hv p 1).toFun z :=
  rowTransport_class (IntrinsicCartierOne.shortComplex v hv p)
    (EtaleCohomologyProducts.cohomologyIso v hv p 1) z

/-- In degree one, `inverseCartier` is `IntrinsicCartierOne.inverseCartier`, through
`oneHomologyIso`. -/
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

/-- For every `a ∈ B`, the inverse Cartier map sends `da` to the class of `a^(p-1) da`. -/
theorem inverseCartier_D (a : B) :
    inverseCartier v hv p 1 ((exteriorPower.oneEquiv B W).symm (KaehlerDifferential.D R B a)) =
      (oneHomologyIso v hv p).hom.hom (IntrinsicCartierOne.generatorClass v hv p a) := by
  have h := congrArg (fun F : W →ₗ[B] (EtaleDeRham.frobeniusComplex v hv p).homology 1 =>
    F (KaehlerDifferential.D R B a)) (inverseCartier_one v hv p)
  exact h.trans (congrArg (oneHomologyIso v hv p).hom.hom (IntrinsicCartierOne.inverseCartier_D v hv p a))

/-- The inverse Cartier maps are multiplicative: they send wedge products to products in the
cohomology of the Frobenius complex. -/
theorem inverseCartier_wedgeProduct (q r : ℕ) (a : ⋀[B]^q W) (b : ⋀[B]^r W) :
    (inverseCartier (R := R) v hv p (r+q)).toFun (EtaleGradedLeibniz.wedgeProduct q r a b) =
      ((EtaleCohomologyProducts.nativeCohomologyProduct (R := R) (B := B) v hv p q r).toFun
        ((inverseCartier (R := R) v hv p q).toFun a)).toFun
          ((inverseCartier (R := R) v hv p r).toFun b) :=
  EtaleClosedExteriorLift.nativeClassMap_wedgeProduct v hv p (coordinateCycleMap v hv p) q r a b

end EnvelopeProperty.Cartier.EtaleCartierCycleRepresentatives
