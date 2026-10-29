import EnvelopeProperty.Cartier.EtaleCohomologyCoefficientProducts
import EnvelopeProperty.Cartier.EtaleCartierCoordinateIndependence
import EnvelopeProperty.Cartier.IntrinsicCartierOneNaturality

/-! # The same canonical Cartier maps are natural for every original coefficient map -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCartierCoefficientNaturality
open CategoryTheory
open scoped Classical
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- SAME actual whole canonical exterior map into the genuine native scalar restriction. -/
def formMap (q : ℕ) : ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A)) ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (⋀[B]^q (KaehlerDifferential R B))) :=
  ModuleCat.ofHom (X := ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A)))
    (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (⋀[B]^q (KaehlerDifferential R B))))
    (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q)

/-- SAME actual internally constructed canonical map on the ENTIRE original cycle quotient. -/
def quotientInverseCartier (q : ℕ) : (⋀[A]^q (KaehlerDifferential R A)) →ₗ[A]
    EtaleCohomologyProducts.cohomology v hv p q :=
  EtaleClosedExteriorLift.classMap v hv p
    (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p) q

private theorem quotient_function_class (a : A) :
    quotientInverseCartier v hv p 1
      ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm (KaehlerDifferential.D R A a)) =
      Submodule.Quotient.mk (IntrinsicCartierOne.generatorCycle v hv p a) := by
  apply (ModuleCat.mono_iff_injective (EtaleCohomologyProducts.cohomologyIso v hv p 1).inv).mp
    inferInstance
  exact EtaleCartierCoordinateIndependence.inverseCartier_function_class v hv p a

private theorem canonicalMap_one_D (a : A) :
    (formMap (R := R) (A := A) (B := B) 1).hom
      ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm (KaehlerDifferential.D R A a)) =
      (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm
        (KaehlerDifferential.D R B (algebraMap A B a)) := by
  have h : (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm
      (KaehlerDifferential.D R A a) = exteriorPower.ιMulti A 1
        (fun _ => KaehlerDifferential.D R A a) := by
    apply (exteriorPower.oneEquiv A (KaehlerDifferential R A)).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_ιMulti]
  change Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) 1 _ = _
  rw [h, Char0.canonicalDifferentialLinearMap_wedge]
  apply (exteriorPower.oneEquiv B (KaehlerDifferential R B)).injective
  rw [exteriorPower.oneEquiv_ιMulti, LinearEquiv.apply_symm_apply, KaehlerDifferential.map_D]

/-- EVERY original function differential has the SAME canonical quotient class after the
actual coefficient map, with its whole original generator form retained. -/
theorem quotientInverseCartier_D (a : A) :
    (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p 1).hom
      (quotientInverseCartier v hv p 1
        ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm (KaehlerDifferential.D R A a))) =
      quotientInverseCartier w hw p 1
        ((formMap (R := R) (A := A) (B := B) 1).hom
          ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm (KaehlerDifferential.D R A a))) := by
  have hg : (EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p 1).hom
      (IntrinsicCartierOne.generatorCycle v hv p a) =
      IntrinsicCartierOne.generatorCycle w hw p (algebraMap A B a) := by
    apply Subtype.ext
    exact IntrinsicCartierOneNaturality.generatorForm_map (R := R) (A := A) (B := B) p a
  rw [quotient_function_class, canonicalMap_one_D, quotient_function_class]
  exact (EtaleCohomologyCoefficientMaps.cohomologyMap_class v hv w hw p 1
    (IntrinsicCartierOne.generatorCycle v hv p a)).trans
      (congrArg (fun z : EtaleCohomologyProducts.cycles w hw p 1 =>
        Submodule.Quotient.mk z) hg)

/-- The ENTIRE original degree-one Cartier map commutes with the SAME original coefficient map. -/
theorem quotientInverseCartier_one (a : ⋀[A]^1 (KaehlerDifferential R A)) :
    (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p 1).hom
      (quotientInverseCartier v hv p 1 a) =
      quotientInverseCartier w hw p 1 ((formMap (R := R) (A := A) (B := B) 1).hom a) := by
  let T := (ModuleCat.restrictScalars (algebraMap A B)).obj
    (ModuleCat.of B (EtaleCohomologyProducts.cohomology w hw p 1))
  let l : (⋀[A]^1 (KaehlerDifferential R A)) →ₗ[A] T :=
    (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p 1).hom.comp
      (quotientInverseCartier v hv p 1)
  let r : (⋀[A]^1 (KaehlerDifferential R A)) →ₗ[A] T :=
    ((ModuleCat.restrictScalars (algebraMap A B)).map
      (ModuleCat.ofHom (quotientInverseCartier w hw p 1))).hom.comp
        (formMap (R := R) (A := A) (B := B) 1).hom
  have h : l.comp (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm.toLinearMap =
      r.comp (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm.toLinearMap := by
    apply (Char0.etaleDifferentialBasis v hv).ext
    intro i
    rw [Char0.etaleDifferentialBasis_apply]
    exact quotientInverseCartier_D v hv w hw p (v i)
  obtain ⟨z, rfl⟩ := (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm.surjective a
  exact LinearMap.congr_fun h z

private theorem cycleRepresentative_zero_tuple (t : Fin 0 → KaehlerDifferential R A) :
    (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p 0
      (exteriorPower.ιMulti A 0 t)).val = exteriorPower.ιMulti A 0 t := by
  apply Subtype.ext
  change ExteriorFrobeniusLift.lift A (KaehlerDifferential R A) p
    (EtaleClosedExteriorLift.oneFormMap v hv p
      (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p))
      (ExteriorAlgebra.ιMulti A 0 t) = ExteriorAlgebra.ιMulti A 0 t
  rw [ExteriorAlgebra.ιMulti_zero_apply, map_one]

private theorem quotient_natural_zero_tuple (t : Fin 0 → KaehlerDifferential R A) :
    (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p 0).hom
      (quotientInverseCartier v hv p 0 (exteriorPower.ιMulti A 0 t)) =
      quotientInverseCartier w hw p 0
        ((formMap (R := R) (A := A) (B := B) 0).hom (exteriorPower.ιMulti A 0 t)) := by
  change Submodule.Quotient.mk
    ((EtaleCohomologyCoefficientMaps.cycleMap v hv w hw p 0).hom
      (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p 0
        (exteriorPower.ιMulti A 0 t))) = Submodule.Quotient.mk
      (EtaleCartierCycleRepresentatives.cycleRepresentative w hw p 0
        (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) 0
          (exteriorPower.ιMulti A 0 t)))
  apply congrArg (fun z : EtaleCohomologyProducts.cycles w hw p 0 => Submodule.Quotient.mk z)
  apply Subtype.ext
  have ha := congrArg
    (Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) 0)
      (cycleRepresentative_zero_tuple v hv p t)
  have hc := Char0.canonicalDifferentialLinearMap_wedge (k := R) (R := A) (A := B) 0 t
  have hb := congrArg (fun a : ⋀[B]^0 (KaehlerDifferential R B) =>
    (EtaleCartierCycleRepresentatives.cycleRepresentative w hw p 0 a).val) hc
  exact ha.trans (hc.trans ((hb.trans
    (cycleRepresentative_zero_tuple w hw p (KaehlerDifferential.map R R A B ∘ t))).symm))

private theorem quotient_natural_product (q r : ℕ)
    (a : ⋀[A]^q (KaehlerDifferential R A)) (b : ⋀[A]^r (KaehlerDifferential R A))
    (ha : (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p q).hom
      (quotientInverseCartier v hv p q a) = quotientInverseCartier w hw p q
        ((formMap (R := R) (A := A) (B := B) q).hom a))
    (hb : (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p r).hom
      (quotientInverseCartier v hv p r b) = quotientInverseCartier w hw p r
        ((formMap (R := R) (A := A) (B := B) r).hom b)) :
    (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p (r+q)).hom
      (quotientInverseCartier v hv p (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b)) =
      quotientInverseCartier w hw p (r+q)
        ((formMap (R := R) (A := A) (B := B) (r+q)).hom
          (EtaleGradedLeibniz.wedgeProduct q r a b)) := by
  have hs := EtaleClosedExteriorLift.classMap_wedgeProduct v hv p
    (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p) q r a b
  have ht := EtaleClosedExteriorLift.classMap_wedgeProduct w hw p
    (EtaleCartierCycleRepresentatives.coordinateCycleMap w hw p) q r
    ((formMap (R := R) (A := A) (B := B) q).hom a)
    ((formMap (R := R) (A := A) (B := B) r).hom b)
  have hm := EtaleCohomologyCoefficientProducts.cohomologyProduct_map v hv w hw p q r
    (quotientInverseCartier v hv p q a) (quotientInverseCartier v hv p r b)
  have hp := EtaleCohomologyCoefficientProducts.canonicalMap_wedgeProduct (B := B) v hv q r a b
  exact (congrArg (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p (r+q)).hom hs).trans
    (hm.trans ((congrArg₂ (fun x y => EtaleCohomologyProducts.cohomologyProduct w hw p q r x y)
      ha hb).trans (ht.symm.trans (congrArg (quotientInverseCartier w hw p (r+q)) hp.symm))))

private theorem wedge_one_tuple (q : ℕ) (t : Fin (q+1) → KaehlerDifferential R A) :
    exteriorPower.ιMulti A (q+1) t = EtaleGradedLeibniz.wedgeProduct 1 q
      ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm (t 0))
        (exteriorPower.ιMulti A q (Matrix.vecTail t)) := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti A (q+1) t = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, EtaleGradedLeibniz.coe_wedgeProduct,
    exteriorPower.oneEquiv_symm_apply]
  change _ = ExteriorAlgebra.ιMulti A 1 (fun _ => t 0) * _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rfl

private theorem quotient_natural_tuple (q : ℕ) (t : Fin q → KaehlerDifferential R A) :
    (EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p q).hom
      (quotientInverseCartier v hv p q (exteriorPower.ιMulti A q t)) =
      quotientInverseCartier w hw p q
        ((formMap (R := R) (A := A) (B := B) q).hom (exteriorPower.ιMulti A q t)) := by
  induction q with
  | zero => exact quotient_natural_zero_tuple v hv w hw p t
  | succ q ih =>
    rw [wedge_one_tuple]
    exact quotient_natural_product v hv w hw p 1 q
      ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm (t 0))
      (exteriorPower.ιMulti A q (Matrix.vecTail t))
      (quotientInverseCartier_one v hv w hw p _) (ih (Matrix.vecTail t))

/-- The ENTIRE SAME canonical inverse Cartier maps commute with EVERY actual original
coefficient map in ALL degrees including zero. No higher or zero-degree agreement is supplied. -/
theorem quotientInverseCartier_naturality (q : ℕ) :
    ModuleCat.ofHom (quotientInverseCartier v hv p q) ≫
      EtaleCohomologyCoefficientMaps.cohomologyMap v hv w hw p q =
    formMap (R := R) (A := A) (B := B) q ≫
      (ModuleCat.restrictScalars (algebraMap A B)).map
        (ModuleCat.ofHom (quotientInverseCartier w hw p q)) := by
  apply ModuleCat.hom_ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro t
  exact quotient_natural_tuple v hv w hw p q t

/-- The SAME entire actual canonical maps into native WHOLE original Frobenius-complex
cohomology commute with EVERY original coefficient map, without flatness or etaleness of it. -/
theorem inverseCartier_naturality (q : ℕ) :
    ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier v hv p q) ≫
      EtaleCohomologyCoefficientMaps.nativeHomologyMap v hv w hw p q =
    formMap (R := R) (A := A) (B := B) q ≫
      (ModuleCat.restrictScalars (algebraMap A B)).map
        (ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier w hw p q)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hq := congrArg (fun F : ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A)) ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (EtaleCohomologyProducts.cohomology w hw p q)) => F a)
      (quotientInverseCartier_naturality v hv w hw p q)
  exact (EtaleCohomologyCoefficientMaps.nativeHomologyMap_cycleClass v hv w hw p q
    (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p q a)).trans
      (congrArg (EtaleCohomologyProducts.cohomologyIso w hw p q).inv.hom hq)

end EnvelopeProperty.Cartier.EtaleCartierCoefficientNaturality
