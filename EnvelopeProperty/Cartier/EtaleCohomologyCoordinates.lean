import EnvelopeProperty.Cartier.EtaleClosedExteriorLift
import EnvelopeProperty.Cartier.EtaleDifferentialIntrinsic

/-! # Whole original cycle and cohomology comparisons for actual etale coordinates -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCohomologyCoordinates
open CategoryTheory
open scoped Classical
universe u

private theorem transportedIso_inv {A : Type u} [CommRing A]
    {H H' Q Q' : ModuleCat A} (ev : H ≅ Q) (ew : H' ≅ Q') (e : Q ≅ Q') (z : Q) :
    (ev ≪≫ e ≪≫ ew.symm).hom.hom (ev.inv.hom z) = ew.inv.hom (e.hom.hom z) := by
  change ew.inv.hom (e.hom.hom (ev.hom.hom (ev.inv.hom z))) = _
  rw [show ev.hom.hom (ev.inv.hom z) = z from Iso.inv_hom_id_apply ev z]

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {n m : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP B p]

/-- The ENTIRE actual original cycle modules agree by SAME-form identity, from the proved
whole original differential equality, even for coordinate tuples of different lengths. -/
def cycleIso (q : ℕ) : EtaleCohomologyProducts.cycles v hv p q ≃ₗ[B]
    EtaleCohomologyProducts.cycles w hw p q where
  toFun z := ⟨z.val, (EtaleDifferentialIntrinsic.differential_eq_of_coordinates w hw v hv q z.val).trans z.property⟩
  invFun z := ⟨z.val, (EtaleDifferentialIntrinsic.differential_eq_of_coordinates v hv w hw q z.val).trans z.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- EVERY actual original cycle keeps its SAME entire original form. -/
theorem cycleIso_val (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    (cycleIso v hv w hw p q z).val = z.val := rfl

/-- The actual entire incoming differentials into cycles commute with this SAME-form comparison. -/
theorem toCycles_map (q : ℕ) (a : EtaleDeRham.frobeniusModule (R := R) (B := B) p q) :
    cycleIso v hv w hw p (q+1) (EtaleCohomologyProducts.toCycles v hv p q a) =
      EtaleCohomologyProducts.toCycles w hw p q a := by
  apply Subtype.ext
  exact EtaleDifferentialIntrinsic.differential_eq_of_coordinates v hv w hw q a

/-- The WHOLE actual original boundary submodules are identified, including degree zero. -/
theorem boundaries_map (q : ℕ) :
    (EtaleCohomologyProducts.boundaries v hv p q).map (cycleIso v hv w hw p q).toLinearMap =
      EtaleCohomologyProducts.boundaries w hw p q := by
  cases q with
  | zero => exact Submodule.map_bot _
  | succ q =>
    change (LinearMap.range (EtaleCohomologyProducts.toCycles v hv p q)).map
      (cycleIso v hv w hw p (q+1)).toLinearMap =
        LinearMap.range (EtaleCohomologyProducts.toCycles w hw p q)
    rw [← LinearMap.range_comp]
    congr 1
    apply LinearMap.ext
    intro a
    exact toCycles_map v hv w hw p q a

/-- Genuine whole original cycle/boundary quotient comparison, with no comparison premise. -/
def quotientIso (q : ℕ) : EtaleCohomologyProducts.cohomology v hv p q ≃ₗ[B]
    EtaleCohomologyProducts.cohomology w hw p q :=
  Submodule.Quotient.equiv _ _ (cycleIso v hv w hw p q) (boundaries_map v hv w hw p q)

/-- EVERY original quotient cycle class retains its SAME entire original form. -/
theorem quotientIso_class (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    quotientIso v hv w hw p q ((EtaleCohomologyProducts.boundaries v hv p q).mkQ z) =
      (EtaleCohomologyProducts.boundaries w hw p q).mkQ (cycleIso v hv w hw p q z) := rfl

/-- The same actual original native whole-complex cohomology comparison in EVERY degree. -/
def nativeHomologyIso (q : ℕ) : (EtaleDeRham.frobeniusComplex v hv p).homology q ≅
    (EtaleDeRham.frobeniusComplex w hw p).homology q :=
  EtaleCohomologyProducts.cohomologyIso v hv p q ≪≫ (quotientIso v hv w hw p q).toModuleIso ≪≫
    (EtaleCohomologyProducts.cohomologyIso w hw p q).symm

/-- EVERY cycle's class in the original native whole-complex cohomology is carried by its SAME
whole form, not merely a selected basis or abstract cohomology-module identification. -/
theorem nativeHomologyIso_cycleClass (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    (nativeHomologyIso v hv w hw p q).hom.hom
      ((EtaleCohomologyProducts.nativeCycleClass v hv p q).toFun z) =
      (EtaleCohomologyProducts.nativeCycleClass w hw p q).toFun (cycleIso v hv w hw p q z) :=
  transportedIso_inv (EtaleCohomologyProducts.cohomologyIso v hv p q)
    (EtaleCohomologyProducts.cohomologyIso w hw p q) (quotientIso v hv w hw p q).toModuleIso
      ((EtaleCohomologyProducts.boundaries v hv p q).mkQ z)

/-- The entire original cycle products commute with the SAME-form coordinate comparison. -/
theorem cycleProduct_map (q r : ℕ) (a : EtaleCohomologyProducts.cycles v hv p q)
    (b : EtaleCohomologyProducts.cycles v hv p r) :
    (cycleIso v hv w hw p (r+q)).toFun
      (((EtaleCohomologyProducts.cycleProduct (R := R) v hv p q r).toFun a).toFun b) =
      ((EtaleCohomologyProducts.cycleProduct (R := R) w hw p q r).toFun
        ((cycleIso v hv w hw p q).toFun a)).toFun ((cycleIso v hv w hw p r).toFun b) := by
  apply Subtype.ext
  rfl

/-- The ENTIRE original cohomology products commute with the SAME-form coordinate comparison. -/
theorem quotientProduct_map (q r : ℕ) (a : EtaleCohomologyProducts.cohomology v hv p q)
    (b : EtaleCohomologyProducts.cohomology v hv p r) :
    (quotientIso v hv w hw p (r+q)).toFun
      (((EtaleCohomologyProducts.cohomologyProduct (R := R) v hv p q r).toFun a).toFun b) =
      ((EtaleCohomologyProducts.cohomologyProduct (R := R) w hw p q r).toFun
        ((quotientIso v hv w hw p q).toFun a)).toFun ((quotientIso v hv w hw p r).toFun b) := by
  refine Submodule.Quotient.induction_on _ a ?_
  intro a
  refine Submodule.Quotient.induction_on _ b ?_
  intro b
  exact congrArg (EtaleCohomologyProducts.boundaries w hw p (r+q)).mkQ
    (cycleProduct_map v hv w hw p q r a b)

/-- ALL actual closed exterior lifts commute with the SAME-form cycle comparison, after
transporting the ACTUAL original one-cycle map itself. -/
theorem cycleRepresentative_map
    (f : KaehlerDifferential R B →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (q : ℕ) (a : ⋀[B]^q (KaehlerDifferential R B)) :
    (cycleIso v hv w hw p q).toFun
      ((EtaleClosedExteriorLift.cycleRepresentative v hv p f q).toFun a) =
      (EtaleClosedExteriorLift.cycleRepresentative w hw p
        ((cycleIso v hv w hw p 1).toLinearMap.comp f) q).toFun a := by
  have hf : EtaleClosedExteriorLift.oneFormMap v hv p f =
      EtaleClosedExteriorLift.oneFormMap w hw p ((cycleIso v hv w hw p 1).toLinearMap.comp f) := by
    apply LinearMap.ext
    intro x
    rfl
  apply Subtype.ext
  exact congrArg (fun F : KaehlerDifferential R B →ₗ[B]
      ExteriorFrobeniusLift.forms B (KaehlerDifferential R B) p 1 =>
    ExteriorFrobeniusLift.homogeneous B (KaehlerDifferential R B) p F q a) hf

/-- The whole original quotient cohomology maps commute with true coordinate transport. -/
theorem classMap_map
    (f : KaehlerDifferential R B →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (q : ℕ) (a : ⋀[B]^q (KaehlerDifferential R B)) :
    (quotientIso v hv w hw p q).toFun ((EtaleClosedExteriorLift.classMap v hv p f q).toFun a) =
      (EtaleClosedExteriorLift.classMap w hw p
        ((cycleIso v hv w hw p 1).toLinearMap.comp f) q).toFun a :=
  (quotientIso_class v hv w hw p q (EtaleClosedExteriorLift.cycleRepresentative v hv p f q a)).trans
    (congrArg (EtaleCohomologyProducts.boundaries w hw p q).mkQ
      (cycleRepresentative_map v hv w hw p f q a))

/-- The SAME whole native original cohomology maps commute with the actual coordinate
comparison, on EVERY original form and in EVERY degree. -/
theorem nativeClassMap_map
    (f : KaehlerDifferential R B →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (q : ℕ) (a : ⋀[B]^q (KaehlerDifferential R B)) :
    (nativeHomologyIso v hv w hw p q).hom.hom
      ((EtaleClosedExteriorLift.nativeClassMap v hv p f q).toFun a) =
      (EtaleClosedExteriorLift.nativeClassMap w hw p
        ((cycleIso v hv w hw p 1).toLinearMap.comp f) q).toFun a :=
  (nativeHomologyIso_cycleClass v hv w hw p q
    (EtaleClosedExteriorLift.cycleRepresentative v hv p f q a)).trans
      (congrArg (EtaleCohomologyProducts.nativeCycleClass w hw p q).toFun
        (cycleRepresentative_map v hv w hw p f q a))

end EnvelopeProperty.Cartier.EtaleCohomologyCoordinates
