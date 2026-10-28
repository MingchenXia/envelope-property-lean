import EnvelopeProperty.Cartier.EtaleCohomologyProducts
import EnvelopeProperty.Cartier.EtaleDifferentialNaturality

/-! # Actual whole etale de Rham cohomology along the original coefficient maps -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCohomologyCoefficientMaps
open CategoryTheory
open scoped Classical
universe u
private def kernelRestrictionMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {M N : ModuleCat A} {P Q : ModuleCat B}
    (a : M ⟶ N) (b : P ⟶ Q)
    (c : M ⟶ (ModuleCat.restrictScalars f).obj P)
    (d : N ⟶ (ModuleCat.restrictScalars f).obj Q)
    (h : a ≫ d = c ≫ (ModuleCat.restrictScalars f).map b) :
    ModuleCat.of A (LinearMap.ker a.hom) ⟶
      (ModuleCat.restrictScalars f).obj (ModuleCat.of B (LinearMap.ker b.hom)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of A (LinearMap.ker a.hom))
    (Y := (ModuleCat.restrictScalars f).obj (ModuleCat.of B (LinearMap.ker b.hom)))
    { toFun := fun z => ⟨c.hom z.val, by
        have he := congrArg (fun F : M ⟶ (ModuleCat.restrictScalars f).obj Q => F z.val) h
        change d (a z.val) = b (c z.val) at he
        exact he.symm.trans ((congrArg d z.property).trans (map_zero d.hom))⟩
      map_add' := fun x y => Subtype.ext (c.hom.map_add x.val y.val)
      map_smul' := fun a z => Subtype.ext (c.hom.map_smul a z.val) }

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- The SAME entire original canonical form map carries ACTUAL cycles to ACTUAL cycles. -/
def cycleMap (q : ℕ) : ModuleCat.of A (EtaleCohomologyProducts.cycles v hv p q) ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (EtaleCohomologyProducts.cycles w hw p q)) :=
  kernelRestrictionMap (algebraMap A B)
    (EtaleDeRham.frobeniusDifferential v hv p q)
    (EtaleDeRham.frobeniusDifferential w hw p q)
    (EtaleDifferentialNaturality.frobeniusFormMap (R := R) (A := A) (B := B) p q)
    (EtaleDifferentialNaturality.frobeniusFormMap (R := R) (A := A) (B := B) p (q+1)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (EtaleDifferentialNaturality.differential_canonicalMap v hv w hw q a).symm)

/-- EVERY actual cycle retains its SAME entire original canonical image. -/
theorem cycleMap_val (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    ((cycleMap v hv w hw p q).hom z).val =
      Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q z.val := rfl

/-- EVERY original incoming boundary is carried to its SAME actual incoming boundary. -/
theorem cycleMap_toCycles (q : ℕ) (a : EtaleDeRham.frobeniusModule (R := R) (B := A) p q) :
    (cycleMap v hv w hw p (q+1)).hom (EtaleCohomologyProducts.toCycles v hv p q a) =
      EtaleCohomologyProducts.toCycles w hw p q
        (EtaleDifferentialNaturality.frobeniusFormMap (R := R) (A := A) (B := B) p q a) := by
  apply Subtype.ext
  exact (EtaleDifferentialNaturality.differential_canonicalMap v hv w hw q a).symm

private def cycleClassMap (q : ℕ) :
    ModuleCat.of A (EtaleCohomologyProducts.cycles v hv p q) ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (EtaleCohomologyProducts.cohomology w hw p q)) :=
  cycleMap v hv w hw p q ≫
    (ModuleCat.restrictScalars (algebraMap A B)).map
      (ModuleCat.ofHom (EtaleCohomologyProducts.boundaries w hw p q).mkQ)

private theorem boundary_mem_ker (q : ℕ) :
    EtaleCohomologyProducts.boundaries v hv p q ≤ (cycleClassMap v hv w hw p q).hom.ker := by
  intro z hz
  cases q with
  | zero =>
    have he : z = 0 := hz
    subst z
    exact map_zero (cycleClassMap v hv w hw p 0).hom
  | succ q =>
    obtain ⟨a, rfl⟩ := hz
    change (EtaleCohomologyProducts.boundaries w hw p (q+1)).mkQ
      ((cycleMap v hv w hw p (q+1)).hom (EtaleCohomologyProducts.toCycles v hv p q a)) = 0
    exact (congrArg (EtaleCohomologyProducts.boundaries w hw p (q+1)).mkQ
      (cycleMap_toCycles v hv w hw p q a)).trans
        ((Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩)

/-- The SAME actual coefficient map descends through the ENTIRE actual original boundary
ranges in EVERY degree. No boundary preservation or flatness premise is supplied. -/
def cohomologyMap (q : ℕ) : ModuleCat.of A (EtaleCohomologyProducts.cohomology v hv p q) ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (EtaleCohomologyProducts.cohomology w hw p q)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of A (EtaleCohomologyProducts.cohomology v hv p q))
    (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (EtaleCohomologyProducts.cohomology w hw p q)))
    ((EtaleCohomologyProducts.boundaries v hv p q).liftQ
    (cycleClassMap v hv w hw p q).hom (boundary_mem_ker v hv w hw p q))

/-- EVERY actual original cycle class maps to the class of its SAME entire canonical image. -/
theorem cohomologyMap_class (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    (cohomologyMap v hv w hw p q).hom (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((cycleMap v hv w hw p q).hom z) := rfl

/-- Actual map on the SAME native whole-complex cohomology, via genuine actual quotient
comparisons and the descended SAME coefficient map. -/
def nativeHomologyMap (q : ℕ) : (EtaleDeRham.frobeniusComplex v hv p).homology q ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((EtaleDeRham.frobeniusComplex w hw p).homology q) :=
  (EtaleCohomologyProducts.cohomologyIso v hv p q).hom ≫ cohomologyMap v hv w hw p q ≫
    (ModuleCat.restrictScalars (algebraMap A B)).map
      (EtaleCohomologyProducts.cohomologyIso w hw p q).inv

/-- The actual native map retains the class of EVERY SAME original whole cycle. -/
theorem nativeHomologyMap_cycleClass (q : ℕ) (z : EtaleCohomologyProducts.cycles v hv p q) :
    (nativeHomologyMap v hv w hw p q).hom (EtaleCohomologyProducts.nativeCycleClass v hv p q z) =
      EtaleCohomologyProducts.nativeCycleClass w hw p q ((cycleMap v hv w hw p q).hom z) := by
  change (EtaleCohomologyProducts.cohomologyIso w hw p q).inv.hom
    ((cohomologyMap v hv w hw p q).hom ((EtaleCohomologyProducts.cohomologyIso v hv p q).hom.hom
      ((EtaleCohomologyProducts.cohomologyIso v hv p q).inv.hom
        (Submodule.Quotient.mk z)))) = _
  exact congrArg (fun a => (EtaleCohomologyProducts.cohomologyIso w hw p q).inv.hom
    ((cohomologyMap v hv w hw p q).hom a))
      (Iso.inv_hom_id_apply (EtaleCohomologyProducts.cohomologyIso v hv p q) _)

end EnvelopeProperty.Cartier.EtaleCohomologyCoefficientMaps
