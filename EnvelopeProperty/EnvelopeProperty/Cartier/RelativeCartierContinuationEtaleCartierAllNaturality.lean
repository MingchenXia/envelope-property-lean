import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierMultiplicativity
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierNaturality
import EnvelopeProperty.Cartier.EtaleCohomologyCoefficientProducts

/-! # Actual native homology products and the SAME Cartier map are natural in every degree -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleCartierAllNaturality
open CategoryTheory
open scoped Classical
universe u

/-- Every actual native homology element is an actual whole-complex kernel cycle class. -/
theorem nativeCycleClass_surjective {S : Type u} [CommRing S]
    (K : CochainComplex (ModuleCat S) ℕ) (q : ℕ) :
    Function.Surjective (ModuleComplexNativeCycleClasses.cycleClass K q) := by
  change Function.Surjective (fun z : LinearMap.ker (K.sc q).g.hom =>
    (K.sc q).homologyπ ((K.sc q).moduleCatCyclesIso.inv z))
  intro x
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.sc q).homologyπ).mp inferInstance x
  refine ⟨(K.sc q).moduleCatCyclesIso.hom z, ?_⟩
  change (K.sc q).homologyπ
    ((K.sc q).moduleCatCyclesIso.inv ((K.sc q).moduleCatCyclesIso.hom z)) = x
  rw [Iso.hom_inv_id_apply]
  exact hz

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
local notation "TA" => RelativeFrobenius.twist (algebraMap k A) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "τ" => (CommRingCat.Hom.hom
  (RelativeEtaleCartierNaturality.twistMap (k := k) (A := A) (B := B) p))

/-- The SAME actual native cotangent map is semilinear along the genuine native twist map. -/
def cotangentSemilinear : KaehlerDifferential k TA →ₛₗ[τ] KaehlerDifferential k TB where
  toFun := RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := A) (B := B) p
  map_add' := (RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := A) (B := B) p).hom.map_add
  map_smul' := (RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := A) (B := B) p).hom.map_smul

/-- Genuine ALL-degree native exterior maps along the SAME original twist coefficient map. -/
def exteriorMap (q : ℕ) : ModuleCat.of TA (⋀[TA]^q (KaehlerDifferential k TA)) ⟶
    (ModuleCat.restrictScalars τ).obj (ModuleCat.of TB (⋀[TB]^q (KaehlerDifferential k TB))) :=
  ConcreteCategory.ofHom (C := ModuleCat TA)
    { toFun := CanonicalGeometry.exteriorSemilinearMap τ (cotangentSemilinear (k := k) p) q
      map_add' := (CanonicalGeometry.exteriorSemilinearMap τ (cotangentSemilinear (k := k) p) q).map_add
      map_smul' := (CanonicalGeometry.exteriorSemilinearMap τ (cotangentSemilinear (k := k) p) q).map_smulₛₗ }

/-- Every original source-function wedge retains its SAME canonical native target wedge,
including the empty wedge, with the unchanged original coefficient inclusion. -/
theorem exteriorMap_sourceWedge (q : ℕ) (t : Fin q → A) :
    exteriorMap (k := k) (A := A) (B := B) p q
      (exteriorPower.ιMulti TA q (fun i => KaehlerDifferential.D k TA
        ((RelativeFrobenius.sourceMap (algebraMap k A) p).hom (t i)))) =
    exteriorPower.ιMulti TB q (fun i => KaehlerDifferential.D k TB
      ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (algebraMap A B (t i)))) := by
  change CanonicalGeometry.exteriorSemilinearMap τ (cotangentSemilinear (k := k) p) q _ = _
  rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti]
  congr 1
  funext i
  change RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := A) (B := B) p
      (KaehlerDifferential.D k TA ((RelativeFrobenius.sourceMap (algebraMap k A) p).hom (t i))) = _
  rw [RelativeEtaleCartierNaturality.cotangentMap_D]
  have hs := congrArg (fun f : CommRingCat.of A ⟶ TB => f.hom (t i))
    (RelativeEtaleCartierNaturality.twistMap_source (k := k) (A := A) (B := B) p)
  exact congrArg (KaehlerDifferential.D k TB) hs

variable [CharP A p] [CharP B p]
variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
local notation "KA" => RelativeEtaleDeRham.complex v hv p
local notation "KB" => RelativeEtaleDeRham.complex w hw p

/-- The ACTUAL image-cycle constructor preserves the SAME entire original native wedge. -/
theorem imageCycle_product (q r : ℕ)
    (a : LinearMap.ker ((KA).sc q).g.hom) (b : LinearMap.ker ((KA).sc r).g.hom) :
    RelativeEtaleCartierNaturality.imageCycle p v hv w hw (r+q)
      (RelativeEtaleCohomologyProducts.nativeCycleProduct v hv p q r a b) =
    RelativeEtaleCohomologyProducts.nativeCycleProduct w hw p q r
      (RelativeEtaleCartierNaturality.imageCycle p v hv w hw q a)
      (RelativeEtaleCartierNaturality.imageCycle p v hv w hw r b) := by
  apply Subtype.ext
  exact EtaleCohomologyCoefficientProducts.canonicalMap_wedgeProduct v hv q r a.val b.val

/-- The ACTUAL native homology maps preserve the actual original product on EVERY homology
input, in ALL degrees, with no representative or product-compatibility assumption. -/
theorem homologyMap_product (q r : ℕ) (x : (KA).homology q) (y : (KA).homology r) :
    RelativeEtaleCartierNaturality.homologyMap p v hv w hw (r+q)
      (RelativeEtaleCohomologyProducts.nativeCohomologyProduct v hv p q r x y) =
    RelativeEtaleCohomologyProducts.nativeCohomologyProduct w hw p q r
      (RelativeEtaleCartierNaturality.homologyMap p v hv w hw q x)
      (RelativeEtaleCartierNaturality.homologyMap p v hv w hw r y) := by
  obtain ⟨a, rfl⟩ := nativeCycleClass_surjective KA q x
  obtain ⟨b, rfl⟩ := nativeCycleClass_surjective KA r y
  rw [RelativeEtaleCohomologyProducts.nativeCohomologyProduct_actual_cycleClass,
    RelativeEtaleCartierNaturality.homologyMap_cycleClass,
    RelativeEtaleCartierNaturality.homologyMap_cycleClass,
    RelativeEtaleCartierNaturality.homologyMap_cycleClass,
    RelativeEtaleCohomologyProducts.nativeCohomologyProduct_actual_cycleClass]
  exact congrArg (ModuleComplexNativeCycleClasses.cycleClass KB (r+q))
    (imageCycle_product p v hv w hw q r a b)

/-- Every arbitrary original function-wedge cycle maps to the SAME actual native target cycle. -/
theorem imageCycle_functionCycle (q : ℕ) (t : Fin q → A) :
    RelativeEtaleCartierNaturality.imageCycle p v hv w hw q
      (RelativeEtaleCartierMultiplicativity.functionCycle v hv p q t) =
    RelativeEtaleCartierMultiplicativity.functionCycle w hw p q (fun i => algebraMap A B (t i)) := by
  apply Subtype.ext
  rw [RelativeEtaleCartierNaturality.imageCycle_val,
    RelativeEtaleCartierMultiplicativity.functionCycle_val,
    RelativeEtaleCartierMultiplicativity.functionCycle_val]
  rw [EtaleDifferentialNaturality.canonicalMap_eq_exteriorSemilinear v hv,
    CanonicalGeometry.exteriorSemilinearMap_ιMulti]
  congr 1
  funext i
  change EtaleDifferentialNaturality.cotangentSemilinearMap
    ((t i)^(p-1) • KaehlerDifferential.D k A (t i)) = _
  rw [map_smulₛₗ, map_pow]
  congr 1
  exact KaehlerDifferential.map_D k k A B (t i)

/-- The SAME actual native relative Cartier equivalences are natural as ENTIRE native
module maps in EVERY degree, for ANY original algebra map between the two etale charts. -/
theorem inverseCartierIso_naturality (q : ℕ) :
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom ≫
      RelativeEtaleCartierNaturality.homologyMap p v hv w hw q =
    exteriorMap (k := k) (A := A) (B := B) p q ≫
      (ModuleCat.restrictScalars τ).map (RelativeEtaleCartierDomain.inverseCartierIso w hw p q).hom := by
  apply ModuleCat.hom_ext
  apply ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q).ext
  intro s
  change RelativeEtaleCartierNaturality.homologyMap p v hv w hw q
      ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom
        ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s)) =
    (RelativeEtaleCartierDomain.inverseCartierIso w hw p q).hom
      (exteriorMap (k := k) (A := A) (B := B) p q
        ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s))
  have hs : (RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s =
      exteriorPower.ιMulti TA q (fun j => KaehlerDifferential.D k TA
        ((RelativeFrobenius.sourceMap (algebraMap k A) p).hom
          (v (Set.powersetCard.ofFinEmbEquiv.symm s j)))) := by
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    congr 1
    funext j
    exact RelativeEtaleCartierDomain.cotangentBasis_D v hv p _
  rw [hs, RelativeEtaleCartierMultiplicativity.inverseCartierIso_sourceWedge,
    exteriorMap_sourceWedge, RelativeEtaleCartierMultiplicativity.inverseCartierIso_sourceWedge,
    RelativeEtaleCartierNaturality.homologyMap_cycleClass]
  exact congrArg (ModuleComplexNativeCycleClasses.cycleClass KB q)
    (imageCycle_functionCycle p v hv w hw q _)

end EnvelopeProperty.Cartier.RelativeEtaleCartierAllNaturality
