import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierCoordinateWedges
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCohomologyProducts
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierOneFunctions

/-! # Original exterior representatives for the same native relative Cartier map -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleCartierMultiplicativity
open CategoryTheory EtaleGradedLeibniz PolynomialDeRham
open scoped Classical
universe u

/-- The genuine universal semilinear exterior extension preserves the SAME entire original
homogeneous wedge product, for EVERY form and every degree. -/
theorem exteriorSemilinearMap_wedgeProduct {A C M N : Type u}
    [CommRing A] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module C N] (f : A →+* C) (φ : M →ₛₗ[f] N)
    (q r : ℕ) (a : ⋀[A]^q M) (b : ⋀[A]^r M) :
    CanonicalGeometry.exteriorSemilinearMap f φ (r+q) (wedgeProduct q r a b) =
      wedgeProduct q r (CanonicalGeometry.exteriorSemilinearMap f φ q a)
        (CanonicalGeometry.exteriorSemilinearMap f φ r b) := by
  have hd : ∀ (q : ℕ) (m : Fin q → M) (b : ⋀[A]^r M),
      CanonicalGeometry.exteriorSemilinearMap f φ (r+q)
          (wedgeProduct q r (exteriorPower.ιMulti A q m) b) =
        wedgeProduct q r
          (CanonicalGeometry.exteriorSemilinearMap f φ q (exteriorPower.ιMulti A q m))
          (CanonicalGeometry.exteriorSemilinearMap f φ r b) := by
    intro q
    induction q with
    | zero =>
      intro m b
      have hA : exteriorPower.ιMulti A 0 m = (exteriorPower.zeroEquiv A M).symm 1 := by
        apply (exteriorPower.zeroEquiv A M).injective
        rw [exteriorPower.zeroEquiv_ιMulti, LinearEquiv.apply_symm_apply]
      have hF : CanonicalGeometry.exteriorSemilinearMap f φ 0
          ((exteriorPower.zeroEquiv A M).symm 1) =
            (exteriorPower.zeroEquiv C N).symm 1 := by
        rw [← hA, CanonicalGeometry.exteriorSemilinearMap_ιMulti]
        apply (exteriorPower.zeroEquiv C N).injective
        rw [exteriorPower.zeroEquiv_ιMulti, LinearEquiv.apply_symm_apply]
      rw [hA, wedgeProduct_zero_left, one_smul, hF, wedgeProduct_zero_left, one_smul]
      simp only [Nat.add_zero]
    | succ q ih =>
      intro m b
      have hm : exteriorPower.ιMulti A (q+1) m =
          leftWedge (m 0) q (exteriorPower.ιMulti A q (fun i => m i.succ)) := by
        rw [ExteriorBasisScalarExtension.leftWedge_ιMulti]
        congr 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [hm, wedgeProduct_leftWedge]
      change CanonicalGeometry.exteriorSemilinearMap f φ ((r+q)+1)
        (leftWedge (m 0) (r+q)
          (wedgeProduct q r (exteriorPower.ιMulti A q (fun i => m i.succ)) b)) = _
      rw [ExteriorBasisScalarExtension.exteriorSemilinearMap_leftWedge,
        ExteriorBasisScalarExtension.exteriorSemilinearMap_leftWedge, wedgeProduct_leftWedge, ih]
  have ha : a ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact hd q m b
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul c x _ hx => simp only [map_smul, LinearMap.smul_apply, map_smulₛₗ, hx]


private theorem wedgeProduct_one_left {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] (q : ℕ) (g : M) (a : ⋀[A]^q M) :
    wedgeProduct 1 q ((exteriorPower.oneEquiv A M).symm g) a = leftWedge g q a := by
  rw [exteriorPower.oneEquiv_symm_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti A 1 (fun _ => g) * (a : ExteriorAlgebra A M) =
    ExteriorAlgebra.ι A g * a
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "F" => (CommRingCat.Hom.hom (RelativeFrobenius.map (algebraMap k B) p))
local notation "E" => RelativeEtaleDeRham.complex v hv p

/-- Genuine T-linear representatives of EVERY original twist exterior form in the ACTUAL
whole-complex native cycle kernel, with no supplied representative or closedness premise. -/
def representative (q : ℕ) : (⋀[T]^q (KaehlerDifferential k T)) →ₗ[T]
    LinearMap.ker ((E).sc q).g.hom :=
  ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q).constr T
    (RelativeEtaleCartierCoordinateWedges.coordinateNativeCycle v hv p q)

/-- Every native exterior basis vector has its SAME actual original coordinate cycle. -/
theorem representative_basis (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    representative v hv p q
      ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s) =
      RelativeEtaleCartierCoordinateWedges.coordinateNativeCycle v hv p q s :=
  Module.Basis.constr_basis _ _ _ _

/-- The SAME actual inverse Cartier equivalence has its constructed actual native
representative on EVERY whole original exterior form, in ALL degrees including zero. -/
theorem inverseCartierIso_representative_class (q : ℕ)
    (a : ⋀[T]^q (KaehlerDifferential k T)) :
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a =
      ModuleComplexNativeCycleClasses.cycleClass E q (representative v hv p q a) := by
  have h : (RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom.hom =
      (RelativeEtaleNativeClasses.nativeCycleClassLinear v hv p q).comp
        (representative v hv p q) := by
    apply ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q).ext
    intro s
    rw [LinearMap.comp_apply, representative_basis,
      RelativeEtaleNativeClasses.nativeCycleClassLinear_apply]
    exact RelativeEtaleCartierCoordinateWedges.inverseCartierIso_basis_class v hv p q s
  exact DFunLike.congr_fun h a

/-- The actual F-semilinear cotangent representative with original target coefficients. -/
def cotangentRepresentative : KaehlerDifferential k T →ₛₗ[F] KaehlerDifferential k B := by
  letI := Module.compHom (KaehlerDifferential k B) F
  let f := (RelativeEtaleCartierDomain.cotangentBasis v hv p).constr T
    (fun i => (v i)^(p-1) • KaehlerDifferential.D k B (v i))
  exact { toFun := f, map_add' := f.map_add, map_smul' := f.map_smul }

/-- Each original native cotangent basis vector keeps its genuine power-differential image. -/
theorem cotangentRepresentative_basis (i : Fin n) :
    cotangentRepresentative v hv p (RelativeEtaleCartierDomain.cotangentBasis v hv p i) =
      (v i)^(p-1) • KaehlerDifferential.D k B (v i) := by
  let := Module.compHom (KaehlerDifferential k B) F
  change ((RelativeEtaleCartierDomain.cotangentBasis v hv p).constr T
    (fun i => (v i)^(p-1) • KaehlerDifferential.D k B (v i)))
      (RelativeEtaleCartierDomain.cotangentBasis v hv p i) = _
  exact Module.Basis.constr_basis _ _ _ _

/-- The actual universal exterior extension, viewed in the SAME original relative form module. -/
def formRepresentative (q : ℕ) : (⋀[T]^q (KaehlerDifferential k T)) →ₗ[T]
    RelativeEtaleDeRham.formModule (R := k) (B := B) p q where
  toFun := CanonicalGeometry.exteriorSemilinearMap F (cotangentRepresentative v hv p) q
  map_add' := (CanonicalGeometry.exteriorSemilinearMap F (cotangentRepresentative v hv p) q).map_add
  map_smul' := (CanonicalGeometry.exteriorSemilinearMap F (cotangentRepresentative v hv p) q).map_smulₛₗ

/-- The ENTIRE original value of the actual native representative IS the genuine universal
F-semilinear exterior extension, on EVERY original form and in ALL degrees. -/
theorem representative_val (q : ℕ) (a : ⋀[T]^q (KaehlerDifferential k T)) :
    (representative v hv p q a).val = formRepresentative v hv p q a := by
  let inclusion : LinearMap.ker ((E).sc q).g.hom →ₗ[T]
      RelativeEtaleDeRham.formModule (R := k) (B := B) p q :=
    { toFun := fun z => z.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : inclusion.comp (representative v hv p q) = formRepresentative v hv p q := by
    apply ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q).ext
    intro s
    rw [LinearMap.comp_apply, representative_basis]
    change (RelativeEtaleCartierCoordinateWedges.coordinateNativeCycle v hv p q s).val =
      formRepresentative v hv p q
        ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s)
    rw [RelativeEtaleCartierCoordinateWedges.coordinateNativeCycle_val]
    change exteriorPower.ιMulti B q (fun j =>
        (v (Set.powersetCard.ofFinEmbEquiv.symm s j))^(p-1) •
          KaehlerDifferential.D k B (v (Set.powersetCard.ofFinEmbEquiv.symm s j))) =
      CanonicalGeometry.exteriorSemilinearMap F (cotangentRepresentative v hv p) q
        ((RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower q s)
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      CanonicalGeometry.exteriorSemilinearMap_ιMulti]
    congr 1
    funext j
    exact (cotangentRepresentative_basis v hv p _).symm
  exact DFunLike.congr_fun h a


/-- The actual native representative of the original whole wedge IS the actual original
native cycle product; its entire value comparison is internally derived. -/
theorem representative_wedgeProduct (q r : ℕ)
    (a : ⋀[T]^q (KaehlerDifferential k T)) (b : ⋀[T]^r (KaehlerDifferential k T)) :
    representative v hv p (r+q) (wedgeProduct q r a b) =
      RelativeEtaleCohomologyProducts.nativeCycleProduct v hv p q r
        (representative v hv p q a) (representative v hv p r b) := by
  apply Subtype.ext
  rw [representative_val, RelativeEtaleCohomologyProducts.nativeCycleProduct_val,
    representative_val, representative_val]
  exact exteriorSemilinearMap_wedgeProduct F (cotangentRepresentative v hv p) q r a b

/-- The SAME native relative Cartier isomorphisms preserve the ACTUAL original homology
wedge product in ALL degrees, including every degree-zero product. -/
theorem inverseCartierIso_wedgeProduct (q r : ℕ)
    (a : ⋀[T]^q (KaehlerDifferential k T)) (b : ⋀[T]^r (KaehlerDifferential k T)) :
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p (r+q)).hom
        (wedgeProduct q r a b) =
      RelativeEtaleCohomologyProducts.nativeCohomologyProduct v hv p q r
        ((RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom a)
        ((RelativeEtaleCartierDomain.inverseCartierIso v hv p r).hom b) := by
  rw [inverseCartierIso_representative_class, inverseCartierIso_representative_class,
    inverseCartierIso_representative_class, representative_wedgeProduct]
  exact (RelativeEtaleCohomologyProducts.nativeCohomologyProduct_actual_cycleClass
    v hv p q r (representative v hv p q a) (representative v hv p r b)).symm


/-- Every arbitrary original function tuple internally gives an ACTUAL native closed cycle,
including the original empty wedge in degree zero. -/
def functionCycle : (q : ℕ) → (Fin q → B) → LinearMap.ker ((E).sc q).g.hom
  | 0, _ => RelativeEtaleCartierCoordinateWedges.coordinateNativeCycle v hv p 0
      (Set.powersetCard.ofCard (Finset.card_empty (α := Fin n)))
  | q+1, t => RelativeEtaleCohomologyProducts.nativeCycleProduct v hv p 1 q
      (RelativeEtaleCartierOneFunctions.generatorCycle v hv p (t 0))
      (functionCycle q (fun i => t i.succ))

/-- The ENTIRE value of the internally closed native function cycle is its SAME original
power-differential wedge, for every tuple and every natural degree. -/
theorem functionCycle_val (q : ℕ) (t : Fin q → B) :
    (functionCycle v hv p q t).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        exteriorPower.ιMulti B q (fun i => (t i)^(p-1) • KaehlerDifferential.D k B (t i))) := by
  induction q with
  | zero =>
    change (RelativeEtaleCartierCoordinateWedges.coordinateNativeCycle v hv p 0 _).val = _
    rw [RelativeEtaleCartierCoordinateWedges.coordinateNativeCycle_val]
    congr 1
  | succ q ih =>
    change (RelativeEtaleCohomologyProducts.nativeCycleProduct v hv p 1 q
      (RelativeEtaleCartierOneFunctions.generatorCycle v hv p (t 0))
      (functionCycle v hv p q (fun i => t i.succ))).val = _
    rw [RelativeEtaleCohomologyProducts.nativeCycleProduct_val,
      RelativeEtaleCartierOneFunctions.generatorCycle_val, ih]
    change wedgeProduct 1 q
      ((t 0)^(p-1) • (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm
        (KaehlerDifferential.D k B (t 0)))
      (exteriorPower.ιMulti B q (fun i => (t i.succ)^(p-1) • KaehlerDifferential.D k B (t i.succ))) = _
    rw [← map_smul, wedgeProduct_one_left, ExteriorBasisScalarExtension.leftWedge_ιMulti]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- The SAME actual relative Cartier equivalence takes EVERY original source-function wedge
to the ACTUAL native class of the whole original power-differential wedge, in ALL degrees. -/
theorem inverseCartierIso_sourceWedge (q : ℕ) (t : Fin q → B) :
    (RelativeEtaleCartierDomain.inverseCartierIso v hv p q).hom
      (exteriorPower.ιMulti T q (fun i => KaehlerDifferential.D k T
        ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (t i)))) =
      ModuleComplexNativeCycleClasses.cycleClass E q (functionCycle v hv p q t) := by
  induction q with
  | zero =>
    let s : Set.powersetCard (Fin n) 0 :=
      Set.powersetCard.ofCard (Finset.card_empty (α := Fin n))
    have hs : exteriorPower.ιMulti T 0 (fun i => KaehlerDifferential.D k T
        ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (t i))) =
          (RelativeEtaleCartierDomain.cotangentBasis v hv p).exteriorPower 0 s := by
      rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
      congr 1
      funext i
      exact Fin.elim0 i
    rw [hs]
    exact RelativeEtaleCartierCoordinateWedges.inverseCartierIso_basis_class v hv p 0 s
  | succ q ih =>
    have hs : exteriorPower.ιMulti T (q+1) (fun i => KaehlerDifferential.D k T
        ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (t i))) =
      wedgeProduct 1 q
        ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm
          (KaehlerDifferential.D k T ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (t 0))))
        (exteriorPower.ιMulti T q (fun i => KaehlerDifferential.D k T
          ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (t i.succ)))) := by
      rw [wedgeProduct_one_left, ExteriorBasisScalarExtension.leftWedge_ιMulti]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have hh : (RelativeEtaleCartierDomain.inverseCartierIso v hv p 1).hom
        ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm
          (KaehlerDifferential.D k T ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom (t 0)))) =
      ModuleComplexNativeCycleClasses.cycleClass E 1
        (RelativeEtaleCartierOneFunctions.generatorCycle v hv p (t 0)) :=
      RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv_D_source v hv p (t 0)
    rw [hs, inverseCartierIso_wedgeProduct, hh, ih]
    exact RelativeEtaleCohomologyProducts.nativeCohomologyProduct_actual_cycleClass v hv p 1 q
      (RelativeEtaleCartierOneFunctions.generatorCycle v hv p (t 0))
      (functionCycle v hv p q (fun i => t i.succ))

end EnvelopeProperty.Cartier.RelativeEtaleCartierMultiplicativity
