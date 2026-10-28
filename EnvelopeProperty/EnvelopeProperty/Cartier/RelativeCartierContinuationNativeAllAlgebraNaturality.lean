import EnvelopeProperty.Cartier.RelativeCartierContinuationNativeAllAlgebraCartier
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierAllNaturality
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses

/-! # Actual all-algebra geometric-beta cochain and native homology maps

Original canonical form maps, actual coefficients and actual native homology
are retained. Zero endpoints need no characteristic instance.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeNativeAllAlgebraNaturality
open CategoryTheory
universe u

private def mapCycleGeneric {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) : LinearMap.ker (L.sc q).g.hom := by
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℕ) q).map φ
  refine ⟨ψ.τ₂ z.val, ?_⟩
  have h := congrArg (fun a : (K.sc q).X₂ ⟶ (L.sc q).X₃ => a z.val) ψ.comm₂₃
  change (L.sc q).g (ψ.τ₂ z.val) = ψ.τ₃ ((K.sc q).g z.val) at h
  exact h.trans ((congrArg ψ.τ₃ z.property).trans (ψ.τ₃.hom.map_zero))

private theorem mapCycleGeneric_val {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (q : ℕ)
    (z : LinearMap.ker (K.sc q).g.hom) :
    (mapCycleGeneric φ q z).val = φ.f q z.val := rfl

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "TA" => RelativeFrobenius.twist (algebraMap k A) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "βA" => CommRingCat.Hom.hom
  (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k A) p)
local notation "βB" => CommRingCat.Hom.hom
  (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p)
local notation "τ" => CommRingCat.Hom.hom
  (RelativeEtaleCartierNaturality.twistMap (k := k) (A := A) (B := B) p)

/-- The ENTIRE actual geometric coefficient square for EVERY original algebra endpoint. -/
theorem geometricCoefficientSquare :
    (algebraMap A B).comp (βA) = (βB).comp (τ) := by
  classical
  by_cases h : Nontrivial B
  · let := h
    let : Nontrivial A := (algebraMap A B).domain_nontrivial
    let : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    let : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    simpa only [SchemeRelativeFrobeniusAffineMap.ringMap_eq_native,
      CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
      (congrArg CommRingCat.Hom.hom
        (RelativeEtaleCartierNaturality.twistMap_frobenius (k := k) (A := A) (B := B) p)).symm
  · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    apply RingHom.ext
    intro t
    exact Subsingleton.elim _ _

private def originalFormMap (q : ℕ) :
    ModuleCat.of A (⋀[A]^q (KaehlerDifferential k A)) ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (⋀[B]^q (KaehlerDifferential k B))) :=
  ModuleCat.ofHom (X := ModuleCat.of A (⋀[A]^q (KaehlerDifferential k A)))
    (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (⋀[B]^q (KaehlerDifferential k B))))
    (Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q)

/-- EVERY original canonical form map with its actual native geometric-beta actions. -/
def formMap (q : ℕ) :
    SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := A) p q ⟶
      (ModuleCat.restrictScalars (τ)).obj
        (SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := B) p q) :=
  (ModuleCat.restrictScalars (βA)).map (originalFormMap (k := k) (A := A) (B := B) q) ≫
    (ModuleCat.restrictScalarsComp (βA) (algebraMap A B)).inv.app _ ≫
    (ModuleCat.restrictScalarsCongr
      (geometricCoefficientSquare (k := k) (A := A) (B := B) p)).hom.app _ ≫
    (ModuleCat.restrictScalarsComp (τ) (βB)).hom.app _

/-- EVERY original form retains its SAME entire canonical exterior pullback. -/
theorem formMap_apply (q : ℕ)
    (z : SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := A) p q) :
    formMap (k := k) (A := A) (B := B) p q z =
      Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q z := rfl

variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
local notation "KA" => SchemeRelativeFrobeniusAffineDeRham.complex v hv p
local notation "KB" => SchemeRelativeFrobeniusAffineDeRham.complex w hw p

/-- The ACTUAL whole original geometric-beta complexes admit their genuine canonical map. -/
def complexMap : (KA) ⟶
    ((ModuleCat.restrictScalars (τ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (KB) where
  f q := formMap (k := k) (A := A) (B := B) p q
  comm' q r h := by
    have hr : q+1 = r := h
    subst r
    simp only [SchemeRelativeFrobeniusAffineDeRham.complex,
      Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact EtaleDifferentialNaturality.differential_canonicalMap v hv w hw q z

/-- The actual cochain map internally produces the SAME original canonical target cycle. -/
def imageCycle (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    LinearMap.ker ((KB).sc q).g.hom :=
  let z' := mapCycleGeneric (complexMap p v hv w hw) q z
  ⟨z'.val, z'.property⟩

/-- EVERY target cycle has the SAME entire original canonical value. -/
theorem imageCycle_val (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    (imageCycle p v hv w hw q z).val =
      Char0.canonicalDifferentialLinearMap (k := k) (R := A) (A := B) q z.val := rfl

/-- Genuine HomologicalComplex homology of the ACTUAL map, with native restriction preservation. -/
def homologyMap (q : ℕ) : (KA).homology q ⟶
    (ModuleCat.restrictScalars (τ)).obj ((KB).homology q) :=
  HomologicalComplex.homologyMap (complexMap p v hv w hw) q ≫
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso (τ) (KB) q).hom

/-- EVERY original native source class maps to its internally derived actual target class. -/
theorem homologyMap_cycleClass (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    homologyMap p v hv w hw q (ModuleComplexNativeCycleClasses.cycleClass (KA) q z) =
      ModuleComplexNativeCycleClasses.cycleClass (KB) q (imageCycle p v hv w hw q z) := by
  let t := mapCycleGeneric (complexMap p v hv w hw) q z
  have h := ModuleComplexNativeCycleClasses.homologyMap_cycleClass (complexMap p v hv w hw)
    q z t rfl
  exact (congrArg (ModuleComplexNativeCycleClasses.restrictionHomologyIso (τ) (KB) q).hom h).trans
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso_cycleClass (τ) (KB) q t
      (imageCycle p v hv w hw q z) rfl)

section NativeComparison
variable [CharP A p]

/-- The actual whole comparison internally gives a native kernel cycle. -/
def nativeCycle (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc q).g.hom :=
  mapCycleGeneric (RelativeNativeAllAlgebraCartier.complexIso_native v hv p).hom q z

/-- Every comparison cycle retains exactly the same entire original form. -/
theorem nativeCycle_val (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    (nativeCycle p v hv q z).val = z.val :=
  (mapCycleGeneric_val (RelativeNativeAllAlgebraCartier.complexIso_native v hv p).hom q z).trans
    (RelativeNativeAllAlgebraCartier.complexIso_native_hom_f_apply v hv p q z.val)

/-- The actual homology comparison retains every original native cycle class. -/
theorem homologyIso_native_cycleClass (q : ℕ) (z : LinearMap.ker ((KA).sc q).g.hom) :
    (RelativeNativeAllAlgebraCartier.homologyIso_native v hv p q).hom
      (ModuleComplexNativeCycleClasses.cycleClass (KA) q z) =
    ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) q
      (nativeCycle p v hv q z) :=
  ModuleComplexNativeCycleClasses.homologyMap_cycleClass
    (RelativeNativeAllAlgebraCartier.complexIso_native v hv p).hom q z
    (nativeCycle p v hv q z)
    (mapCycleGeneric_val (RelativeNativeAllAlgebraCartier.complexIso_native v hv p).hom q z).symm

variable [CharP B p]

/-- Entire actual native homology squares agree, derived on every actual cycle class. -/
theorem homologyMap_native_square (q : ℕ) :
    (RelativeNativeAllAlgebraCartier.homologyIso_native v hv p q).hom ≫
      RelativeEtaleCartierNaturality.homologyMap p v hv w hw q =
    homologyMap p v hv w hw q ≫
      (ModuleCat.restrictScalars (τ)).map
        (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := RelativeEtaleCartierAllNaturality.nativeCycleClass_surjective (KA) q x
  change RelativeEtaleCartierNaturality.homologyMap p v hv w hw q
      ((RelativeNativeAllAlgebraCartier.homologyIso_native v hv p q).hom
        (ModuleComplexNativeCycleClasses.cycleClass (KA) q z)) =
    (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q).hom
      (homologyMap p v hv w hw q (ModuleComplexNativeCycleClasses.cycleClass (KA) q z))
  rw [homologyIso_native_cycleClass,
    RelativeEtaleCartierNaturality.homologyMap_cycleClass,
    homologyMap_cycleClass, homologyIso_native_cycleClass]
  apply congrArg (ModuleComplexNativeCycleClasses.cycleClass
    (RelativeEtaleDeRham.complex w hw p) q)
  apply Subtype.ext
  rw [RelativeEtaleCartierNaturality.imageCycle_val, nativeCycle_val,
    nativeCycle_val, imageCycle_val]

/-- The actual homology map is the genuine native map through the whole-complex isos. -/
theorem homologyMap_eq_native (q : ℕ) :
    homologyMap p v hv w hw q =
    (RelativeNativeAllAlgebraCartier.homologyIso_native v hv p q).hom ≫
      RelativeEtaleCartierNaturality.homologyMap p v hv w hw q ≫
      (ModuleCat.restrictScalars (τ)).map
        (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q).inv := by
  have h := congrArg (fun F => F ≫ (ModuleCat.restrictScalars (τ)).map
    (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q).inv)
    (homologyMap_native_square p v hv w hw q)
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at h
  have h0 := congrArg (fun F => homologyMap p v hv w hw q ≫ F)
    ((ModuleCat.restrictScalars (τ)).map_id ((KB).homology q))
  exact ((h0.trans (Category.comp_id _)).symm).trans h.symm
end NativeComparison

attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra

/-- The SAME actual T-linear all-degree Cartier square includes every zero endpoint. -/
theorem inverseCartierIso_naturality (q : ℕ) :
    (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom ≫
      homologyMap p v hv w hw q =
    RelativeEtaleCartierAllNaturality.exteriorMap (k := k) (A := A) (B := B) p q ≫
      (ModuleCat.restrictScalars (τ)).map
        (RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q).hom := by
  classical
  by_cases h : Nontrivial B
  · let := h
    let : Nontrivial A := (algebraMap A B).domain_nontrivial
    let : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    let : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    rw [RelativeNativeAllAlgebraCartier.inverseCartierIso_eq_native,
      RelativeNativeAllAlgebraCartier.inverseCartierIso_eq_native, homologyMap_eq_native]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, RelativeEtaleCartierAllNaturality.inverseCartierIso_naturality]
    simp only [Functor.map_comp, Category.assoc]
  · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    have : Subsingleton TB := RelativeAllAlgebraCartier.twist_subsingleton (k := k) (B := B) p
    have : Subsingleton ((ModuleCat.restrictScalars (τ)).obj ((KB).homology q)) :=
      RelativeAllAlgebraCartier.zeroRingModuleSubsingleton ((KB).homology q)
    exact (ModuleCat.isZero_of_subsingleton
      ((ModuleCat.restrictScalars (τ)).obj ((KB).homology q))).eq_of_tgt _ _

end EnvelopeProperty.Cartier.RelativeNativeAllAlgebraNaturality
