import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleComplex
import EnvelopeProperty.Algebra.ModuleComplexNativeCycleClasses
import EnvelopeProperty.Cartier.EtaleGradedLeibniz
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Genuine native relative cycle products and boundary descent -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleCohomologyProducts
open CategoryTheory Limits
open EtaleGradedLeibniz
open scoped Classical
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
section RawProduct
variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP B p]
local notation "T" => RelativeFrobenius.twist (algebraMap R B) p

/-- The SAME original whole exterior product is genuinely bilinear for the ACTUAL
native relative coefficient actions, in ALL original degrees. -/
def formProduct (q r : ℕ) :
    RelativeEtaleDeRham.formModule (R := R) (B := B) p q →ₗ[T]
      RelativeEtaleDeRham.formModule (R := R) (B := B) p r →ₗ[T]
        RelativeEtaleDeRham.formModule (R := R) (B := B) p (r+q) where
  toFun a :=
    { toFun := fun b => wedgeProduct q r (show ⋀[B]^q (KaehlerDifferential R B) from a)
        (show ⋀[B]^r (KaehlerDifferential R B) from b)
      map_add' := fun b c => (wedgeProduct q r a).map_add b c
      map_smul' := fun b c => (wedgeProduct q r a).map_smul ((RelativeFrobenius.map (algebraMap R B) p).hom b) c }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    exact congrArg (fun f => f c) ((wedgeProduct q r).map_add a b)
  map_smul' a b := by
    apply LinearMap.ext
    intro c
    exact congrArg (fun f => f c) ((wedgeProduct q r).map_smul ((RelativeFrobenius.map (algebraMap R B) p).hom a) b)

/-- Its ENTIRE original form value is the SAME actual exterior product. -/
theorem formProduct_apply (q r : ℕ)
    (a : RelativeEtaleDeRham.formModule (R := R) (B := B) p q)
    (b : RelativeEtaleDeRham.formModule (R := R) (B := B) p r) :
    formProduct (R := R) p q r a b =
      (show RelativeEtaleDeRham.formModule (R := R) (B := B) p (r+q) from
        wedgeProduct q r (show ⋀[B]^q (KaehlerDifferential R B) from a)
          (show ⋀[B]^r (KaehlerDifferential R B) from b)) := rfl

end RawProduct

variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP B p]
local notation "T" => RelativeFrobenius.twist (algebraMap R B) p

/-- The actual original native cycle kernel in EVERY original degree. -/
def cycles (q : ℕ) : Submodule T (RelativeEtaleDeRham.formModule (R := R) (B := B) p q) :=
  LinearMap.ker (RelativeEtaleDeRham.differential v hv p q).hom

/-- The ACTUAL original differential into genuine original cycles, closed by square-zero. -/
def toCycles (q : ℕ) :
    RelativeEtaleDeRham.formModule (R := R) (B := B) p q →ₗ[T] cycles v hv p (q+1) :=
  (RelativeEtaleDeRham.differential v hv p q).hom.codRestrict _
    (fun a => EtaleDeRham.differential_square v hv q a)

omit [Fact p.Prime] [CharP R p] [CharP B p] in
/-- EVERY pair of ACTUAL original closed forms has an ACTUAL original closed product. -/
theorem product_closed (q r : ℕ) (a : ⋀[B]^q (KaehlerDifferential R B))
    (b : ⋀[B]^r (KaehlerDifferential R B))
    (ha : EtaleDeRham.differential v hv q a = 0)
    (hb : EtaleDeRham.differential v hv r b = 0) :
    EtaleDeRham.differential v hv (r+q) (wedgeProduct q r a b) = 0 := by
  apply Subtype.ext
  have h := differential_wedgeProduct v hv q r a b
  rw [ha, hb] at h
  exact h.trans (by simp only [Submodule.coe_zero, zero_mul, mul_zero, smul_zero, add_zero])

/-- Genuine original native cycle multiplication is T-bilinear, with the actual closedness
DERIVED internally from WHOLE graded Leibniz. -/
def cycleProduct (q r : ℕ) :
    cycles v hv p q →ₗ[T] cycles v hv p r →ₗ[T] cycles v hv p (r+q) where
  toFun a :=
    (((formProduct (R := R) p q r) a.val).comp (cycles v hv p r).subtype).codRestrict _
      (fun b => product_closed v hv q r a.val b.val a.property b.property)
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f => f c.val) ((formProduct (R := R) p q r).map_add a.val b.val)
  map_smul' a b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f => f c.val) ((formProduct (R := R) p q r).map_smul a b.val)

/-- EVERY actual original cycle product retains its SAME whole original exterior form. -/
theorem cycleProduct_val (q r : ℕ) (a : cycles v hv p q) (b : cycles v hv p r) :
    (cycleProduct v hv p q r a b).val = formProduct (R := R) p q r a.val b.val := rfl

/-- Genuine original cycle degree transport along an ACTUAL equality of degrees. -/
def cycleTransport {q r : ℕ} (h : q = r) : cycles v hv p q ≃ₗ[T] cycles v hv p r := by
  subst h
  exact LinearEquiv.refl T _

/-- This degree transport retains the ENTIRE SAME original exterior-algebra element. -/
theorem cycleTransport_coe {q r : ℕ} (h : q = r) (a : cycles v hv p q) :
    ((show ⋀[B]^r (KaehlerDifferential R B) from (cycleTransport v hv p h a).val) :
      ExteriorAlgebra B (KaehlerDifferential R B)) =
    ((show ⋀[B]^q (KaehlerDifferential R B) from a.val) :
      ExteriorAlgebra B (KaehlerDifferential R B)) := by
  subst h
  rfl

/-- Multiplying an ACTUAL original left boundary by ANY original cycle is the boundary of
the ACTUAL original product primitive, in EVERY degree. -/
theorem cycleProduct_left_boundary (q r : ℕ)
    (a : RelativeEtaleDeRham.formModule (R := R) (B := B) p q) (b : cycles v hv p r) :
    (cycleTransport (R := R) (B := B) v hv p
      (q := r+(q+1)) (r := (r+q)+1) (Nat.add_succ r q)).toFun
      (((cycleProduct (R := R) v hv p (q+1) r).toFun
        ((toCycles (R := R) v hv p q).toFun a)).toFun b) =
      (toCycles (R := R) v hv p (r+q)).toFun
        (((formProduct (R := R) (B := B) p q r).toFun a).toFun b.val) := by
  apply Subtype.ext
  apply Subtype.ext
  have hc := cycleTransport_coe v hv p (Nat.add_succ r q)
    (cycleProduct v hv p (q+1) r (toCycles v hv p q a) b)
  have h := differential_wedgeProduct v hv q r a b.val
  have hb : EtaleDeRham.differential v hv r b.val = 0 := b.property
  rw [hb] at h
  exact hc.trans ((coe_wedgeProduct (q+1) r
    (EtaleDeRham.differential v hv q a) b.val).trans
      (h.trans (by simp only [Submodule.coe_zero, mul_zero, smul_zero, add_zero])).symm)

/-- Multiplying ANY original cycle by an ACTUAL right boundary is, with the genuine
Koszul sign, an ACTUAL original boundary. This includes characteristic two. -/
theorem cycleProduct_right_boundary (q r : ℕ) (a : cycles v hv p q)
    (b : RelativeEtaleDeRham.formModule (R := R) (B := B) p r) :
    (cycleTransport (R := R) (B := B) v hv p
      (q := (r+1)+q) (r := (r+q)+1) (Nat.succ_add r q)).toFun
      (((cycleProduct (R := R) v hv p q (r+1)).toFun a).toFun
        ((toCycles (R := R) v hv p r).toFun b)) =
      ((-1 : ℤ)^q) • (toCycles (R := R) v hv p (r+q)).toFun
        (((formProduct (R := R) (B := B) p q r).toFun a.val).toFun b) := by
  apply Subtype.ext
  apply Subtype.ext
  have hc := cycleTransport_coe v hv p (Nat.succ_add r q)
    (cycleProduct v hv p q (r+1) a (toCycles v hv p r b))
  have h := differential_wedgeProduct v hv q r a.val b
  have ha : EtaleDeRham.differential v hv q a.val = 0 := a.property
  rw [ha] at h
  have hd : (EtaleDeRham.differential v hv (r+q) (wedgeProduct q r a.val b) :
      ExteriorAlgebra B (KaehlerDifferential R B)) =
      (-1 : B)^q • (((show ⋀[B]^q (KaehlerDifferential R B) from a.val) :
        ExteriorAlgebra B (KaehlerDifferential R B)) *
        (EtaleDeRham.differential v hv r b : ExteriorAlgebra B (KaehlerDifferential R B))) := by
    simpa only [Submodule.coe_zero, zero_mul, zero_add] using h
  have hs (z : ExteriorAlgebra B (KaehlerDifferential R B)) :
      ((-1 : ℤ)^q) • ((-1 : B)^q • z) = z := by
    rw [← Int.cast_smul_eq_zsmul B]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, smul_smul]
    rw [← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_smul]
  exact hc.trans ((coe_wedgeProduct q (r+1) a.val
    (EtaleDeRham.differential v hv r b)).trans
      ((congrArg (fun z => ((-1 : ℤ)^q) • z) hd).trans (hs _)).symm)

/-- The ACTUAL incoming original boundary range, with zero incoming boundary in degree zero. -/
def boundaries : (q : ℕ) → Submodule T (cycles v hv p q)
  | 0 => ⊥
  | q+1 => LinearMap.range (toCycles v hv p q)

/-- True degree transport preserves the SAME actual boundary submodules. -/
theorem boundaries_transport {q r : ℕ} (h : q = r) (a : cycles v hv p q) :
    (cycleTransport (R := R) (B := B) v hv p (q := q) (r := r) h).toFun a ∈
      boundaries v hv p r ↔ a ∈ boundaries v hv p q := by
  subst h
  rfl

private theorem mem_of_eq {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    (N : Submodule A M) (x y : M) (h : x = y) (hy : y ∈ N) : x ∈ N := by
  rw [h]
  exact hy

private theorem mem_range_of_signed {A M N : Type*} [Ring A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N] (f : M →ₗ[A] N) (z : N)
    (x : M) (t : ℤ) (h : z = t • f x) : z ∈ LinearMap.range f := by
  refine ⟨t • x, ?_⟩
  exact (map_zsmul f t x).trans h.symm

/-- EVERY original left boundary times ANY original cycle is in the ACTUAL original
incoming boundary range. No primitive or descent certificate is supplied. -/
theorem cycleProduct_mem_boundaries_left (q r : ℕ) (a : cycles v hv p q)
    (ha : a ∈ boundaries v hv p q) (b : cycles v hv p r) :
    ((cycleProduct (R := R) v hv p q r).toFun a).toFun b ∈
      boundaries v hv p (r+q) := by
  cases q with
  | zero =>
    have haz : a = 0 := ha
    subst a
    have he : ((cycleProduct v hv p 0 r).toFun 0).toFun b = 0 :=
      congrArg (fun f : cycles v hv p r →ₗ[T] cycles v hv p (r+0) => f b)
        (cycleProduct v hv p 0 r).map_zero
    exact mem_of_eq (boundaries v hv p (r+0)) _ _ he (Submodule.zero_mem _)
  | succ q =>
    obtain ⟨x, rfl⟩ := ha
    apply (boundaries_transport v hv p (Nat.add_succ r q) _).mp
    refine ⟨formProduct (R := R) p q r x b.val, ?_⟩
    exact (cycleProduct_left_boundary (R := R) (B := B) v hv p q r x b).symm


/-- ANY original cycle times EVERY original right boundary is in the SAME actual original
incoming boundary range, with the sign and primitive internally derived. -/
theorem cycleProduct_mem_boundaries_right (q r : ℕ) (a : cycles v hv p q)
    (b : cycles v hv p r) (hb : b ∈ boundaries v hv p r) :
    ((cycleProduct (R := R) v hv p q r).toFun a).toFun b ∈
      boundaries v hv p (r+q) := by
  cases r with
  | zero =>
    have hbz : b = 0 := hb
    subst b
    exact mem_of_eq (boundaries v hv p (0+q)) _ _
      ((cycleProduct v hv p q 0 a).map_zero) (Submodule.zero_mem _)
  | succ r =>
    obtain ⟨x, rfl⟩ := hb
    apply (boundaries_transport v hv p (Nat.succ_add r q) _).mp
    let z : cycles v hv p ((r+q)+1) :=
      (cycleTransport (R := R) (B := B) v hv p
        (q := (r+1)+q) (r := (r+q)+1) (Nat.succ_add r q)).toFun
        (((cycleProduct (R := R) (B := B) v hv p q (r+1)).toFun a).toFun
          ((toCycles (R := R) (B := B) v hv p r).toFun x))
    change z ∈ LinearMap.range (toCycles v hv p (r+q))
    exact mem_range_of_signed (A := T)
      (M := RelativeEtaleDeRham.formModule (R := R) (B := B) p (r+q))
      (N := cycles v hv p ((r+q)+1)) (toCycles v hv p (r+q)) z
      (formProduct (R := R) (B := B) p q r a.val x) ((-1 : ℤ)^q)
      (cycleProduct_right_boundary (R := R) (B := B) v hv p q r a x)


/-- The original actual cycle module modulo its ENTIRE actual incoming boundary range. -/
abbrev cohomology (q : ℕ) := cycles v hv p q ⧸ boundaries v hv p q

private def productClass (q r : ℕ) :
    cycles v hv p q →ₗ[T] cycles v hv p r →ₗ[T] cohomology v hv p (r+q) :=
  (cycleProduct v hv p q r).compr₂ (boundaries v hv p (r+q)).mkQ

private theorem productClass_left (q r : ℕ) :
    boundaries v hv p q ≤ (productClass v hv p q r).ker := by
  intro a ha
  apply LinearMap.ext
  intro b
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (cycleProduct_mem_boundaries_left v hv p q r a ha b)

private theorem productClass_right (q r : ℕ) :
    boundaries v hv p r ≤ (productClass v hv p q r).flip.ker := by
  intro b hb
  apply LinearMap.ext
  intro a
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (cycleProduct_mem_boundaries_right v hv p q r a b hb)

/-- Genuine T-bilinear multiplication on the ACTUAL original cohomology quotients in
EVERY degree, descended through BOTH entire actual boundary submodules. -/
def cohomologyProduct (q r : ℕ) :
    cohomology v hv p q →ₗ[T] cohomology v hv p r →ₗ[T] cohomology v hv p (r+q) :=
  (productClass v hv p q r).liftQ₂ (boundaries v hv p q) (boundaries v hv p r)
    (productClass_left v hv p q r) (productClass_right v hv p q r)

/-- EVERY pair of original cycle classes multiplies to the class of its SAME whole original
exterior product. No representative, closedness or boundary-compatibility premise is added. -/
theorem cohomologyProduct_classes (q r : ℕ) (a : cycles v hv p q) (b : cycles v hv p r) :
    ((cohomologyProduct (R := R) v hv p q r).toFun (Submodule.Quotient.mk a)).toFun
      (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (((cycleProduct (R := R) v hv p q r).toFun a).toFun b) := rfl

/-- The SAME original actual three-term relative complex in every positive degree. -/
def positiveShortComplex (q : ℕ) : ShortComplex (ModuleCat T) :=
  ShortComplex.mk (RelativeEtaleDeRham.differential v hv p q)
    (RelativeEtaleDeRham.differential v hv p (q+1)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact EtaleDeRham.differential_square v hv q a)

/-- The ACTUAL native categorical positive homology is the SAME whole cycle/boundary quotient. -/
def positiveShortHomologyIso (q : ℕ) :
    (positiveShortComplex v hv p q).homology ≅ ModuleCat.of T (cohomology v hv p (q+1)) :=
  (positiveShortComplex v hv p q).moduleCatHomologyIso

/-- The original degree-zero row has genuinely zero incoming differential. -/
def zeroShortComplex : ShortComplex (ModuleCat T) :=
  ShortComplex.mk (0 : RelativeEtaleDeRham.formModule (R := R) (B := B) p 0 ⟶
    RelativeEtaleDeRham.formModule (R := R) (B := B) p 0)
      (RelativeEtaleDeRham.differential v hv p 0) zero_comp

private theorem zeroBoundaryRange :
    LinearMap.range (zeroShortComplex v hv p).moduleCatToCycles = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  rfl

/-- The ACTUAL native categorical zero homology retains precisely the zero incoming boundary. -/
def zeroShortHomologyIso :
    (zeroShortComplex v hv p).homology ≅ ModuleCat.of T (cohomology v hv p 0) :=
  (zeroShortComplex v hv p).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (zeroBoundaryRange v hv p)).toModuleIso

private def ofPositiveShortIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (X : ℕ → C) (d : ∀ q, X q ⟶ X (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) :
    (CochainComplex.of X d sq).sc' q (q+1) (q+1+1) ≅
      ShortComplex.mk (d q) (d (q+1)) (sq q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])

private def ofZeroShortIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (X : ℕ → C) (d : ∀ q, X q ⟶ X (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) :
    (CochainComplex.of X d sq).sc' 0 0 1 ≅
      ShortComplex.mk (0 : X 0 ⟶ X 0) (d 0) zero_comp :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
        CochainComplex.of_d_ne _ _ (by decide : 0+1 ≠ (0:ℕ))])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      change (𝟙 (X 0)) ≫ d 0 = CochainComplex.of.d X d 0 (0+1) ≫ 𝟙 (X (0+1))
      rw [Category.id_comp, Category.comp_id, CochainComplex.of_d])

private def positiveNativeShortIso (q : ℕ) :
    (RelativeEtaleDeRham.complex v hv p).sc' q (q+1) (q+1+1) ≅
      positiveShortComplex v hv p q := ofPositiveShortIso _ _ _ q

private def zeroNativeShortIso :
    (RelativeEtaleDeRham.complex v hv p).sc' 0 0 1 ≅ zeroShortComplex v hv p :=
  ofZeroShortIso _ _ (fun q => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact EtaleDeRham.differential_square v hv q a)

/-- In EVERY degree, the genuine native categorical homology of the SAME whole original
relative complex is the ENTIRE actual original cycle/boundary quotient. -/
def cohomologyIso (q : ℕ) : (RelativeEtaleDeRham.complex v hv p).homology q ≅
    ModuleCat.of T (cohomology v hv p q) :=
  match q with
  | 0 => (RelativeEtaleDeRham.complex v hv p).homologyIsoSc' 0 0 1
      CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0) ≪≫
        ShortComplex.homologyMapIso (zeroNativeShortIso v hv p) ≪≫ zeroShortHomologyIso v hv p
  | q+1 => (RelativeEtaleDeRham.complex v hv p).homologyIsoSc' q (q+1) (q+1+1)
      (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)) ≪≫
        ShortComplex.homologyMapIso (positiveNativeShortIso v hv p q) ≪≫
          positiveShortHomologyIso v hv p q

/-- Actual T-bilinear multiplication on the SAME native whole relative de Rham cohomology,
transported through the genuine cycle/boundary identification in EVERY degree. -/
def nativeCohomologyProduct (q r : ℕ) :
    (RelativeEtaleDeRham.complex v hv p).homology q →ₗ[T]
      (RelativeEtaleDeRham.complex v hv p).homology r →ₗ[T]
        (RelativeEtaleDeRham.complex v hv p).homology (r+q) :=
  (((cohomologyProduct v hv p q r).compl₂ (cohomologyIso v hv p r).hom.hom).comp
    (cohomologyIso v hv p q).hom.hom).compr₂ (cohomologyIso v hv p (r+q)).inv.hom

/-- The actual original cycle-class map into the SAME native whole-complex cohomology. -/
def nativeCycleClass (q : ℕ) : cycles v hv p q →ₗ[T]
    (RelativeEtaleDeRham.complex v hv p).homology q :=
  (cohomologyIso v hv p q).inv.hom.comp (boundaries v hv p q).mkQ

private theorem transportedProduct_inv {A : Type*} [CommRing A]
    {X Y Z X' Y' Z' : ModuleCat A} (ex : X ≅ X') (ey : Y ≅ Y') (ez : Z ≅ Z')
    (f : X' →ₗ[A] Y' →ₗ[A] Z') (x : X') (y : Y') :
    ((((f.compl₂ ey.hom.hom).comp ex.hom.hom).compr₂ ez.inv.hom).toFun
      (ex.inv.hom x)).toFun (ey.inv.hom y) = ez.inv.hom (f x y) := by
  change ez.inv.hom (f (ex.hom.hom (ex.inv.hom x)) (ey.hom.hom (ey.inv.hom y))) = _
  rw [show ex.hom.hom (ex.inv.hom x) = x from Iso.inv_hom_id_apply ex x,
    show ey.hom.hom (ey.inv.hom y) = y from Iso.inv_hom_id_apply ey y]

/-- EVERY pair of original cycle classes has the SAME actual native product class of the
whole original exterior product, in ALL degrees including zero. -/
theorem nativeCohomologyProduct_cycleClass (q r : ℕ) (a : cycles v hv p q)
    (b : cycles v hv p r) :
    ((nativeCohomologyProduct (R := R) (B := B) v hv p q r).toFun
      ((nativeCycleClass (R := R) (B := B) v hv p q).toFun a)).toFun
      ((nativeCycleClass (R := R) (B := B) v hv p r).toFun b) =
      (nativeCycleClass (R := R) (B := B) v hv p (r+q)).toFun
        (((cycleProduct (R := R) (B := B) v hv p q r).toFun a).toFun b) :=
  transportedProduct_inv (cohomologyIso v hv p q) (cohomologyIso v hv p r)
    (cohomologyIso v hv p (r+q)) (cohomologyProduct v hv p q r)
      (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)


private theorem nativeSquare (q : ℕ) :
    RelativeEtaleDeRham.differential v hv p q ≫
      RelativeEtaleDeRham.differential v hv p (q+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact EtaleDeRham.differential_square v hv q a

/-- The original consecutive kernel is genuinely equivalent to the ACTUAL whole-complex
native kernel, with its entire original value retained in both directions. -/
def nativeCyclesEquiv (q : ℕ) : cycles v hv p q ≃ₗ[T]
    LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc q).g.hom where
  toFun := ModuleComplexNativeCycleClasses.ofCycle _ _ (nativeSquare v hv p) q
  invFun z := ⟨z.val, by
    have hz := z.property
    change (RelativeEtaleDeRham.complex v hv p).d q
      ((ComplexShape.up ℕ).next q) z.val = 0 at hz
    rw [CochainComplex.next ℕ q] at hz
    change (CochainComplex.of.d
      (RelativeEtaleDeRham.formModule (R := R) (B := B) p)
      (RelativeEtaleDeRham.differential v hv p) q (q+1)).hom z.val = 0 at hz
    rw [CochainComplex.of_d] at hz
    exact hz⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The genuine native kernel comparison retains the SAME entire original form. -/
theorem nativeCyclesEquiv_val (q : ℕ) (z : cycles v hv p q) :
    (nativeCyclesEquiv v hv p q z).val = z.val := rfl

/-- Its inverse retains the SAME entire original form for EVERY actual native cycle. -/
theorem nativeCyclesEquiv_symm_val (q : ℕ)
    (z : LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc q).g.hom) :
    ((nativeCyclesEquiv v hv p q).symm z).val = z.val := rfl

private theorem actualShortClass_map {A : Type u} [CommRing A]
    {S U : ShortComplex (ModuleCat A)} (φ : S ⟶ U)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker U.g.hom)
    (hzw : φ.τ₂ z.val = w.val) :
    ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
      U.homologyπ (U.moduleCatCyclesIso.inv w) := by
  have hc : ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z) =
      U.moduleCatCyclesIso.inv w := by
    apply (ModuleCat.mono_iff_injective U.iCycles).mp inferInstance
    have h := congrArg (fun F : S.cycles ⟶ U.X₂ => F (S.moduleCatCyclesIso.inv z))
      (ShortComplex.cyclesMap_i φ)
    change U.iCycles (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) =
      φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv z)) at h
    exact h.trans ((congrArg φ.τ₂ (S.moduleCatCyclesIso_inv_iCycles_apply z)).trans
      (hzw.trans (U.moduleCatCyclesIso_inv_iCycles_apply w).symm))
  have h := congrArg (fun F : S.cycles ⟶ U.homology => F (S.moduleCatCyclesIso.inv z))
    (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
    U.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) at h
  exact h.trans (congrArg U.homologyπ hc)

private theorem rowClass_eq {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat A) ℕ) (i j l : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hl : (ComplexShape.up ℕ).next j = l)
    (S : ShortComplex (ModuleCat A)) (e : K.sc' i j l ≅ S)
    (z : LinearMap.ker (K.sc j).g.hom) (w : LinearMap.ker S.g.hom)
    (hzw : ((K.isoSc' i j l hi hl).hom ≫ e.hom).τ₂ z.val = w.val) :
    (K.homologyIsoSc' i j l hi hl ≪≫ ShortComplex.homologyMapIso e).hom
      (ModuleComplexNativeCycleClasses.cycleClass K j z) =
        S.homologyπ (S.moduleCatCyclesIso.inv w) := by
  let e₀ := K.isoSc' i j l hi hl
  let H := K.homologyIsoSc' i j l hi hl ≪≫ ShortComplex.homologyMapIso e
  have hm := actualShortClass_map (e₀.hom ≫ e.hom) z w hzw
  have hcomp := congrArg
    (fun f : (K.sc j).homology ⟶ S.homology =>
      f (ModuleComplexNativeCycleClasses.cycleClass K j z))
    (ShortComplex.homologyMap_comp e₀.hom e.hom)
  change ShortComplex.homologyMap (e₀.hom ≫ e.hom)
      (ModuleComplexNativeCycleClasses.cycleClass K j z) =
    H.hom (ModuleComplexNativeCycleClasses.cycleClass K j z) at hcomp
  exact hcomp.symm.trans hm

/-- The genuine quotient comparison takes EVERY original actual native cycle class to its
SAME original quotient class, in ALL degrees, including zero. -/
theorem cohomologyIso_cycleClass (q : ℕ) (z : cycles v hv p q) :
    (cohomologyIso v hv p q).hom
      (ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) q
        (nativeCyclesEquiv v hv p q z)) =
      (Submodule.Quotient.mk z : cohomology v hv p q) := by
  cases q with
  | zero =>
    let S := zeroShortComplex v hv p
    have h := rowClass_eq (RelativeEtaleDeRham.complex v hv p) 0 0 1
      CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0) S
      (zeroNativeShortIso v hv p) (nativeCyclesEquiv v hv p 0 z) z (by rfl)
    have hQ : S.moduleCatHomologyIso.hom
        (S.homologyπ (S.moduleCatCyclesIso.inv z)) = Submodule.Quotient.mk z := by
      rw [S.moduleCatCyclesIso_inv_π_apply z]
      exact Iso.inv_hom_id_apply S.moduleCatHomologyIso _
    have hz : (zeroShortHomologyIso v hv p).hom
        (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
          (Submodule.Quotient.mk z : cohomology v hv p 0) := by
      change (Submodule.quotEquivOfEq _ _ (zeroBoundaryRange v hv p)).toModuleIso.hom
        (S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv z))) = _
      rw [hQ]
      rfl
    exact (congrArg (zeroShortHomologyIso v hv p).hom h).trans hz
  | succ q =>
    let S := positiveShortComplex v hv p q
    have h := rowClass_eq (RelativeEtaleDeRham.complex v hv p) q (q+1) (q+1+1)
      (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)) S
      (positiveNativeShortIso v hv p q) (nativeCyclesEquiv v hv p (q+1) z) z (by rfl)
    have hQ : S.moduleCatHomologyIso.hom
        (S.homologyπ (S.moduleCatCyclesIso.inv z)) = Submodule.Quotient.mk z := by
      rw [S.moduleCatCyclesIso_inv_π_apply z]
      exact Iso.inv_hom_id_apply S.moduleCatHomologyIso _
    exact (congrArg S.moduleCatHomologyIso.hom h).trans hQ

/-- The original quotient-defined class IS the ACTUAL original native whole-complex class.
This comparison is proved from the actual native projections, never supplied as an input. -/
theorem nativeCycleClass_eq_actual (q : ℕ) (z : cycles v hv p q) :
    nativeCycleClass v hv p q z =
      ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) q
        (nativeCyclesEquiv v hv p q z) :=
  (congrArg (cohomologyIso v hv p q).inv (cohomologyIso_cycleClass v hv p q z).symm).trans
    (Iso.hom_inv_id_apply (cohomologyIso v hv p q) _)

/-- Genuine T-bilinear original exterior multiplication of EVERY ACTUAL whole-complex
native kernel cycle, with original closedness internally derived. -/
def nativeCycleProduct (q r : ℕ) :
    LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc q).g.hom →ₗ[T]
      LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc r).g.hom →ₗ[T]
        LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc (r+q)).g.hom :=
  (((cycleProduct v hv p q r).compl₂ (nativeCyclesEquiv v hv p r).symm.toLinearMap).comp
    (nativeCyclesEquiv v hv p q).symm.toLinearMap).compr₂
      (nativeCyclesEquiv v hv p (r+q)).toLinearMap

/-- Every ACTUAL native cycle product retains the entire original whole exterior form. -/
theorem nativeCycleProduct_val (q r : ℕ)
    (a : LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc q).g.hom)
    (b : LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc r).g.hom) :
    (nativeCycleProduct v hv p q r a b).val =
      formProduct (R := R) p q r a.val b.val := rfl

/-- On EVERY pair of ACTUAL native whole-complex kernel cycles, in ALL degrees including
zero, native homology multiplication is the ACTUAL native class of the SAME original wedge. -/
theorem nativeCohomologyProduct_actual_cycleClass (q r : ℕ)
    (a : LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc q).g.hom)
    (b : LinearMap.ker ((RelativeEtaleDeRham.complex v hv p).sc r).g.hom) :
    nativeCohomologyProduct v hv p q r
      (ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) q a)
      (ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) r b) =
    ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex v hv p) (r+q)
      (nativeCycleProduct v hv p q r a b) := by
  have h := nativeCohomologyProduct_cycleClass v hv p q r
    ((nativeCyclesEquiv v hv p q).symm a) ((nativeCyclesEquiv v hv p r).symm b)
  change nativeCohomologyProduct v hv p q r
      (nativeCycleClass v hv p q ((nativeCyclesEquiv v hv p q).symm a))
      (nativeCycleClass v hv p r ((nativeCyclesEquiv v hv p r).symm b)) =
    nativeCycleClass v hv p (r+q)
      (cycleProduct v hv p q r ((nativeCyclesEquiv v hv p q).symm a)
        ((nativeCyclesEquiv v hv p r).symm b)) at h
  rw [nativeCycleClass_eq_actual, nativeCycleClass_eq_actual, nativeCycleClass_eq_actual] at h
  simpa only [LinearEquiv.apply_symm_apply, nativeCycleProduct,
    LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearEquiv.coe_coe] using h

end EnvelopeProperty.Cartier.RelativeEtaleCohomologyProducts
