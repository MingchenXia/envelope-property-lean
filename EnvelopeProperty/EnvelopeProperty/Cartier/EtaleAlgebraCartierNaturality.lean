import EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusNaturality
import EnvelopeProperty.Cartier.EtaleAlgebraCartierIsomorphism
import EnvelopeProperty.Cartier.EtaleNativeCohomologyCoherence

/-! # SAME canonical Cartier naturality for ACTUAL native homology, ALL original algebras -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleAlgebraCartierNaturality
open CategoryTheory
universe u

private theorem restrictionHomology_naturality {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {K L : CochainComplex (ModuleCat B) ℕ} (e : K ⟶ L) (q : ℕ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map e) q ≫
      (ModuleComplexNativeCycleClasses.restrictionHomologyIso f L q).hom =
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso f K q).hom ≫
      (ModuleCat.restrictScalars f).map (HomologicalComplex.homologyMap e q) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat B) (ComplexShape.up ℕ) q).map e)
      (ModuleCat.restrictScalars f)

private theorem compose_comparison {C : Type*} [Category* C] {P Q R S T U : C}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ U) (d : Q ⟶ S) (e : S ⟶ U)
    (f : P ⟶ T) (g : T ⟶ S) (hb : b ≫ c = d ≫ e) (ha : a ≫ d = f ≫ g) :
    (a ≫ b) ≫ c = f ≫ (g ≫ e) := by
  rw [Category.assoc, hb, ← Category.assoc a d, ha, Category.assoc]

private theorem naturality_of_comparison {C : Type*} [Category* C]
    {X Y Y' Z W W' : C} {a : X ⟶ Y} {b : Z ⟶ W} {t : Y ⟶ W} {g : X ⟶ Z}
    (e : Y ⟶ Y') (d : W ⟶ W') [Mono d]
    (a' : X ⟶ Y') (b' : Z ⟶ W') (t' : Y' ⟶ W')
    (ha : a ≫ e = a') (hb : b ≫ d = b') (ht : t ≫ d = e ≫ t')
    (h : a' ≫ t' = g ≫ b') : a ≫ t = g ≫ b := by
  apply (cancel_mono d).mp
  calc
    (a ≫ t) ≫ d = (a ≫ e) ≫ t' := by rw [Category.assoc, ht, ← Category.assoc]
    _ = a' ≫ t' := congrArg (fun z => z ≫ t') ha
    _ = g ≫ b' := h
    _ = (g ≫ b) ≫ d := by rw [Category.assoc, hb]

private theorem zeroRingModuleSubsingleton {A : Type u} [CommRing A] [Subsingleton A]
    (M : ModuleCat A) : Subsingleton M := by
  have hz (x : M) : x = 0 := by
    calc
      x = (1 : A) • x := (one_smul A x).symm
      _ = (0 : A) • x := congrArg (fun a : A => a • x) (Subsingleton.elim _ _)
      _ = 0 := zero_smul A x
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)

/-- ACTUAL native homology-functor map of the SAME whole original coefficient complex. -/
def nativeHomologyMap (q : ℕ) : (EtaleAlgebraFrobeniusComplex.complex v hv p).homology q ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((EtaleAlgebraFrobeniusComplex.complex w hw p).homology q) :=
  HomologicalComplex.homologyMap (EtaleAlgebraFrobeniusNaturality.complexMap p v hv w hw) q ≫
    (ModuleComplexNativeCycleClasses.restrictionHomologyIso (algebraMap A B)
      (EtaleAlgebraFrobeniusComplex.complex w hw p) q).hom

/-- BOTH entire original coefficient complexes commute with their genuine old native comparisons. -/
theorem complexMap_native [CharP A p] [CharP B p] :
    EtaleAlgebraFrobeniusNaturality.complexMap p v hv w hw ≫
      ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (EtaleAlgebraFrobeniusComplex.nativeComplexIso w hw p).hom =
    (EtaleAlgebraFrobeniusComplex.nativeComplexIso v hv p).hom ≫
      EtaleDifferentialNaturality.frobeniusComplexMap v hv w hw p := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- ACTUAL native homology and coefficient restriction commute with SAME original native comparisons. -/
theorem nativeHomologyMap_native [CharP A p] [CharP B p] (q : ℕ) :
    nativeHomologyMap p v hv w hw q ≫
      (ModuleCat.restrictScalars (algebraMap A B)).map
        (EtaleAlgebraCartierIsomorphism.nativeHomologyIso w hw p q).hom =
    (EtaleAlgebraCartierIsomorphism.nativeHomologyIso v hv p q).hom ≫
      EtaleNativeCohomologyCoherence.nativeFunctorHomologyMap v hv p w hw q := by
  let F := ModuleCat.restrictScalars (algebraMap A B)
  let H := HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q
  let a := EtaleAlgebraFrobeniusNaturality.complexMap p v hv w hw
  let eA := (EtaleAlgebraFrobeniusComplex.nativeComplexIso v hv p).hom
  let eB := (EtaleAlgebraFrobeniusComplex.nativeComplexIso w hw p).hom
  let b := EtaleDifferentialNaturality.frobeniusComplexMap v hv w hw p
  have hc : H.map a ≫ H.map ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map eB) =
      H.map eA ≫ H.map b :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (complexMap_native p v hv w hw)).trans (H.map_comp _ _))
  exact compose_comparison _ _ _ _ _ _ _
    (restrictionHomology_naturality (algebraMap A B) eB q).symm hc

variable [PerfectRing k p]

/-- SAME canonical inverse Cartier is natural for ACTUAL native homology in EVERY original
algebra, including ZERO internally, with NO target CharP/nonzero/map-flatness assumptions. -/
theorem inverseCartier_naturality (q : ℕ) :
    EtaleAlgebraCartierIsomorphism.inverseCartier v hv p q ≫ nativeHomologyMap p v hv w hw q =
      EtaleCartierCoefficientNaturality.formMap (R := k) (A := A) (B := B) q ≫
        (ModuleCat.restrictScalars (algebraMap A B)).map
          (EtaleAlgebraCartierIsomorphism.inverseCartier w hw p q) := by
  by_cases h : Nontrivial B
  · let : Nontrivial B := h
    let : Nontrivial A := ⟨⟨0, 1, fun he => zero_ne_one
      (by simpa only [map_zero, map_one] using congrArg (algebraMap A B) he)⟩⟩
    let : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    let : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    let F := ModuleCat.restrictScalars (algebraMap A B)
    refine naturality_of_comparison
      (EtaleAlgebraCartierIsomorphism.nativeHomologyIso v hv p q).hom
      (F.map (EtaleAlgebraCartierIsomorphism.nativeHomologyIso w hw p q).hom)
      (ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier v hv p q))
      (F.map (ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier w hw p q)))
      (EtaleNativeCohomologyCoherence.nativeFunctorHomologyMap v hv p w hw q) ?_ ?_ ?_ ?_
    · exact EtaleAlgebraCartierIsomorphism.inverseCartier_native_map v hv p q
    · exact (F.map_comp _ _).symm.trans
        (congrArg F.map (EtaleAlgebraCartierIsomorphism.inverseCartier_native_map w hw p q))
    · exact nativeHomologyMap_native p v hv w hw q
    · exact EtaleNativeCohomologyCoherence.inverseCartier_nativeFunctor_naturality v hv p w hw q
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (zeroRingModuleSubsingleton
      ((EtaleAlgebraFrobeniusComplex.complex w hw p).homology q)).elim _ _

end EnvelopeProperty.Cartier.EtaleAlgebraCartierNaturality
