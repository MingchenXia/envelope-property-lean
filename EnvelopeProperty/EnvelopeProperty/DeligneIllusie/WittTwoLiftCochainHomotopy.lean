import EnvelopeProperty.DeligneIllusie.WittTwoLocalQuasiIsomorphism
import EnvelopeProperty.Algebra.ModuleComplexNativeBoundaries
import Mathlib.Algebra.Homology.Homotopy

/-! # Actual local whole cochain homotopies between the SAME original Witt lift maps -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoLiftCochainHomotopy
open CategoryTheory Limits
open scoped TensorProduct Classical
universe u

private def nativeComponent {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ}
    (s : ∀ q, K.X (q+1) ⟶ L.X q) (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    K.X i ⟶ L.X j := by
  have hi : j+1 = i := h
  subst i
  exact s j

private def assemble {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (F G : K ⟶ L)
    (hzero : F.f 0 = G.f 0) (s : ∀ q, K.X (q+1) ⟶ L.X q)
    (hd : ∀ i j, K.d i j = 0)
    (hs : ∀ q, s q ≫ L.d q (q+1) = F.f (q+1) - G.f (q+1)) : Homotopy F G := by
  have he : Homotopy.nullHomotopicMap' (nativeComponent s) = F-G := by
    apply HomologicalComplex.Hom.ext
    funext q
    cases q with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
        (show (ComplexShape.up ℕ).Rel 0 1 from rfl) (by intro l hl; exact Nat.noConfusion hl)]
      rw [hd, zero_comp]
      change 0 = F.f 0 - G.f 0
      rw [hzero, sub_self]
    | succ q =>
      rw [Homotopy.nullHomotopicMap'_f
        (show (ComplexShape.up ℕ).Rel q (q+1) from rfl)
        (show (ComplexShape.up ℕ).Rel (q+1) (q+1+1) from rfl)]
      rw [hd, zero_comp, zero_add]
      exact hs q
  refine (Homotopy.equivSubZero (f := F) (g := G)).symm ?_
  rw [← he]
  exact Homotopy.nullHomotopy' (nativeComponent s)

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
  WittTwoExteriorLiftMaps.originalCommSemiring WittTwoExteriorLiftMaps.originalSemiring
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev N := KaehlerDifferential k (B p k A)
variable (f g : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
private abbrev D := Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p

/-- The difference of the SAME actual native cycle-valued lift maps on EVERY original form. -/
def differenceCycle (q : ℕ) : (⋀[B p k A]^q (N p k A)) →ₗ[B p k A]
    LinearMap.ker ((D p k A v hv).sc q).g.hom :=
  WittTwoNativeCycleClasses.cycleMap p k A f hf v hv q -
    WittTwoNativeCycleClasses.cycleMap p k A g hg v hv q

/-- The actual difference has zero SAME whole native class, from the proved original Cartier values. -/
theorem differenceCycle_class_zero (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    ModuleComplexNativeCycleClasses.cycleClass (D p k A v hv) q
      (differenceCycle p k A f g hf hg v hv q w) = 0 := by
  change WittTwoNativeCycleClasses.classLinear (D p k A v hv) q
    (WittTwoNativeCycleClasses.cycleMap p k A f hf v hv q w -
      WittTwoNativeCycleClasses.cycleMap p k A g hg v hv q w) = 0
  rw [map_sub]
  change WittTwoNativeCycleClasses.classMap p k A f hf v hv q w -
    WittTwoNativeCycleClasses.classMap p k A g hg v hv q w = 0
  rw [WittTwoCartierClassComparison.classMap_eq_inverseCartier,
    WittTwoCartierClassComparison.classMap_eq_inverseCartier, sub_self]

private theorem exists_primitive (q : ℕ) (w : ⋀[B p k A]^(q+1) (N p k A)) :
    ∃ a : (D p k A v hv).X q, (D p k A v hv).d q (q+1) a =
      (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f (q+1) w -
        (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f (q+1) w := by
  have he := ModuleComplexNativeBoundaries.exists_preimage_of_cycleClass_zero
    (D p k A v hv) (q+1) (differenceCycle p k A f g hf hg v hv (q+1) w)
    (differenceCycle_class_zero p k A f g hf hg v hv (q+1) w)
  change ∃ a : (D p k A v hv).X ((ComplexShape.up ℕ).prev (q+1)),
    (D p k A v hv).d ((ComplexShape.up ℕ).prev (q+1)) (q+1) a =
      (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f (q+1) w -
        (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f (q+1) w at he
  rw [CochainComplex.prev_nat_succ] at he
  exact he

private def exteriorBasis (q : ℕ) := (Char0.etaleDifferentialBasis v hv).exteriorPower q

/-- Actual primitives on the original etale exterior basis extend to a genuine whole linear component. -/
def primitive (q : ℕ) : (⋀[B p k A]^(q+1) (N p k A)) →ₗ[B p k A] (D p k A v hv).X q :=
  (exteriorBasis p k A v hv (q+1)).constr (B p k A)
    (fun i => Classical.choose (exists_primitive p k A f g hf hg v hv q
      (exteriorBasis p k A v hv (q+1) i)))

/-- Its actual target differential equals the ENTIRE original component difference. -/
theorem primitive_d (q : ℕ) (w : ⋀[B p k A]^(q+1) (N p k A)) :
    (D p k A v hv).d q (q+1) (primitive p k A f g hf hg v hv q w) =
      (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f (q+1) w -
        (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f (q+1) w := by
  have he : ((D p k A v hv).d q (q+1)).hom.comp (primitive p k A f g hf hg v hv q) =
      ((WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f (q+1)).hom -
        ((WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f (q+1)).hom := by
    apply (exteriorBasis p k A v hv (q+1)).ext
    intro i
    change (D p k A v hv).d q (q+1) (primitive p k A f g hf hg v hv q
      (exteriorBasis p k A v hv (q+1) i)) = _
    unfold primitive
    rw [Module.Basis.constr_basis]
    exact Classical.choose_spec (exists_primitive p k A f g hf hg v hv q
      (exteriorBasis p k A v hv (q+1) i))
  exact LinearMap.congr_fun he w

/-- The SAME original whole degree-zero maps agree, since there is no original incoming differential. -/
theorem zero_component : (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f 0 =
    (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  have he := ModuleComplexNativeBoundaries.exists_preimage_of_cycleClass_zero
    (D p k A v hv) 0 (differenceCycle p k A f g hf hg v hv 0 w)
    (differenceCycle_class_zero p k A f g hf hg v hv 0 w)
  change ∃ a : (D p k A v hv).X ((ComplexShape.up ℕ).prev 0),
    (D p k A v hv).d ((ComplexShape.up ℕ).prev 0) 0 a =
      (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f 0 w -
        (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f 0 w at he
  rw [CochainComplex.prev_nat_zero] at he
  obtain ⟨a, ha⟩ := he
  have hz : (D p k A v hv).d 0 0 = 0 := (D p k A v hv).shape 0 0 (by decide)
  rw [hz] at ha
  exact sub_eq_zero.mp ha.symm

/-- The SAME original whole divided maps admit a genuine native ALLq cochain homotopy. -/
def cochainHomotopy : Homotopy (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv)
    (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv) := by
  apply assemble _ _ (zero_component p k A f g hf hg v hv)
    (fun q => ModuleCat.ofHom
      (X := (WittTwoExteriorLiftMaps.zeroComplex p k A).X (q+1))
      (Y := (D p k A v hv).X q) (primitive p k A f g hf hg v hv q))
  · intro i j
    exact ZeroComplexNativeHomology.d_eq_zero
      (fun q => ModuleCat.of (B p k A) (⋀[B p k A]^q (N p k A))) i j
  · intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact primitive_d p k A f g hf hg v hv q

/-- Actual original Witt lifts with their reductions DERIVE local homotopy existence, without supplied data. -/
theorem exists_cochainHomotopy : Nonempty (Homotopy
    (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv)
    (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv)) :=
  ⟨cochainHomotopy p k A f g hf hg v hv⟩

end EnvelopeProperty.DeligneIllusie.WittTwoLiftCochainHomotopy
