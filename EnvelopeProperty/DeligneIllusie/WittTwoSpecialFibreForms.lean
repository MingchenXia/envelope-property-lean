import EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreReduction
import EnvelopeProperty.Algebra.KaehlerAlgebraEquivalence
import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf

/-! # Native whole forms on the SAME actual geometric special-fibre opens -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreForms
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local instance] KaehlerAlgebraEquivalence.inversePair

private instance inversePairReverse {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    RingHomInvPair e.symm.toRingHom e.toRingHom where
  comp_eq := by ext b; exact e.apply_symm_apply b
  comp_eq₂ := by ext a; exact e.symm_apply_apply a

private def nativeCotangentMap {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (β : A →ₐ[R] B) :
    KaehlerDifferential R A →ₛₗ[β.toRingHom] KaehlerDifferential R B := by
  letI : Algebra A B := β.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun a => (β.commutes a).symm)
  let f := KaehlerDifferential.map R R A B
  exact { f.toAddMonoidHom with
    map_smul' := fun a w => by
      change f (a • w) = β a • f w
      rw [f.map_smul]
      exact (IsScalarTower.algebraMap_smul B a (f w)).symm }

private theorem nativeCotangentMap_D {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (β : A →ₐ[R] B) (a : A) :
    nativeCotangentMap β (KaehlerDifferential.D R A a) = KaehlerDifferential.D R B (β a) := by
  let : Algebra A B := β.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun a => (β.commutes a).symm)
  change KaehlerDifferential.map R R A B (KaehlerDifferential.D R A a) = _
  exact KaehlerDifferential.map_D R R A B a

private def nativeFormMap {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (β : A →ₐ[R] B) (q : ℕ) :
    (⋀[A]^q (KaehlerDifferential R A)) →ₛₗ[β.toRingHom] (⋀[B]^q (KaehlerDifferential R B)) :=
  CanonicalGeometry.exteriorSemilinearMap β.toRingHom (nativeCotangentMap β) q

private def nativeFormEquiv {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (q : ℕ) :
    (⋀[A]^q (KaehlerDifferential R A)) ≃ₛₗ[e.toRingHom] (⋀[B]^q (KaehlerDifferential R B)) := by
  let := RingHomInvPair.of_ringEquiv e.toRingEquiv
  let := RingHomInvPair.of_ringEquiv e.toRingEquiv.symm
  exact LinearEquiv.ofBijective
    (CanonicalGeometry.exteriorSemilinearMap e.toRingHom (KaehlerAlgebraEquivalence.equiv e).toLinearMap q)
    (CanonicalGeometry.exteriorSemilinearMap_bijective_of_ringIso e.toRingEquiv _
      (KaehlerAlgebraEquivalence.equiv e).bijective q)

private theorem nativeCotangentNaturality {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (eA : A ≃ₐ[R] C) (eB : B ≃ₐ[R] D) (β : A →ₐ[R] B) (r : C →ₐ[R] D)
    (he : ∀ a, eB (β a) = r (eA a)) (w : KaehlerDifferential R A) :
    (KaehlerAlgebraEquivalence.equiv eB).toLinearMap (nativeCotangentMap β w) =
      nativeCotangentMap r ((KaehlerAlgebraEquivalence.equiv eA).toLinearMap w) := by
  have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a,rfl⟩ := hw
    rw [nativeCotangentMap_D]
    exact (KaehlerAlgebraEquivalence.equiv_D eB (β a)).trans
      ((congrArg (KaehlerDifferential.D R D) (he a)).trans
        ((nativeCotangentMap_D r (eA a)).symm.trans
          (congrArg (nativeCotangentMap r) (KaehlerAlgebraEquivalence.equiv_D eA a)).symm))
  | zero => simp only [map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  | smul a w _ hw =>
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      LinearMap.map_smulₛₗ]
    exact congrArg₂ (fun (c : D) z => c • z) (he a) hw

private theorem nativeFormNaturality {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (eA : A ≃ₐ[R] C) (eB : B ≃ₐ[R] D) (β : A →ₐ[R] B) (r : C →ₐ[R] D)
    (he : ∀ a, eB (β a) = r (eA a)) (q : ℕ) (w : ⋀[A]^q (KaehlerDifferential R A)) :
    (nativeFormEquiv eB q).toLinearMap (nativeFormMap β q w) =
      nativeFormMap r q ((nativeFormEquiv eA q).toLinearMap w) := by
  have hw : w ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := KaehlerDifferential R A))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t,rfl⟩ := hw
    change CanonicalGeometry.exteriorSemilinearMap _ _ q
      (CanonicalGeometry.exteriorSemilinearMap _ _ q (exteriorPower.ιMulti A q t)) =
      CanonicalGeometry.exteriorSemilinearMap _ _ q
        (CanonicalGeometry.exteriorSemilinearMap _ _ q (exteriorPower.ιMulti A q t))
    rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti, CanonicalGeometry.exteriorSemilinearMap_ιMulti,
      CanonicalGeometry.exteriorSemilinearMap_ιMulti, CanonicalGeometry.exteriorSemilinearMap_ιMulti]
    congr 1
    funext j
    exact nativeCotangentNaturality eA eB β r he (t j)
  | zero => simp only [map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  | smul a w _ hw =>
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      LinearMap.map_smulₛₗ]
    exact congrArg₂ (fun (c : D) z => c • z) (he a) hw

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
attribute [local instance] WittTwoResidue.reductionAlgebra
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))

@[instance_reducible] private def liftedAlgebra (U : Y.Opens) :
    Algebra (WittTwo.Ring p k) Γ(Y,U) := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
private abbrev X := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev U₀ (U : Y.Opens) := WittTwoSpecialFibreOpens.residueOpen p k f U
private abbrev B (U : Y.Opens) :=
  letI := liftedAlgebra p k f U
  WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)
private abbrev C (U : Y.Opens) := Γ(X p k f,U₀ p k f U)
@[instance_reducible] private def specialAlgebra (U : Y.Opens) : Algebra k (C p k f U) :=
  WittTwoSchemeAffineRestrictions.sectionAlgebra
    (pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f) (U₀ p k f U)

/-- Actual whole native cotangent equivalence on the original geometric special-fibre open. -/
def cotangentEquiv {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := liftedAlgebra p k f U
    letI := specialAlgebra p k f U
    KaehlerDifferential k (B p k f U) ≃ₛₗ[(WittTwoSpecialFibreOpens.residueOpenSections p k f hU).toRingHom]
      KaehlerDifferential k (C p k f U) := by
  let := liftedAlgebra p k f U
  let := specialAlgebra p k f U
  exact KaehlerAlgebraEquivalence.equiv (WittTwoSpecialFibreOpens.residueOpenSections p k f hU)

/-- EVERY original universal derivative has its SAME actual geometric section derivative. -/
theorem cotangentEquiv_D {U : Y.Opens} (hU : IsAffineOpen U) (b : B p k f U) :
    letI := liftedAlgebra p k f U
    letI := specialAlgebra p k f U
    (cotangentEquiv p k f hU).toLinearMap (KaehlerDifferential.D k (B p k f U) b) =
      KaehlerDifferential.D k (C p k f U) (WittTwoSpecialFibreOpens.residueOpenSections p k f hU b) := by
  let := liftedAlgebra p k f U
  let := specialAlgebra p k f U
  exact KaehlerAlgebraEquivalence.equiv_D _ b

/-- Actual ALLq whole native exterior equivalence, including q=0 and the zero section ring. -/
def formsEquiv {U : Y.Opens} (hU : IsAffineOpen U) (q : ℕ) :
    letI := liftedAlgebra p k f U
    letI := specialAlgebra p k f U
    (⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) ≃ₛₗ[
      (WittTwoSpecialFibreOpens.residueOpenSections p k f hU).toRingHom]
        (⋀[C p k f U]^q (KaehlerDifferential k (C p k f U))) := by
  let := liftedAlgebra p k f U
  let := specialAlgebra p k f U
  exact nativeFormEquiv (WittTwoSpecialFibreOpens.residueOpenSections p k f hU) q

/-- EVERY original universal function wedge retains its actual geometric derivative formula. -/
theorem formsEquiv_universalWedge {U : Y.Opens} (hU : IsAffineOpen U) (q : ℕ) (b : Fin q → B p k f U) :
    letI := liftedAlgebra p k f U
    letI := specialAlgebra p k f U
    (formsEquiv p k f hU q).toLinearMap (exteriorPower.ιMulti (B p k f U) q
      (fun j => KaehlerDifferential.D k (B p k f U) (b j))) =
    exteriorPower.ιMulti (C p k f U) q (fun j => KaehlerDifferential.D k (C p k f U)
      (WittTwoSpecialFibreOpens.residueOpenSections p k f hU (b j))) := by
  let := liftedAlgebra p k f U
  let := specialAlgebra p k f U
  change CanonicalGeometry.exteriorSemilinearMap _ _ q _ = _
  rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti]
  congr 1
  funext j
  exact KaehlerAlgebraEquivalence.equiv_D _ (b j)

private def residueRestriction {U V : Y.Opens} (i : U ⟶ V) : B p k f V →ₐ[k] B p k f U := by
  let := liftedAlgebra p k f V
  let := liftedAlgebra p k f U
  exact WittTwoAlgebraDivisionNaturality.residueMap p k
    (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i)
private def specialRestriction {U V : Y.Opens} (i : U ⟶ V) :
    letI := specialAlgebra p k f V
    letI := specialAlgebra p k f U
    C p k f V →ₐ[k] C p k f U := by
  let := specialAlgebra p k f V
  let := specialAlgebra p k f U
  exact WittTwoSchemeAffineRestrictions.restrictionAlgebraHom
    (pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f)
    (WittTwoSpecialFibreReduction.residueInclusion p k f i)

/-- Genuine whole cotangent restriction square from the actual original scheme geometry. -/
theorem cotangent_restrict {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : U ⟶ V) (w : KaehlerDifferential k (B p k f V)) :
    letI := liftedAlgebra p k f V
    letI := liftedAlgebra p k f U
    letI := specialAlgebra p k f V
    letI := specialAlgebra p k f U
    (cotangentEquiv p k f hU).toLinearMap (nativeCotangentMap (residueRestriction p k f i) w) =
      nativeCotangentMap (specialRestriction p k f i) ((cotangentEquiv p k f hV).toLinearMap w) := by
  let := liftedAlgebra p k f V
  let := liftedAlgebra p k f U
  let := specialAlgebra p k f V
  let := specialAlgebra p k f U
  apply nativeCotangentNaturality
  intro b
  exact WittTwoSpecialFibreReduction.residueOpenSections_restrict p k f hU hV i b

/-- Genuine ALLq whole exterior restriction square on EVERY original form, with no matching input. -/
theorem forms_restrict {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : U ⟶ V) (q : ℕ) (w : ⋀[B p k f V]^q (KaehlerDifferential k (B p k f V))) :
    letI := liftedAlgebra p k f V
    letI := liftedAlgebra p k f U
    letI := specialAlgebra p k f V
    letI := specialAlgebra p k f U
    (formsEquiv p k f hU q).toLinearMap (nativeFormMap (residueRestriction p k f i) q w) =
      nativeFormMap (specialRestriction p k f i) q ((formsEquiv p k f hV q).toLinearMap w) := by
  let := liftedAlgebra p k f V
  let := liftedAlgebra p k f U
  let := specialAlgebra p k f V
  let := specialAlgebra p k f U
  apply nativeFormNaturality
  intro b
  exact WittTwoSpecialFibreReduction.residueOpenSections_restrict p k f hU hV i b

end EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreForms
