import EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreForms
import EnvelopeProperty.Cartier.EtaleSchemeSectionDifferential

noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoOriginalFormPresheaf
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

/-- The SAME actual original structural coefficient algebra is used by the native cotangent presheaf. -/
theorem sectionAlgebra_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    WittTwoSchemeAffineRestrictions.sectionAlgebra g U = CanonicalGeometry.cotangentOpenAlgebra g U := by
  have h0 : g.appLE ⊤ ⊤ le_top = g.appTop := by
    simpa only [Scheme.Hom.preimage_top] using (g.appLE_eq_app (U := ⊤))
  have h := Scheme.Hom.appLE_map g (U := ⊤) (V := ⊤) (V' := U) le_top U.leTop.op
  rw [h0] at h
  unfold WittTwoSchemeAffineRestrictions.sectionAlgebra CanonicalGeometry.cotangentOpenAlgebra
    CanonicalGeometry.schemeConstantPresheafMap
  rw [← h]
  rfl

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

private theorem nativeFormMap_eq_canonical {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (β : A →ₐ[R] B) (q : ℕ) (w : ⋀[A]^q (KaehlerDifferential R A)) :
    letI := β.toAlgebra
    letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun a => (β.commutes a).symm
    nativeFormMap β q w = Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) q w := by
  let := β.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun a => (β.commutes a).symm
  have hw : w ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A q (M := KaehlerDifferential R A))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t,rfl⟩ := hw
    change CanonicalGeometry.exteriorSemilinearMap _ _ q _ = _
    rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti, Char0.canonicalDifferentialLinearMap_wedge]
    rfl
  | zero => simp only [map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, hz, hw]
  | smul a w _ hw =>
    rw [LinearMap.map_smulₛₗ, map_smul, hw]
    exact IsScalarTower.algebraMap_smul B a _

private theorem nativeFormMap_eq_raw {k : Type u} [Field k] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (CommRingCat.of k)) {U V : Z.Opens} (i : U ⟶ V) (q : ℕ)
    (w : letI := CanonicalGeometry.cotangentOpenAlgebra h V;
      ⋀[Γ(Z,V)]^q (KaehlerDifferential k Γ(Z,V))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra h V
    letI := CanonicalGeometry.cotangentOpenAlgebra h U
    nativeFormMap (Cartier.EtaleSchemeSectionDifferential.restrictionAlgebraHom h i) q w =
      (CanonicalGeometry.exteriorCotangentPresheaf h q).map i.op w := by
  let := CanonicalGeometry.cotangentOpenAlgebra h V
  let := CanonicalGeometry.cotangentOpenAlgebra h U
  exact (nativeFormMap_eq_canonical
    (Cartier.EtaleSchemeSectionDifferential.restrictionAlgebraHom h i) q w).trans
      (Cartier.EtaleSchemeSectionDifferential.exterior_restrict h i q w).symm

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
attribute [local instance] WittTwoResidue.reductionAlgebra
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
private abbrev X := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev g : X p k f ⟶ Spec (CommRingCat.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev U₀ (U : Y.Opens) := WittTwoSpecialFibreOpens.residueOpen p k f U
private abbrev B (U : Y.Opens) :=
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)

@[instance_reducible] private def rawModule (U : Y.Opens) (q : ℕ) :
    Module Γ(X p k f,U₀ p k f U)
      ((CanonicalGeometry.exteriorCotangentPresheaf (g p k f) q).obj (op (U₀ p k f U))) :=
  ((CanonicalGeometry.exteriorCotangentPresheaf (g p k f) q).obj (op (U₀ p k f U))).isModule
attribute [local instance] rawModule

private def canonicalSections {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
    B p k f U ≃ₐ[k] Γ(X p k f,U₀ p k f U) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  let e := WittTwoSpecialFibreOpens.residueOpenSections p k f hU
  refine { e.toRingEquiv with commutes' := ?_ }
  intro a
  exact (e.commutes a).trans (congrArg (fun ab : Algebra k Γ(X p k f,U₀ p k f U) =>
    @algebraMap k Γ(X p k f,U₀ p k f U) _ _ ab a)
      (sectionAlgebra_eq (g p k f) (U₀ p k f U)))

/-- Whole original residue forms identify with the SAME original raw geometric form presheaf. -/
def rawFormsEquiv {U : Y.Opens} (hU : IsAffineOpen U) (q : ℕ) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) ≃ₛₗ[
      (WittTwoSpecialFibreOpens.residueOpenSections p k f hU).toRingHom]
        ((CanonicalGeometry.exteriorCotangentPresheaf (g p k f) q).obj (op (U₀ p k f U))) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  exact nativeFormEquiv (canonicalSections p k f hU) q

/-- EVERY original universal function wedge has its literal original raw geometric form value. -/
theorem rawFormsEquiv_universalWedge {U : Y.Opens} (hU : IsAffineOpen U) (q : ℕ)
    (b : Fin q → B p k f U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
    (rawFormsEquiv p k f hU q).toLinearMap (exteriorPower.ιMulti (B p k f U) q
      (fun j => KaehlerDifferential.D k (B p k f U) (b j))) =
    exteriorPower.ιMulti Γ(X p k f,U₀ p k f U) q
      (fun j => KaehlerDifferential.D k Γ(X p k f,U₀ p k f U)
        (WittTwoSpecialFibreOpens.residueOpenSections p k f hU (b j))) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  change CanonicalGeometry.exteriorSemilinearMap _ _ q _ = _
  rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti]
  congr 1
  funext j
  exact KaehlerAlgebraEquivalence.equiv_D (canonicalSections p k f hU) (b j)

/-- The ACTUAL original tensor-residue restriction induces its native whole exterior map. -/
def residueFormsRestriction {U V : Y.Opens} (i : U ⟶ V) (q : ℕ) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (⋀[B p k f V]^q (KaehlerDifferential k (B p k f V))) →ₛₗ[
      (WittTwoAlgebraDivisionNaturality.residueMap p k
        (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i)).toRingHom]
      (⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  exact nativeFormMap (WittTwoAlgebraDivisionNaturality.residueMap p k
    (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i)) q

/-- The SAME ALLq whole equivalences retain ACTUAL original raw presheaf restriction on EVERY form. -/
theorem rawFormsEquiv_restrict {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : U ⟶ V) (q : ℕ) (w : ⋀[B p k f V]^q (KaehlerDifferential k (B p k f V))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (CanonicalGeometry.exteriorCotangentPresheaf (g p k f) q).map
      (WittTwoSpecialFibreReduction.residueInclusion p k f i).op
      ((rawFormsEquiv p k f hV q).toLinearMap w) =
    (rawFormsEquiv p k f hU q).toLinearMap (residueFormsRestriction p k f i q w) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  let β := WittTwoAlgebraDivisionNaturality.residueMap p k
    (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i)
  let j := WittTwoSpecialFibreReduction.residueInclusion p k f i
  let r := Cartier.EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) j
  have he (b : B p k f V) : canonicalSections p k f hU (β b) = r (canonicalSections p k f hV b) :=
    WittTwoSpecialFibreReduction.residueOpenSections_restrict p k f hU hV i b
  have hs := nativeFormNaturality (canonicalSections p k f hV) (canonicalSections p k f hU) β r he q w
  have hr := nativeFormMap_eq_raw (g p k f) j q ((rawFormsEquiv p k f hV q).toLinearMap w)
  exact hr.symm.trans hs.symm

end EnvelopeProperty.DeligneIllusie.WittTwoOriginalFormPresheaf
