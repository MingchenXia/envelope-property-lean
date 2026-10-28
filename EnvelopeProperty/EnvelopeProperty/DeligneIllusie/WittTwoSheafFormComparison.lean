import EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreEtaleBasis
import EnvelopeProperty.Cartier.EtaleAffineSectionDifferential

/-! # Whole native residue forms in the SAME original geometric form sheaf -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoSheafFormComparison
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local instance] KaehlerAlgebraEquivalence.inversePair
private instance inversePairReverse {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    RingHomInvPair e.symm.toRingHom e.toRingHom where
  comp_eq := by ext b; exact e.apply_symm_apply b
  comp_eq₂ := by ext a; exact e.symm_apply_apply a

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
@[instance_reducible] private def sheafModule (U : Y.Opens) (q : ℕ) :
    Module Γ(X p k f,U₀ p k f U) Γ(CanonicalGeometry.exteriorCotangentSheaf (g p k f) q,U₀ p k f U) :=
  ((CanonicalGeometry.exteriorCotangentSheaf (g p k f) q).val.obj (op (U₀ p k f U))).isModule
attribute [local instance] sheafModule

/-- Actual ALLq native residue-form map to the ENTIRE SAME original form sheaf sections. -/
def sheafFormsMap {U : Y.Opens} (hU : IsAffineOpen U) (q : ℕ) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) →ₛₗ[
      (WittTwoSpecialFibreOpens.residueOpenSections p k f hU).toRingHom]
      Γ(CanonicalGeometry.exteriorCotangentSheaf (g p k f) q,U₀ p k f U) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  exact ((CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf (g p k f)) q).app
    (op (U₀ p k f U))).hom.comp (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU q).toLinearMap

/-- EVERY original whole form retains its literal SAME original sheafification unit image. -/
theorem sheafFormsMap_value {U : Y.Opens} (hU : IsAffineOpen U) (q : ℕ)
    (w : ⋀[B p k f U]^q (KaehlerDifferential k (B p k f U))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    sheafFormsMap p k f hU q w =
      ((CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf (g p k f)) q).app
        (op (U₀ p k f U))) ((WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU q).toLinearMap w) := by
  rfl

/-- ACTUAL original form-sheaf restrictions commute on EVERY original native residue form. -/
theorem sheafFormsMap_restrict {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : U ⟶ V) (q : ℕ) (w : ⋀[B p k f V]^q (KaehlerDifferential k (B p k f V))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    (CanonicalGeometry.exteriorCotangentSheaf (g p k f) q).presheaf.map
      (WittTwoSpecialFibreReduction.residueInclusion p k f i).op (sheafFormsMap p k f hV q w) =
    sheafFormsMap p k f hU q (WittTwoOriginalFormPresheaf.residueFormsRestriction p k f i q w) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let η := CanonicalGeometry.exteriorSheafificationMap (CanonicalGeometry.cotangentPresheaf (g p k f)) q
  let j := WittTwoSpecialFibreReduction.residueInclusion p k f i
  have hn := PresheafOfModules.naturality_apply η j.op
    ((WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hV q).toLinearMap w)
  exact hn.symm.trans (congrArg (η.app (op (U₀ p k f U)))
    (WittTwoOriginalFormPresheaf.rawFormsEquiv_restrict p k f hU hV i q w))

/-- On an ACTUAL native etale-coordinate affine open, the SAME whole sheaf-form map is bijective. -/
theorem sheafFormsMap_bijective {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (v : Fin n → Γ(X p k f,U₀ p k f U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U);
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    Function.Bijective (sheafFormsMap p k f hU q) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  exact (CanonicalGeometry.affineChartExteriorSheafificationMap_bijective (g p k f)
    (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) (Char0.etaleDifferentialBasis v hv) q).comp
      (WittTwoOriginalFormPresheaf.rawFormsEquiv p k f hU q).bijective

/-- GENUINE ALLq whole sheaf-section equivalence on the actual original lifted etale basis. -/
def basisFormsEquiv (n : ℕ) (U : WittTwoSpecialFibreEtaleBasis.coordinateOpens p k f n) (q : ℕ) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U.val
    (⋀[B p k f U.val]^q (KaehlerDifferential k (B p k f U.val))) ≃ₛₗ[
      (WittTwoSpecialFibreOpens.residueOpenSections p k f U.property.1).toRingHom]
      Γ(CanonicalGeometry.exteriorCotangentSheaf (g p k f) q,U₀ p k f U.val) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U.val
  apply LinearEquiv.ofBijective (sheafFormsMap p k f U.property.1 q)
  obtain ⟨v,hv⟩ := U.property.2
  exact sheafFormsMap_bijective p k f U.property.1 v hv q

/-- EVERY basis equivalence has exactly the SAME original actual sheafification-unit value. -/
theorem basisFormsEquiv_value (n : ℕ) (U : WittTwoSpecialFibreEtaleBasis.coordinateOpens p k f n) (q : ℕ)
    (w : ⋀[B p k f U.val]^q (KaehlerDifferential k (B p k f U.val))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U.val
    (basisFormsEquiv p k f n U q).toLinearMap w = sheafFormsMap p k f U.property.1 q w := by
  rfl

/-- SAME whole basis equivalences preserve ACTUAL original form-sheaf restriction on EVERY form. -/
theorem basisFormsEquiv_restrict (n : ℕ) (U V : WittTwoSpecialFibreEtaleBasis.coordinateOpens p k f n)
    (i : U.val ⟶ V.val) (q : ℕ) (w : ⋀[B p k f V.val]^q (KaehlerDifferential k (B p k f V.val))) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V.val
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U.val
    (CanonicalGeometry.exteriorCotangentSheaf (g p k f) q).presheaf.map
      (WittTwoSpecialFibreReduction.residueInclusion p k f i).op
        ((basisFormsEquiv p k f n V q).toLinearMap w) =
    (basisFormsEquiv p k f n U q).toLinearMap
      (WittTwoOriginalFormPresheaf.residueFormsRestriction p k f i q w) := by
  exact sheafFormsMap_restrict p k f U.property.1 V.property.1 i q w

end EnvelopeProperty.DeligneIllusie.WittTwoSheafFormComparison
