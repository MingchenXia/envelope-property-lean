import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartNativeDifferentialSquareGeneralRestricted

/-! # The fixed whole-chart square of the pushed canonical differential

Let `π : Y ⟶ X` be a morphism of schemes and let `C : WholeFreeChart π D` be a whole free chart:
an affine open `g = C.base.2.fromSpec : Spec Γ(X, U) ⟶ X`, the coefficient algebra `B = C.coeff`
with `p = C.scalarMap : Spec B ⟶ Spec Γ(X, U)`, and the open immersion
`v = C.sourceMap : Spec B ⟶ Y` onto `π⁻¹ U`, forming the Cartesian square `p ≫ g = v ≫ π`
(`WholeFreeChart.isPullback`). For `f : X ⟶ Spec k` and `n : ℕ` write
`d_a : a^* Ω^n_f ⟶ Ω^n_{a ≫ f}` for the exterior pullback differential
`exteriorCotangentSheafPullbackMap f a n`.

The two fixed chart comparisons of the original pushforwards are
* `WholeFreeChart.canonicalPullbackRestrictionIso`:
  `(π_* π^* Ω^n_f)|_U ≅ p_* p^* Ω^n_{g ≫ f}` and
* `WholeFreeChart.canonicalSourceRestrictionIso`:
  `(π_* Ω^n_{π ≫ f})|_U ≅ p_* Ω^n_{p ≫ g ≫ f}`;
both are the Cartesian restriction--pushforward comparison followed by `p_*` of a fixed
native comparison built from the open-immersion differentials `d_g`, `d_v`.

The main result, `WholeFreeChart.canonicalSourceRestrictionIso_differential`, says that these
comparisons carry the restriction of the pushed differential `π_* d_π` to the chart's own pushed
differential `p_* d_p`:
```
(π_* d_π)|_U ≫ canonicalSourceRestrictionIso = canonicalPullbackRestrictionIso ≫ p_* d_p.
```
This is the chart-level differential square used to transport the normalization of the chart
trace candidate back to the original canonical pushforward (lane NV2 of the relative Nadel plan;
the consumer is `producedOriginalCanonicalCandidate_differential`).

## Proof design

The geometric content is the restricted native square
`NativeDifferentialSquareData.general_restricted_differential_square`, already proved for
arbitrary scheme arrows with `v` an open immersion. What remains is categorical: apply `p_*` and
transport along the natural Cartesian comparison, which is the abstract lemma
`NativeDifferentialSquareData.finish_fixed_native_iso_square`.

The kernel must never compare two structurally different concrete composites `a ≫ b` of
sheaf-of-modules morphisms: `CategoryStruct.comp` is a projection with abbreviation hints, so
the kernel unfolds the composition of the concrete category instead of comparing arguments
first, and through the `eqToHom` field transport it reaches the scheme morphisms themselves (a
direct `rfl` identification of the homomorphism of `restrictedSourceIso` with
`restrictedSourceDifferential` hit the kernel heartbeat limit, and used 11 GB in a full
compile). Therefore the composites `a`, `b` of the abstract assembly are not written by hand: they
are read off, by unification, from the type of the restricted square, and the isomorphisms
`eA`, `eB` from the two comparison unfoldings `canonicalSourceRestrictionIso_eq_trans`,
`canonicalPullbackRestrictionIso_eq_trans` (proved by `rfl` against `Iso.trans` terms). The
identifications `eA.hom = a`, `eB.hom = b` are then abstract identities
(`inverse_comparison_word_hom`, `iso_asIso_eqToIso_hom`) all of whose arguments are read off
from the goals, so every concrete comparison the kernel performs is structural.
No `simp` runs on concrete sheaf-of-modules terms.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart

open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
open NativeDifferentialSquareData

attribute [local instance] sourceMap_isOpenImmersion
  isIso_exteriorCotangentSheafPullbackMap_openImmersion

/-! ### Abstract identities -/

/-- The homomorphism of a three-step isomorphism word `a ≪≫ asIso b ≪≫ eqToIso h`. The two
equality proofs are separate inputs, so that each side keeps its own original proof term. -/
private theorem iso_asIso_eqToIso_hom {E : Type*} [Category E] {A B P Q : E} (a : A ≅ B)
    (b : B ⟶ P) [IsIso b] (h h' : P = Q) :
    (a ≪≫ asIso b ≪≫ eqToIso h).hom = a.hom ≫ b ≫ eqToHom h' :=
  rfl

/-- The homomorphism of the inverse of a comparison word `ρ_M ≪≫ κ_M ≪≫ τ_M⁻¹`, between a
restriction-type isomorphism `u` and the image of an isomorphism `δ`, is the original inverse
word `u ; τ_M ; κ_M⁻¹ ; ρ_M⁻¹ ; Fp(δ)`, with its original composed and nested functor indices. -/
private theorem inverse_comparison_word_hom
    {C₀ C₁ C₂ E : Type*} [Category C₀] [Category C₁] [Category C₂] [Category E]
    (Fg : C₀ ⥤ C₁) (Fp : C₁ ⥤ E) (Fπ : C₀ ⥤ C₂) (Fv : C₂ ⥤ E) {P Q : C₀ ⥤ E}
    (ρ : Fg ⋙ Fp ≅ P) (κ : P ≅ Q) (τ : Fπ ⋙ Fv ≅ Q) (M : C₀) {W : E} {B : C₁}
    (u : W ≅ Fv.obj (Fπ.obj M)) (δ : Fg.obj M ⟶ B) [IsIso δ] :
    (u ≪≫ (ρ.app M ≪≫ κ.app M ≪≫ (τ.app M).symm).symm ≪≫ Fp.mapIso (asIso δ)).hom =
      composeOriginalInverseWord Fπ Fv M u.hom
        (τ.hom.app M ≫ κ.inv.app M ≫ ρ.inv.app M ≫ Fp.map δ) := by
  simp only [composeOriginalInverseWord, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, asIso_hom, Category.assoc]

/-- Whisker a commuting square on the right, in an abstract category. -/
private theorem square_whisker_assoc {E : Type*} [Category E] {P Q R S Z : E}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ S} {d : S ⟶ R} (h : a ≫ b = c ≫ d) (g : R ⟶ Z) :
    a ≫ b ≫ g = c ≫ d ≫ g := by
  rw [← Category.assoc, h, Category.assoc]

/-! ### The fixed chart comparisons -/

variable {X Y : Scheme.{u}} {π : Y ⟶ X} {D : ℕ} (C : WholeFreeChart π D) {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (n : ℕ)

/-- The structural equality of the two composites `Spec B ⟶ Spec k` of a whole chart. -/
theorem sourceMap_comp_eq :
    C.sourceMap ≫ (π ≫ f) = C.scalarMap ≫ (C.base.2.fromSpec ≫ f) := by
  rw [← Category.assoc, ← C.isPullback.w, Category.assoc]

/-- The fixed source canonical comparison is the Cartesian comparison followed by the pushforward
of `ρ_v ≪≫ d_v ≪≫ (field transport)`. -/
theorem canonicalSourceRestrictionIso_eq_trans :
    C.canonicalSourceRestrictionIso f n =
      (restrictPushforwardIsoOfIsPullback π C.scalarMap C.sourceMap C.base.2.fromSpec
          C.isPullback).app (exteriorCotangentSheaf (π ≫ f) n) ≪≫
        (pushforward C.scalarMap).mapIso
          ((restrictFunctorIsoPullback C.sourceMap).app (exteriorCotangentSheaf (π ≫ f) n) ≪≫
            asIso (exteriorCotangentSheafPullbackMap (π ≫ f) C.sourceMap n) ≪≫
              eqToIso (congrArg (fun q => exteriorCotangentSheaf q n) (C.sourceMap_comp_eq f))) :=
  rfl

/-- The fixed pulled canonical comparison is the Cartesian comparison followed by the pushforward
of `ρ_v ≪≫ χ⁻¹ ≪≫ p^* d_g`, where `χ` is the native pullback comparison word. -/
theorem canonicalPullbackRestrictionIso_eq_trans :
    C.canonicalPullbackRestrictionIso f n =
      (restrictPushforwardIsoOfIsPullback π C.scalarMap C.sourceMap C.base.2.fromSpec
          C.isPullback).app ((pullback π).obj (exteriorCotangentSheaf f n)) ≪≫
        (pushforward C.scalarMap).mapIso
          ((restrictFunctorIsoPullback C.sourceMap).app
              ((pullback π).obj (exteriorCotangentSheaf f n)) ≪≫
            ((pullbackComp C.scalarMap C.base.2.fromSpec).app (exteriorCotangentSheaf f n) ≪≫
              (pullbackCongr C.isPullback.w).app (exteriorCotangentSheaf f n) ≪≫
                ((pullbackComp C.sourceMap π).app (exteriorCotangentSheaf f n)).symm).symm ≪≫
            (pullback C.scalarMap).mapIso
              (asIso (exteriorCotangentSheafPullbackMap f C.base.2.fromSpec n))) :=
  rfl

/-! ### The fixed whole-chart differential square -/

/-- **The fixed whole-chart differential square.** The fixed native comparisons
`canonicalPullbackRestrictionIso` and `canonicalSourceRestrictionIso` carry the restriction of
the pushed original canonical differential `π_* d_π` to the chart's pushed differential `p_* d_p`.
No comparison or commuting-square certificate is an input. -/
theorem canonicalSourceRestrictionIso_differential :
    (restrictFunctor C.base.2.fromSpec).map
        ((pushforward π).map (exteriorCotangentSheafPullbackMap f π n)) ≫
          (C.canonicalSourceRestrictionIso f n).hom =
      (C.canonicalPullbackRestrictionIso f n).hom ≫
        (pushforward C.scalarMap).map
          (exteriorCotangentSheafPullbackMap (C.base.2.fromSpec ≫ f) C.scalarMap n) := by
  -- The restricted native square fixes the two composites `a`, `b` of the abstract assembly
  -- lemma; the two canonical comparisons fix the isomorphisms `eA`, `eB`. The remaining two
  -- goals identify the homomorphisms of `eA`, `eB` with `a`, `b` by abstract identities whose
  -- arguments are all read off from the goals.
  have hs := general_restricted_differential_square f C.base.2.fromSpec π C.scalarMap
    C.sourceMap C.isPullback.w n
  refine finish_fixed_native_iso_square (pushforward π) (restrictFunctor C.base.2.fromSpec)
    (restrictFunctor C.sourceMap) (pushforward C.scalarMap)
    (restrictPushforwardIsoOfIsPullback π C.scalarMap C.sourceMap C.base.2.fromSpec
      C.isPullback)
    (exteriorCotangentSheafPullbackMap f π n) _ _
    (exteriorCotangentSheafPullbackMap (C.base.2.fromSpec ≫ f) C.scalarMap n) _ _ ?_ ?_
    (C.canonicalSourceRestrictionIso f n) (C.canonicalPullbackRestrictionIso f n)
    (canonicalSourceRestrictionIso_eq_trans C f n)
    (canonicalPullbackRestrictionIso_eq_trans C f n) hs
  · exact inverse_comparison_word_hom _ _ _ _ _ _ _ _ _ _
  · exact iso_asIso_eqToIso_hom _ _ _ _

/-- `canonicalSourceRestrictionIso_differential`, followed by an arbitrary morphism. -/
theorem canonicalSourceRestrictionIso_differential_assoc {Z : (Spec Γ(X, C.base.1)).Modules}
    (g : (pushforward C.scalarMap).obj
      (exteriorCotangentSheaf (C.scalarMap ≫ (C.base.2.fromSpec ≫ f)) n) ⟶ Z) :
    (restrictFunctor C.base.2.fromSpec).map
        ((pushforward π).map (exteriorCotangentSheafPullbackMap f π n)) ≫
          (C.canonicalSourceRestrictionIso f n).hom ≫ g =
      (C.canonicalPullbackRestrictionIso f n).hom ≫
        (pushforward C.scalarMap).map
          (exteriorCotangentSheafPullbackMap (C.base.2.fromSpec ≫ f) C.scalarMap n) ≫ g :=
  square_whisker_assoc (canonicalSourceRestrictionIso_differential C f n) g

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
