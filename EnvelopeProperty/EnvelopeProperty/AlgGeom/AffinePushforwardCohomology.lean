import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import ModularCurves.ForMathlib.SheafCechRestrictionAcyclicComparison
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechHomotopyEquiv
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Actual affine pushforward cohomology and invertible twists -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.AffinePushforwardCohomology
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Actual positive cohomology vanishing is equivalent to zero ordered affine Cech homology. -/
theorem subsingleton_H_iff_ordered_zero {X S : Scheme.{u}} [X.IsSeparated]
    (p : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) ↔
      IsZero ((orderedBaseCechComplex p M U).homology (q + 1)) := by
  have hcech := TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    U M.sheaf hU (fun a j b => cechIntersection_subsingleton_H M U hUa a j b) q
  constructor
  · intro h
    have hb := (baseCechComplex_exactAt_iff p M U (q + 1)).mpr (hcech.mpr h)
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hb
    exact IsZero.of_iso hz (baseCechOrderedHomologyIso p M U (q + 1)).symm
  · intro h
    have hb : IsZero ((baseCechComplex p M U).homology (q + 1)) :=
      IsZero.of_iso h (baseCechOrderedHomologyIso p M U (q + 1))
    exact hcech.mp ((baseCechComplex_exactAt_iff p M U (q + 1)).mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hb))

/-- An original affine morphism identifies positive vanishing of actual cohomology
with that of its original pushforward, via original finite affine covers. -/
theorem subsingleton_H_iff_pushforward {X Y S : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] [Y.IsSeparated] (p : Y ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι]
    (U : ι → Y.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H ((pushforward f).obj M).sheaf (q + 1)) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : ((pushforward f).obj M).IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom f
  have hs := subsingleton_H_iff_ordered_zero (f ≫ p) M (fun i => f ⁻¹ᵁ U i)
    (f.iSup_preimage_eq_top hU) (fun i => (hUa i).preimage f) q
  have ht := subsingleton_H_iff_ordered_zero p ((pushforward f).obj M) U hU hUa q
  let e := HomologicalComplex.homologyMapIso
    (orderedBaseCechComplexPushforwardIso f p M U) (q + 1)
  exact hs.trans ⟨fun h => ht.mpr (IsZero.of_iso h e.symm),
    fun h => IsZero.of_iso (ht.mp h) e⟩

private theorem subsingleton_H_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) := h
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

/-- The original invertible twist comparison uses the genuine line projection formula. -/
theorem subsingleton_H_twist_iff_pushforward {X Y S : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] [Y.IsSeparated] (p : Y ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent] (L : Y.Modules) (hL : IsInvertible L)
    {ι : Type u} [LinearOrder ι] [Finite ι]
    (U : ι → Y.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H (M ⊗ (Scheme.Modules.pullback f).obj L).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H ((pushforward f).obj M ⊗ L).sheaf (q + 1)) := by
  let B := (Scheme.Modules.pullback f).obj L
  let : (M ⊗ B).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M B (hL.pullback f)
  have hc := subsingleton_H_iff_pushforward f p (M ⊗ B) U hU hUa q
  let e := SchemeLineProjectionFormula.lineProjectionFormulaObj f L hL M
  exact hc.trans ⟨fun h => subsingleton_H_of_iso e (q + 1) h,
    fun h => subsingleton_H_of_iso e.symm (q + 1) h⟩

/-- Actual cohomology vanishing descends through a genuine original linear retraction,
including degree zero and without quasicoherence. -/
theorem subsingleton_H_of_retract {X : Scheme.{u}} {M N : X.Modules}
    (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M) (q : ℕ)
    (hN : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let F := AlgebraicGeometry.Scheme.Modules.toSheaf X ⋙
    CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q
  let : Subsingleton (F.obj N) := hN
  have hz := AddCommGrpCat.isZero_of_subsingleton (F.obj N)
  change Subsingleton (F.obj M)
  apply AddCommGrpCat.subsingleton_of_isZero
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← F.map_id, ← h, F.map_comp, hz.eq_of_tgt (F.map i) 0, zero_comp]

end EnvelopeProperty.AffinePushforwardCohomology
