import EnvelopeProperty.Cartier.SchemeRelativeFrobenius
import ModularCurves.Picard.UnitPullback

/-! # Original line modules on the actual relative Frobenius twist

The relative pullback comparison is an actual original scheme comparison.
The scalar identities below supply the Frobenius side of the transition
calculation for `F_X^* L ≅ L^p`; they do not assume that global isomorphism.
-/

open AlgebraicGeometry CategoryTheory
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.FrobeniusLineComparison

open Cartier

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The original module pulled to the actual geometric Frobenius twist. -/
def twistedLine (L : X.Modules) : (SchemeRelativeFrobenius.twist p f).Modules :=
  (pullback (Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p))).obj L

/-- Genuine relative pullback of the twisted original module is its
genuine absolute-Frobenius pullback, using the original scheme triangle. -/
def relativePullbackIso (L : X.Modules) :
    (pullback (SchemeRelativeFrobenius.map p f)).obj (twistedLine f p L) ≅
      (pullback (SchemeFrobenius.map f p)).obj L :=
  (pullbackComp (SchemeRelativeFrobenius.map p f)
    (Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p))).app L ≪≫
      (pullbackCongr (SchemeRelativeFrobenius.map_fst p f)).app L

/-- Pullback by original Frobenius raises every actual global scalar
endomorphism to its literal pth-power scalar. -/
theorem pullback_unitScalar (a : Γ(X, ⊤)) :
    (pullbackUnitIso (SchemeFrobenius.map f p)).inv ≫
      (pullback (SchemeFrobenius.map f p)).map
        (ModularCurves.unitEndomorphismOfTopSection a) ≫
        (pullbackUnitIso (SchemeFrobenius.map f p)).hom =
      ModularCurves.unitEndomorphismOfTopSection (a ^ p) := by
  rw [ModularCurves.pullback_unitEndomorphismOfTopSection]
  congr 1
  exact SchemeFrobenius.map_app f p ⊤ a

/-- The same statement for actual whole structure-module automorphisms,
so it can be applied to every genuine line-frame transition. -/
theorem pullback_unitAutomorphism (a : Γ(X, ⊤)ˣ) :
    (pullbackUnitIso (SchemeFrobenius.map f p)).symm ≪≫
      (pullback (SchemeFrobenius.map f p)).mapIso
        (ModularCurves.unitAutomorphismOfTopUnit a) ≪≫
        pullbackUnitIso (SchemeFrobenius.map f p) =
      ModularCurves.unitAutomorphismOfTopUnit (a ^ p) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ModularCurves.unitAutomorphismOfTopUnit_hom, Units.val_pow_eq_pow_val] using
      pullback_unitScalar f p (a : Γ(X, ⊤))

/-- The frame obtained by genuinely pulling back an original whole frame. -/
def pulledFrame {L : X.Modules} (e : L ≅ unitObj X) :
    (pullback (SchemeFrobenius.map f p)).obj L ≅ unitObj X :=
  (pullback (SchemeFrobenius.map f p)).mapIso e ≪≫
    pullbackUnitIso (SchemeFrobenius.map f p)

/-- Two actual frame maps whose transition is multiplication by `a`
have pulled frame transition given by multiplication by `a^p`. -/
theorem pulledFrame_hom_eq_comp_scalar {L : X.Modules}
    (e e' : L ≅ unitObj X) (a : Γ(X, ⊤))
    (he : e.hom = e'.hom ≫ ModularCurves.unitEndomorphismOfTopSection a) :
    (pulledFrame f p e).hom =
      (pulledFrame f p e').hom ≫ ModularCurves.unitEndomorphismOfTopSection (a ^ p) := by
  let F := pullback (SchemeFrobenius.map f p)
  let u := pullbackUnitIso (SchemeFrobenius.map f p)
  have hs : F.map (ModularCurves.unitEndomorphismOfTopSection a) ≫ u.hom =
      u.hom ≫ ModularCurves.unitEndomorphismOfTopSection (a ^ p) := by
    have h := congrArg (fun q => u.hom ≫ q) (pullback_unitScalar f p a)
    simpa only [u, F, Iso.hom_inv_id_assoc] using h
  change F.map e.hom ≫ u.hom =
    (F.map e'.hom ≫ u.hom) ≫ ModularCurves.unitEndomorphismOfTopSection (a ^ p)
  rw [he, F.map_comp, Category.assoc, hs, Category.assoc]

end EnvelopeProperty.Vanishing.FrobeniusLineComparison
