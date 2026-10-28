import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleBaseChange
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineCoefficient
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Group.Commute.Units

/-! # Actual native twist localization with the unchanged original coefficient map -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistPrincipalLocalization
open CategoryTheory Limits
universe u
variable {k B : Type u} [CommRing k] [CommRing B]
variable (α : k →+* B) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist α p
local notation "s" => CommRingCat.Hom.hom (RelativeFrobenius.sourceMap α p)
local notation "f" b => algebraMap B (Localization.Away b)

private def awaySourceMap (b : B) :
    Localization.Away b →+* Localization.Away (s b) :=
  IsLocalization.Away.map (Localization.Away b) (Localization.Away (s b)) s b

private theorem awaySourceMap_triangle (b : B) :
    (awaySourceMap α p b).comp (f b) =
      (algebraMap T (Localization.Away (s b))).comp s := by
  ext x
  change awaySourceMap α p b (algebraMap B (Localization.Away b) x) =
    algebraMap T (Localization.Away (s b)) (s x)
  dsimp only [awaySourceMap, IsLocalization.Away.map]
  exact IsLocalization.map_eq (M := Submonoid.powers b) («T» := Submonoid.powers (s b)) _ x

/-- The actual original source/localization square is genuinely a native ring pushout. -/
theorem awaySourceSquare (b : B) :
    IsPushout (RelativeFrobenius.sourceMap α p) (CommRingCat.ofHom (f b))
      (CommRingCat.ofHom (algebraMap T (Localization.Away (s b))))
      (CommRingCat.ofHom (awaySourceMap α p b)) :=
  CommRingCat.isPushout_of_isLocalization s (awaySourceMap α p b)
    (awaySourceMap_triangle α p b) (Submonoid.powers b)

/-- The SAME actual native twist of the actual original principal localization. -/
def awayTwistIso (b : B) :
    RelativeFrobenius.twist ((f b).comp α) p ≅ CommRingCat.of (Localization.Away (s b)) :=
  (RelativeEtaleBaseChange.sourceSquare α (f b) p).isoIsPushout _ _ (awaySourceSquare α p b)

/-- The ENTIRE original native twist numerator triangle. -/
theorem awayTwistIso_twistMap (b : B) :
    RelativeEtaleBaseChange.twistMap α (f b) p ≫ (awayTwistIso α p b).hom =
      CommRingCat.ofHom (algebraMap T (Localization.Away (s b))) :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- The ENTIRE actual localized source triangle. -/
theorem awayTwistIso_source (b : B) :
    RelativeFrobenius.sourceMap ((f b).comp α) p ≫ (awayTwistIso α p b).hom =
      CommRingCat.ofHom (awaySourceMap α p b) :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

/-- EVERY original coefficient is retained by the actual entire ring comparison. -/
theorem awayTwistIso_coefficient (b : B) :
    RelativeFrobenius.coefficientMap ((f b).comp α) p ≫ (awayTwistIso α p b).hom =
      RelativeFrobenius.coefficientMap α p ≫
        CommRingCat.ofHom (algebraMap T (Localization.Away (s b))) := by
  rw [← RelativeEtaleBaseChange.coefficientMap_twistMap α (f b) p,
    Category.assoc, awayTwistIso_twistMap]
  rfl

section Powers
variable {R : Type u} [CommRing R]

private def awayPowerForward (x : R) (n : ℕ) :
    Localization.Away (x^n) →ₐ[R] Localization.Away x :=
  IsLocalization.Away.liftAlgHom (A := R) (S := Localization.Away (x^n))
    («f» := Algebra.ofId R (Localization.Away x)) (x^n) (by
      change IsUnit (algebraMap R (Localization.Away x) (x^n))
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x).pow n)

private def awayPowerBackward (x : R) (n : ℕ) (hn : 0 < n) :
    Localization.Away x →ₐ[R] Localization.Away (x^n) :=
  IsLocalization.Away.liftAlgHom (A := R) (S := Localization.Away x)
    («f» := Algebra.ofId R (Localization.Away (x^n))) x (by
      change IsUnit (algebraMap R (Localization.Away (x^n)) x)
      apply (isUnit_pow_iff hn.ne').mp
      rw [← map_pow]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (x^n)) (x^n))

/-- The actual positive-power principal localizations are equivalent over the ORIGINAL ring. -/
def awayPowerEquiv (x : R) (n : ℕ) (hn : 0 < n) :
    Localization.Away (x^n) ≃ₐ[R] Localization.Away x :=
  AlgEquiv.ofAlgHom (awayPowerForward x n) (awayPowerBackward x n hn)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers x)
      ext)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (x^n))
      ext)

/-- The ENTIRE original coefficient/numerator map is retained by the positive-power equivalence. -/
theorem awayPowerEquiv_numerator (x : R) (n : ℕ) (hn : 0 < n) :
    CommRingCat.ofHom (algebraMap R (Localization.Away (x^n))) ≫
        (awayPowerEquiv x n hn).toRingEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap R (Localization.Away x)) := by
  ext a
  exact (awayPowerEquiv x n hn).commutes a

private theorem awayEquality_numerator (x y : R) (h : x = y) :
    CommRingCat.ofHom (algebraMap R (Localization.Away x)) ≫
        (eqToIso (congrArg (fun z : R => CommRingCat.of (Localization.Away z)) h)).hom =
      CommRingCat.ofHom (algebraMap R (Localization.Away y)) := by
  subst y
  rfl
end Powers

section Field
variable {k B : Type u} [Field k] [CommRing B]
variable (α : k →+* B) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The ACTUAL geometric beta/source composition is the original principal pth power,
including zero endpoints, with no incoming endpoint characteristic instance. -/
theorem source_beta_pow (t : RelativeFrobenius.twist α p) :
    (RelativeFrobenius.sourceMap α p).hom
        ((SchemeRelativeFrobeniusAffineMap.ringMap α p).hom t) = t^p := by
  classical
  by_cases h : Nontrivial B
  · let := h
    let : Algebra k B := α.toAlgebra
    let : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    rw [SchemeRelativeFrobeniusAffineMap.ringMap_eq_native]
    exact congrArg (fun F : RelativeFrobenius.twist α p ⟶ RelativeFrobenius.twist α p => F.hom t)
      (RelativeFrobenius.map_sourceMap α p)
  · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    have : Subsingleton (RelativeFrobenius.twist α p) :=
      (RelativeFrobenius.sourceMap α p).hom.codomain_trivial
    exact Subsingleton.elim _ _

/-- The actual twist on B[1/beta(t)] is the actual original T[1/t], including zero endpoints. -/
def principalIso (t : RelativeFrobenius.twist α p) :
    RelativeFrobenius.twist
      ((algebraMap B (Localization.Away ((SchemeRelativeFrobeniusAffineMap.ringMap α p).hom t))).comp α) p ≅
      CommRingCat.of (Localization.Away t) :=
  awayTwistIso α p ((SchemeRelativeFrobeniusAffineMap.ringMap α p).hom t) ≪≫
    eqToIso (congrArg (fun z : RelativeFrobenius.twist α p => CommRingCat.of (Localization.Away z))
      (source_beta_pow α p t)) ≪≫
    (awayPowerEquiv t p (Fact.out : p.Prime).pos).toRingEquiv.toCommRingCatIso

/-- The ENTIRE actual original twist numerator triangle for the relative principal open. -/
theorem principalIso_twistMap (t : RelativeFrobenius.twist α p) :
    RelativeEtaleBaseChange.twistMap α
        (algebraMap B (Localization.Away ((SchemeRelativeFrobeniusAffineMap.ringMap α p).hom t))) p ≫
      (principalIso α p t).hom =
        CommRingCat.ofHom (algebraMap (RelativeFrobenius.twist α p) (Localization.Away t)) := by
  simp only [principalIso, Iso.trans_hom]
  rw [← Category.assoc, awayTwistIso_twistMap, ← Category.assoc,
    awayEquality_numerator _ _ (source_beta_pow α p t), awayPowerEquiv_numerator]

/-- The SAME original coefficient inclusion survives the ENTIRE relative-principal comparison. -/
theorem principalIso_coefficient (t : RelativeFrobenius.twist α p) :
    RelativeFrobenius.coefficientMap
        ((algebraMap B (Localization.Away ((SchemeRelativeFrobeniusAffineMap.ringMap α p).hom t))).comp α) p ≫
      (principalIso α p t).hom =
        RelativeFrobenius.coefficientMap α p ≫
          CommRingCat.ofHom (algebraMap (RelativeFrobenius.twist α p) (Localization.Away t)) := by
  rw [← RelativeEtaleBaseChange.coefficientMap_twistMap,
    Category.assoc, principalIso_twistMap]
  rfl
end Field

end EnvelopeProperty.Cartier.RelativeTwistPrincipalLocalization
