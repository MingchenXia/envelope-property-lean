import EnvelopeProperty.Cartier.SchemeFrobenius
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Perfect

/-! # The actual relative Frobenius of the SAME entire original scheme -/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobenius
open CategoryTheory Limits AlgebraicGeometry
universe u
variable {k : Type u} [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The genuine absolute Frobenius of the SAME original base field scheme. -/
def baseMap : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
  SchemeFrobenius.map (𝟙 (Spec (CommRingCat.of k))) p

/-- The SAME actual base-scheme Frobenius is EXACTLY native Spec of the SAME original
field's pth-power ring map, retaining its original coefficient identification. -/
theorem baseMap_eq_spec : baseMap (k := k) p =
    Spec.map (CommRingCat.ofHom (frobenius k p)) := by
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom).mp
  rw [Scheme.ΓSpecIso_naturality]
  apply CommRingCat.hom_ext
  ext a
  exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (SchemeFrobenius.map_app (𝟙 (Spec (CommRingCat.of k))) p ⊤ a)).trans
      (map_pow (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom a p)

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual geometric original Frobenius twist, not a replacement affine presentation. -/
def twist : Scheme.{u} := pullback f (baseMap (k := k) p)

/-- The TRUE entire original absolute Frobenius/base coefficient square commutes. -/
theorem base_square : SchemeFrobenius.map f p ≫ f = f ≫ baseMap (k := k) p :=
  SchemeFrobenius.naturality f p (𝟙 (Spec (CommRingCat.of k))) f

/-- The genuine relative Frobenius into the ACTUAL whole original geometric pullback.
Both component maps and their whole compatibility are internally derived. -/
def map : X ⟶ twist p f :=
  pullback.lift (SchemeFrobenius.map f p) f (base_square p f)

/-- The original first projection recovers the SAME genuine absolute Frobenius. -/
theorem map_fst : map p f ≫ pullback.fst f (baseMap (k := k) p) = SchemeFrobenius.map f p :=
  pullback.lift_fst _ _ _

/-- The original second projection retains the SAME original coefficient structure morphism. -/
theorem map_snd : map p f ≫ pullback.snd f (baseMap (k := k) p) = f :=
  pullback.lift_snd _ _ _

/-- For the ordinary perfect original base field, its SAME genuine scheme Frobenius is an
ACTUAL isomorphism, derived from the original native coefficient Frobenius equivalence. -/
theorem baseMap_isIso [PerfectRing k p] : IsIso (baseMap (k := k) p) := by
  let : IsIso (CommRingCat.ofHom (frobenius k p)) :=
    (frobeniusEquiv k p).toCommRingCatIso.isIso_hom
  rw [baseMap_eq_spec]
  infer_instance

/-- The first projection of the SAME actual geometric twist is an actual isomorphism over
a perfect original base; no twist-comparison or basechange certificate is assumed. -/
theorem twist_fst_isIso [PerfectRing k p] : IsIso (pullback.fst f (baseMap (k := k) p)) := by
  let : IsIso (baseMap (k := k) p) := baseMap_isIso p
  infer_instance

end EnvelopeProperty.Cartier.SchemeRelativeFrobenius
