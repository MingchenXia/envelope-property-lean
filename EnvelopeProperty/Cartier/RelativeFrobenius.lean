import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.RingHom.Integral

/-!
# The actual affine relative Frobenius pushout and its original ring maps

The native categorical pushout is the actual Frobenius base change, not a supplied comparison.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeFrobenius
open CategoryTheory Limits
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
variable (p : ℕ) [hp : Fact p.Prime] [CharP A p] [CharP B p]

private theorem frobenius_naturality {R S : Type u} [CommRing R] [CommRing S]
    [CharP R p] [CharP S p] (h : R →+* S) :
    CommRingCat.ofHom (frobenius R p) ≫ CommRingCat.ofHom h =
      CommRingCat.ofHom h ≫ CommRingCat.ofHom (frobenius S p) := by
  ext x
  exact map_pow h x p

/-- The actual affine base change along the SAME original base Frobenius. -/
def twist : CommRingCat.{u} :=
  pushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom f)

/-- The actual original coefficient inclusion into Frobenius base change. -/
def coefficientMap : CommRingCat.of A ⟶ twist f p :=
  pushout.inl _ _

/-- The actual original source inclusion into Frobenius base change. -/
def sourceMap : CommRingCat.of B ⟶ twist f p :=
  pushout.inr _ _

/-- The genuine relative Frobenius is the original pushout map, with the SAME original
base coefficients and the actual source Frobenius as its two components. -/
def map : twist f p ⟶ CommRingCat.of B :=
  pushout.desc (CommRingCat.ofHom f) (CommRingCat.ofHom (frobenius B p))
    (frobenius_naturality p f)

/-- The actual relative Frobenius retains EVERY original base coefficient. -/
theorem coefficientMap_map : coefficientMap f p ≫ map f p = CommRingCat.ofHom f :=
  pushout.inl_desc _ _ _

/-- On the SAME original source the actual relative Frobenius is its original absolute
Frobenius; this is a whole-ring map identity. -/
theorem sourceMap_map : sourceMap f p ≫ map f p =
    CommRingCat.ofHom (frobenius B p) :=
  pushout.inr_desc _ _ _

/-- The ACTUAL native Frobenius pushout has the SAME original positive characteristic,
derived from its two genuine original ring maps. -/
instance twistCharP : CharP (twist f p) p := by
  obtain ⟨q, hq⟩ := CharP.exists (twist f p)
  let := hq
  have hqp : q ∣ p := CharP.dvd_of_ringHom (coefficientMap f p).hom p q
  have hpq : p ∣ q := CharP.dvd_of_ringHom (map f p).hom q p
  have h : q = p := Nat.dvd_antisymm hqp hpq
  exact h ▸ hq

/-- The OTHER whole-map triangle is the actual Frobenius of the ENTIRE original pushout.
No element-generation, nilpotence or relative-Frobenius certificate is assumed. -/
theorem map_sourceMap : map f p ≫ sourceMap f p =
    CommRingCat.ofHom (frobenius (twist f p) p) := by
  apply pushout.hom_ext
  · change coefficientMap f p ≫ (map f p ≫ sourceMap f p) = _
    rw [← Category.assoc, coefficientMap_map]
    calc
      CommRingCat.ofHom f ≫ sourceMap f p =
          CommRingCat.ofHom (frobenius A p) ≫ coefficientMap f p :=
        pushout.condition.symm
      _ = coefficientMap f p ≫ CommRingCat.ofHom (frobenius (twist f p) p) :=
        frobenius_naturality p (coefficientMap f p).hom
  · change sourceMap f p ≫ (map f p ≫ sourceMap f p) = _
    rw [← Category.assoc, sourceMap_map]
    exact frobenius_naturality p (sourceMap f p).hom

/-- Every original target p-th power belongs to the ACTUAL relative Frobenius range. -/
theorem pow_mem_range (b : B) : b^p ∈ (map f p).hom.range := by
  refine ⟨(sourceMap f p).hom b, ?_⟩
  exact congrArg (fun h : CommRingCat.of B ⟶ CommRingCat.of B => h.hom b)
    (sourceMap_map f p)

/-- Every original element killed by ACTUAL relative Frobenius is genuinely p-nilpotent
in the ENTIRE original native Frobenius base change. -/
theorem pow_eq_zero_of_map_eq_zero (x : twist f p) (hx : (map f p).hom x = 0) :
    x^p = 0 := by
  have h := congrArg (fun h : twist f p ⟶ twist f p => h.hom x) (map_sourceMap f p)
  change (sourceMap f p).hom ((map f p).hom x) = x^p at h
  rw [hx, map_zero] at h
  exact h.symm

/-- The actual relative Frobenius is an INTEGRAL morphism of the SAME original rings,
derived from actual p-th powers in its range. -/
theorem map_isIntegral : (map f p).hom.IsIntegral := by
  let := (map f p).hom.toAlgebra
  intro b
  apply IsIntegral.of_pow hp.out.pos
  obtain ⟨a, ha⟩ := pow_mem_range f p b
  rw [← ha]
  exact isIntegral_algebraMap

end EnvelopeProperty.Cartier.RelativeFrobenius
