import EnvelopeProperty.Cartier.RelativeCartierContinuationNativePrincipalCartierLocalization

/-! # Zero-safe geometric Frobenius base change and the original native target -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeGeometricTwistBaseChange
open CategoryTheory Limits
universe u
variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

private theorem geometricSquare (α : k →+* A) (f : A →+* B) :
    RelativeEtaleBaseChange.twistMap α f p ≫ SchemeRelativeFrobeniusAffineMap.ringMap (f.comp α) p =
      SchemeRelativeFrobeniusAffineMap.ringMap α p ≫ CommRingCat.ofHom f := by
  apply pushout.hom_ext
  · change RelativeFrobenius.coefficientMap α p ≫
        (RelativeEtaleBaseChange.twistMap α f p ≫ SchemeRelativeFrobeniusAffineMap.ringMap (f.comp α) p) =
      RelativeFrobenius.coefficientMap α p ≫
        (SchemeRelativeFrobeniusAffineMap.ringMap α p ≫ CommRingCat.ofHom f)
    rw [← Category.assoc, RelativeEtaleBaseChange.coefficientMap_twistMap,
      SchemeRelativeFrobeniusAffineMap.coefficient_ringMap, ← Category.assoc,
      SchemeRelativeFrobeniusAffineMap.coefficient_ringMap]
    rfl
  · change RelativeFrobenius.sourceMap α p ≫
        (RelativeEtaleBaseChange.twistMap α f p ≫ SchemeRelativeFrobeniusAffineMap.ringMap (f.comp α) p) =
      RelativeFrobenius.sourceMap α p ≫
        (SchemeRelativeFrobeniusAffineMap.ringMap α p ≫ CommRingCat.ofHom f)
    rw [← Category.assoc, RelativeEtaleBaseChange.sourceMap_twistMap, Category.assoc,
      SchemeRelativeFrobeniusAffineMap.source_ringMap, ← Category.assoc,
      SchemeRelativeFrobeniusAffineMap.source_ringMap]
    ext a
    exact (SchemeRelativeFrobeniusAffineMap.absoluteRingMap_apply (f.comp α) p (f a)).trans
      ((map_pow f a p).symm.trans
        (congrArg f (SchemeRelativeFrobeniusAffineMap.absoluteRingMap_apply α p a)).symm)

/-- ENTIRE original geometric-beta square, with no endpoint characteristic/nonzero premises. -/
theorem geometricCoefficientSquare (α : k →+* A) (f : A →+* B) :
    (SchemeRelativeFrobeniusAffineMap.ringMap (f.comp α) p).hom.comp
        (RelativeEtaleBaseChange.twistMap α f p).hom =
      f.comp (SchemeRelativeFrobeniusAffineMap.ringMap α p).hom := by
  exact congrArg CommRingCat.Hom.hom (geometricSquare p α f)

private theorem coefficient_eqToIso (α β : k →+* B) (h : α = β) :
    RelativeFrobenius.coefficientMap α p ≫
      (eqToIso (congrArg (fun a : k →+* B => RelativeFrobenius.twist a p) h)).hom =
      RelativeFrobenius.coefficientMap β p := by
  subst β
  rfl

private theorem source_eqToIso (α β : k →+* B) (h : α = β) :
    RelativeFrobenius.sourceMap α p ≫
      (eqToIso (congrArg (fun a : k →+* B => RelativeFrobenius.twist a p) h)).hom =
      RelativeFrobenius.sourceMap β p := by
  subst β
  rfl

private theorem ringMap_eqToIso (α β : k →+* B) (h : α = β) :
    (eqToIso (congrArg (fun a : k →+* B => RelativeFrobenius.twist a p) h)).hom ≫
        SchemeRelativeFrobeniusAffineMap.ringMap β p =
      SchemeRelativeFrobeniusAffineMap.ringMap α p := by
  subst β
  rfl

variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- The ACTUAL native target is compared to its DERIVED composed-base target. -/
def targetBaseIso : RelativeFrobenius.twist (algebraMap k B) p ≅
    RelativeFrobenius.twist ((algebraMap A B).comp (algebraMap k A)) p :=
  eqToIso (congrArg (fun α : k →+* B => RelativeFrobenius.twist α p)
    (IsScalarTower.algebraMap_eq k A B))

/-- The ENTIRE original coefficient inclusion is preserved by the genuine base-map iso. -/
theorem targetBaseIso_coefficient :
    RelativeFrobenius.coefficientMap (algebraMap k B) p ≫
        (targetBaseIso (k := k) (A := A) (B := B) p).hom =
      RelativeFrobenius.coefficientMap ((algebraMap A B).comp (algebraMap k A)) p :=
  coefficient_eqToIso p _ _ (IsScalarTower.algebraMap_eq k A B)

/-- The ENTIRE original source inclusion is preserved, including zero targets. -/
theorem targetBaseIso_source :
    RelativeFrobenius.sourceMap (algebraMap k B) p ≫
        (targetBaseIso (k := k) (A := A) (B := B) p).hom =
      RelativeFrobenius.sourceMap ((algebraMap A B).comp (algebraMap k A)) p :=
  source_eqToIso p _ _ (IsScalarTower.algebraMap_eq k A B)

/-- The SAME entire original geometric-beta map is preserved by this actual base-map iso. -/
theorem targetBaseIso_ringMap :
    (targetBaseIso (k := k) (A := A) (B := B) p).hom ≫
        SchemeRelativeFrobeniusAffineMap.ringMap ((algebraMap A B).comp (algebraMap k A)) p =
      SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p :=
  ringMap_eqToIso p _ _ (IsScalarTower.algebraMap_eq k A B)

/-- ENTIRE actual native numerator equals the ORIGINAL composed-base numerator through this iso. -/
theorem twistMap_targetBaseIso :
    RelativeEtaleCartierNaturality.twistMap (k := k) (A := A) (B := B) p ≫
        (targetBaseIso (k := k) (A := A) (B := B) p).hom =
      RelativeEtaleBaseChange.twistMap (algebraMap k A) (algebraMap A B) p := by
  apply pushout.hom_ext
  · change RelativeFrobenius.coefficientMap (algebraMap k A) p ≫ _ = _
    rw [← Category.assoc, RelativeEtaleCartierNaturality.twistMap_coefficient]
    exact (targetBaseIso_coefficient (k := k) (A := A) (B := B) p).trans
      (RelativeEtaleBaseChange.coefficientMap_twistMap (algebraMap k A) (algebraMap A B) p).symm
  · change RelativeFrobenius.sourceMap (algebraMap k A) p ≫ _ = _
    rw [← Category.assoc, RelativeEtaleCartierNaturality.twistMap_source, Category.assoc]
    exact (congrArg (fun F => CommRingCat.ofHom (algebraMap A B) ≫ F)
      (targetBaseIso_source (k := k) (A := A) (B := B) p)).trans
      (RelativeEtaleBaseChange.sourceMap_twistMap (algebraMap k A) (algebraMap A B) p).symm

end EnvelopeProperty.Cartier.RelativeGeometricTwistBaseChange
