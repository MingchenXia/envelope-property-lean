import EnvelopeProperty.Cartier.RelativeCartierContinuationGlobalDomain

/-! # Genuine native cotangent exchange along the actual twist evaluation isomorphism

The maps are the original universal Kaehler maps of actual ring squares.
Bijectivity is derived internally from the actual inverse ring isomorphism.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeGlobalCotangentExchange
open AlgebraicGeometry CategoryTheory Opposite
universe u

section RingIso
variable {R A B : CommRingCat.{u}} (a : R ⟶ A) (b : R ⟶ B)
variable (e : A ≅ B) (h : a ≫ e.hom = b)
include h

/-- The inverse actual coefficient square follows from the original ring isomorphism. -/
theorem inverseCoefficientSquare : b ≫ e.inv = a := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The actual universal Kaehler map of the genuine coefficient square. -/
def cotangentMap : CommRingCat.KaehlerDifferential a ⟶
    (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential b) :=
  CommRingCat.KaehlerDifferential.map (g := 𝟙 R) (g' := e.hom)
    ((Category.id_comp b).trans h.symm)

/-- Every original universal differential has its actual ring-isomorphism image. -/
theorem cotangentMap_D (x : A) :
    cotangentMap a b e h (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d (e.hom x) :=
  CommRingCat.KaehlerDifferential.map_d _ x

/-- The original actual coefficient action is transported by the SAME ring isomorphism. -/
theorem cotangentMap_smul (c : A) (x : CommRingCat.KaehlerDifferential a) :
    cotangentMap a b e h (c • x) = e.hom c • cotangentMap a b e h x :=
  (cotangentMap a b e h).hom.map_smul c x

private def undoLinear : CommRingCat.KaehlerDifferential a ⟶ CommRingCat.KaehlerDifferential a :=
  cotangentMap a b e h ≫
    (ModuleCat.restrictScalars e.hom.hom).map
      (cotangentMap b a e.symm (inverseCoefficientSquare a b e h)) ≫
    (ModuleCat.restrictScalarsComp' e.hom.hom e.inv.hom (RingHom.id A)
      (congrArg CommRingCat.Hom.hom e.hom_inv_id).symm).inv.app
        (CommRingCat.KaehlerDifferential a) ≫
    (ModuleCat.restrictScalarsId' (RingHom.id A) rfl).hom.app
      (CommRingCat.KaehlerDifferential a)

/-- Inverting the ACTUAL ring isomorphism internally produces an inverse on EVERY
original cotangent element, by universal uniqueness rather than a comparison premise. -/
theorem cotangentMap_leftInverse : Function.LeftInverse
    (cotangentMap b a e.symm (inverseCoefficientSquare a b e h)) (cotangentMap a b e h) := by
  have hi : undoLinear a b e h = 𝟙 (CommRingCat.KaehlerDifferential a) := by
    apply CommRingCat.KaehlerDifferential.ext
    intro x
    change cotangentMap b a e.symm (inverseCoefficientSquare a b e h)
      (cotangentMap a b e h (CommRingCat.KaehlerDifferential.d x)) =
        CommRingCat.KaehlerDifferential.d x
    rw [cotangentMap_D, cotangentMap_D]
    exact congrArg CommRingCat.KaehlerDifferential.d (Iso.hom_inv_id_apply e x)
  intro x
  exact congrArg (fun f : CommRingCat.KaehlerDifferential a ⟶ CommRingCat.KaehlerDifferential a => f x) hi

/-- Genuine bijectivity of the SAME actual universal Kaehler map. -/
theorem cotangentMap_bijective : Function.Bijective (cotangentMap a b e h) := by
  have hl := cotangentMap_leftInverse a b e h
  have hr := cotangentMap_leftInverse b a e.symm (inverseCoefficientSquare a b e h)
  exact ⟨hl.injective, hr.surjective⟩

/-- The actual native coefficient-preserving ring isomorphism gives the actual cotangent iso. -/
def cotangentIso : CommRingCat.KaehlerDifferential a ≅
    (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential b) :=
  (LinearEquiv.ofBijective (cotangentMap a b e h).hom (cotangentMap_bijective a b e h)).toModuleIso

/-- The entire original universal differential formula for the genuine cotangent iso. -/
theorem cotangentIso_D (x : A) :
    (cotangentIso a b e h).hom (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d (e.hom x) :=
  cotangentMap_D a b e h x
end RingIso

section Global
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "TG" => RelativeGlobalCartierDomain.twistPresheaf f p
local notation "CG" => RelativeGlobalCartierDomain.coefficientMap f p
local notation "E" => RelativeGlobalCartierDomain.evaluationIso f p

/-- The actual global twist cotangent value is the SAME native affine twist cotangent,
including zero section rings, by the proved actual coefficient-evaluation triangle. -/
def evaluationCotangentIso (U : X.Opensᵒᵖ) :
    (RelativeGlobalCartierDomain.cotangentPresheaf f p).obj U ≅
      (ModuleCat.restrictScalars (E U).hom.hom).obj
        (CommRingCat.KaehlerDifferential (RelativeFrobenius.coefficientMap (A := k)
          ((CanonicalGeometry.schemeConstantPresheafMap f).app U).hom p)) :=
  cotangentIso ((CG).app U) _ (E U)
    (RelativeGlobalCartierDomain.coefficientMap_evaluationIso f p U)

/-- Evaluation preserves EVERY actual universal differential, without a local chart
or section-ring characteristic input. -/
theorem evaluationCotangentIso_D (U : X.Opensᵒᵖ) (x : (TG).obj U) :
    (evaluationCotangentIso f p U).hom (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d ((E U).hom x) :=
  cotangentIso_D ((CG).app U) _ (E U)
    (RelativeGlobalCartierDomain.coefficientMap_evaluationIso f p U) x
end Global
end EnvelopeProperty.Cartier.RelativeGlobalCotangentExchange
