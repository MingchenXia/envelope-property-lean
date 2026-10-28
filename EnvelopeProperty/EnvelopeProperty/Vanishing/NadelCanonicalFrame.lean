import EnvelopeProperty.Vanishing.NadelKummerCanonicalTrace

/-! # Native canonical-frame construction and actual counit formulas

The generic algebra/module data here are instantiated by proved geometric
frames and native finite duals in the whole mixed producers.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalFrame

open CategoryTheory ModuleCat CanonicalGeometry
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    {n : ℕ} (f : A →+* B) (bA : Module.Basis (Fin n) A (KaehlerDifferential k A))
    (bB : Module.Basis (Fin n) B (KaehlerDifferential k B))
    (F : ModuleCat.of B B ≅ (coextendScalars f).obj (ModuleCat.of A A))

/-- Genuine top differential frames transfer an actual native finite dual to the actual original canonical modules. -/
def iso : ModuleCat.of B (affineCanonicalModule k B n) ≅
    (coextendScalars f).obj (ModuleCat.of A (affineCanonicalModule k A n)) :=
  (affineCanonicalTrivialization bB).toModuleIso ≪≫ F ≪≫
    (coextendScalars f).mapIso (affineCanonicalTrivialization bA).symm.toModuleIso

/-- The native functional formula, without unfolding any supplied frame or dual construction. -/
theorem iso_apply (w : affineCanonicalModule k B n) (c : B) :
    (iso f bA bB F).hom w c =
      (affineCanonicalTrivialization bA).symm (F.hom (affineCanonicalTrivialization bB w) c) := rfl

/-- The actual native canonical counit of this constructed isomorphism. -/
def counit : (restrictScalars f).obj (ModuleCat.of B (affineCanonicalModule k B n)) ⟶
    ModuleCat.of A (affineCanonicalModule k A n) :=
  (restrictScalars f).map (iso f bA bB F).hom ≫
    (restrictCoextendScalarsAdj f).counit.app (ModuleCat.of A (affineCanonicalModule k A n))

/-- The genuine native counit is evaluation at the original unit, under the actual frame. -/
theorem counit_apply (w : affineCanonicalModule k B n) :
    counit f bA bB F w =
      (affineCanonicalTrivialization bA).symm (F.hom (affineCanonicalTrivialization bB w) (1 : B)) := rfl

end EnvelopeProperty.Vanishing.NadelCanonicalFrame
