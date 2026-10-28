import EnvelopeProperty.DI.LeadingCartierCycleTransport

/-! # Homology of the SAME zero-differential source retains its actual component -/
noncomputable section
namespace EnvelopeProperty.DI.ZeroSourceHomology
open CategoryTheory CategoryTheory.Limits
universe u
variable {A : Type u} [CommRing A]
variable (q : ℕ) (G E : CochainComplex (ModuleCat A) ℕ)
  (Φ : G ⟶ E) (hd : ∀ i j, G.d i j = 0)

/-- The original cycles and homology identifications for the SAME zero-differential source. -/
def homologySelfIso : G.homology q ≅ G.X q :=
  (G.isoHomologyπ _ q rfl (hd _ _)).symm ≪≫ G.iCyclesIso q _ rfl (hd _ _)

include hd in
/-- Closedness of the SAME original component follows from the whole chain-map identity. -/
theorem component_closed : ∀ j, (ComplexShape.up ℕ).Rel q j → Φ.f q ≫ E.d q j = 0 := by
  intro j _
  rw [Φ.comm, hd, zero_comp]

/-- The normalized original zero-source homology map equals the genuine single-component class map. -/
theorem homologyMap_eq_singleClassMap :
    (homologySelfIso q G hd).inv ≫ HomologicalComplex.homologyMap Φ q =
      LeadingCartierCycleTransport.singleClassMap q (G.X q) E (Φ.f q)
        (component_closed q G E Φ hd) := by
  let e := G.iCyclesIso q _ rfl (hd _ _)
  let L := E.liftCycles (Φ.f q) (q+1) (by simp)
    (component_closed q G E Φ hd (q+1) (by simp))
  have hc : e.inv ≫ HomologicalComplex.cyclesMap Φ q = L := by
    apply (cancel_mono (E.iCycles q)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i]
    dsimp only [L]
    rw [HomologicalComplex.liftCycles_i, ← Category.assoc]
    change e.inv ≫ e.hom ≫ Φ.f q = Φ.f q
    rw [Iso.inv_hom_id_assoc]
  rw [LeadingCartierCycleTransport.singleClassMap_eq_liftCycles]
  change (e.inv ≫ G.homologyπ q) ≫ HomologicalComplex.homologyMap Φ q = L ≫ E.homologyπ q
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc]
end EnvelopeProperty.DI.ZeroSourceHomology
