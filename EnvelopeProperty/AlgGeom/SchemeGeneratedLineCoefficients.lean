import EnvelopeProperty.AlgGeom.SchemeGeneratorCoefficientOpens

/-! # Actual affine-frame coefficients of SAME original globally generated lines -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.SchemeGeneratedLineCoefficients
open SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {L : X.Modules}

/-- The SAME actual original generators, followed by a genuine original whole frame. -/
def framedGenerators (G : L.GeneratingSections) (e : L ≅ unitObj X) :
    (unitObj X).GeneratingSections := G.ofEpi e.hom

/-- The actual whole original coefficient of each SAME original generator. -/
def coefficient (G : L.GeneratingSections) (e : L ≅ unitObj X) (i : G.I) : Γ(X, ⊤) :=
  SchemeGeneratorCoefficientOpens.coefficient (framedGenerators G e) i

/-- These are the literal original frame values of the SAME original sections. -/
theorem coefficient_apply (G : L.GeneratingSections) (e : L ≅ unitObj X) (i : G.I) :
    coefficient G e i = (e.hom.val.app (op ⊤)).hom
      (((generatorHom G i).val.app (op ⊤)).hom (1 : Γ(X, ⊤))) := by
  have h := congrArg (fun q : unitObj X ⟶ unitObj X =>
    (q.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) (generatorHom_ofEpi G e.hom i)
  change coefficient G e i = _ at h
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
  exact h

/-- Actual original generators DERIVE the whole unit-ideal condition in EVERY original affine frame. -/
theorem span_coefficients_eq_top [IsAffine X] (G : L.GeneratingSections) (e : L ≅ unitObj X) :
    Ideal.span (Set.range (coefficient G e)) = ⊤ :=
  SchemeGeneratorCoefficientOpens.span_coefficients_eq_top (framedGenerators G e)

private theorem scalar_top_apply {B : Scheme.{u}} (r a : Γ(B, ⊤)) :
    ((ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤)).hom a = a * r := by
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  simp only [homOfLE_refl, op_id]
  change a * (B.presheaf.map (𝟙 (op (⊤ : B.Opens)))).hom r = a * r
  exact congrArg (fun q : Γ(B, ⊤) ⟶ Γ(B, ⊤) => a * q.hom r)
    (B.presheaf.map_id (op (⊤ : B.Opens)))

private theorem scalar_post {B : Scheme.{u}}
    (a : unitObj B ⟶ unitObj B) (r : Γ(B, ⊤)) :
    ((a ≫ ModularCurves.unitEndomorphismOfTopSection r).val.app (op ⊤)).hom
      (1 : Γ(B, ⊤)) = (show Γ(B, ⊤) from (a.val.app (op ⊤)).hom (1 : Γ(B, ⊤))) * r := by
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact scalar_top_apply r _

/-- Two ACTUAL original frames DERIVE one genuine original global unit
multiplying the ENTIRE SAME original coefficient family. -/
theorem exists_unit_coefficient_transition (G : L.GeneratingSections)
    (e e' : L ≅ unitObj X) :
    ∃ v : Γ(X, ⊤)ˣ, ∀ i : G.I, coefficient G e' i = (v : Γ(X, ⊤)) * coefficient G e i := by
  obtain ⟨v, hv⟩ := unitIso_eq_globalUnit (e.symm ≪≫ e')
  have he : e'.hom = e.hom ≫ ModularCurves.unitEndomorphismOfTopSection (v : Γ(X, ⊤)) := by
    have h := congrArg (fun q : unitObj X ≅ unitObj X => e.hom ≫ q.hom) hv
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc,
      ModularCurves.unitAutomorphismOfTopUnit_hom] using h
  refine ⟨v, fun i => ?_⟩
  have hgen : generatorHom (framedGenerators G e') i =
      generatorHom (framedGenerators G e) i ≫
        ModularCurves.unitEndomorphismOfTopSection (v : Γ(X, ⊤)) := by
    simp only [framedGenerators, generatorHom_ofEpi]
    rw [he, Category.assoc]
  have hc := congrArg (fun q : unitObj X ⟶ unitObj X =>
    (q.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) hgen
  exact hc.trans ((scalar_post _ _).trans (mul_comm (coefficient G e i) (v : Γ(X, ⊤))))

/-- Actual original pullback and genuine whole pulled frame preserve the
ENTIRE SAME original generator coefficient family over the original scalar map. -/
theorem coefficient_pullback (f : Y ⟶ X) (G : L.GeneratingSections) (e : L ≅ unitObj X) (i : G.I) :
    coefficient (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G)
      ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f) i =
        f.appTop.hom (coefficient G e i) := by
  have h : generatorHom (framedGenerators
      (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G)
      ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f)) i =
      generatorHom ((ClosedProjectiveGlobalGeneration.pullback_generatingSections f
        (framedGenerators G e)).ofEpi (pullbackUnitIso f).hom) i := by
    simp only [framedGenerators, generatorHom_ofEpi, generatorHom_pullback,
      Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  exact (congrArg (fun q : unitObj Y ⟶ unitObj Y =>
    (q.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) h).trans
      (SchemeGeneratorCoefficientOpens.coefficient_pullback f (framedGenerators G e) i)

/-- Relabel a finite ORIGINAL tuple and append one actual zero coordinate. -/
def paddedCoefficients {ι : Type u} [Fintype ι] {A : Type u} [Zero A]
    (a : ι → A) : Fin (Fintype.card ι + 1) → A :=
  Fin.cases 0 (fun i => a ((Fintype.equivFin ι).symm i))

/-- The SAME original ring map commutes with all actual padded coefficients. -/
theorem paddedCoefficients_map {ι : Type u} [Fintype ι] {A B : Type u}
    [CommRing A] [CommRing B] (a : ι → A) (f : A →+* B) :
    paddedCoefficients (fun i => f (a i)) = fun j => f (paddedCoefficients a j) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact (map_zero f).symm
  · rfl

/-- A genuine whole-ring unit scales the ENTIRE SAME padded original tuple. -/
theorem paddedCoefficients_unit {ι : Type u} [Fintype ι] {A : Type u} [CommRing A]
    (a : ι → A) (v : Aˣ) :
    paddedCoefficients (fun i => (v : A) * a i) = fun j => (v : A) * paddedCoefficients a j := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact (mul_zero _).symm
  · rfl

/-- EVERY actual original unit-spanning family retains the true unit-ideal
condition after actual relabeling/padding, including the original empty family. -/
theorem span_paddedCoefficients_eq_top {ι : Type u} [Fintype ι] {A : Type u} [CommRing A]
    (a : ι → A) (ha : Ideal.span (Set.range a) = ⊤) :
    Ideal.span (Set.range (paddedCoefficients a)) = ⊤ := by
  apply top_unique
  rw [← ha]
  apply Ideal.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨((Fintype.equivFin ι) i).succ, by simp only [paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply]⟩

end EnvelopeProperty.SchemeGeneratedLineCoefficients
