import EnvelopeProperty.AlgGeom.SchemeRationalDenominators
import Hironaka.Scheme.Modules.IdealSheaf

/-! # Genuine original numerator sections of the denominator ideal sheaf -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
namespace EnvelopeProperty.SchemeRationalDenominatorSections
open SchemeRationalDenominators
variable (X : Scheme.{u}) [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original restriction retains the literal generic germ in the same K(X). -/
theorem germ_restriction {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : U ≤ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map (homOfLE h).op s) =
      X.germToFunctionField V s :=
  X.presheaf.germ_res_apply (homOfLE h) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))) s

omit [IsIntegral X] in
private theorem subsingleton_sections_of_not_nonempty (U : X.Opens) (h : ¬ Nonempty U) :
    Subsingleton Γ(X, U) := by
  have he : U = ⊥ := by
    apply SetLike.ext
    intro x
    simp only [Opens.mem_bot, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty he)

/-- Every genuine original denominator-ideal section has an actual numerator
on the SAME original whole open, with its literal SAME-field product. -/
theorem exists_numerator (f : X.functionField) (U : X.Opens) [Nonempty U]
    (s : Γ(X, U)) (hs : (idealSheaf X f).IsLocallyMem U s) :
    ∃ b : Γ(X, U), X.germToFunctionField U b = X.germToFunctionField U s * f := by
  let ι := {V : X.affineOpens // V.1 ≤ U ∧ Nonempty V.1}
  let W : ι → X.Opens := fun i => i.val.1
  let hmem (i : ι) : letI := i.property.2; ∃ b : Γ(X, W i),
      X.germToFunctionField (W i) b = X.germToFunctionField U s * f := by
    let : Nonempty (W i) := i.property.2
    have hi := hs i.val i.property.1
    rw [idealSheaf_ideal] at hi
    obtain ⟨b, hb⟩ := hi
    refine ⟨b, ?_⟩
    change X.germToFunctionField (W i) b =
      X.germToFunctionField (W i) (X.presheaf.map (homOfLE i.property.1).op s) * f at hb
    exact hb.trans (congrArg (fun c : X.functionField => c * f)
      (germ_restriction X i.property.1 s))
  let b (i : ι) : Γ(X, W i) := (hmem i).choose
  have hb (i : ι) : letI := i.property.2
      X.germToFunctionField (W i) (b i) = X.germToFunctionField U s * f :=
    (hmem i).choose_spec
  have hcover : U ≤ iSup W := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU, ⟨⟨x, hxV⟩⟩⟩, hxV⟩
  have hcpt : ∀ i j, X.presheaf.map (Opens.infLELeft (W i) (W j)).op (b i) =
      X.presheaf.map (Opens.infLERight (W i) (W j)).op (b j) := by
    intro i j
    by_cases h : Nonempty ((W i ⊓ W j : X.Opens) : Set X)
    · have hcap : Nonempty ((W i ⊓ W j : X.Opens) : Set X) := h
      have hWi : Nonempty (W i) := i.property.2
      have hWj : Nonempty (W j) := j.property.2
      apply @Scheme.germToFunctionField_injective X _ (W i ⊓ W j) hcap
      exact (@germ_restriction X _ (W i ⊓ W j) (W i) hcap hWi inf_le_left (b i)).trans
        ((hb i).trans ((hb j).symm.trans (@germ_restriction X _ (W i ⊓ W j) (W j) hcap hWj inf_le_right (b j)).symm))
    · let := subsingleton_sections_of_not_nonempty X _ h
      exact Subsingleton.elim _ _
  obtain ⟨a, ha, _⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W U
    (fun i => homOfLE i.property.1) hcover b hcpt
  refine ⟨a, ?_⟩
  obtain ⟨x, hx⟩ := (inferInstance : Nonempty U)
  obtain ⟨i, _⟩ := Opens.mem_iSup.mp (hcover hx)
  let : Nonempty (W i) := i.property.2
  calc
    X.germToFunctionField U a =
        X.germToFunctionField (W i) (X.presheaf.map (homOfLE i.property.1).op a) :=
      (germ_restriction X i.property.1 a).symm
    _ = X.germToFunctionField (W i) (b i) := congrArg (X.germToFunctionField (W i))
      (show X.presheaf.map (homOfLE i.property.1).op a = b i from ha i)
    _ = X.germToFunctionField U s * f := hb i

/-- Exact whole original section condition, on EVERY nonempty original open. -/
theorem isLocallyMem_iff (f : X.functionField) (U : X.Opens) [Nonempty U]
    (s : Γ(X, U)) :
    (idealSheaf X f).IsLocallyMem U s ↔
      ∃ b : Γ(X, U), X.germToFunctionField U b = X.germToFunctionField U s * f := by
  refine ⟨exists_numerator X f U s, ?_⟩
  rintro ⟨b, hb⟩ V hVU
  by_cases h : Nonempty V.1
  · let := h
    rw [idealSheaf_ideal]
    refine ⟨X.presheaf.map (homOfLE hVU).op b, ?_⟩
    change X.germToFunctionField V.1 _ = X.germToFunctionField V.1 _ * f
    rw [germ_restriction, germ_restriction, hb]
  · change X.presheaf.map (homOfLE hVU).op s ∈ affineIdeal X f V
    rw [affineIdeal, dif_neg h]
    trivial


/-- The genuine original numerator on the same whole original open. -/
def numerator (f : X.functionField) (U : X.Opens)
    (s : Γ((idealSheaf X f).toModules, U)) : Γ(X, U) := by
  classical
  exact if h : Nonempty U then
    letI := h
    (exists_numerator X f U s.val s.property).choose
  else 0

/-- The actual chosen whole numerator has the literal original field coefficient. -/
theorem germ_numerator (f : X.functionField) (U : X.Opens) [Nonempty U]
    (s : Γ((idealSheaf X f).toModules, U)) :
    X.germToFunctionField U (numerator X f U s) = X.germToFunctionField U s.val * f := by
  rw [numerator, dif_pos (inferInstance : Nonempty U)]
  exact (exists_numerator X f U s.val s.property).choose_spec

private theorem numerator_empty (f : X.functionField) (U : X.Opens) (h : ¬ Nonempty U)
    (s : Γ((idealSheaf X f).toModules, U)) : numerator X f U s = 0 := by
  rw [numerator, dif_neg h]

/-- Multiplication by f lands in the SAME original denominator sheaf of g
whenever the actual original field identity fg=1 holds. -/
theorem numerator_mem (f g : X.functionField) (hfg : f * g = 1)
    (U : X.Opens) (s : Γ((idealSheaf X f).toModules, U)) :
    (idealSheaf X g).IsLocallyMem U (numerator X f U s) := by
  by_cases h : Nonempty U
  · let := h
    apply (isLocallyMem_iff X g U _).mpr
    refine ⟨s.val, ?_⟩
    rw [germ_numerator, mul_assoc, hfg, mul_one]
  · rw [numerator_empty X f U h]
    intro V hVU
    rw [map_zero]
    exact Ideal.zero_mem _

/-- Genuine original structure-ring linearity of whole multiplication by f. -/
def multiplicationSection (f g : X.functionField) (hfg : f * g = 1) (U : X.Opens) :
    Γ((idealSheaf X f).toModules, U) →ₗ[Γ(X, U)] Γ((idealSheaf X g).toModules, U) where
  toFun s := ⟨numerator X f U s, numerator_mem X f g hfg U s⟩
  map_add' a b := by
    apply Subtype.ext
    change numerator X f U (a + b) = numerator X f U a + numerator X f U b
    by_cases h : Nonempty U
    · let := h
      apply X.germToFunctionField_injective U
      rw [germ_numerator, map_add, germ_numerator, germ_numerator]
      change X.germToFunctionField U (a.val + b.val) * f = _
      rw [map_add, add_mul]
    · let := subsingleton_sections_of_not_nonempty X U h
      exact Subsingleton.elim _ _
  map_smul' r a := by
    apply Subtype.ext
    change numerator X f U (r • a) = r * numerator X f U a
    by_cases h : Nonempty U
    · let := h
      apply X.germToFunctionField_injective U
      rw [germ_numerator, map_mul, germ_numerator]
      let av : Γ(X, U) := a.val
      have hs : ((r • a).val : Γ(X, U)) = r * av := rfl
      rw [hs, map_mul, mul_assoc]
    · let := subsingleton_sections_of_not_nonempty X U h
      exact Subsingleton.elim _ _

/-- Actual whole original ideal-module multiplication by the SAME f. -/
def multiplicationHom (f g : X.functionField) (hfg : f * g = 1) :
    (idealSheaf X f).toModules ⟶ (idealSheaf X g).toModules where
  val :=
    { app U := ModuleCat.ofHom (multiplicationSection X f g hfg U.unop)
      naturality := fun {U V} h => by
        apply ModuleCat.hom_ext
        ext s
        apply Subtype.ext
        change numerator X f V.unop ((idealSheaf X f).toModules.val.map h s) =
          X.presheaf.map h (numerator X f U.unop s)
        by_cases hV : Nonempty V.unop
        · let := hV
          let : Nonempty U.unop := Nonempty.map (fun x => ⟨x.val, h.unop.le x.property⟩) hV
          apply X.germToFunctionField_injective V.unop
          rw [germ_numerator]
          change X.germToFunctionField V.unop (X.presheaf.map h s.val) * f = _
          exact (congrArg (fun c : X.functionField => c * f)
            (germ_restriction X h.unop.le s.val)).trans
              ((germ_numerator X f U.unop s).symm.trans
                (germ_restriction X h.unop.le (numerator X f U.unop s)).symm)
        · let := subsingleton_sections_of_not_nonempty X V.unop hV
          exact Subsingleton.elim _ _ }

/-- Literal original generic coefficient of the whole multiplication morphism. -/
theorem multiplicationHom_coefficient (f g : X.functionField) (hfg : f * g = 1)
    (U : X.Opens) [Nonempty U] (s : Γ((idealSheaf X f).toModules, U)) :
    X.germToFunctionField U (((multiplicationHom X f g hfg).val.app (op U)) s).val =
      X.germToFunctionField U s.val * f := germ_numerator X f U s

private theorem multiplicationHom_comp (f g : X.functionField)
    (hfg : f * g = 1) (hgf : g * f = 1) :
    multiplicationHom X f g hfg ≫ multiplicationHom X g f hgf =
      𝟙 (idealSheaf X f).toModules := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  apply Subtype.ext
  change numerator X g U.unop (multiplicationSection X f g hfg U.unop s) =
    (s.val : Γ(X, U.unop))
  by_cases h : Nonempty U.unop
  · let := h
    apply X.germToFunctionField_injective U.unop
    rw [germ_numerator]
    change X.germToFunctionField U.unop (numerator X f U.unop s) * g = _
    rw [germ_numerator, mul_assoc, hfg, mul_one]
  · let := subsingleton_sections_of_not_nonempty X U.unop h
    exact Subsingleton.elim _ _

/-- Whole original reciprocal denominator modules are genuinely isomorphic
by multiplication by the SAME original nonzero rational function. -/
def reciprocalIso (f : X.functionField) (hf : f ≠ 0) :
    (idealSheaf X f).toModules ≅ (idealSheaf X f⁻¹).toModules where
  hom := multiplicationHom X f f⁻¹ (mul_inv_cancel₀ hf)
  inv := multiplicationHom X f⁻¹ f (inv_mul_cancel₀ hf)
  hom_inv_id := multiplicationHom_comp X f f⁻¹ _ _
  inv_hom_id := multiplicationHom_comp X f⁻¹ f _ _

/-- The WHOLE original isomorphism retains literal original multiplication by f. -/
theorem reciprocalIso_coefficient (f : X.functionField) (hf : f ≠ 0)
    (U : X.Opens) [Nonempty U] (s : Γ((idealSheaf X f).toModules, U)) :
    X.germToFunctionField U (((reciprocalIso X f hf).hom.val.app (op U)) s).val =
      X.germToFunctionField U s.val * f :=
  multiplicationHom_coefficient X f f⁻¹ (mul_inv_cancel₀ hf) U s

end EnvelopeProperty.SchemeRationalDenominatorSections
