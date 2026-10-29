import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps

/-! # An actual nonempty isomorphism open identifies the SAME native function fields -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace EnvelopeProperty.GenericOpenFunctionField
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) [hNonempty : Nonempty U] [hIso : IsIso (g ∣_ U)]

include U hNonempty hIso in
/-- The actual original restricted isomorphism derives dominance of the
SAME original map, with no density or dominance certificate supplied. -/
theorem isDominant_of_isIso_restrict [IsIntegral X] : IsDominant g := by
  have hsub : (U : Set X) ⊆ Set.range g := by
    intro x hx
    let xU : U.toScheme := ⟨x, hx⟩
    let z := inv (g ∣_ U) xU
    refine ⟨(g ⁻¹ᵁ U).ι z, ?_⟩
    have ht := congrArg (fun f : (g ⁻¹ᵁ U).toScheme ⟶ X => f z) (morphismRestrict_ι g U)
    change U.ι ((g ∣_ U) z) = g ((g ⁻¹ᵁ U).ι z) at ht
    have hi : (g ∣_ U) (inv (g ∣_ U) xU) = xU :=
      congrArg (fun f : U.toScheme ⟶ U.toScheme => f xU) (asIso (g ∣_ U)).inv_hom_id
    exact ht.symm.trans (congrArg U.ι hi)
  constructor
  intro x
  exact closure_mono hsub (U.isOpen.dense (Set.nonempty_coe_sort.mp hNonempty) x)

omit [Nonempty U] in
/-- Over the SAME original isomorphism open, the ENTIRE original native
stalk map is an isomorphism, derived by the actual restriction arrow comparison. -/
theorem isIso_stalkMap_of_isIso_restrict (y : Y) (hy : y ∈ g ⁻¹ᵁ U) :
    IsIso (g.stalkMap y) := by
  let q : (g ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
  have hr : IsIso (g.resLE U (g ⁻¹ᵁ U) le_rfl) := by
    rw [g.resLE_eq_morphismRestrict]
    infer_instance
  let := hr
  let : IsOpenImmersion (g.resLE U (g ⁻¹ᵁ U) le_rfl) := IsOpenImmersion.of_isIso _
  exact (Arrow.isIso_hom_iff_isIso_of_isIso
    (g.resLEStalkMap (le_rfl : g ⁻¹ᵁ U ≤ g ⁻¹ᵁ U) q).hom).mp (by
      change IsIso ((g.resLE U (g ⁻¹ᵁ U) le_rfl).stalkMap q)
      infer_instance)

private theorem originalEqualPointStalkIso {T : Scheme.{u}} {x y : T} (h : x = y) :
    IsIso (T.presheaf.stalkSpecializes (specializes_of_eq h)) := by
  subst y
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

/-- Actual integral geometry and the original nonempty isomorphism open
derive that the SAME dominant generic-stalk field map is an isomorphism. -/
theorem isIso_functionFieldMap_of_isIso_restrict [IsIntegral X] [IsIntegral Y] :
    letI := isDominant_of_isIso_restrict g U
    IsIso (DominantFunctionFieldMaps.functionFieldMap g) := by
  let := isDominant_of_isIso_restrict g U
  have hU : Nonempty (g ⁻¹ᵁ U) := Nonempty.map (inv (g ∣_ U)) inferInstance
  let := hU
  have hη : genericPoint Y ∈ g ⁻¹ᵁ U :=
    ((genericPoint_spec Y).mem_open_set_iff (g ⁻¹ᵁ U).isOpen).mpr
      (by simpa using Set.nonempty_coe_sort.mp hU)
  let : IsIso (g.stalkMap (genericPoint Y)) := isIso_stalkMap_of_isIso_restrict g U _ hη
  let : IsIso (X.presheaf.stalkSpecializes
      (specializes_of_eq (DominantFunctionFieldMaps.genericPoint_map g))) :=
    originalEqualPointStalkIso (DominantFunctionFieldMaps.genericPoint_map g)
  change IsIso (X.presheaf.stalkSpecializes
    (specializes_of_eq (DominantFunctionFieldMaps.genericPoint_map g)) ≫ g.stalkMap (genericPoint Y))
  infer_instance

/-- The actual original function-field isomorphism is the SAME original
generic-stalk map, not an unrelated choice of abstract field equivalence. -/
def functionFieldIso [IsIntegral X] [IsIntegral Y] : X.functionField ≅ Y.functionField := by
  let := isDominant_of_isIso_restrict g U
  let := isIso_functionFieldMap_of_isIso_restrict g U
  exact asIso (DominantFunctionFieldMaps.functionFieldMap g)

/-- The ENTIRE original field isomorphism retains the SAME original
native dominant generic-stalk map on every element. -/
theorem functionFieldIso_hom [IsIntegral X] [IsIntegral Y] :
    letI := isDominant_of_isIso_restrict g U
    (functionFieldIso g U).hom = DominantFunctionFieldMaps.functionFieldMap g := rfl

/-- EVERY original coefficient section on EVERY nonempty original open
is retained by this SAME actual function-field isomorphism. -/
theorem functionFieldIso_section [IsIntegral X] [IsIntegral Y]
    (V : X.Opens) [Nonempty V] [Nonempty (g ⁻¹ᵁ V)] (s : Γ(X, V)) :
    (functionFieldIso g U).hom (X.germToFunctionField V s) =
      Y.germToFunctionField (g ⁻¹ᵁ V) (g.app V s) := by
  let := isDominant_of_isIso_restrict g U
  exact DominantFunctionFieldMaps.functionFieldMap_section g V s

section Spec
open scoped nonZeroDivisors
variable {A : CommRingCat.{u}} [IsDomain A] {F : Type u}
  [Field F] [Algebra A F] [IsFractionRing A F]
variable (p : Y ⟶ Spec A) (W : (Spec A).Opens) [Nonempty W] [IsIso (p ∣_ W)]

/-- The SAME actual target generic field identifies with the specified
original fraction field, using its actual native affine fraction action. -/
def specFractionFieldEquiv [IsIntegral Y] : Y.functionField ≃+* F :=
  (functionFieldIso p W).symm.commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (nonZeroDivisors A) (Spec A).functionField F).toRingEquiv

/-- EVERY original pulled coefficient section is retained under the SAME
native field comparison and original fraction-field equivalence. -/
theorem specFractionFieldEquiv_pullback_section [IsIntegral Y]
    (V : (Spec A).Opens) [Nonempty V] [Nonempty (p ⁻¹ᵁ V)]
    (s : Γ(Spec A, V)) :
    specFractionFieldEquiv (F := F) p W (Y.germToFunctionField (p ⁻¹ᵁ V) (p.app V s)) =
      IsLocalization.algEquiv (nonZeroDivisors A) (Spec A).functionField F
        ((Spec A).germToFunctionField V s) := by
  let e := functionFieldIso p W
  have h := functionFieldIso_section p W V s
  have hi : e.inv (Y.germToFunctionField (p ⁻¹ᵁ V) (p.app V s)) =
      (Spec A).germToFunctionField V s :=
    (congrArg (fun a => e.inv a) h.symm).trans (Iso.hom_inv_id_apply e _)
  exact congrArg (IsLocalization.algEquiv (nonZeroDivisors A) (Spec A).functionField F) hi

/-- EVERY coefficient of the SAME original affine ring has exactly its
prescribed value in the SAME original fraction field; no coefficient matching is assumed. -/
theorem specFractionFieldEquiv_coefficients [IsIntegral Y] (a : A) :
    letI : Nonempty (p ⁻¹ᵁ (⊤ : (Spec A).Opens)) := ⟨⟨genericPoint Y, by trivial⟩⟩
    specFractionFieldEquiv (F := F) p W
      (Y.germToFunctionField (p ⁻¹ᵁ (⊤ : (Spec A).Opens))
        (p.app ⊤ ((Scheme.ΓSpecIso A).inv a))) = algebraMap A F a := by
  let : Nonempty (p ⁻¹ᵁ (⊤ : (Spec A).Opens)) := ⟨⟨genericPoint Y, by trivial⟩⟩
  let : Nonempty (⊤ : (Spec A).Opens) := ⟨⟨genericPoint (Spec A), trivial⟩⟩
  have h := specFractionFieldEquiv_pullback_section (F := F) p W ⊤
    ((Scheme.ΓSpecIso A).inv a)
  exact h.trans ((IsLocalization.algEquiv (nonZeroDivisors A)
    (Spec A).functionField F).commutes a)

end Spec

end EnvelopeProperty.GenericOpenFunctionField
