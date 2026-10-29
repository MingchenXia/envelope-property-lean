import EnvelopeProperty.AlgGeom.Canonical.GenericLineSections
import EnvelopeProperty.AlgGeom.Canonical.InvertibleLineAtlas
import EnvelopeProperty.Algebra.NormalizedLineFrame

/-! # SAME original line sections normalized by an actual original global section -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace EnvelopeProperty.CanonicalGeometry
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} [IsIntegral X]

private theorem originalSectionGenericGermNeZero {L : X.Modules} (a : LineBundleAtlas L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) : bundleGenericGerm L ⊤ d ≠ 0 := by
  intro h
  apply hd
  apply bundleGenericGerm_global_injective a
  exact h.trans (bundleGenericGerm L ⊤).map_zero.symm

/-- The SAME entire original generic module stalk has its TRUE frame
normalized by the SAME actual original nonzero global section. -/
def genericNormalizedFrame (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) : genericBundleFiber L ≃ₗ[X.functionField] X.functionField := by
  let a := invertibleLineAtlas L hL
  let i := Classical.choose (a.covers (genericPoint X))
  let : Nonempty (a.opens i) := ⟨⟨genericPoint X, Classical.choose_spec (a.covers (genericPoint X))⟩⟩
  exact NormalizedLineFrame.normalize (genericBundleFiberFrame (a.frame i))
    (bundleGenericGerm L ⊤ d) (originalSectionGenericGermNeZero a d hd)

/-- The SAME original global section has true generic coefficient one. -/
theorem genericNormalizedFrame_generator (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) :
    genericNormalizedFrame L hL d hd (bundleGenericGerm L ⊤ d) = 1 := by
  dsimp only [genericNormalizedFrame]
  exact NormalizedLineFrame.normalize_generator _ _ _

/-- EVERY genuine original local frame gives the SAME entire normalized
coefficient, without a frame-matching premise. -/
theorem genericNormalizedFrame_apply_frame (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) (m : genericBundleFiber L) :
    genericNormalizedFrame L hL d hd m =
      genericBundleFiberFrame e m / genericBundleFiberFrame e (bundleGenericGerm L ⊤ d) := by
  dsimp only [genericNormalizedFrame]
  rw [NormalizedLineFrame.normalize_independent _ (genericBundleFiberFrame e)]
  exact NormalizedLineFrame.normalize_apply _ _ _ _

private theorem originalOpenModuleGermInjective {L : X.Modules} (a : LineBundleAtlas L)
    (U : X.Opens) [Nonempty U] : Function.Injective (bundleGenericGerm L U) := by
  intro s t h
  change L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U) s =
    L.presheaf.germ U (genericPoint X) (genericPoint_mem_nonempty_open U) t at h
  obtain ⟨V, hV, i, j, heq⟩ := L.presheaf.germ_eq _ _ _ _ _ h
  cases Subsingleton.elim i j
  let : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
  exact a.restriction_injective i heq

/-- ALL original sections on a nonempty original open have their SAME
actual rational coefficient normalized by the original section. -/
def sectionRatio (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) (U : X.Opens) [Nonempty U] :
    Γ(L, U) →ₛₗ[(X.germToFunctionField U).hom] X.functionField :=
  (genericNormalizedFrame L hL d hd).toLinearMap.comp (bundleGenericGerm L U)

/-- The entire actual original section-to-field coefficient is faithful,
derived from actual integral geometry, not an injectivity certificate. -/
theorem sectionRatio_injective (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) (U : X.Opens) [Nonempty U] :
    Function.Injective (sectionRatio L hL d hd U) :=
  (genericNormalizedFrame L hL d hd).injective.comp
    (originalOpenModuleGermInjective (invertibleLineAtlas L hL) U)

/-- EVERY original frame computes the exact SAME normalized rational
coefficient of EVERY original section, with the SAME original generator. -/
theorem sectionRatio_frame_formula (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L U) (s : Γ(L, U)) :
    sectionRatio L hL d hd U s = e.toFunctionField s / globalSectionToFunctionField e d := by
  change genericNormalizedFrame L hL d hd (bundleGenericGerm L U s) = _
  rw [genericNormalizedFrame_apply_frame L hL d hd e,
    genericBundleFiberFrame_germ, genericBundleFiberFrame_global_germ]

/-- Actual original restriction retains the SAME entire rational coefficient. -/
theorem sectionRatio_restrict (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (s : Γ(L, U)) :
    sectionRatio L hL d hd V (L.presheaf.map (homOfLE hVU).op s) =
      sectionRatio L hL d hd U s :=
  congrArg (genericNormalizedFrame L hL d hd)
    (L.presheaf.germ_res_apply (homOfLE hVU) (genericPoint X)
      (genericPoint_mem_nonempty_open V) s)

/-- The SAME original global section restricts to coefficient one on
EVERY original nonempty open, without local generator matching data. -/
theorem sectionRatio_generator (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (d : Γ(L, ⊤)) (hd : d ≠ 0) (U : X.Opens) [Nonempty U] :
    sectionRatio L hL d hd U (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op d) = 1 := by
  rw [sectionRatio_restrict]
  exact genericNormalizedFrame_generator L hL d hd

end
end EnvelopeProperty.CanonicalGeometry
