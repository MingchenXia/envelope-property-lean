import EnvelopeProperty.Vanishing.NadelNefBigAffineGeneratorSpan

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigAffineIdealGenerators
open NadelNefBigAffineGeneratorSpan
variable {A : CommRingCat.{u}} (D : (Spec (.of A)).IdealSheafData)
    (G : D.toModules.GeneratingSections)

def generatorValue (i : G.I) : D.ideal ⟨⊤, isAffineOpen_top _⟩ :=
  D.toModulesSectionsEquiv ⟨⊤, isAffineOpen_top _⟩ (NadelNefBigAffineGeneratorSpan.generatorValue D.toModules G i)

theorem span_generatorValues :
    Ideal.span (Set.range (fun i => (generatorValue D G i : Γ(Spec (.of A), ⊤)))) =
      D.ideal ⟨⊤, isAffineOpen_top _⟩ := by
  let J := Ideal.span (Set.range (fun i => (generatorValue D G i : Γ(Spec (.of A), ⊤))))
  apply le_antisymm
  · exact Ideal.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ (generatorValue D G i).property)
  · intro x hx
    let V : ModuleCat A := (moduleSpecΓFunctor (R := A)).obj D.toModules
    let v : G.I → V := NadelNefBigAffineGeneratorSpan.generatorValue D.toModules G
    have hspan : Submodule.span A (Set.range v) = ⊤ :=
      @span_generatorValues_eq_top A D.toModules D.isQuasicoherent_toModules G
    have hin (s : V) (hs : s ∈ Submodule.span A (Set.range v)) :
        (s : D.toSubmodule.obj (op ⊤)).1 ∈ J := by
      induction hs using Submodule.span_induction with
      | mem s hs =>
        obtain ⟨i, rfl⟩ := hs
        exact Ideal.subset_span ⟨i, rfl⟩
      | zero => exact J.zero_mem
      | add s t _hs _ht hjs hjt => exact J.add_mem hjs hjt
      | smul a s _hs hjs =>
        change (Scheme.ΓSpecIso (CommRingCat.of (A : Type u))).inv.hom a *
          (show Γ(Spec (.of A), ⊤) from (s : D.toSubmodule.obj (op ⊤)).1) ∈ J
        exact J.mul_mem_left _ hjs
    let s : V := (D.toModulesSectionsEquiv ⟨⊤, isAffineOpen_top _⟩).symm ⟨x, hx⟩
    exact hin s (hspan ▸ Submodule.mem_top)
end EnvelopeProperty.Vanishing.NadelNefBigAffineIdealGenerators
