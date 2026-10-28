# Additional strong-resolution producer

This report records the historical isolated validation before vendoring. The
consuming EP checkpoint subsequently registers these exact sources, imports the
terminal theorem, and records its ordinary parent build and audit under
`audit/continuation-20261015/resolution-cartier-*`.

The genuine upstream theorem `AlgebraicGeometry.exists_strong_resolution` has been checked under the existing Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 pin. Its input is only a characteristic-zero field and an actual integral separated finite-type scheme (`AlgScheme`); its output is an actual finite sequence of blowups with smooth final scheme, projective birational map, smooth-locus isomorphism and SNC exceptional support. This is a proved resolution producer, not a hypothesis class.

The exact target cone has 624 upstream modules: 519 are reused from the already validated principalization cone and 105 additional source modules were compiled here with two workers. One proved tensor induction compatibility helper is inherited from that cone. The union of both cones has 626 upstream modules plus that one helper. All additional module source and olean outputs are isolated; individual read-only symlinks reference original validated dependency artifacts. The project and vendored dependency sources/artifacts were not edited by these checks.

The 105 additional modules pass actual direct Lean kernel compilation. `audit/StrongResolution.lean` imports the actual terminal module and prints the full types and transitive axioms of strong and functorial resolution; both have exactly propext, Classical.choice and Quot.sound. Exact source hashes and original commit provenance are in ADDITIONAL-UPSTREAM.json, the compatibility diff is compatibility.patch, and compiler arguments/environment are in BUILD-CONFIG.json and status.json. The patch uses the previously checked core API renames and proved tensor-induction helper, plus the old Sigma.ι_desc_assoc name. No definition or theorem hypothesis was weakened. No proof placeholder or project axiom occurs in the added source cone.

This result can support characteristic-zero alterations once the genuine smooth projective resolution is transported to the multiprojective model. That transport, positive-characteristic alterations, local positivity, the Jacobian/multiplier-ideal envelope argument, and the full paper goal remain separate. The extended source cone is not yet vendored or root-imported at this isolated validation checkpoint.
