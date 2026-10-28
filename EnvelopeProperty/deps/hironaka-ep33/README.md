# hironakaEp33: Hironaka resolution (vendored)

An import cone of [resolutionorg/hironaka](https://github.com/resolutionorg/hironaka) at commit
`a0d237580a68818b5142b6d404a2670b3fcee697`, backported from Lean v4.34.0 to Lean v4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Copyright (c) 2026 Resolution; Apache-2.0 (see
[`LICENSE`](LICENSE)). The original source headers are retained.

Contents (627 modules: 626 upstream modules and one compatibility helper):

* the algebraic principalization cone (521 upstream modules), with roots
  `Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.{Monomial,Centers,IsoLocus}`; the
  convenience root `Hironaka` imports only these three;
* the strong resolution extension (105 further upstream modules, root
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36`): `exists_strong_resolution` for integral
  algebraic schemes in characteristic zero, and the projectivity of blowups and of finite blowup
  sequences.

No analytic, example, `Challenge` or full-upstream umbrella module is vendored. No definition or
theorem statement was weakened and no hypothesis was added.

Provenance:

* [`UPSTREAM-CONE.json`](UPSTREAM-CONE.json): upstream commit, toolchains and the list of source
  files of the principalization cone;
* [`strong-resolution-extension/ADDITIONAL-UPSTREAM.json`](strong-resolution-extension/ADDITIONAL-UPSTREAM.json):
  the same for the extension;
* [`compatibility.patch`](compatibility.patch) and
  [`strong-resolution-extension/compatibility.patch`](strong-resolution-extension/compatibility.patch):
  every source change against upstream.

This package is a Lake path dependency of `EnvelopeProperty` (`deps/hironaka-ep33`); build it from
`EnvelopeProperty/` as described in the top-level README. Do not run `lake update`.
