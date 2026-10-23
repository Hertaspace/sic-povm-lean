# Provenance

Vendored from https://github.com/CBirkbeck/chebotarev-density, branch `development`, commit
8575c9df1ae0a61120ab5c964c7911414254bec7 (2026-07-25), Apache License 2.0 (see `LICENSE` in this
directory). The authors listed upstream are Chris Birkbeck, Riccardo Brasca and Xavier Roblot. The
upstream toolchain is Lean v4.31.0-rc1 with Mathlib 66748b489336.

This copy has been modified. Eight files were ported to Lean v4.35.0-rc2 with Mathlib
065356127b1d. Each of them starts with a notice saying so, and `PORTING.diff` lists every change
relative to the upstream commit. The changes adapt proofs and names to the Mathlib API of that
version, for example `Ideal.inertiaDeg` to `Ideal.inertiaDeg'` and `Ideal.ramificationIdx` to
`Ideal.ramificationIdx'`, also in the statements of a few internal lemmas, and add one private
helper instance. The statements of the four headline theorems (`chebotarev_density`,
`chebotarev_cyclotomic`, `chebotarev_abelian`, `density_split_completely`) are as upstream.

All other text, including the comments, is as written upstream. Some comments refer to upstream
development notes or to the documents `docs/algnum.pdf` and `docs/cheb.pdf` of the upstream
repository. These are not included here. Comments that speak of planned steps, for example
"intended to be discharged" or "API gap", describe the upstream development; every statement in
this directory is proved. The module names `Chebotarev.*` listed in `CebotarevDensity.lean`
correspond to `CebotarevDensity.*` here.
