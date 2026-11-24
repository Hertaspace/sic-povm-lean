# Provenance

Vendored from https://github.com/CBirkbeck/chebotarev-density, branch `development`, commit
8575c9df1ae0a61120ab5c964c7911414254bec7 (2026-07-25), Apache License 2.0 (see `LICENSE` in this
directory). The upstream blueprint names Chris Birkbeck as its author, and the branch history up
to this commit also has commits by Riccardo Brasca. The upstream toolchain is Lean v4.31.0-rc1
with Mathlib 66748b489336.

This copy has been modified. Eight files were ported to Lean v4.35.0-rc2 with Mathlib
065356127b1d. Each of them starts with a notice saying so, and `PORTING.diff` lists every change
relative to the upstream commit. The changes adapt proofs and names to the Mathlib API of that
version, for example `Ideal.inertiaDeg` to `Ideal.inertiaDeg'` and `Ideal.ramificationIdx` to
`Ideal.ramificationIdx'`, also in the statements of a few internal lemmas, and add one private
helper instance. `Main.lean`, which contains the four headline theorems named in the upstream
`certification/` directory (`chebotarev_density`, `chebotarev_density_of_comm`,
`density_split_completely`, `dirichlet_primes_in_AP`), is unchanged, and the statements of
`chebotarev_cyclotomic` and `chebotarev_abelian` are as upstream.

All other text, including the comments, is as written upstream. Some comments refer to upstream
development notes or to the documents `docs/algnum.pdf` and `docs/cheb.pdf` of the upstream
repository. These are not included here. Comments that speak of planned steps, for example
"intended to be discharged" or "API gap", describe the upstream development; every statement in
this directory is proved. The module names `Chebotarev.*` listed in `CebotarevDensity.lean`
correspond to `CebotarevDensity.*` here.

## Release v1.1

For release v1.1 the repository moved to Lean v4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842, and every Lean file of the repository became a Lean `module`. The upstream files of this directory already began with `module` and `public import`, so the module syntax needed no change here. Seven files received further small proof adaptations to the newer Mathlib API:

- `Density.lean`, `Frobenius.lean`, `Main.lean` and `ForMathlib/NormLeOneLipschitz.lean`: a renamed lemma (for example `Ideal.IsIntegral.comap_ne_bot` to `Ideal.IsIntegral.under_ne_bot`), explicit arguments that the new elaboration needs (`contDiff_apply ℝ (fun _ => ℝ)`, an explicit set in `Set.Finite.subset`), a separability argument in `Frobenius.lean` that now goes through perfect fields, and one `simp only` step removed from `Main.lean`.
- `NumberFieldEulerProduct.lean`: the renamed lemma `Ring.HasFiniteQuotients.finite_absNorm_eq` in place of `Ideal.finite_setOf_absNorm_eq`, with the explicit set arguments it needs, and one added import.
- `ZetaProduct.lean`: explicit set arguments in a finiteness proof, and one added local fact, `Ring.HasFiniteQuotients R`, derived from `Module.Finite ℤ R`.
- `Cyclotomic.lean`: one added import, `Mathlib.Analysis.Calculus.SmoothSeries`.

No statement changed. `Main.lean`, which was unchanged relative to upstream in v1.0, now differs from upstream by the one removed `simp only` step. `PORTING.diff` is the v1.0 diff against the upstream commit and does not include the v1.1 changes. Those are the differences between the v1.0 tag and the v1.1 tag in these seven files, which `git diff 0f4ec7e -- CebotarevDensity` shows. The notices at the head of the files ported in v1.0 still name Lean v4.35.0-rc2 and Mathlib 065356127b1d, the targets of the v1.0 port.
