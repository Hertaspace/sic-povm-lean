# SIC-POVMs exist in every dimension: a Lean 4 formalization

This repository contains a complete, machine-checked proof in Lean 4 that **symmetric informationally complete POVMs (SIC-POVMs) exist in every finite dimension**. This is the existence part of Zauner's conjecture. Stronger forms of the conjecture, which involve Weyl–Heisenberg covariance and an additional order-three symmetry, are not formalized here. The proof formalizes the recent argument of Radchenko and Wheeler [RW26, RW-rec] together with a theorem of Appleby, Flammia and Kopp [AFK25].

## Main theorem

```lean
theorem SICLean.FinalAssembly.zaunerExistence : OpenQuantumProblem23.ZaunerExistence
```

`ZaunerExistence` is our name for the statement of `OpenQuantumProblem23.sicPOVMs` in Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) repository (Open Quantum Problem 23). The definitions below are copied verbatim from that repository. The code block omits their docstrings and the helper `mkStateVector`. `SICLean/Statement.lean` contains them all, and the original file is kept in `vendor/`.

```lean
abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

instance {d : ℕ} : CoeFun (StateVector d) (fun _ => Fin d → ℂ) where
  coe ψ := ψ.ofLp

def IsNormalized {d : ℕ} (ψ : StateVector d) : Prop := ‖ψ‖ = 1

def overlapSq {d : ℕ} (φ ψ : StateVector d) : ℝ :=
  Complex.normSq (∑ i : Fin d, star (φ i) * ψ i)

def HasConstantOverlapSq {d N : ℕ} (c : ℝ) (Φ : Fin N → StateVector d) : Prop :=
  Pairwise fun i j => overlapSq (Φ i) (Φ j) = c

def sicOverlapSq (d : ℕ) : ℝ := (d + 1 : ℝ)⁻¹

def IsSICFamily (d : ℕ) (Φ : Fin (d ^ 2) → StateVector d) : Prop :=
  (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq (sicOverlapSq d) Φ

def HasSICPOVM (d : ℕ) : Prop :=
  ∃ Φ : Fin (d ^ 2) → StateVector d, IsSICFamily d Φ
```

The statement itself, word for word that of `sicPOVMs`, is defined here as

```lean
def ZaunerExistence : Prop :=
  ∀ d : ℕ, 1 ≤ d → HasSICPOVM d
```

The repository also proves the analogous statement for rank-r SICs [AFK25], `SICLean.FinalAssembly.hasRSIC`, for all `r ≥ 1`, `d > 2r + 1` with `r(d − r) ∣ d² − 1`. For `r > 1` it follows the extension of the twisted convolution identity to all ranks [AFK26].

## Checking the proof

Install [elan](https://github.com/leanprover/elan), then:

```bash
git clone https://github.com/Hertaspace/sic-povm-lean
cd sic-povm-lean
lake exe cache get        # download the Mathlib build cache
lake build                # builds the class field theory dependency and this project
lake env lean CheckAxioms.lean
```

The last command prints the definition of `ZaunerExistence` and the axioms used by the two main theorems and by the twelve theorems of `SICLean/Solution.lean`. Each list consists of the three standard axioms `propext`, `Classical.choice` and `Quot.sound`. The class field theory dependency is large (the project uses about 950 of its modules) and is built from source, which can take an hour or more.

`SICLean/Solution.lean` restates the twelve open statements of Open Quantum Problem 23 in formal-conjectures (the full conjecture `sicPOVMs` and eleven single dimensions) with the same names and statements, and proves them. `Challenge.lean` contains the same statements with `sorry`, copied from formal-conjectures. It is the only compiled file with `sorry`, it is not a default build target, and it exists only for the checker that ships with Lean:

```bash
lake comparator --paranoid     # judges SICLean.Solution against Challenge, see comparator.json
lake check --paranoid          # exports the default target and replays it through all bundled checkers
```

`lake comparator` checks that the twelve theorems of `SICLean.Solution` have exactly the statements in `Challenge.lean` and use only the permitted axioms, and it replays their proofs. `lake check` exports the whole environment of the default build target, including all of Mathlib, and replays it, so it needs much more time and memory. With `--paranoid` both use Lean's kernel and the bundled independent checkers (`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`). Both commands ship with Lean `v4.35.0-rc2` and need `bubblewrap` (Linux).

## Verification performed

- **This release.** The checks below were run on the release commit with Lean `v4.35.0-rc2` on Linux: a full build, `CheckAxioms.lean`, `lake comparator --paranoid` and `lake check --paranoid`. The commands, the environment and the outputs are recorded in `VERIFICATION.md`.
- **Independent kernel.** The full dependency closure of the two main theorems (145,591 declarations, including every Mathlib declaration they use) was exported with [lean4export](https://github.com/leanprover/lean4export) (tag `v4.35.0-rc2`) and accepted by [nanoda](https://github.com/ammkrn/nanoda_lib) 0.4.17, an independent type checker written in Rust. Only the three standard axioms occur in the export.
- **Replay.** [lean4checker](https://github.com/leanprover/lean4checker) replayed through the Lean kernel, without errors, every declaration of the project, of the vendored Chebotarev library, and of the 948 modules of the class field theory library that the project uses. It was built from commit `91a7f0e` with its toolchain set to Lean `v4.35.0-rc2`, a one-line adaptation to the kernel API of that version, and progress output.

The last two checks were run on a development version before the release. Its declarations are those of this release except the twelve theorems of `SICLean/Solution.lean`, which were added afterwards and which restate the main theorem (`VERIFICATION.md` records the comparison). The two versions differ otherwise only in comments and in the import list of `SICLean.lean`.

## Trust base

A reader needs to trust the statement above, Mathlib's definitions of the notions it uses (complex Euclidean space, its norm and coordinates, `Complex.normSq`), the Lean kernel (or one of the independent checkers) and the three standard axioms. The intermediate definitions of this project and of its dependencies (for example ray class fields) cannot affect the meaning of the result, whatever they say, because every step is checked by the kernel. `Challenge.lean` is compiled here with `import Mathlib` instead of the utilities of formal-conjectures. That its text matches the formal-conjectures file is checked by reading, not by machine.

## Mathematical sources

- [RW26] D. Radchenko, C. Wheeler, *Real quadratic fields and finite quantum dilogarithms I*, [arXiv:2609.21892v2](https://arxiv.org/abs/2609.21892v2).
- [RW-rec] D. Radchenko, C. Wheeler, *Stark units for real quadratic fields and reciprocity laws*, 4 October 2026, <https://www.danrad.net/papers/stark-reciprocity.pdf> (accessed October 2026).
- [AFK25] M. Appleby, S. T. Flammia, G. S. Kopp, *A constructive approach to Zauner's conjecture via the Stark conjectures*, [arXiv:2501.03970](https://arxiv.org/abs/2501.03970).
- [AFK26] M. Appleby, S. T. Flammia, G. S. Kopp, *The twisted convolution identity and ghost r-SICs from finite quantum dilogarithms*, [arXiv:2609.39192](https://arxiv.org/abs/2609.39192).

The mathematics is due to these authors. This repository is a formalization of their proof. Bracketed references in comments point to the part of a source that a declaration formalizes or supports. Auxiliary lemmas cite the surrounding argument.

## Repository layout

| Path | Content |
|---|---|
| `SICLean.lean` | root module, with an overview of the layers |
| `SICLean/Statement.lean` | the target statement, verbatim from formal-conjectures |
| `SICLean/*.lean` | from ghost SICs with a unimodular Galois flip to SICs [AFK25], including rank r |
| `SICLean/Galois` | the algebraic closure, embeddings and the statement of [RW-rec, Prop. 7] used by the reduction |
| `SICLean/L2*` | reduction to the finite identities of [RW26] (Theorems 2 and 7, Proposition 8), for rank r > 1 following [AFK26] |
| `SICLean/L3` | algebraicity of the special values [RW26, §5] |
| `SICLean/L4` | analytic properties of the modular quantum dilogarithm [RW26, §§2–3]. Files `G1*` prove the integral identities (22) and (23) of [RW26, Thm. 3]. Files `G2*` derive from them Fourier (6) and the five-term identity (7) of [RW26] by contour shifts and residues. Files `M74*`, `M75*` and `M78*` show that the actual special values satisfy the finite system of `SICLean/L3`. Statements in the `G1*` files carry file-local labels such as `R05` |
| `SICLean/L5` | [RW-rec, Prop. 7] via ray class fields, Artin reciprocity and the Chebotarev density theorem |
| `SICLean/Final`, `SICLean/L5/ActualProp7.lean` | final assembly: `zaunerExistence` and `hasRSIC` |
| `SICLean/Solution.lean` | the formal-conjectures statements, proved |
| `Challenge.lean`, `comparator.json` | the formal-conjectures statements with `sorry`, for `lake comparator` |
| `CheckAxioms.lean` | prints the definition of the statement and the axioms used by the main theorems |
| `CebotarevDensity/`, `CebotarevDensity.lean` | Chebotarev density theorem, vendored and ported (see `CebotarevDensity/PROVENANCE.md` and `LICENSE`) |
| `vendor/` | the original formal-conjectures file for Open Quantum Problem 23 (not compiled) |

Theorems in intermediate files may carry explicit hypotheses, for example the inputs in `SICLean/Inputs.lean`. The final assembly proves all of them, so the two main theorems have none. Many files end with `#check` and `#print axioms` commands that record the API and axioms used. They add no declarations, and `lake build` prints their output.

## Dependencies

All versions are pinned in `lake-manifest.json`:

- [Mathlib](https://github.com/leanprover-community/mathlib4)
- the class field theory library [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory) (Apache-2.0), commit `fbd320c`
- the Chebotarev density theorem from [CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0), commit `8575c9d`, vendored in `CebotarevDensity/`

Lean `v4.35.0-rc2` and Mathlib `0653561` are the versions pinned by the class field theory library.

## How this formalization was produced

The Lean code was written by large language model agents under human direction. One agent fixed each intermediate statement before any proof was attempted and checked it numerically. Other agents wrote the proofs, and every merge was checked declaration by declaration against the fixed statements. Further agents audited the final result and reviewed the released code. According to their documentation, the class field theory dependency and the Chebotarev library were also developed with AI systems. None of this affects the trust base described above.

## License

Apache License 2.0 (see `LICENSE`). Third-party material keeps its own notices: `CebotarevDensity/` and `CebotarevDensity.lean` (Apache-2.0, see `CebotarevDensity/LICENSE` and `PROVENANCE.md`), and the material from google-deepmind/formal-conjectures (Apache-2.0) in `vendor/formal-conjectures-OQP23.lean`, `SICLean/Statement.lean`, `Challenge.lean` and `SICLean/LowDim.lean`.

## Citation

A short note describing this formalization is in preparation.
