# Verification record

This file records the checks run on commit `7a557d09bf66468e1ed550841b9e6e37e7b57153`. The release tag adds this file, the scripts in `verification/` and the figure in `docs/`, edits `README.md` and `CebotarevDensity/PROVENANCE.md`, and adds `.DS_Store` to `.gitignore`. It also corrects comments in `SICLean.lean`, `SICLean/Inputs.lean` and `SICLean/Final/Unconditional.lean`, which said that `hasRSIC` has no hypotheses. Apart from these comments, the Lean files of `SICLean` and `CebotarevDensity`, `Challenge.lean` and `CheckAxioms.lean` are those of the checked commit. Section 6 records a rebuild of the Lean files of the release.

## Environment

- Linux 5.15.0 x86_64, Ubuntu 20.04.6 LTS, in an LXD container. All builds ran on tmpfs.
- Lean 4.35.0-rc2 (commit `11acb17ec6b07a8f9e9173e6845197929540936b`) and Lake 5.0.0-src+11acb17, as pinned in `lean-toolchain`.
- Dependencies as pinned in `lake-manifest.json`. All of them, including Mathlib, were compiled from source on this machine with `LAKE_NO_CACHE=1`, without the Mathlib build cache. The check of this commit reused these compiled dependencies and compiled from scratch the modules of this repository that the default target needs, the 459 modules of `SICLean` and `CebotarevDensity`.
- bubblewrap 0.11.0, built from source, for the sandbox of `lake comparator` and `lake check`. In this container procfs cannot be mounted inside a new PID namespace. `bwrap` was therefore called through a wrapper that replaces `--unshare-all` by `--unshare-user --unshare-ipc --unshare-net --unshare-uts --unshare-cgroup-try` and passes every other argument unchanged. The sandbox therefore shares the PID namespace of the container. This affects the isolation of the checkers, not what they check.

## Results

### 1. Build

`lake build`: `Build completed successfully (10339 jobs).`

### 2. Axioms

`lake env lean CheckAxioms.lean`:

```
def OpenQuantumProblem23.ZaunerExistence : Prop :=
∀ (d : ℕ), 1 ≤ d → OpenQuantumProblem23.HasSICPOVM d
'SICLean.FinalAssembly.zaunerExistence' depends on axioms: [propext, Classical.choice, Quot.sound]
'SICLean.FinalAssembly.hasRSIC' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.sicPOVMs' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_56' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_58' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_59' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_60' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_64' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_68' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_69' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_70' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_71' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_72' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem23.hasSICPOVM_75' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 3. Scans of the compiled environment

Two short Lean scripts, `verification/direct_sorry_modules.lean` and `verification/axiom_scan.lean`, run on the built environment, reported:

- no constant of a `SICLean` module mentions `sorryAx` in its type or value;
- the 14,298 constants of the 459 modules of `SICLean` and `CebotarevDensity` depend, directly or through their dependencies, on no axiom other than `propext`, `Classical.choice` and `Quot.sound`.

### 4. `lake comparator --paranoid`

```
Running Lean paranoid kernel on solution
Lean paranoid kernel accepts the solution
Running lean4lean kernel on solution
checked 141441 declarations
lean4lean kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running con-leche kernel on solution
con-leche: accepted 141440 declarations (--verified)
con-leche kernel accepts the solution
Running con-ron kernel on solution
con-ron: accepted 141440 declarations (--verified)
con-ron kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

Wall-clock time 1 h 23 min, CPU time 2 h 53 min (user and system), peak memory 8.6 GB. The lean4lean run also printed the declarations that took more than one second to check, which are omitted here.

The challenge module `Challenge.lean` is a copy of the file of Open Quantum Problem 23 in formal-conjectures, which is kept in `vendor/`. `verification/check_challenge.py` checks the copy and `comparator.json`. The file in `vendor/` must have the Git blob hash `6e3d4f42e066f7d4de45b44f2cebdc0bf2fc9c85` of `FormalConjectures/OpenQuantumProblems/23.lean` at formal-conjectures commit `90d18f666eb98adec4eee4d12f1d37e30b4eb204`. Every declaration of `Challenge.lean`, with its docstring, must be a whole declaration in the namespace of that file, verbatim and in the same order, after the attribute lines of the file are removed. These lines are the classification tags of formal-conjectures and the line `@[expose] public section`. A whole declaration is delimited by blank lines, so a truncated copy, or one without its docstring, fails. The theorems of `Challenge.lean` must be exactly those that the file tags as open. `comparator.json` must have exactly four entries, none of them twice: it compares `SICLean.Solution` with `Challenge`, names each of these theorems once and no other, and permits only the axioms `propext`, `Quot.sound` and `Classical.choice`. A further entry such as `definition_names`, which lets the solution change the bodies of the listed definitions, fails the check. Run from the root of the repository on 25 October 2026 on macOS, with Python 3.15.0 and with Python 3.8.20:

```bash
python3 verification/check_challenge.py
```

```
21 declarations of Challenge.lean are whole declarations of vendor/formal-conjectures-OQP23.lean (formal-conjectures commit 90d18f6), verbatim and in order, among them its 12 open theorems, each named once in comparator.json.
```

(exit status 0 in both runs).

### 5. `lake check --paranoid`

This command exports the environment of the default target and runs six kernels over the export in turn: Lean's paranoid kernel, lean4lean, nanoda, con-leche, con-ron and Lean's default kernel. The export has 741,811 declarations, Mathlib included. As Lean's exporter writes it, the export contains every declaration of the environment whose name is not internal, together with all declarations these depend on, and it leaves out unsafe declarations, which no theorem can use. A name is internal if one of its components begins with `_`. The names of private declarations, for example, begin with `_private`. A declaration with an internal name is therefore exported only when an exported declaration depends on it.

```
checked 741811 declarations
lean4lean kernel accepts the solution
Running nanoda kernel on solution

thread 'thread_2' (1974457) has overflowed its stack
fatal runtime error: stack overflow, aborting
nanoda kernel rejected the solution
Running con-leche kernel on solution
con-leche: accepted 741809 declarations (--verified)
con-leche kernel accepts the solution
Running con-ron kernel on solution
con-ron: accepted 741809 declarations (--verified)
con-ron kernel accepts the solution
Running Lean default kernel on solution
error: nanoda exited with 134
Lean default kernel accepts the solution
```

Wall-clock time 5 h 10 min, CPU time 10 h 13 min (user and system), peak memory 56 GB, exit status 1. Only the last 60 lines of the output were kept, and they begin after the Lean paranoid kernel. Lake runs the kernels in the order above and reports the first one that fails. It reported nanoda, so the Lean paranoid kernel and lean4lean accepted. Because a kernel failed, the command stopped before its final check of the axioms used.

nanoda did not reject a declaration. One of its worker threads, whose stack is fixed at 16 MiB in the source, overflowed. The following runs complete the record.

- **Export and axiom check.** The export was made again as `lake check` makes it, written to a file, and checked from that file:

  ```bash
  LAKE_CHECK_EXPORT=1 LEAN_ABORT_ON_PANIC=1 lake check > check-export.ndjson
  lake check --from-export check-export.ndjson
  ```

  The export has 6.97 GB and SHA-256 `d5805a4ad302afd4a00477c4a062927156bb31244b9d65c122da42956afd34d0`. The second command ran Lean's default kernel and the axiom check, and exited with status 0:

  ```
  Running Lean default kernel on solution
  Lean default kernel accepts the solution
  Uses axioms: propext, Quot.sound, Classical.choice
  ```

- **nanoda on the whole environment.** nanoda 0.4.17 could not process this export. Run serially on the main thread with a 32 GiB stack limit, it stopped after 49 minutes with an internal capacity error (`index 2147483648 exceeds 31-bit capacity`). Built from the same version (source commit `4c544ed`) with the worker-thread stack raised from 16 MiB to 1 GiB and no other change, it again overflowed a stack after 26 minutes.

- **nanoda on the whole project.** `verification/list_consts.lean` lists 14,295 of the 14,298 constants of the modules of `SICLean` and `CebotarevDensity`, private ones included. The other three are `_unsafe_rec` definitions that Lean generates for its compiler. They are unsafe, so no theorem can use them. `leanexport` would leave them out anyway, as it exports unsafe declarations only when given the option `--export-unsafe`, which no command here uses. The bundled `leanexport` exported the listed constants with all their dependencies (1.7 GB). The bundled, unmodified `nanoda_bin` accepted it, with the configuration that `lake check` writes, pointed at this export and with `print_success_message` added so that nanoda reports how many declarations it checked (`verification/nanoda-project.json`). From the root of the repository, after `lake build`:

  ```bash
  lake env lean verification/list_consts.lean      # writes project-consts.txt
  lake env leanexport SICLean -- $(cat project-consts.txt) > project-export.ndjson
  lake env nanoda_bin verification/nanoda-project.json
  ```

  These commands were run again on 24 October 2026 with the same result:

  ```
  Checked 151455 declarations with no typechecker errors, 1 pretty printer errors: [
      "Unable to print axioms",
  ]
  ```

  (exit status 0). The pretty printer error concerns nanoda's display output, not type checking.

In summary, five kernels accepted the export of the default target, and nanoda accepted the export of all declarations of this project with their dependencies as well as, in step 4, that of the twelve theorems.

### 6. Rebuild of the release

The Lean files of the release, which differ from the checked commit only in the comments named at the top of this file, were built again on 25 October 2026 with Lean 4.35.0-rc2 on a MacBook Pro with an Apple M5 Max (macOS), from a fresh clone and as in steps 3 to 5 of the README. Mathlib and the libraries it builds on came from its download cache. Lake compiled the 444 modules of `SICLean`, the 15 modules of `CebotarevDensity` and 948 modules of the class field theory library, and ended with `Build completed successfully (10339 jobs).` Then `lake env lean CheckAxioms.lean` printed exactly the output of section 2.
