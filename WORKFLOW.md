# Development workflow

Write Go → translate to Rocq → prove. Three steps.

## TL;DR

    ./build.sh        # go build -> goose translation -> make (proof check)

Step by step when something breaks:

    ./build.sh go      # Go type check only (run first after editing Go)
    ./build.sh goose   # translate to Rocq (also runs go build)
    ./build.sh make    # compile = type check + proof check, assuming translation is done

## Day-to-day loop

1. Edit Go (.go files in example/, dll/, codec/)
2. `./build.sh go` to check it compiles
3. `./build.sh goose` to translate; this updates src/code/.../*.v (the model)
   and src/generatedproof/.../*.v (struct lemmas)
4. Write/fix proofs in src/proof/*.v
5. `./build.sh make`; exit 0 means type check + proof check passed

Note: after changing Go, always re-run goose. `make` alone keeps the stale
translation and your change will appear to have no effect. Plain `./build.sh`
(= all) is the safe default.

## Checking a single proof file by hand (fast)

`make` recompiles everything, so to try just one proof file:

    set ARGS (sed -E -e '/^#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)
    rocq compile $ARGS src/proof/dll_proof.v -o src/proof/dll_proof.vo

- The output name must match the source name (`-o .../dll_proof.vo`).
  A different name gives "Source and target file names must coincide".
- Insert a temporary `Show.` at the line you want to inspect and run; it
  dumps the goal at that point (the standard debugging trick).

## Directory layout

| path | contents | edit? |
|---|---|---|
| example/ dll/ codec/ | hand-written Go | yes |
| src/proof/*.v | hand-written proofs | yes |
| src/code/.../*.v | goose translation (GooseLang model) | no, generated |
| src/generatedproof/.../*.v | proofgen (struct points-to lemmas) | no, generated |

Generated files (src/code, src/generatedproof) are gitignored. Only Go and
src/proof are committed.

## Gotchas (absorbed by build.sh)

- Go version: the system go is 1.25 but perennial requires go 1.26.
  GOTOOLCHAIN=go1.26.0 is prepended (exported by build.sh).
- goose location: goose/proofgen are not registered as tools in go.mod, so
  make's automatic translation does not run; perennial's bundled goose is
  called directly via --local. This matches the perennial commit pinned in
  the opam file. The v0.10.0 you would get from `go get goose@latest` is the
  archived version and incompatible — do not use it.
- `.goose-output` is touched to tell make the translation already happened;
  otherwise make walks into the broken goose step and dies.
- `src/generatedproof/_` is cleaned up every run (proofgen occasionally
  emits broken files there).

On a machine with perennial elsewhere:

    env PERENNIAL=/path/to/perennial ./build.sh

## Prerequisites (one-time)

- The perennial opam switch is active with Perennial itself installed
  (New / Perennial under user-contrib). This keeps _RocqProject a clean
  `-Q src New` only, and both VsRocq and make resolve everything.
- A local perennial checkout (with bundled goose) at the same commit as the
  pin in perennial-sandbox.opam.
