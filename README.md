# hadamard-formal

A Lean 4 / Mathlib formalization of the first Hadamard-M/Hadamard-T pour:
the handshake parity obstruction, the Goethals--Seidel and Cooper--Wallis
constructions, two periodic T-matrix witnesses, seven Williamson witnesses,
and eight resulting Hadamard orders.

## What Lean proves

- `handshake_mod_four`: an odd-order symmetric integer matrix with zero
  diagonal, off-diagonal entries in `{+1, -1}`, and zero row sums has order
  congruent to `1` modulo `4`.
- The standard Goethals--Seidel block-array theorem, followed by a single
  generic Cooper--Wallis theorem: a periodic T-matrix quadruple of order `t`
  and a symmetric-circulant Williamson quadruple of order `w` give a Hadamard
  matrix of order `4tw`.
- The generated witnesses are periodic T-matrix quadruples at orders `103`
  and `163`, and Williamson quadruples at orders `7`, `11`, `13`, `17`, `19`,
  `23`, and `29`.
- Hadamard matrices therefore exist at orders `2884`, `4532`, `7004`, `7172`,
  `7828`, `8476`, `9476`, and `11948`.

The order-103 claim is periodic, not aperiodic: this repository does not assert
the existence of a T-sequence of length 103. The final existence theorems are
symbolic applications of the generic theorem; Lean never materializes the
eight large Hadamard matrices.

`Challenge.lean` is the small Mathlib-only statement surface for Palomar and
contains only the deliberate proof holes that Comparator expects.
`Solution.lean` repeats those statements and connects them to the completed
proof development under `HadamardFormal/`. The proof library and solution have
no proof holes.

## Data and proof boundary

The committed, standard-library-only `scripts/export_data.py` reads four JSON
files from a Hadamard-T checkout. Before parsing, it requires their bytes to
match the SHA-256 pins below; it then validates their schemas and emits
`HadamardFormal/Data/Generated.lean` deterministically.

| Source at `Hadamard-T@d9e2e64a57f331e7528f0849e36206ca03c71588` | SHA-256 |
| --- | --- |
| `data/T103.json` | `cf59cb40fcdc74f9309161ad2d50ddd7ad462446da365efb527de0dd4e295a06` |
| `data/T163.json` | `285557b7fc0f846af4fcec2e83d5d97eabcff3b82b2171bd0a6bdf32f8d27a4d` |
| `data/williamson-quadruples.json` | `515dac963269e31694445c5ad7635b001e16b3ea3cdb58fa8ee12eaae47e0446` |
| `data/williamson-13.json` | `249ba0919c5f0b82faab5d6c248a1a2ab18107d5a6ee2175195236fc3509935f` |

The exporter proves neither the mathematical predicates nor the history of
the data. Lean evaluates the imported finite witnesses in the kernel to prove
`IsTMatrixQuadruple` and `IsWilliamson`; it does not use `native_decide`.
Conversely, this repository does not formalize Hadamard-T's Python
certificates, searches, artifact decode, prior-art audit, or priority wording.
Those claims remain in their source repository.

## Sources and provenance

- `Hadamard-M@1319c9d282f6c73ba024d6ec81b3212fdc122db2`,
  `note/NOTE.md` section 2.5, is the source for the handshake proposition.
- `Hadamard-T@d9e2e64a57f331e7528f0849e36206ca03c71588`,
  `note/NOTE.md` section 2, is the source for the periodic T-matrix and
  Williamson definitions, the Goethals--Seidel array, the Cooper--Wallis sign
  table, and the data files pinned above.

The source repository records that `T(103)` was decoded from a public
Hadamard artifact, `T(163)` came from its search, and the Williamson
quadruples came from its banked data. Those are provenance records, not Lean
theorems. This formalization makes no firstness, openness, search-exhaustion,
or database-status claim. See `DISCLOSURE.md` for the human/AI work split and
credit for the classical mathematics.

## Reproduce

Lean 4 and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json` at
`v4.33.0` — the newest Lean release with a matching
[lean4export](https://github.com/leanprover/lean4export) release, which
Palomar's export check requires. With Elan installed:

```powershell
lake exe cache get
lake build
python .\scripts\export_data.py `
  --source-root C:\GitHub_Files\Claude-Repos\Hadamard-T `
  --check
```

For a portable checkout, replace the final source path with the path to a
Hadamard-T checkout at the pinned commit. `lake build` also runs the transitive
axiom audit; it rejects dependencies outside Mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound` allowlist. Warnings caused by
the deliberate holes in `Challenge.lean` are expected; warnings or proof
holes in the proof library or `Solution.lean` are regressions.

The first build of the generated T-matrix certificates is intentionally slow
and uses one Lean worker to bound memory. Subsequent builds reuse the compiled
certificate object.

Licensed under the MIT License; see `LICENSE`.
