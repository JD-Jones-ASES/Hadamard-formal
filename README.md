# hadamard-formal

A Lean 4 / Mathlib formalization of the first Hadamard-M/Hadamard-T pour:
Hadamard existence at eight orders that the maintained construction database
lists as not recorded known, and the obstruction behind an erratum to
Miyamoto's 1991 construction paper — with the paper's displayed C₂-matrix
ingredient proved nonexistent at every applicable block order, closing both
printed readings of the affected corollary. All public theorems are
kernel-checked on Lean's three standard axioms.

## What Lean proves

- The standard Goethals--Seidel block-array theorem, followed by a single
  generic Cooper--Wallis theorem: a periodic T-matrix quadruple of order `t`
  and a symmetric-circulant Williamson quadruple of order `w` give a Hadamard
  matrix of order `4tw`.
- The generated witnesses are periodic T-matrix quadruples at orders `103`
  and `163`, and Williamson quadruples at orders `7`, `11`, `13`, `17`, `19`,
  `23`, and `29` — each checked against its defining predicate by kernel
  reduction.
- Hadamard matrices therefore exist at orders `2884`, `4532`, `7004`, `7172`,
  `7828`, `8476`, `9476`, and `11948`.
- `handshake_mod_four`: an odd-order symmetric integer matrix with zero
  diagonal, off-diagonal entries in `{+1, -1}`, and zero row sums has order
  congruent to `1` modulo `4`.
- `no_handshake_matrix`: for every positive order `m` with `m % 4 ≠ 1` that
  class is empty.
- `no_c2_matrix`: the displayed C₂-matrix form consumed by Corollary 4 of
  Miyamoto 1991 has no instance at any positive block order `m` with
  `m % 4 ≠ 1` — the erratum's application (see below).

## The eight orders in the literature

Table 4 of Cati and Pasechnik's maintained construction database
(arXiv:2411.18897v2, 2025-08-30), which updates Seberry and Yamada's Table
A.17 in the standard reference, records, for odd `n ≤ 2999`, the least `m`
for which a Hadamard matrix of order `2^m · n` is known; an entry `n(m)` with
`m ≥ 3` means no Hadamard matrix of order `4n` was recorded. All eight
formalized orders land on such entries:

| Order | Factorization | Table 4 entry |
| --- | --- | --- |
| 2884 | 4 · 103 · 7 | 721(3) |
| 4532 | 4 · 103 · 11 | 1133(3) |
| 7004 | 4 · 103 · 17 | 1751(3) |
| 7172 | 4 · 163 · 11 | 1793(4) |
| 7828 | 4 · 103 · 19 | 1957(3) |
| 8476 | 4 · 163 · 13 | 2119(4) |
| 9476 | 4 · 103 · 23 | 2369(3) |
| 11948 | 4 · 103 · 29 | 2987(3) |

Two of the eight orders — `7172` and `8476` — rest on `T(163)`, a search
result of Hadamard-T; the other six rest on `T(103)`, which Hadamard-T
decoded from the Hadamard matrix of order 2060 posted publicly on 2026-08-23
and credited to Schneider. Hadamard-T carries the machine-diffed
transcription of the table (195/195 entries against the v2 e-print,
re-checked at release), and its firsthand audit of the construction
literature (closed 2026-08-29) located no published route to a T-object at
either order. With a T-object of order 103 in hand, the six orders it yields
follow from the classical Cooper--Wallis composite, which Cati and Pasechnik
implement; the contribution at those six is the object's application and its
kernel-checked verification, not the composite. The two entries at `m = 4`
say that Sylvester doubling of `H(7172)` and `H(8476)` also settles orders
`14344` and `16952`; those corollaries are recorded in Hadamard-T and are
not part of this formalization's theorem surface. The natural readers are
researchers in Hadamard matrices and combinatorial designs, the maintainers
of the status tables among them.

## The erratum obstruction

Miyamoto, *A construction of Hadamard matrices*, J. Combin. Theory Ser. A 57
(1991) 86--108, lists order `103` among the Hadamard matrices of M-partition
it obtains and order `515` among the orders reached from them — through the
classical Baumert--Hall multiplication, a claim of a Hadamard matrix of
order `4 · 515 = 2060`. The companion repository Hadamard-M derives (its
Proposition 2, block algebra over the paper's displayed form) that any
instance of the paper's Corollary 4 — the only engine in the paper reaching
odd part `≡ 3 (mod 4)` — forces a symmetric sign matrix with zero diagonal
and zero row sums at the corollary's block order `m`. The theorems
formalized here state the displayed C₂ form itself and close it: the class
it forces is empty at every positive `m ≢ 1 (mod 4)`, so Corollary 4 has no
instance at `m = 51, 63, 75` — the paper's printed entries at orders `103`,
`127`, `151` — and none at `m = 50`, which also closes the printed
`4(2m + 3)` reading of its output order. The
order-515 entry, and with it the paper's claim at order 2060, is unsupported
by the paper's own machinery.

Order 2060 itself is not open: a Hadamard matrix of that order was posted
publicly on 2026-08-23, credited to Schneider, by other means — the erratum
concerns the paper's route, not the order's status. Cati and Pasechnik
record that, for want of details, they were "unable to verify these
constructions" claimed in the paper's section 7, naming order `4 · 515` as
their example; the obstruction supplies an independent mathematical reason
the printed route cannot deliver that entry. At `m = 41` (the paper's entry
at order `83`) the class is inhabited (Hadamard-M note, section 2.5,
Remark), so the test admits the paper's own engine there: the obstruction
cuts exactly the printed entries at `103`, `127` and `151` and leaves `83`
alone. Neither the inhabitedness nor that sharpness statement is formalized
here. The premises about the printed 1991 text — the transcriptions of the
displayed form, hypothesis (4.1), and the section-7 lists, and the reading
that Corollary 4 is the paper's only engine at odd part `≡ 3 (mod 4)` — are
human-audited in Hadamard-M, sections 2.1--2.4, which quotes the
load-bearing printed sentence verbatim; the mathematics downstream of those
premises is what Lean checks.

`Challenge.lean` is the small Mathlib-only statement surface for Palomar and
contains only the deliberate proof holes that Comparator expects.
`Solution.lean` repeats those statements and connects them to the completed
proof development under `HadamardFormal/`. The proof library and solution
have no proof holes.

## Relation to previous formalisations

Mathlib at the pinned revision provides the `Matrix.IsHadamard` predicate
(`Mathlib/LinearAlgebra/Matrix/HadamardMatrix.lean`, added 2026-06-16,
mathlib4 PR #38582) with closure lemmas — including the Kronecker product —
and the `4 ∣ n` obstruction, but no Hadamard matrix of any order and no
existence theorem; it has no content on Williamson quadruples, T-matrices,
orthogonal designs, or the Goethals--Seidel and Cooper--Wallis
constructions. The DeepMind `formal-conjectures` repository states the
Hadamard conjecture and its known-for-`4k`, `k ≤ 166` variant in Lean with
every proof left as `sorry`. The one prior proof-assistant effort on
Hadamard constructions our search located is Lu-Ming Zhang's 2021 Oxford MSc
dissertation, cited by Cati and Pasechnik as work towards verifying
constructions covering orders up to 112; we could not locate its text,
artifact, or proof assistant, and its stated range is disjoint from the
orders here. Because that range plausibly includes Williamson- and
Goethals--Seidel-type constructions at small orders, the negatives below are
negatives about what our searches located, not claims that no such
formalisation exists.

The maintainers of the database frame this as open work: "Implementing
constructions is a first step towards a formal verification of them, using a
proof assistant … Currently, proof assistants are severely deficient in
doing even slightly nontrivial calculations, and closing this lacuna is an
active research area" (arXiv:2411.18897v2, section 1). This development
supplies kernel-checked instances of constructions their database
implements, at orders their Table 4 records as not known. The
Cooper--Wallis and Goethals--Seidel constructions exist as executable
SageMath code (Cati--Pasechnik), and Williamson-type objects at small orders
have been enumerated with SAT+CAS pipelines (Bright--Kotsireas--Ganesh and
collaborators); neither line proves a composition theorem inside a proof
assistant or checks witnesses through a trusted kernel. Across searches run
for this repository on 2026-08-30 — the pinned Mathlib tree and its PR
history, the Archive of Formal Proofs entry and file listings, GitHub
repository and code search, and arXiv API queries — our searches located no
prior formalisation of the Goethals--Seidel or Cooper--Wallis theorems, no
prior kernel-checked T-matrix or Williamson witness, and no prior
machine-checked Hadamard existence result at any of the eight orders, with
that one inaccessible dissertation the exception we cannot rule on. The AFP
check was at entry- and file-name level rather than full text, and the
Mizar negative rests on web search alone.

## Data and proof boundary

The committed, standard-library-only `scripts/export_data.py` reads four JSON
files from a Hadamard-T checkout. Before parsing, it requires their bytes to
match the SHA-256 pins below; it then validates their schemas and emits
`HadamardFormal/Data/Generated.lean` deterministically.

| Source at `Hadamard-T@eec1bed6216c44675d946fe80d47695a7ae2ab40` | SHA-256 |
| --- | --- |
| `data/T103.json` | `cf59cb40fcdc74f9309161ad2d50ddd7ad462446da365efb527de0dd4e295a06` |
| `data/T163.json` | `285557b7fc0f846af4fcec2e83d5d97eabcff3b82b2171bd0a6bdf32f8d27a4d` |
| `data/williamson-quadruples.json` | `515dac963269e31694445c5ad7635b001e16b3ea3cdb58fa8ee12eaae47e0446` |
| `data/williamson-13.json` | `249ba0919c5f0b82faab5d6c248a1a2ab18107d5a6ee2175195236fc3509935f` |

The exporter enforces byte identity against the pins and validates schemas
before emitting; it proves neither the mathematical predicates nor the
provenance of the data. Lean then evaluates the imported finite witnesses in
the kernel to prove `IsTMatrixQuadruple` and `IsWilliamson`; it does not use
`native_decide`. The order-103 claim is periodic, not aperiodic: this
repository does not assert the existence of a T-sequence of length 103. The
final existence theorems are symbolic applications of the generic theorem;
Lean never materializes the eight large Hadamard matrices. Hadamard-T's
Python certificates, searches, and artifact decode are that repository's own
replayable record and are not re-proved here.

## Sources and provenance

- `Hadamard-M@0208cf661fcd6b1e7d69eb52078d873eefc4d7cf`,
  `note/NOTE.md` sections 2.1 and 2.4--2.6 (the displayed form and
  Propositions 2--4), is the source for the handshake obstruction and the
  erratum it drives.
- `Hadamard-T@eec1bed6216c44675d946fe80d47695a7ae2ab40`,
  `note/NOTE.md` sections 1, 2, 4, 5 and 6.1, is the source for the periodic
  T-matrix and Williamson definitions, the Goethals--Seidel array, the
  Cooper--Wallis sign table, the data files pinned above, and the dated
  Table-4 status of the eight orders.

The source repositories record where each witness came from: `T(103)` was
decoded from a publicly posted Hadamard matrix of order 2060, `T(163)` came
from Hadamard-T's search, and the Williamson quadruples from its banked
data, with priority postures stated there. Kernel replay, Comparator
statement matching, and the axiom audit establish proof replay and statement
fidelity, not literature status; the status facts above are documentary,
dated, and rest on the cited public sources. See `DISCLOSURE.md` for the
human/AI work split and credit for the classical mathematics.

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
Hadamard-T checkout at the pinned commit. `lake build` also runs the
transitive axiom audit; it rejects dependencies outside Mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound` allowlist. Warnings caused by
the deliberate holes in `Challenge.lean` are expected; warnings or proof
holes in the proof library or `Solution.lean` are regressions.

The first build of the generated T-matrix certificates is intentionally slow
and uses one Lean worker to bound memory. Subsequent builds reuse the
compiled certificate object.

Licensed under the MIT License; see `LICENSE`.
