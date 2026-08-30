# Disclosure

AI-generated formalization with a human managing the workflow. The Lean
development, deterministic data exporter, Palomar packaging, and local
verification machinery were produced in Codex (OpenAI). The mathematical
source repositories were produced in Claude Code (Fable 5, Anthropic) and
supplied to Codex after external review and source-side revision.

## Work split

The Codex station translated the ruled tranche into Lean: definitions, the
handshake proof, the Goethals--Seidel block calculation, the generic
Cooper--Wallis theorem, finite witness checks, the eight symbolic existence
corollaries, the exporter, and the challenge/solution package. It also checked
the current Palomar policy and prepared the local intake surface. The Fable
station added the empty-class corollary `no_handshake_matrix` and the
C₂-display nonexistence theorem `no_c2_matrix` with their proofs, and revised
the registry-facing metadata.

The human owner selected the tranche, supplied and relayed the source
repositories, controlled licensing and scope, and retains sole control of any
remote, publication, or Palomar submission. The owner's name appears in the
citation metadata and copyright line. This disclosure does not convert
workflow ownership into a claim of having personally written the derivations.

## What is independently checked here

There are three distinct layers:

1. Hadamard-M and Hadamard-T contain prose arguments, searches, Python
   certificates, artifact provenance, and exact-integer verification of their
   source results. Those source-side computations are not imported as proof.
2. `scripts/export_data.py` authenticates the four selected Hadamard-T JSON
   files by SHA-256, validates their expected schemas, and translates their
   entries deterministically. This establishes byte identity and faithful
   decoding, not the T-matrix or Williamson identities.
3. Lean checks the translated finite witnesses against the formal periodic
   T-matrix and Williamson predicates by kernel reduction, then proves the
   eight existence statements from the generic Cooper--Wallis theorem. No
   large output matrix is accepted merely because a source script accepted it.

The axiom audit is transitive and permits only `propext`,
`Classical.choice`, and `Quot.sound`. The formal proof development does not use
`native_decide`; the only proof holes are the deliberate Palomar challenge
holes, with completed counterparts in `Solution.lean`.

## Formal scope

Lean proves mathematical statements about the pinned witness values and the
two obstruction theorems. Witness provenance, search history, the dated
Table-4 status of the eight output orders, and the erratum's transcription
premises about the printed 1991 text are documentary records carried by the
cited source repositories; Lean's kernel establishes the proofs, not those
histories. This repository also does not replay Hadamard-T's full-matrix
Python certificates.

The order-103 predicate formalized here is periodic autocorrelation. No
aperiodic T-sequence claim is made.

## Credit for external mathematics and data

- `Hadamard-M@0208cf661fcd6b1e7d69eb52078d873eefc4d7cf` supplies the
  handshake obstruction, its graph proof, and the erratum application the
  empty-class corollary formalizes.
- `Hadamard-T@eec1bed6216c44675d946fe80d47695a7ae2ab40` supplies the exact
  periodic definitions, Cooper--Wallis sign table, and pinned data selected
  for this tranche.
- Williamson; Goethals and Seidel; and Cooper and Wallis supply the classical
  sequence and block constructions formalized here. Hadamard-T carries the
  detailed bibliographic and object-level provenance for its inputs.

The repository is licensed under MIT; see `LICENSE`.
