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
the current Palomar policy and prepared the local intake surface.

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

Lean proves mathematical statements about the pinned witness values. It does
not prove how those witnesses were found, who found them first, whether a
database listed the resulting orders as open, whether a search was exhaustive,
or the provenance of the public artifact from which Hadamard-T reports decoding
`T(103)`. It also does not replay Hadamard-T's full-matrix Python certificates.
Those histories and claims belong to the cited source repositories and are
intentionally absent from the theorem statements.

The order-103 predicate formalized here is periodic autocorrelation. No
aperiodic T-sequence claim is made.

## Credit for external mathematics and data

- `Hadamard-M@1319c9d282f6c73ba024d6ec81b3212fdc122db2` supplies the
  handshake obstruction and its graph proof.
- `Hadamard-T@d9e2e64a57f331e7528f0849e36206ca03c71588` supplies the exact
  periodic definitions, Cooper--Wallis sign table, and pinned data selected
  for this tranche.
- Williamson; Goethals and Seidel; and Cooper and Wallis supply the classical
  sequence and block constructions formalized here. Hadamard-T carries the
  detailed bibliographic and object-level provenance for its inputs.

The repository is licensed under MIT; see `LICENSE`.
