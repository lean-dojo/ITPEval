# Corrected NTP4VC Source Authorities

This directory records narrowly scoped semantic errata discovered while
translating pinned NTP4VC verification conditions. The original files under
`data/ntp4vc/data/why3_sources/` remain unchanged for reproducibility.

The corrected files are additional source authorities, not rewritten history.
They remove only the inconsistency named in `index.json`:

- `A_Accumulate.mlw` removes global signed-32 range axioms for an unbounded
  mathematical sum. Range assumptions remain scoped to
  `p_accumulatebounds`.
- `A_StrSpn.mlw` and `A_StrPBrk.mlw` make each logical string operation depend
  explicitly on the character memory used by its recursive laws.
- `GilbreathCardTrickPure.mlw` requires distinct indices before asserting that
  two positions in a suit block contain different cards.

Target statements validated against these authorities must still use each
target prover's normal libraries and semantics. These corrections do not
authorize contradictory assumptions, arbitrary target axioms, trust tags, or
proof-bypass mechanisms.
