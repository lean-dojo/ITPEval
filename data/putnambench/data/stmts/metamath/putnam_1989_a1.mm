$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_a1: the extended cardinality of the positive primes whose
  usual base-10 digits alternate 1 and 0, beginning and ending with 1,
  equals the specified solution value. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is set.mm's class of positive natural primes. For k in NN0, the
  sum of 10^(2*i) over i from 0 through k has exactly the odd-length decimal
  digit string 1,0,1,0,...,1. Thus the existential condition below is
  definitionally equivalent to the canonical digit-list predicate in the
  Lean and Isabelle sources.

  The hash function takes values in NN0* = NN0 union {+oo}, so it is exactly
  the sources' extended-natural cardinality and does not assume the displayed
  prime set is finite. The right side is the resolved Putnam answer 1. The
  declaration below is an unproved $a statement, and this database contains
  no $p proof statement.
$)

${
  $d i k p $.

  putnambench-putnam-1989-a1 $a |- (
    #
    `
    {
      p e. Prime |
      E. k e. NN0
        p
        =
        (
          sum_ i e. ( 0 ... k )
            ( ( ; 1 0 ) ^ ( 2 x. i ) )
        )
    }
  )
  =
  1
  $.
$}
