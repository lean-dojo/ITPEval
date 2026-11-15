$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_b1: positive integers with a unique base-10 over-expansion
  using coefficients from 0 through 10 are exactly those whose ordinary
  decimal expansion has no zero digit. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Word ( 0 ... 10 ) is set.mm's class of arbitrary finite sequences with
  entries from 0 through 10, and # gives their length. Excluding the empty
  word and requiring its last entry to be nonzero preserve the source's
  finite digit list and leading-coefficient condition. The positional sum
  is exactly the source over-expansion value, with index zero the units
  coefficient. Thus the restricted unique existential quantifies the entire
  finite list internally.

  For a positive natural N, the ordinary decimal position i is active
  exactly when 10^i <= N. Its digit is nonzero exactly when the residue of N
  modulo 10^(i+1) is at least 10^i. Hence the right side is bidirectionally
  equivalent to saying that the ordinary base-10 expansion of N contains no
  zero digit. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

$c P14B1Overexpansion $.

p14b1-overexpansion-syntax $a
  wff ( P14B1Overexpansion N d ) $.

${
  $d N d i $.

  p14b1-overexpansion-definition $a |- (
    ( P14B1Overexpansion N d )
    <->
    (
      (
        d e. ( Word ( 0 ... ; 1 0 ) \ { (/) } )
        /\
        ( d ` ( ( # ` d ) - 1 ) ) =/= 0
      )
      /\
      N
      =
      (
        sum_ i e. ( 0 ..^ ( # ` d ) )
          (
            ( d ` i )
            x.
            ( ; 1 0 ^ i )
          )
      )
    )
  ) $.
$}

${
  $d N d i $.

  putnambench-putnam-2014-b1 $a |- A. N e. NN
    (
      E! d e. Word ( 0 ... ; 1 0 )
        ( P14B1Overexpansion N d )
      <->
      A. i e. NN0
        (
          ( ; 1 0 ^ i ) <_ N
          ->
          ( ; 1 0 ^ i )
          <_
          (
            N
            mod
            ( ; 1 0 ^ ( i + 1 ) )
          )
        )
    )
  $.
$}
