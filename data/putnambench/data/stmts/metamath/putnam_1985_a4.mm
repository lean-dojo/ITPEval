$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_a4: the only last-two-digit residue occurring infinitely often
  in the sequence a(1) = 3, a(i+1) = 3^a(i), is 87.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 ^m NN0 is set.mm's class of all natural-number sequences indexed by
  the nonnegative integers. The antecedent preserves the source initial value
  at index 1 and its recurrence at every positive index. The Rocq source uses
  the same sequence shifted down by one index; this finite shift preserves
  exactly which residues occur infinitely often.

  The carrier 0 ..^ 100 consists exactly of the integers from 0 through 99.
  For each such k, the restricted-class predicate says that beyond every
  natural bound n there is an index i at least n with a(i) mod 100 = k.
  Thus equality with the singleton {87} is the source conclusion with its
  explicit solution inlined. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof declaration.
$)

${
  $d a i k n $.

  putnambench-putnam-1985-a4 $a |-
    A. a e. ( NN0 ^m NN0 )
      (
        (
          ( a ` 1 ) = 3
          /\
          A. i e. NN
            ( a ` ( i + 1 ) ) = ( 3 ^ ( a ` i ) )
        )
        ->
        {
          k e. ( 0 ..^ ; ; 1 0 0 ) |
          A. n e. NN0 E. i e. NN0
            (
              n <_ i
              /\
              ( ( a ` i ) mod ; ; 1 0 0 ) = k
            )
        }
        =
        { ; 8 7 }
      )
  $.
$}
