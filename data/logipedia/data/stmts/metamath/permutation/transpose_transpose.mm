$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.transpose_transpose
  (logipedia__metamath__permutation.transpose_transpose), catalog title
  "permutation.transpose_transpose": applying the transposition of two natural
  numbers twice returns the original natural number. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves all three source natural-number domains. Each nested
  conditional exactly unfolds permutation.transpose: it sends i to j, sends j
  to i, and otherwise returns its input. The outer conditional applies that
  same transposition to the result of the inner conditional, so the displayed
  equality is precisely transpose i j (transpose i j n) = n. SetMM's native
  equality preserves the source equality predicate. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

${
  $d i j n $.

  logipedia-permutation-transpose-transpose $a |-
    A. i e. NN0
      A. j e. NN0
        A. n e. NN0
          if (
            if ( n = i , j , if ( n = j , i , n ) ) = i ,
            j ,
            if (
              if ( n = i , j , if ( n = j , i , n ) ) = j ,
              i ,
              if ( n = i , j , if ( n = j , i , n ) )
            )
          ) = n
  $.
$}
