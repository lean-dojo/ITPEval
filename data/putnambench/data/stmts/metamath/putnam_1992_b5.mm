$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_b5: boundedness of the rational sequence obtained by dividing
  the determinant of the specified variable-size matrix by n factorial,
  identified with the source's solution proposition. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, 0 ..^ (n - 1) is the (n-1)-element carrier corresponding
  to Fin (n - 1). The binary map has entry i + 3 on the diagonal and 1 off
  the diagonal, and maDet over RRfld is its determinant. Although maDet is
  taken over the real field, every entry is rational and D is required to be
  QQ-valued, so this is exactly the rational determinant in the Lean source
  and the integer determinant coerced to QQ in the Isabelle source.

  The internal rational witness r and the universal quantification over all
  n at least 2 state boundedness of the full displayed set, without imposing
  a finite carrier or choosing a bound externally. The resolved answer is
  False, so the final biconditional asserts that this boundedness proposition
  is false. The declaration is an unproved $a statement encoding, and this
  database contains no $p proof statement.
$)

${
  $d d i j n r $.

  putnambench-putnam-1992-b5 $a |-
    A. d e. ( QQ ^m NN0 )
      (
        A. n e. NN0
          ( d ` n )
          =
          (
            (
              ( ( 0 ..^ ( n - 1 ) ) maDet RRfld )
              `
              (
                i e. ( 0 ..^ ( n - 1 ) ) ,
                j e. ( 0 ..^ ( n - 1 ) ) |->
                  if ( i = j , ( i + 3 ) , 1 )
              )
            )
          )
        ->
        (
          F.
          <->
          E. r e. QQ
            A. n e. NN0
              (
                2 <_ n
                ->
                (
                  abs
                  `
                  (
                    ( d ` n )
                    /
                    ( ! ` n )
                  )
                )
                <_
                r
              )
        )
      )
  $.
$}
