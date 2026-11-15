$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_a4: binary digits arranged on a finite circle, with zero counts
  on equal-length arcs differing by at most one, admit an arc realizing the
  integral average zero and one counts of any finite family of arcs. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 0 ..^ n represents Fin n, and 0 ... n represents Fin (n + 1).
  Thus their Cartesian product is the full carrier of circular arcs, encoded
  by a starting position and a length from zero through n. Addition modulo n
  renders Fin n addition and hence circular wraparound exactly.

  C ranges over every binary-valued function on the n positions. Z and N are
  integer-valued functions on all arcs and are constrained to be precisely the
  zero and one counts. W is an arbitrary k-indexed family of arcs. The integer
  variables z and q satisfy the same real average equalities as Zsum and Nsum
  in the primary Lean source. The final existential remains internal to the
  conclusion. The sole declaration below is an unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d C N W Z j k l n q v w z $.

  putnambench-putnam-2013-a4 $a |- A. n e. NN A. k e. NN
    A. C e. ( ( 0 ..^ 2 ) ^m ( 0 ..^ n ) )
      A. Z e. ( ZZ ^m ( ( 0 ..^ n ) X. ( 0 ... n ) ) )
        A. N e. ( ZZ ^m ( ( 0 ..^ n ) X. ( 0 ... n ) ) )
          A. W e.
            ( ( ( 0 ..^ n ) X. ( 0 ... n ) ) ^m ( 0 ..^ k ) )
            A. z e. ZZ A. q e. ZZ
              (
                (
                  A. w e. ( ( 0 ..^ n ) X. ( 0 ... n ) )
                    ( Z ` w )
                    =
                    (
                      sum_ l e. ( 0 ..^ ( 2nd ` w ) )
                        if (
                          (
                            C
                            `
                            (
                              (
                                ( 1st ` w )
                                +
                                l
                              )
                              mod
                              n
                            )
                          )
                          =
                          0 ,
                          1 ,
                          0
                        )
                    )
                  /\
                  (
                    A. w e. ( ( 0 ..^ n ) X. ( 0 ... n ) )
                      ( N ` w )
                      =
                      (
                        sum_ l e. ( 0 ..^ ( 2nd ` w ) )
                          if (
                            (
                              C
                              `
                              (
                                (
                                  ( 1st ` w )
                                  +
                                  l
                                )
                                mod
                                n
                              )
                            )
                            =
                            1 ,
                            1 ,
                            0
                          )
                      )
                    /\
                    (
                      A. w e. ( ( 0 ..^ n ) X. ( 0 ... n ) )
                        A. v e. ( ( 0 ..^ n ) X. ( 0 ... n ) )
                          (
                            ( 2nd ` w ) = ( 2nd ` v )
                            ->
                            (
                              abs
                              `
                              (
                                ( Z ` w )
                                -
                                ( Z ` v )
                              )
                            )
                            <_
                            1
                          )
                      /\
                      (
                        z
                        =
                        (
                          ( 1 / k )
                          x.
                          (
                            sum_ j e. ( 0 ..^ k )
                              ( Z ` ( W ` j ) )
                          )
                        )
                        /\
                        q
                        =
                        (
                          ( 1 / k )
                          x.
                          (
                            sum_ j e. ( 0 ..^ k )
                              ( N ` ( W ` j ) )
                          )
                        )
                      )
                    )
                  )
                )
                ->
                E. w e. ( ( 0 ..^ n ) X. ( 0 ... n ) )
                  (
                    ( Z ` w ) = z
                    /\
                    ( N ` w ) = q
                  )
              )
  $.
$}
