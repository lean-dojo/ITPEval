$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_a3: two successive nine-digit substitution relations force
  each original and final digit to be congruent modulo seven. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The functions d, e, and f range over all NN0-indexed integer sequences,
  matching the Isabelle source. Only indices 0 through 8 occur, so restriction
  to those indices gives the Lean Fin 9 representation, and every Fin 9
  function conversely has an arbitrary NN0-indexed extension.

  Each displayed finite sum is the source digits_to_num definition after
  replacing the digit at i. The two large conjuncts inline the defining
  biconditional for relation at (d,e) and (e,f), respectively. Eliminating
  these uniquely defined function and relation parameters is a definitional
  equivalence, while retaining all digit bounds, substitutions, and
  divisibility conditions. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d d e f i j $.

  putnambench-putnam-1995-a3 $a |-
    A. d e. ( ZZ ^m NN0 )
      A. e e. ( ZZ ^m NN0 )
        A. f e. ( ZZ ^m NN0 )
          (
            (
              (
                A. i e. ( 0 ... 8 )
                  (
                    (
                      (
                        ( d ` i ) < ; 1 0
                        /\
                        0 <_ ( d ` i )
                      )
                      /\
                      (
                        ( e ` i ) < ; 1 0
                        /\
                        0 <_ ( e ` i )
                      )
                    )
                    /\
                    7
                    ||
                    sum_ j e. ( 0 ... 8 )
                      (
                        if (
                          j = i ,
                          ( e ` j ) ,
                          ( d ` j )
                        )
                        x.
                        ( ; 1 0 ^ j )
                      )
                  )
              )
              /\
              (
                A. i e. ( 0 ... 8 )
                  (
                    (
                      (
                        ( e ` i ) < ; 1 0
                        /\
                        0 <_ ( e ` i )
                      )
                      /\
                      (
                        ( f ` i ) < ; 1 0
                        /\
                        0 <_ ( f ` i )
                      )
                    )
                    /\
                    7
                    ||
                    sum_ j e. ( 0 ... 8 )
                      (
                        if (
                          j = i ,
                          ( f ` j ) ,
                          ( e ` j )
                        )
                        x.
                        ( ; 1 0 ^ j )
                      )
                  )
              )
            )
            ->
            A. i e. ( 0 ... 8 )
              7 || ( ( d ` i ) - ( f ` i ) )
          )
  $.
$}
