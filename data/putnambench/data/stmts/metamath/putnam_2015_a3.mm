$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_a3: the base-two logarithm of a 2015-by-2015 product of
  complex exponential factors is 13725. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's CC-valued exp and log are the complex exponential and principal
  natural logarithm, while _i and _pi are the imaginary unit and pi. The
  inclusive range 1 ... 2015 is definitionally the shifted Fin 2015 carrier
  used in the Lean source. The nested prod_ binders therefore preserve both
  finite products, and division by log(2) is the source base-two logarithm.

  The right side inlines the explicit value from the Rocq source and the
  solution annotations in the Lean and Isabelle sources. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof declaration.
$)

${
  $d a b $.

  putnambench-putnam-2015-a3 $a |- (
    (
      log
      `
      (
        prod_ a e. ( 1 ... ; ; ; 2 0 1 5 )
          prod_ b e. ( 1 ... ; ; ; 2 0 1 5 )
            (
              1
              +
              (
                exp
                `
                (
                  (
                    (
                      (
                        ( 2 x. _pi )
                        x.
                        _i
                      )
                      x.
                      a
                    )
                    x.
                    b
                  )
                  /
                  ; ; ; 2 0 1 5
                )
              )
            )
      )
    )
    /
    ( log ` 2 )
  ) = ; ; ; ; 1 3 7 2 5 $.
$}
