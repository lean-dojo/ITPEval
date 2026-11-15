$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_a3: nonexistence of a finite real limit at positive infinity
  for the specified exponentially scaled iterated integral. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The nested S. binders are set.mm's real Lebesgue integrals. For positive
  t, the open interval (0,t) differs from the half-open or closed source
  intervals only at endpoints of measure zero. Values for negative t are
  irrelevant to the limit at positive infinity.

  The epsilon-threshold formula expands Tendsto atTop to a finite real L.
  Its outer negation is the source equivalence with the solution False.
  The declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d L e m t x y $.

  putnambench-putnam-1981-a3 $a |- -. E. L e. RR
    A. e e. RR
      (
        0 < e
        ->
        E. m e. RR
          A. t e. RR
            (
              m <_ t
              ->
              (
                abs
                `
                (
                  (
                    ( exp ` ( -u t ) )
                    x.
                    S. ( 0 (,) t )
                      (
                        S. ( 0 (,) t )
                          (
                            (
                              ( exp ` x )
                              -
                              ( exp ` y )
                            )
                            /
                            ( x - y )
                          )
                          _d x
                      )
                      _d y
                  )
                  -
                  L
                )
              )
              < e
            )
      )
  $.
$}
