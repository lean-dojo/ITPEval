$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_a3: every three-times continuously differentiable real
  function has a real point where the product of its value and first three
  derivatives is nonnegative. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of all total real-valued functions. Membership in
  ( ( C^n ` RR ) ` 3 ) is set.mm's native assertion of global continuous
  differentiability through order three, and the entries of ( RR Dn f ) are
  the iterated real derivatives. The witness a remains internally
  existential over the full real line. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a f $.

  putnambench-putnam-1998-a3 $a |-
    A. f e. ( RR ^m RR )
      (
        f e. ( ( C^n ` RR ) ` 3 )
        ->
        E. a e. RR
          0
          <_
          (
            (
              (
                ( f ` a )
                x.
                ( ( ( RR Dn f ) ` 1 ) ` a )
              )
              x.
              ( ( ( RR Dn f ) ` 2 ) ` a )
            )
            x.
            ( ( ( RR Dn f ) ` 3 ) ` a )
          )
      )
  $.
$}
