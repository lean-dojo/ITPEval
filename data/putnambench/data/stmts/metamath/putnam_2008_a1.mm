$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_a1: a real-valued function of two real variables whose cyclic
  three-term sum always vanishes is the difference of values of a real
  function of one variable. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m ( RR X. RR ) is the class of all total real-valued functions on
  ordered pairs of reals, and RR ^m RR is the class of all total real-valued
  functions on the reals. Application to an ordered pair represents the
  source's curried binary function. The antecedent and existential conclusion
  preserve all real domains and quantifier scopes exactly.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f g x y z $.

  putnambench-putnam-2008-a1 $a |-
    A. f e. ( RR ^m ( RR X. RR ) )
      (
        A. x e. RR A. y e. RR A. z e. RR
          (
            (
              ( f ` <. x , y >. )
              +
              ( f ` <. y , z >. )
            )
            +
            ( f ` <. z , x >. )
          )
          =
          0
        ->
        E. g e. ( RR ^m RR )
          A. x e. RR A. y e. RR
            ( f ` <. x , y >. )
            =
            ( ( g ` x ) - ( g ` y ) )
      )
  $.
$}
