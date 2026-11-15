$(
  Statement-only formalization of Thousand Theorems corpus artifact Q939927
  (thousand-theorems__metamath__Q939927), "Stone-Weierstrass theorem": a
  point-separating unital real subalgebra of the continuous real-valued
  functions on an arbitrary compact topological space is uniformly dense.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM represents a compact topological space by a compact topology J, whose
  carrier is U. J. The class ( J Cn ( TopOpen ` RRfld ) ) is the full algebra
  of continuous real-valued functions on that carrier.

  The antecedent says that A is a unital real subalgebra: it contains every
  real constant function and is closed under pointwise addition and
  multiplication. These conditions also give scalar multiplication and
  additive inverses. It then states the source point-separation hypothesis.

  The conclusion is the positive-epsilon uniform approximation criterion for
  every continuous real-valued function. On a compact source this is
  equivalent to the source assertion that the topological closure of A in the
  uniform-norm topology is the whole continuous-function algebra.

  The final declaration is the single unproved corpus $a statement. This
  root statement file contains no $p proof statement.
$)

${
  $d A E F J c f g h r t $.

  thousand-theorems-q939927-stone-weierstrass $a |-
    A. J A. A
      (
        (
          J e. Comp
          /\
          A C_ ( J Cn ( TopOpen ` RRfld ) )
          /\
          A. c e. RR
            ( t e. U. J |-> c ) e. A
          /\
          A. f e. A A. g e. A
            (
              (
                t e. U. J |->
                ( ( f ` t ) + ( g ` t ) )
              ) e. A
              /\
              (
                t e. U. J |->
                ( ( f ` t ) x. ( g ` t ) )
              ) e. A
            )
          /\
          A. r e. U. J A. t e. U. J
            (
              r =/= t
              ->
              E. h e. A
                ( h ` r ) =/= ( h ` t )
            )
        )
        ->
        A. F e. ( J Cn ( TopOpen ` RRfld ) )
          A. E e. RR+
            E. f e. A
              A. t e. U. J
                (
                  abs `
                  (
                    ( f ` t )
                    -
                    ( F ` t )
                  )
                )
                <
                E
      )
  $.
$}
