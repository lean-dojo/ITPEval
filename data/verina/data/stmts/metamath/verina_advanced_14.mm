$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_14, catalog title ifPowerOfFour: an executable natural-
  number recursion decides whether its input is a power of four, with the
  corresponding Boolean correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, Word NN0 is exactly the type
  of arbitrary finite natural-number lists, and { 0 , 1 } represents Bool
  with false = 0 and true = 1.

  VERINA14HelperGraph is the exact finite execution graph of the source local
  helper. A trace starts at the input. Every nonterminal entry is at least two
  and divisible by four, and the next entry is its natural-number quotient by
  four. The trace stops at zero, at one, or at a value at least two that is
  not divisible by four. Its output is true exactly when the terminal entry
  is one and false in the other terminal cases. Since every recursive step
  strictly decreases the current natural number, this graph has exactly the
  source helper's unique output on every input.

  VERINA14Helper selects that unique Boolean output, and
  VERINA14IfPowerOfFour is the source executable implementation. The
  proof-valued True precondition argument is computationally unused and is
  omitted from the target function. VERINA14Post states that the returned
  Boolean is true exactly when the input is four to a natural-number power.
  The final $a declaration applies the executable implementation to this
  postcondition under the source precondition. Every earlier $a is syntax or
  a faithful definition, and this artifact adds no $p declaration.
$)

$c
  VERINA14HelperGraph VERINA14Helper
  VERINA14IfPowerOfFour VERINA14Pre VERINA14Post
$.

verina14-helper-graph-syntax
  $a wff ( VERINA14HelperGraph A B ) $.
verina14-helper-syntax
  $a class ( VERINA14Helper A ) $.
verina14-if-power-of-four-syntax
  $a class ( VERINA14IfPowerOfFour A ) $.
verina14-precondition-syntax
  $a wff ( VERINA14Pre A ) $.
verina14-postcondition-syntax
  $a wff ( VERINA14Post A B ) $.

${
  $d i k s A B $.

  verina14-helper-graph-definition $a |- (
    VERINA14HelperGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. { 0 , 1 }
    )
    /\
    E. k e. NN0 E. s e. Word NN0
      (
        (
          ( # ` s ) = ( k + 1 )
          /\
          ( s ` 0 ) = A
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              (
                1 < ( s ` i )
                /\
                ( ( s ` i ) mod 4 ) = 0
              )
              /\
              (
                s ` ( i + 1 )
              ) = (
                |_ ` ( ( s ` i ) / 4 )
              )
            )
          /\
          (
            (
              ( s ` k ) = 1
              /\
              B = 1
            )
            \/
            (
              (
                ( s ` k ) = 0
                \/
                (
                  1 < ( s ` k )
                  /\
                  ( ( s ` k ) mod 4 ) =/= 0
                )
              )
              /\
              B = 0
            )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina14-helper-definition $a |- (
    VERINA14Helper A
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA14HelperGraph A y )
  ) $.
$}

verina14-if-power-of-four-definition $a |- (
  VERINA14IfPowerOfFour A
) = (
  VERINA14Helper A
) $.

verina14-precondition-definition $a |- (
  VERINA14Pre A
) <-> (
  A e. NN0
) $.

${
  $d m A B $.

  verina14-postcondition-definition $a |- (
    VERINA14Post A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      B = 1
      <->
      E. m e. NN0 A = ( 4 ^ m )
    )
  ) $.
$}

verina-advanced-14-if-power-of-four $a |- A. n e. NN0
  (
    ( VERINA14Pre n )
    ->
    (
      VERINA14Post
        n
        ( VERINA14IfPowerOfFour n )
    )
  )
$.
