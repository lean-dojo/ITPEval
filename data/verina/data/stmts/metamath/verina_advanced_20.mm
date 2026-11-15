$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_20, catalog title isItEight: an executable integer
  computation decides whether the input is divisible by eight or its absolute
  value has a decimal digit equal to eight, with the corresponding Boolean
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, NN0 is the full natural-number
  domain, and { 0 , 1 } represents Bool with false = 0 and true = 1.
  VERINA20NatAbs is Lean's Int.natAbs on integer inputs.

  VERINA20HasDigitEightGraph is the exact finite execution graph of the local
  hasDigitEight recursion. A trace starts at the input natural number. Every
  nonterminal entry is positive, has last decimal digit different from eight,
  and is followed by its natural-number quotient by ten. The trace terminates
  at zero with false or at a positive number whose last digit is eight with
  true. Thus VERINA20HasDigitEight selects exactly the helper's unique output
  on every natural-number input.

  VERINA20IsItEight is the source short-circuit Boolean implementation: it
  returns true when the integer remainder modulo eight is zero and otherwise
  returns the helper applied to the absolute value. VERINA20Pre is the source
  True precondition together with the Int input type. VERINA20Post preserves
  the source equivalence between the returned Boolean and the disjunction of
  divisibility by eight with the unbounded natural existential asserting a
  decimal digit eight. The proof-valued precondition argument is
  computationally unused and is omitted from the target function. The final
  $a declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA20NatAbs
  VERINA20HasDigitEightGraph VERINA20HasDigitEight
  VERINA20Pre VERINA20IsItEight VERINA20Post
$.

verina20-nat-abs-syntax
  $a class ( VERINA20NatAbs A ) $.
verina20-has-digit-eight-graph-syntax
  $a wff ( VERINA20HasDigitEightGraph A B ) $.
verina20-has-digit-eight-syntax
  $a class ( VERINA20HasDigitEight A ) $.
verina20-precondition-syntax
  $a wff ( VERINA20Pre A ) $.
verina20-is-it-eight-syntax
  $a class ( VERINA20IsItEight A ) $.
verina20-postcondition-syntax
  $a wff ( VERINA20Post A B ) $.

verina20-nat-abs-definition $a |- (
  VERINA20NatAbs A
) = (
  abs ` A
) $.

${
  $d i k s A B $.

  verina20-has-digit-eight-graph-definition $a |- (
    VERINA20HasDigitEightGraph A B
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
                0 < ( s ` i )
                /\
                ( ( s ` i ) mod ; 1 0 ) =/= 8
              )
              /\
              (
                s ` ( i + 1 )
              ) = (
                |_ ` ( ( s ` i ) / ; 1 0 )
              )
            )
          /\
          (
            (
              ( s ` k ) = 0
              /\
              B = 0
            )
            \/
            (
              (
                0 < ( s ` k )
                /\
                ( ( s ` k ) mod ; 1 0 ) = 8
              )
              /\
              B = 1
            )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina20-has-digit-eight-definition $a |- (
    VERINA20HasDigitEight A
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA20HasDigitEightGraph A y )
  ) $.
$}

verina20-precondition-definition $a |- (
  VERINA20Pre A
) <-> (
  A e. ZZ
) $.

verina20-is-it-eight-definition $a |- (
  VERINA20IsItEight A
) = if (
  ( A mod 8 ) = 0 ,
  1 ,
  VERINA20HasDigitEight ( VERINA20NatAbs A )
) $.

${
  $d i A B $.

  verina20-postcondition-definition $a |- (
    VERINA20Post A B
  ) <-> (
    (
      A e. ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      (
        ( A mod 8 ) = 0
        \/
        E. i e. NN0
          (
            (
              |_ ` (
                ( VERINA20NatAbs A )
                /
                ( ; 1 0 ^ i )
              )
            ) mod ; 1 0
          ) = 8
      )
      <->
      B = 1
    )
  ) $.
$}

verina-advanced-20-is-it-eight $a |- A. n e. ZZ
  (
    ( VERINA20Pre n )
    ->
    (
      VERINA20Post
        n
        ( VERINA20IsItEight n )
    )
  )
$.
