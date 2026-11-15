$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_26
  (verina__metamath__verina_basic_26), catalog title isEven: the exact
  executable integer parity test returns true precisely when the input has
  remainder zero modulo two and satisfies its Boolean correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and { 0 , 1 } represents Bool with
  false = 0 and true = 1. For the positive divisor two, SetMM integer
  remainder agrees with Lean's nonnegative Int remainder, including on
  negative inputs.

  VERINAB26Pre is the source True precondition together with the Int input
  type. VERINAB26IsEven is exactly the source executable expression
  n % 2 == 0: it returns true exactly when the remainder is zero and false
  otherwise. VERINAB26Post preserves both source implications, interpreting
  a Boolean as a proposition exactly when it is true and its negation exactly
  when it is false.

  The proof-valued precondition argument has no computational or
  propositional effect and is represented by the explicit antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB26Pre VERINAB26IsEven VERINAB26Post
$.

verinab26-precondition-syntax
  $a wff ( VERINAB26Pre A ) $.
verinab26-program-syntax
  $a class ( VERINAB26IsEven A ) $.
verinab26-postcondition-syntax
  $a wff ( VERINAB26Post A B ) $.

verinab26-precondition-definition $a |- (
  VERINAB26Pre A
) <-> (
  A e. ZZ
) $.

verinab26-program-definition $a |- (
  VERINAB26IsEven A
) = if (
  ( A mod 2 ) = 0 ,
  1 ,
  0
) $.

verinab26-postcondition-definition $a |- (
  VERINAB26Post A B
) <-> (
  (
    A e. ZZ
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      B = 1
      ->
      ( A mod 2 ) = 0
    )
    /\
    (
      B = 0
      ->
      ( A mod 2 ) =/= 0
    )
  )
) $.

verina-basic-26-is-even $a |- A. n e. ZZ
  (
    ( VERINAB26Pre n )
    ->
    (
      VERINAB26Post
        n
        ( VERINAB26IsEven n )
    )
  )
$.
