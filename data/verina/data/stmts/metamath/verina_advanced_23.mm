$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_23 (verina__metamath__verina_advanced_23), catalog title
  isPowerOfTwo: a fuel-bounded executable integer recursion decides whether
  its input is a positive power of two, together with its Boolean correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, NN0 is the full natural-number
  domain, and { 0 , 1 } represents Bool with false = 0 and true = 1.
  VERINA23NatAbs is Lean's Int.natAbs on integer inputs, and VERINA23Pow is
  the source recursive integer-base, natural-exponent power helper.

  VERINA23State is the pair (m, fuel) used by the source local aux function.
  VERINA23Continue is exactly its recursive branch: positive fuel, m
  different from one, and even m lead to floor division by two and fuel
  decremented by one. On the only call made by the implementation m is
  positive, so floor division agrees exactly with Lean integer division.
  VERINA23Stop preserves the source test priority: exhausted fuel returns
  false; otherwise m equal to one returns true; otherwise odd m returns
  false. VERINA23AuxGraph records the complete finite execution trace, and
  VERINA23Aux selects its unique Boolean result.

  VERINA23IsPowerOfTwo is the source executable implementation: nonpositive
  inputs return false, while positive inputs run the exact helper from
  (n, n.natAbs). VERINA23Pre is the source True precondition together with
  the Int input type. VERINA23Post reproduces both branches of the source
  Boolean postcondition using the unrestricted natural exponent witness and
  the explicit positivity condition. The proof-valued precondition argument
  is computationally and propositionally unused and is omitted from the
  target function and predicate. The final $a declaration is the source
  correctness proposition. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA23NatAbs VERINA23Pow
  VERINA23State VERINA23Continue VERINA23Stop
  VERINA23AuxGraph VERINA23Aux
  VERINA23Pre VERINA23IsPowerOfTwo VERINA23Post
$.

verina23-nat-abs-syntax
  $a class ( VERINA23NatAbs A ) $.
verina23-pow-syntax
  $a class ( VERINA23Pow A B ) $.
verina23-state-syntax
  $a class VERINA23State $.
verina23-continue-syntax
  $a wff ( VERINA23Continue A B ) $.
verina23-stop-syntax
  $a wff ( VERINA23Stop A B ) $.
verina23-aux-graph-syntax
  $a wff ( VERINA23AuxGraph A B C ) $.
verina23-aux-syntax
  $a class ( VERINA23Aux A B ) $.
verina23-precondition-syntax
  $a wff ( VERINA23Pre A ) $.
verina23-is-power-of-two-syntax
  $a class ( VERINA23IsPowerOfTwo A ) $.
verina23-postcondition-syntax
  $a wff ( VERINA23Post A B ) $.

verina23-nat-abs-definition $a |- (
  VERINA23NatAbs A
) = (
  abs ` A
) $.

verina23-pow-definition $a |- (
  VERINA23Pow A B
) = (
  A ^ B
) $.

verina23-state-definition $a |- VERINA23State = (
  ZZ X. NN0
) $.

verina23-continue-definition $a |- (
  VERINA23Continue A B
) <-> (
  (
    A e. VERINA23State
    /\
    B e. VERINA23State
  )
  /\
  (
    (
      ( 2nd ` A ) =/= 0
      /\
      ( 1st ` A ) =/= 1
    )
    /\
    (
      ( ( 1st ` A ) mod 2 ) = 0
      /\
      B = <.
        ( |_ ` ( ( 1st ` A ) / 2 ) ) ,
        ( ( 2nd ` A ) - 1 )
      >.
    )
  )
) $.

verina23-stop-definition $a |- (
  VERINA23Stop A B
) <-> (
  (
    A e. VERINA23State
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      ( 2nd ` A ) = 0
      /\
      B = 0
    )
    \/
    (
      (
        ( 2nd ` A ) =/= 0
        /\
        ( 1st ` A ) = 1
      )
      /\
      B = 1
    )
    \/
    (
      (
        (
          ( 2nd ` A ) =/= 0
          /\
          ( 1st ` A ) =/= 1
        )
        /\
        ( ( 1st ` A ) mod 2 ) =/= 0
      )
      /\
      B = 0
    )
  )
) $.

${
  $d i k t A B C $.

  verina23-aux-graph-definition $a |- (
    VERINA23AuxGraph A B C
  ) <-> (
    (
      (
        A e. ZZ
        /\
        B e. NN0
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    E. k e. NN0 E. t e. Word VERINA23State
      (
        (
          ( # ` t ) = ( k + 1 )
          /\
          ( t ` 0 ) = <. A , B >.
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              VERINA23Continue
                ( t ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          (
            VERINA23Stop
              ( t ` k )
              C
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina23-aux-definition $a |- (
    VERINA23Aux A B
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA23AuxGraph A B y )
  ) $.
$}

verina23-precondition-definition $a |- (
  VERINA23Pre A
) <-> (
  A e. ZZ
) $.

verina23-is-power-of-two-definition $a |- (
  VERINA23IsPowerOfTwo A
) = if (
  A <_ 0 ,
  0 ,
  VERINA23Aux A ( VERINA23NatAbs A )
) $.

${
  $d x A B $.

  verina23-postcondition-definition $a |- (
    VERINA23Post A B
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
        /\
        E. x e. NN0
          (
            ( VERINA23Pow 2 x ) = A
            /\
            0 < A
          )
      )
      \/
      (
        B = 0
        /\
        -.
        E. x e. NN0
          (
            ( VERINA23Pow 2 x ) = A
            /\
            0 < A
          )
      )
    )
  ) $.
$}

verina-advanced-23-is-power-of-two $a |- A. n e. ZZ
  (
    ( VERINA23Pre n )
    ->
    (
      VERINA23Post
        n
        ( VERINA23IsPowerOfTwo n )
    )
  )
$.
