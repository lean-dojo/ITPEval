$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_81
  (verina__metamath__verina_basic_81), catalog title DivisionFunction: the
  exact total natural-number quotient-and-remainder program, including its
  zero-divisor branch, satisfies its complete integer-valued division
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 and ZZ are the full natural-number and integer domains. Their
  shared nonnegative numerals identify Lean's Int.ofNat coercion exactly.

  VERINAB81NatDiv and VERINAB81NatMod reproduce Lean's total Nat.div and
  Nat.mod operations. At divisor zero they return zero and the dividend,
  respectively. At a positive natural divisor, floor of rational division
  is the natural quotient and SetMM remainder is the nonnegative natural
  remainder.

  VERINAB81DivMod preserves the source helper's result order (remainder,
  quotient). VERINAB81Pre is the source True precondition together with the
  two Nat input types. VERINAB81DivisionFunction preserves the executable
  source conditional: divisor zero returns (x, 0), and a nonzero divisor
  invokes VERINAB81DivMod.

  VERINAB81Post preserves both source implications for the integer pair
  (r, q). At divisor zero it requires r = x and q = 0. At nonzero divisor it
  requires q * y + r = x, 0 <= r < y, and 0 <= q. The proof-valued
  precondition arguments to the implementation and postcondition are
  computationally and propositionally unused beyond the explicit
  precondition antecedent in the final correctness assertion. Every earlier
  $a is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB81NatDiv VERINAB81NatMod VERINAB81DivMod
  VERINAB81Pre VERINAB81DivisionFunction VERINAB81Post
$.

verinab81-nat-div-syntax
  $a class ( VERINAB81NatDiv A B ) $.
verinab81-nat-mod-syntax
  $a class ( VERINAB81NatMod A B ) $.
verinab81-div-mod-syntax
  $a class ( VERINAB81DivMod A B ) $.
verinab81-precondition-syntax
  $a wff ( VERINAB81Pre A B ) $.
verinab81-program-syntax
  $a class ( VERINAB81DivisionFunction A B ) $.
verinab81-postcondition-syntax
  $a wff ( VERINAB81Post A B C ) $.

verinab81-nat-div-definition $a |- (
  VERINAB81NatDiv A B
) = if (
  B = 0 ,
  0 ,
  ( |_ ` ( A / B ) )
) $.

verinab81-nat-mod-definition $a |- (
  VERINAB81NatMod A B
) = if (
  B = 0 ,
  A ,
  ( A mod B )
) $.

verinab81-div-mod-definition $a |- (
  VERINAB81DivMod A B
) = <.
  ( VERINAB81NatMod A B ) ,
  ( VERINAB81NatDiv A B )
>. $.

verinab81-precondition-definition $a |- (
  VERINAB81Pre A B
) <-> (
  A e. NN0
  /\
  B e. NN0
) $.

verinab81-program-definition $a |- (
  VERINAB81DivisionFunction A B
) = if (
  B = 0 ,
  <. A , 0 >. ,
  ( VERINAB81DivMod A B )
) $.

verinab81-postcondition-definition $a |- (
  VERINAB81Post A B C
) <-> (
  (
    (
      A e. NN0
      /\
      B e. NN0
    )
    /\
    C e. ( ZZ X. ZZ )
  )
  /\
  (
    (
      B = 0
      ->
      (
        ( 1st ` C ) = A
        /\
        ( 2nd ` C ) = 0
      )
    )
    /\
    (
      B =/= 0
      ->
      (
        (
          (
            ( 2nd ` C ) x. B
          ) + ( 1st ` C )
        ) = A
        /\
        (
          (
            0 <_ ( 1st ` C )
            /\
            ( 1st ` C ) < B
          )
          /\
          0 <_ ( 2nd ` C )
        )
      )
    )
  )
) $.

verina-basic-81-division-function $a |- A. x e. NN0
  A. y e. NN0
    (
      ( VERINAB81Pre x y )
      ->
      (
        VERINAB81Post
          x
          y
          ( VERINAB81DivisionFunction x y )
      )
    )
$.
