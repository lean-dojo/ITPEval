$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_18
  (verina__metamath__verina_basic_18), catalog title sumOfDigits: the exact
  accumulator recursion sums the decimal digits of an arbitrary natural
  number and satisfies the decimal-representation correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number traces and digit lists.

  VERINAB18LoopGraph is the exact finite execution graph of the source local
  loop for an arbitrary current number and accumulator. Its traces repeatedly
  replace a positive current number by its natural quotient by ten and add
  its remainder modulo ten to the accumulator, stopping precisely at zero.
  VERINAB18Loop selects the unique final accumulator, and
  VERINAB18SumOfDigits invokes that loop with accumulator zero. Thus the
  executable result is fixed independently of the postcondition and admits
  no additional outputs.

  VERINAB18DecimalDigits is the unique canonical most-significant-first
  decimal digit word of a natural number, including the one-digit word
  containing zero for input zero. This is exactly the result of mapping
  Char.toNat c - Char.toNat '0' over String.toList (Nat.repr n), since every
  character emitted by Nat.repr is an ASCII decimal digit.
  VERINAB18DecimalDigitSum is the source List.sum of that mapped list.

  VERINAB18NatSub is Lean's truncated natural subtraction. VERINAB18Pre is
  the source True precondition together with the Nat input type.
  VERINAB18Post preserves both source conjuncts: each truncated difference
  between the executable result and the decimal-representation digit sum is
  zero. The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB18LoopGraph VERINAB18Loop VERINAB18SumOfDigits
  VERINAB18DecimalDigitsGraph VERINAB18DecimalDigits
  VERINAB18DecimalDigitSum
  VERINAB18NatSub VERINAB18Pre VERINAB18Post
$.

verinab18-loop-graph-syntax
  $a wff ( VERINAB18LoopGraph A B C ) $.
verinab18-loop-syntax
  $a class ( VERINAB18Loop A B ) $.
verinab18-program-syntax
  $a class ( VERINAB18SumOfDigits A ) $.
verinab18-decimal-digits-graph-syntax
  $a wff ( VERINAB18DecimalDigitsGraph A B ) $.
verinab18-decimal-digits-syntax
  $a class ( VERINAB18DecimalDigits A ) $.
verinab18-decimal-digit-sum-syntax
  $a class ( VERINAB18DecimalDigitSum A ) $.
verinab18-nat-sub-syntax
  $a class ( VERINAB18NatSub A B ) $.
verinab18-precondition-syntax
  $a wff ( VERINAB18Pre A ) $.
verinab18-postcondition-syntax
  $a wff ( VERINAB18Post A B ) $.

${
  $d i k s t A B C $.

  verinab18-loop-graph-definition $a |- (
    VERINAB18LoopGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    E. k e. NN0 E. s e. Word NN0 E. t e. Word NN0
      (
        (
          (
            ( # ` s ) = ( k + 1 )
            /\
            ( # ` t ) = ( k + 1 )
          )
          /\
          (
            ( s ` 0 ) = A
            /\
            ( t ` 0 ) = B
          )
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              0 < ( s ` i )
              /\
              (
                (
                  s ` ( i + 1 )
                ) = (
                  |_ ` ( ( s ` i ) / ; 1 0 )
                )
                /\
                (
                  t ` ( i + 1 )
                ) = (
                  ( t ` i )
                  +
                  ( ( s ` i ) mod ; 1 0 )
                )
              )
            )
          /\
          (
            ( s ` k ) = 0
            /\
            C = ( t ` k )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab18-loop-definition $a |- (
    VERINAB18Loop A B
  ) = (
    iota_ y e. NN0
      ( VERINAB18LoopGraph A B y )
  ) $.
$}

verinab18-program-definition $a |- (
  VERINAB18SumOfDigits A
) = (
  VERINAB18Loop A 0
) $.

${
  $d i A B $.

  verinab18-decimal-digits-graph-definition $a |- (
    VERINAB18DecimalDigitsGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word NN0
    )
    /\
    (
      0 < ( # ` B )
      /\
      (
        A. i e. ( 0 ..^ ( # ` B ) )
          ( B ` i ) < ; 1 0
        /\
        (
          (
            (
              A = 0
              ->
              ( # ` B ) = 1
            )
            /\
            (
              0 < A
              ->
              0 < ( B ` 0 )
            )
          )
          /\
          A = sum_ i e. ( 0 ..^ ( # ` B ) )
            (
              ( B ` i )
              x.
              (
                ; 1 0
                ^
                ( ( ( # ` B ) - 1 ) - i )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d y A $.

  verinab18-decimal-digits-definition $a |- (
    VERINAB18DecimalDigits A
  ) = (
    iota_ y e. Word NN0
      ( VERINAB18DecimalDigitsGraph A y )
  ) $.
$}

${
  $d i A $.

  verinab18-decimal-digit-sum-definition $a |- (
    VERINAB18DecimalDigitSum A
  ) = (
    sum_ i e. (
      0 ..^ ( # ` ( VERINAB18DecimalDigits A ) )
    )
      (
        ( VERINAB18DecimalDigits A ) ` i
      )
  ) $.
$}

verinab18-nat-sub-definition $a |- (
  VERINAB18NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab18-precondition-definition $a |- (
  VERINAB18Pre A
) <-> (
  A e. NN0
) $.

verinab18-postcondition-definition $a |- (
  VERINAB18Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    (
      VERINAB18NatSub
        B
        ( VERINAB18DecimalDigitSum A )
    ) = 0
    /\
    (
      VERINAB18NatSub
        ( VERINAB18DecimalDigitSum A )
        B
    ) = 0
  )
) $.

verina-basic-18-sum-of-digits $a |- A. n e. NN0
  (
    ( VERINAB18Pre n )
    ->
    (
      VERINAB18Post
        n
        ( VERINAB18SumOfDigits n )
    )
  )
$.
