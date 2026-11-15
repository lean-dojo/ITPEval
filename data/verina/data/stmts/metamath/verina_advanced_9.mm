$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_9 (verina__metamath__verina_advanced_9), catalog title
  countSumDivisibleBy: exact decimal digit-sum recursion and a descending
  natural-number scan count the values below n whose digit sum is divisible
  by a positive divisor d, with the complete correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, Word NN0 is exactly the type
  of arbitrary finite natural-number traces, and { 0 , 1 } represents Bool
  with false = 0 and true = 1.

  VERINA9NatMod is Lean's Nat.mod on all natural arguments, including the
  source behavior A % 0 = A. VERINA9SumDigitsGoGraph is the exact execution
  graph of the local go function in sumOfDigits for arbitrary current number
  and accumulator. Its traces repeatedly divide a positive current number by
  ten and add its last decimal digit, stopping precisely at zero.
  VERINA9SumDigitsGo selects the unique final accumulator, and
  VERINA9SumOfDigits invokes it with accumulator zero.

  VERINA9IsSumDivisibleBy is the source Boolean equality test. VERINA9NatSub
  is Lean's truncated natural subtraction. VERINA9CountGoGraph is the exact
  execution graph of the local go function in countSumDivisibleBy for
  arbitrary index, accumulator, and divisor. Starting from index i, each
  step processes i - 1, increments the accumulator exactly when the Boolean
  helper is true, and then decrements the index. VERINA9CountSumDivisibleBy
  invokes this recursion at n with accumulator zero. Thus the implementation
  is fixed independently of the postcondition and permits no extra outputs.

  VERINA9FilteredCount is exactly the length of the source List.filter over
  List.range n: the retained indices are those x below n satisfying the
  source conjunction x < n and sumOfDigits x % d = 0. VERINA9Pre is the
  positive-divisor precondition. VERINA9Post preserves both source conjuncts,
  namely truncated subtraction of the result from the filtered length equals
  zero and the result is at most that length. The proof-valued precondition
  arguments are computationally and propositionally unused inside the source
  function and postcondition, and the final assertion supplies the complete
  precondition as its explicit antecedent.

  The final $a declaration is the complete source correctness proposition.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINA9NatMod
  VERINA9SumDigitsGoGraph VERINA9SumDigitsGo VERINA9SumOfDigits
  VERINA9IsSumDivisibleBy
  VERINA9NatSub
  VERINA9CountGoGraph VERINA9CountGo VERINA9CountSumDivisibleBy
  VERINA9FilteredCount
  VERINA9Pre VERINA9Post
$.

verina9-nat-mod-syntax
  $a class ( VERINA9NatMod A B ) $.
verina9-sum-digits-go-graph-syntax
  $a wff ( VERINA9SumDigitsGoGraph A B C ) $.
verina9-sum-digits-go-syntax
  $a class ( VERINA9SumDigitsGo A B ) $.
verina9-sum-of-digits-syntax
  $a class ( VERINA9SumOfDigits A ) $.
verina9-is-sum-divisible-by-syntax
  $a class ( VERINA9IsSumDivisibleBy A B ) $.
verina9-nat-sub-syntax
  $a class ( VERINA9NatSub A B ) $.
verina9-count-go-graph-syntax
  $a wff ( VERINA9CountGoGraph A B C D ) $.
verina9-count-go-syntax
  $a class ( VERINA9CountGo A B C ) $.
verina9-program-syntax
  $a class ( VERINA9CountSumDivisibleBy A B ) $.
verina9-filtered-count-syntax
  $a class ( VERINA9FilteredCount A B ) $.
verina9-precondition-syntax
  $a wff ( VERINA9Pre A B ) $.
verina9-postcondition-syntax
  $a wff ( VERINA9Post A B C ) $.

verina9-nat-mod-definition $a |- (
  VERINA9NatMod A B
) = if (
  B = 0 ,
  A ,
  ( A mod B )
) $.

${
  $d i k s t A B C $.

  verina9-sum-digits-go-graph-definition $a |- (
    VERINA9SumDigitsGoGraph A B C
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
                  (
                    VERINA9NatMod
                      ( s ` i )
                      ; 1 0
                  )
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

  verina9-sum-digits-go-definition $a |- (
    VERINA9SumDigitsGo A B
  ) = (
    iota_ y e. NN0
      ( VERINA9SumDigitsGoGraph A B y )
  ) $.
$}

verina9-sum-of-digits-definition $a |- (
  VERINA9SumOfDigits A
) = (
  VERINA9SumDigitsGo A 0
) $.

verina9-is-sum-divisible-by-definition $a |- (
  VERINA9IsSumDivisibleBy A B
) = if (
  (
    VERINA9NatMod
      ( VERINA9SumOfDigits A )
      B
  ) = 0 ,
  1 ,
  0
) $.

verina9-nat-sub-definition $a |- (
  VERINA9NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d k s t A B C D $.

  verina9-count-go-graph-definition $a |- (
    VERINA9CountGoGraph A B C D
  ) <-> (
    (
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
      D e. NN0
    )
    /\
    E. s e. Word NN0 E. t e. Word NN0
      (
        (
          (
            ( # ` s ) = ( A + 1 )
            /\
            ( # ` t ) = ( A + 1 )
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
          A. k e. ( 0 ..^ A )
            (
              0 < ( s ` k )
              /\
              (
                (
                  s ` ( k + 1 )
                ) = (
                  VERINA9NatSub
                    ( s ` k )
                    1
                )
                /\
                (
                  t ` ( k + 1 )
                ) = if (
                  (
                    VERINA9IsSumDivisibleBy
                      (
                        VERINA9NatSub
                          ( s ` k )
                          1
                      )
                      C
                  ) = 1 ,
                  ( ( t ` k ) + 1 ) ,
                  ( t ` k )
                )
              )
            )
          /\
          (
            ( s ` A ) = 0
            /\
            D = ( t ` A )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina9-count-go-definition $a |- (
    VERINA9CountGo A B C
  ) = (
    iota_ y e. NN0
      ( VERINA9CountGoGraph A B C y )
  ) $.
$}

verina9-program-definition $a |- (
  VERINA9CountSumDivisibleBy A B
) = (
  VERINA9CountGo A 0 B
) $.

${
  $d x A B $.

  verina9-filtered-count-definition $a |- (
    VERINA9FilteredCount A B
  ) = (
    # ` {
      x e. ( 0 ..^ A )
      |
      (
        x < A
        /\
        (
          VERINA9NatMod
            ( VERINA9SumOfDigits x )
            B
        ) = 0
      )
    }
  ) $.
$}

verina9-precondition-definition $a |- (
  VERINA9Pre A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  0 < B
) $.

verina9-postcondition-definition $a |- (
  VERINA9Post A B C
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
  (
    (
      VERINA9NatSub
        ( VERINA9FilteredCount A B )
        C
    ) = 0
    /\
    C <_ ( VERINA9FilteredCount A B )
  )
) $.

verina-advanced-9-count-sum-divisible-by
  $a |- A. n e. NN0 A. d e. NN0
    (
      ( VERINA9Pre n d )
      ->
      (
        VERINA9Post
          n
          d
          ( VERINA9CountSumDivisibleBy n d )
      )
    )
  $.
