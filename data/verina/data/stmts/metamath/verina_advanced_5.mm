$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_5 (verina__metamath__verina_advanced_5), catalog title
  addTwoNumbers: exact carry-propagating addition of two nonempty canonical
  little-endian decimal natural-number lists returns their canonical decimal
  sum with the stated value and digit-range contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA5ListToNat is the source little-endian base-ten evaluation helper:
  the finite sum of digit[k] times ten to the kth power is definitionally
  equivalent to listToNat [] = 0 and
  listToNat (d :: ds) = d + 10 * listToNat ds.
  VERINA5GetLast reproduces List.getLast! on natural-number lists, including
  its default value zero on the empty list. VERINA5Pre preserves both
  nonemptiness clauses, every digit bound, and both canonical-last-digit
  clauses of addTwoNumbers_precond.

  VERINA5DigitAt returns the indexed digit when present and zero after the end
  of a word. VERINA5AddAuxGraph is an exact finite execution graph of the
  local recursive addAux. Its natural-number trace begins at the supplied
  carry. At each position below the larger input length it adds both present
  digits and the current carry, emits the remainder modulo ten, and records
  the quotient by ten as the next carry. After all input digits are consumed,
  the output stops when the carry is zero and otherwise appends that carry,
  exactly matching the source's [], [] branch. This single indexed recurrence
  is bidirectionally equivalent to the source's four exhaustive list-pattern
  branches, including either one-sided remainder.

  VERINA5AddAux selects the unique word fixed by that graph, and
  VERINA5AddTwoNumbers calls it with initial carry zero. Thus the executable
  result is fixed independently of the postcondition. VERINA5Post preserves
  the source value equality, every output digit bound, and its exact
  no-leading-zero disjunction. The Lean proof-valued precondition argument is
  computationally unused by the implementation and propositionally unused by
  the postcondition body, so it is represented by the explicit final
  precondition antecedent rather than as data. The final $a declaration is
  the source correctness proposition. Every earlier $a is syntax or a
  faithful definition, and this database has no $p declaration.
$)

$c
  VERINA5NatMax
  VERINA5ListToNat VERINA5GetLast
  VERINA5Pre
  VERINA5DigitAt
  VERINA5AddAuxGraph VERINA5AddAux VERINA5AddTwoNumbers
  VERINA5Post
$.

verina5-nat-max-syntax
  $a class ( VERINA5NatMax A B ) $.
verina5-list-to-nat-syntax
  $a class ( VERINA5ListToNat A ) $.
verina5-get-last-syntax
  $a class ( VERINA5GetLast A ) $.
verina5-precondition-syntax
  $a wff ( VERINA5Pre A B ) $.
verina5-digit-at-syntax
  $a class ( VERINA5DigitAt A B ) $.
verina5-add-aux-graph-syntax
  $a wff ( VERINA5AddAuxGraph A B C D ) $.
verina5-add-aux-syntax
  $a class ( VERINA5AddAux A B C ) $.
verina5-add-two-numbers-syntax
  $a class ( VERINA5AddTwoNumbers A B ) $.
verina5-postcondition-syntax
  $a wff ( VERINA5Post A B C ) $.

verina5-nat-max-definition $a |- (
  VERINA5NatMax A B
) = if (
  B < A ,
  A ,
  B
) $.

${
  $d k A $.

  verina5-list-to-nat-definition $a |- (
    VERINA5ListToNat A
  ) = (
    sum_ k e. ( 0 ..^ ( # ` A ) )
      ( ( A ` k ) x. ( ; 1 0 ^ k ) )
  ) $.
$}

verina5-get-last-definition $a |- (
  VERINA5GetLast A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  ( A ` ( ( # ` A ) - 1 ) )
) $.

${
  $d k A B $.

  verina5-precondition-definition $a |- (
    VERINA5Pre A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word NN0
    )
    /\
    (
      (
        0 < ( # ` A )
        /\
        0 < ( # ` B )
      )
      /\
      (
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            ( A ` k ) < ; 1 0
          /\
          A. k e. ( 0 ..^ ( # ` B ) )
            ( B ` k ) < ; 1 0
        )
        /\
        (
          (
            ( VERINA5GetLast A ) =/= 0
            \/
            A = <" 0 ">
          )
          /\
          (
            ( VERINA5GetLast B ) =/= 0
            \/
            B = <" 0 ">
          )
        )
      )
    )
  ) $.
$}

verina5-digit-at-definition $a |- (
  VERINA5DigitAt A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k n s A B C D $.

  verina5-add-aux-graph-definition $a |- (
    VERINA5AddAuxGraph A B C D
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. Word NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. Word NN0
      )
    )
    /\
    E. n e. NN0 E. s e. Word NN0
      (
        (
          n = ( VERINA5NatMax ( # ` A ) ( # ` B ) )
          /\
          (
            ( # ` s ) = ( n + 1 )
            /\
            ( s ` 0 ) = C
          )
        )
        /\
        (
          (
            ( # ` D ) = if (
              ( s ` n ) = 0 ,
              n ,
              ( n + 1 )
            )
            /\
            A. k e. ( 0 ..^ n )
              (
                (
                  D ` k
                ) = (
                  (
                    (
                      ( VERINA5DigitAt A k )
                      +
                      ( VERINA5DigitAt B k )
                    )
                    +
                    ( s ` k )
                  ) mod ; 1 0
                )
                /\
                (
                  s ` ( k + 1 )
                ) = (
                  |_ ` (
                    (
                      (
                        (
                          VERINA5DigitAt A k
                        )
                        +
                        (
                          VERINA5DigitAt B k
                        )
                      )
                      +
                      ( s ` k )
                    )
                    /
                    ; 1 0
                  )
                )
              )
          )
          /\
          (
            ( s ` n ) =/= 0
            ->
            ( D ` n ) = ( s ` n )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina5-add-aux-definition $a |- (
    VERINA5AddAux A B C
  ) = (
    iota_ y e. Word NN0
      ( VERINA5AddAuxGraph A B C y )
  ) $.
$}

verina5-add-two-numbers-definition $a |- (
  VERINA5AddTwoNumbers A B
) = (
  VERINA5AddAux A B 0
) $.

${
  $d k A B C $.

  verina5-postcondition-definition $a |- (
    VERINA5Post A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      (
        ( VERINA5ListToNat C )
        =
        (
          ( VERINA5ListToNat A )
          +
          ( VERINA5ListToNat B )
        )
      )
      /\
      (
        A. k e. ( 0 ..^ ( # ` C ) )
          ( C ` k ) < ; 1 0
        /\
        (
          ( VERINA5GetLast C ) =/= 0
          \/
          (
            A = <" 0 ">
            /\
            (
              B = <" 0 ">
              /\
              C = <" 0 ">
            )
          )
        )
      )
    )
  ) $.
$}

verina-advanced-5-add-two-numbers $a |-
  A. u e. Word NN0 A. v e. Word NN0
    (
      ( VERINA5Pre u v )
      ->
      (
        VERINA5Post
          u
          v
          ( VERINA5AddTwoNumbers u v )
      )
    )
$.
