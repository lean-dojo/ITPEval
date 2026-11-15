$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_74 (verina__metamath__verina_advanced_74), catalog title
  solution: the exact nested finite-list program sums, over every contiguous
  subarray, the square of its number of distinct natural values, together
  with its complete bounded-input correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, ran w is its entry set,
  and 0 ..^ ( # ` w ) is its complete index set.

  VERINA74NatMin and VERINA74NatSub preserve Lean's natural minimum and
  truncated subtraction. VERINA74Subarray is the exact helper
  (nums.drop i).take (j - i + 1), including arbitrary natural arguments:
  its start is clipped at the input length and its requested length is
  clipped at the remaining suffix. VERINA74ProgramSubarray and
  VERINA74PostSubarray are the implementation and postcondition local helper
  bindings, respectively.

  Folding a HashSet by insertion leaves exactly the set of entries of the
  source word, so VERINA74ProgramDistinct is the exact implementation
  distinctCount. The postcondition's duplicate-eliminating list fold also
  retains exactly one occurrence of every entry, so
  VERINA74PostDistinct has the same cardinality characterization. Hash-table
  capacity, bucket order, and the retained-list order are unobservable.
  VERINA74Square is the postcondition's square_local helper.

  VERINA74ProgramTotal reproduces the outer List.range n fold and, for every
  i, the inner List.range (n - i) fold. At inner index d it invokes the exact
  program subarray helper at i and i + d, squares its distinct count, and
  adds the value. Finite sums are definitionally equivalent to these
  natural-addition folds from zero. VERINA74Solution is therefore fixed by
  the executable computation independently of the postcondition.

  VERINA74ExpectedTotal separately reproduces the postcondition's nested
  folds using its local helpers. VERINA74Pre preserves the nonempty
  length-at-most-100 condition and every element bound from one through one
  hundred. VERINA74Post preserves the source's internal implication from
  that condition, the explicit nonnegativity conjunct, and equality with the
  expected sum. The final assertion has no additional precondition: exactly
  as in the Lean source, it states this implication-valued postcondition for
  every natural-number list. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINA74NatMin VERINA74NatSub
  VERINA74SubarrayGraph VERINA74Subarray
  VERINA74ProgramSubarray VERINA74PostSubarray
  VERINA74ProgramDistinct VERINA74PostDistinct VERINA74Square
  VERINA74Pre
  VERINA74ProgramTotal VERINA74Solution
  VERINA74ExpectedTotal VERINA74Post
$.

verina74-nat-min-syntax
  $a class ( VERINA74NatMin A B ) $.
verina74-nat-sub-syntax
  $a class ( VERINA74NatSub A B ) $.
verina74-subarray-graph-syntax
  $a wff ( VERINA74SubarrayGraph A B C D ) $.
verina74-subarray-syntax
  $a class ( VERINA74Subarray A B C ) $.
verina74-program-subarray-syntax
  $a class ( VERINA74ProgramSubarray A B C ) $.
verina74-post-subarray-syntax
  $a class ( VERINA74PostSubarray A B C ) $.
verina74-program-distinct-syntax
  $a class ( VERINA74ProgramDistinct A ) $.
verina74-post-distinct-syntax
  $a class ( VERINA74PostDistinct A ) $.
verina74-square-syntax
  $a class ( VERINA74Square A ) $.
verina74-precondition-syntax
  $a wff ( VERINA74Pre A ) $.
verina74-program-total-syntax
  $a class ( VERINA74ProgramTotal A ) $.
verina74-solution-syntax
  $a class ( VERINA74Solution A ) $.
verina74-expected-total-syntax
  $a class ( VERINA74ExpectedTotal A ) $.
verina74-postcondition-syntax
  $a wff ( VERINA74Post A B ) $.

verina74-nat-min-definition $a |- (
  VERINA74NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

verina74-nat-sub-definition $a |- (
  VERINA74NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d k A B C D $.

  verina74-subarray-graph-definition $a |- (
    VERINA74SubarrayGraph A B C D
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. Word NN0
      )
    )
    /\
    (
      (
        # ` D
      ) = (
        VERINA74NatMin
          (
            (
              VERINA74NatSub C B
            ) + 1
          )
          (
            VERINA74NatSub
              ( # ` A )
              ( VERINA74NatMin B ( # ` A ) )
          )
      )
      /\
      A. k e. ( 0 ..^ ( # ` D ) )
        (
          D ` k
        ) = (
          A ` (
            ( VERINA74NatMin B ( # ` A ) ) + k
          )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verina74-subarray-definition $a |- (
    VERINA74Subarray A B C
  ) = (
    iota_ y e. Word NN0
      ( VERINA74SubarrayGraph A B C y )
  ) $.
$}

verina74-program-subarray-definition $a |- (
  VERINA74ProgramSubarray A B C
) = (
  VERINA74Subarray A B C
) $.

verina74-post-subarray-definition $a |- (
  VERINA74PostSubarray A B C
) = (
  VERINA74Subarray A B C
) $.

verina74-program-distinct-definition $a |- (
  VERINA74ProgramDistinct A
) = (
  # ` ran A
) $.

verina74-post-distinct-definition $a |- (
  VERINA74PostDistinct A
) = (
  # ` ran A
) $.

verina74-square-definition $a |- (
  VERINA74Square A
) = (
  A x. A
) $.

${
  $d k A $.

  verina74-precondition-definition $a |- (
    VERINA74Pre A
  ) <-> (
    (
      A e. Word NN0
      /\
      (
        1 <_ ( # ` A )
        /\
        ( # ` A ) <_ ; 1 0 0
      )
    )
    /\
    A. k e. ( 0 ..^ ( # ` A ) )
      (
        1 <_ ( A ` k )
        /\
        ( A ` k ) <_ ; 1 0 0
      )
  ) $.
$}

${
  $d i d A $.

  verina74-program-total-definition $a |- (
    VERINA74ProgramTotal A
  ) = (
    sum_ i e. ( 0 ..^ ( # ` A ) )
      (
        sum_ d e. (
          0 ..^ (
            VERINA74NatSub ( # ` A ) i
          )
        )
          (
            (
              VERINA74ProgramDistinct
                (
                  VERINA74ProgramSubarray
                    A
                    i
                    ( i + d )
                )
            )
            x.
            (
              VERINA74ProgramDistinct
                (
                  VERINA74ProgramSubarray
                    A
                    i
                    ( i + d )
                )
            )
          )
      )
  ) $.
$}

verina74-solution-definition $a |- (
  VERINA74Solution A
) = (
  VERINA74ProgramTotal A
) $.

${
  $d i d A $.

  verina74-expected-total-definition $a |- (
    VERINA74ExpectedTotal A
  ) = (
    sum_ i e. ( 0 ..^ ( # ` A ) )
      (
        sum_ d e. (
          0 ..^ (
            VERINA74NatSub ( # ` A ) i
          )
        )
          (
            VERINA74Square
              (
                VERINA74PostDistinct
                  (
                    VERINA74PostSubarray
                      A
                      i
                      ( i + d )
                  )
              )
          )
      )
  ) $.
$}

verina74-postcondition-definition $a |- (
  VERINA74Post A B
) <-> (
  (
    A e. Word NN0
    /\
    B e. NN0
  )
  /\
  (
    ( VERINA74Pre A )
    ->
    (
      0 <_ B
      /\
      B = ( VERINA74ExpectedTotal A )
    )
  )
) $.

verina-advanced-74-solution $a |- A. w e. Word NN0
  (
    VERINA74Post
      w
      ( VERINA74Solution w )
  )
$.
