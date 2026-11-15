$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_30 (verina__metamath__verina_advanced_30), catalog title
  longestIncreasingStreak: the exact recursive scan returns the maximum
  length of a strictly increasing contiguous streak in an arbitrary finite
  integer list, with its range-based correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  i ..^ j is the half-open natural interval from i through j - 1.

  VERINA30RunGraph gives an exact operational graph for the source's local
  recursive auxiliary function at its sole call. The words c and m record
  currLen and maxLen before and after each consumed input entry. At index
  zero the source Option-valued prev is none; afterward it is some of the
  preceding entry, so the transition compares precisely the same adjacent
  integers. Each branch performs the source additions, resets, and Nat.max
  updates. The graph's output also applies the source empty-list branch's
  final Nat.max after all entries have been consumed.

  VERINA30LongestIncreasingStreak selects the unique output of that graph,
  independently of the postcondition. VERINA30Pre is the source True
  precondition together with the List Int input type.

  VERINA30Post reproduces the three source clauses. Its bounded existential
  is List.range(...).any for a maximal streak of exactly the returned length;
  its bounded universals are the two List.range(...).all expressions, and
  the inner existential is the nested List.any. SetMM subtraction on natural
  operands is ordinary integer subtraction, not Lean's truncated Nat.sub.
  The uses are nevertheless equivalent under their guards: B - 1 occurs
  under 0 < B; k - 1 and s - 1 matter only when their minuends are positive;
  s + B is positive under 0 < B, so ( s + B ) - 1 is nonnegative and agrees
  with Nat.sub; and when B exceeds # ` A, the relevant SetMM intervals are
  empty, while the sole index zero in the source range
  (nums.length - result + 1) cannot satisfy
  start + result <= nums.length. Thus every selected branch and satisfiable
  bounded quantifier has the same meaning.
  Every potentially out-of-range get! lookup is behind the same bound or
  disjunction that makes its value irrelevant, while all semantically
  selected lookups are valid.

  The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  postcondition predicate. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINA30RunGraph VERINA30LongestIncreasingStreak
  VERINA30Pre VERINA30Post
$.

verina30-run-graph-syntax
  $a wff ( VERINA30RunGraph A B ) $.
verina30-longest-increasing-streak-syntax
  $a class ( VERINA30LongestIncreasingStreak A ) $.
verina30-precondition-syntax
  $a wff ( VERINA30Pre A ) $.
verina30-postcondition-syntax
  $a wff ( VERINA30Post A B ) $.

${
  $d k c m A B $.

  verina30-run-graph-definition $a |- (
    VERINA30RunGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    E. c e. Word NN0
      E. m e. Word NN0
        (
          (
            (
              ( # ` c ) = ( ( # ` A ) + 1 )
              /\
              ( # ` m ) = ( ( # ` A ) + 1 )
            )
            /\
            (
              ( c ` 0 ) = 0
              /\
              ( m ` 0 ) = 0
            )
          )
          /\
          (
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                (
                  c ` ( k + 1 )
                ) = if (
                  k = 0 ,
                  1 ,
                  if (
                    ( A ` ( k - 1 ) ) < ( A ` k ) ,
                    ( ( c ` k ) + 1 ) ,
                    1
                  )
                )
                /\
                (
                  m ` ( k + 1 )
                ) = if (
                  k = 0 ,
                  if (
                    ( m ` k ) < 1 ,
                    1 ,
                    ( m ` k )
                  ) ,
                  if (
                    ( A ` ( k - 1 ) ) < ( A ` k ) ,
                    if (
                      ( m ` k ) < ( ( c ` k ) + 1 ) ,
                      ( ( c ` k ) + 1 ) ,
                      ( m ` k )
                    ) ,
                    if (
                      ( m ` k ) < ( c ` k ) ,
                      ( c ` k ) ,
                      ( m ` k )
                    )
                  )
                )
              )
            /\
            B = if (
              ( c ` ( # ` A ) ) < ( m ` ( # ` A ) ) ,
              ( m ` ( # ` A ) ) ,
              ( c ` ( # ` A ) )
            )
          )
        )
  ) $.
$}

${
  $d y A $.

  verina30-longest-increasing-streak-definition $a |- (
    VERINA30LongestIncreasingStreak A
  ) = (
    iota_ y e. NN0
      ( VERINA30RunGraph A y )
  ) $.
$}

verina30-precondition-definition $a |- (
  VERINA30Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i s A B $.

  verina30-postcondition-definition $a |- (
    VERINA30Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      (
        A = (/)
        ->
        B = 0
      )
      /\
      (
        0 < B
        ->
        E. s e. (
          0 ..^ ( ( ( # ` A ) - B ) + 1 )
        )
          (
            (
              ( s + B ) <_ ( # ` A )
              /\
              A. i e. ( 0 ..^ ( B - 1 ) )
                (
                  A ` ( s + i )
                ) < (
                  A ` ( ( s + i ) + 1 )
                )
            )
            /\
            (
              (
                s = 0
                \/
                ( A ` s ) <_ ( A ` ( s - 1 ) )
              )
              /\
              (
                ( s + B ) = ( # ` A )
                \/
                (
                  A ` ( s + B )
                ) <_ (
                  A ` ( ( s + B ) - 1 )
                )
              )
            )
          )
      )
      /\
      A. s e. ( 0 ..^ ( ( # ` A ) - B ) )
        E. i e. ( 0 ..^ B )
          (
            ( # ` A ) <_ ( ( s + i ) + 1 )
            \/
            (
              A ` ( ( s + i ) + 1 )
            ) <_ (
              A ` ( s + i )
            )
          )
    )
  ) $.
$}

verina-advanced-30-longest-increasing-streak
  $a |- A. w e. Word ZZ
    (
      ( VERINA30Pre w )
      ->
      (
        VERINA30Post
          w
          ( VERINA30LongestIncreasingStreak w )
      )
    )
  $.
