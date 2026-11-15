$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/cursor_examples_TestListCursor_list_sumqtvc: the list-cursor summation
  verification condition initializes an empty visited prefix, preserves cursor
  permission and a decreasing remaining-length measure when one integer is
  appended, and equates the completed prefix sum with the full list sum. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. The source cursor type
  remains an arbitrary carrier A: B and C are its total visited and collection
  maps into Word ZZ, so distinct cursors with identical projections and every
  source cursor quantifier are retained.

  NTP4VCPermitted and NTP4VCComplete directly expand the source definitions.
  NTP4VCSum is the finite integer sum over all zero-based positions of a word.
  It is definitionally equivalent both to int.Sum.sum applied to get_closure
  from zero to the word length and to List.sum; get_closure's totalized
  out-of-bounds behavior is irrelevant because the finite range contains
  exactly the valid indices. Word concatenation with <" x "> is exactly source
  list append with the singleton [x].

  NTP4VCBranch renders the proposition-valued conditional as two exhaustive
  guarded cases. It retains the complete/noncomplete test, permission facts,
  both cursor quantifiers, the integer quantifier, collection equality, the
  singleton-extension premise, the nonnegative and strictly decreasing
  remaining-length obligations, the incremental sum equality, and final
  permission. Splitting typed parameters, definitions, and fact0--fact2 into
  scoped essential hypotheses is bidirectionally equivalent to the source
  theorem context. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c NTP4VCPermitted NTP4VCComplete NTP4VCSum NTP4VCBranch $.

ntp4vc-permitted-syntax
  $a wff ( NTP4VCPermitted A B C ) $.
ntp4vc-complete-syntax
  $a wff ( NTP4VCComplete A B C ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A ) $.
ntp4vc-branch-syntax
  $a wff ( NTP4VCBranch A B C D E ) $.

${
  $d i A B C $.

  ntp4vc-permitted-definition $a |- (
    ( NTP4VCPermitted A B C )
    <->
    (
      ( # ` ( B ` A ) ) <_ ( # ` ( C ` A ) )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` ( B ` A ) )
          )
          ->
          ( ( B ` A ) ` i ) = ( ( C ` A ) ` i )
        )
    )
  ) $.
$}

ntp4vc-complete-definition $a |- (
  ( NTP4VCComplete A B C )
  <->
  ( # ` ( B ` A ) ) = ( # ` ( C ` A ) )
) $.

${
  $d k A $.

  ntp4vc-sum-definition $a |- (
    NTP4VCSum A
  ) = sum_ k e. ( 0 ..^ ( # ` A ) ) ( A ` k ) $.
$}

${
  $d q x A B C D E $.

  $(
    Source arguments: A is the cursor carrier, B is visited, C is collection,
    D is the original list l, and E is the loop cursor c1.
  $)
  ntp4vc-branch-definition $a |- (
    ( NTP4VCBranch A B C D E )
    <->
    (
      (
        -. ( NTP4VCComplete E B C )
        /\
        (
          (
            -. ( NTP4VCComplete E B C )
            /\
            ( NTP4VCPermitted E B C )
          )
          /\
          A. q e. A
            (
              ( C ` q ) = ( C ` E )
              ->
              A. x e. ZZ
                (
                  (
                    ( B ` q ) = ( ( B ` E ) ++ <" x "> )
                    /\
                    ( NTP4VCPermitted q B C )
                  )
                  ->
                  (
                    (
                      0 <_
                        (
                          ( # ` D )
                          -
                          ( # ` ( B ` E ) )
                        )
                      /\
                      (
                        ( # ` D )
                        -
                        ( # ` ( B ` q ) )
                      )
                      <
                      (
                        ( # ` D )
                        -
                        ( # ` ( B ` E ) )
                      )
                    )
                    /\
                    (
                      (
                        ( NTP4VCSum ( B ` E ) )
                        +
                        x
                      )
                      =
                      ( NTP4VCSum ( B ` q ) )
                      /\
                      ( NTP4VCPermitted q B C )
                    )
                  )
                )
            )
        )
      )
      \/
      (
        ( NTP4VCComplete E B C )
        /\
        (
          NTP4VCSum ( B ` E )
        ) = ( NTP4VCSum D )
      )
    )
  ) $.
$}

${
  $d i k q r x A B C D E $.

  $( Source parameters: A is cursor ZZ, B is visited, C is collection,
     D is c, and E is l. $)
  ntp4vc-cursor-visited-function
    $e |- B e. ( ( Word ZZ ) ^m A ) $.
  ntp4vc-cursor-collection-function
    $e |- C e. ( ( Word ZZ ) ^m A ) $.
  ntp4vc-c-cursor $e |- D e. A $.
  ntp4vc-l-list $e |- E e. Word ZZ $.

  ntp4vc-fact0 $e |- ( NTP4VCPermitted D B C ) $.
  ntp4vc-fact1 $e |- ( B ` D ) = (/) $.
  ntp4vc-fact2 $e |- ( C ` D ) = E $.

  ntp4vc-pearl-cursor-examples-test-list-cursor-list-sum-vc $a |- (
    0 = ( NTP4VCSum ( B ` D ) )
    /\
    (
      ( NTP4VCPermitted D B C )
      /\
      A. r e. A
        (
          ( C ` r ) = ( C ` D )
          ->
          (
            ( NTP4VCPermitted r B C )
            ->
            (
              ( NTP4VCPermitted r B C )
              /\
              ( NTP4VCBranch A B C E r )
            )
          )
        )
    )
  ) $.
$}
