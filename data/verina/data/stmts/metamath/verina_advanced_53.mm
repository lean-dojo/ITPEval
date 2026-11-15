$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_53 (verina__metamath__verina_advanced_53), catalog title
  minimumRightShifts: the exact bounded search through successive right
  rotations of an arbitrary finite distinct integer list returns the least
  rotation count making it nondecreasing, or -1 when none does. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its natural-number
  length, w ` k is zero-based lookup, and 0 ..^ ( # ` w ) is its complete
  index set. The empty word (/) represents the empty list.

  VERINA53Nodup is List.Nodup, and VERINA53Sorted is both the Boolean
  isSortedAux computation and List.Pairwise with integer <=; on finite lists
  those characterizations are equivalent. VERINA53Pre is the source
  precondition together with the input type.

  VERINA53RightShiftOnceGraph moves the last element of a nonempty word to
  the front and fixes the empty word, exactly matching the reverse-based
  rightShiftOnce helper. VERINA53RightShiftOnce selects its unique output.
  VERINA53RotateGraph records exactly k successive applications of that
  helper, and VERINA53Rotate selects the unique result. This is precisely
  List.rotateRight k, including empty words and counts at least the length.

  VERINA53CheckGraph is the exact operational graph of checkShifts for all
  arbitrary captured lengths, starting counts, and current lists. Its trace
  advances only while the current count is below the captured length and the
  current list is not sorted. It stops at the first state where the source
  recursion stops, returning -1 when count is at least the length before the
  sortedness test, and otherwise returning that count. VERINA53CheckShifts
  selects this unique integer result.

  VERINA53MinimumRightShifts preserves the two initial source tests and then
  invokes checkShifts at count one on the first right shift. The proof-valued
  precondition argument is computationally unused and is omitted from the
  target function.

  VERINA53Post is the source postcondition. Length at most one forces zero.
  Otherwise, a nonnegative result is below the length, sorts that rotation,
  and has no smaller sorting rotation; result -1 means no rotation count
  below the length sorts the input. On an integer result, membership in NN0
  is exactly the source result >= 0 condition and makes result.toNat equal
  to the same number. The propositionally unused proof argument is omitted.
  The final $a declaration is the source correctness proposition. Every
  earlier $a is syntax or a faithful definition, and this database has no
  $p declaration.
$)

$c
  VERINA53Nodup VERINA53Sorted VERINA53Pre
  VERINA53RightShiftOnceGraph VERINA53RightShiftOnce
  VERINA53RotateGraph VERINA53Rotate
  VERINA53CheckGraph VERINA53CheckShifts
  VERINA53MinimumRightShifts VERINA53Post
$.

verina53-nodup-syntax
  $a wff ( VERINA53Nodup A ) $.
verina53-sorted-syntax
  $a wff ( VERINA53Sorted A ) $.
verina53-precondition-syntax
  $a wff ( VERINA53Pre A ) $.
verina53-right-shift-once-graph-syntax
  $a wff ( VERINA53RightShiftOnceGraph A B ) $.
verina53-right-shift-once-syntax
  $a class ( VERINA53RightShiftOnce A ) $.
verina53-rotate-graph-syntax
  $a wff ( VERINA53RotateGraph A B C ) $.
verina53-rotate-syntax
  $a class ( VERINA53Rotate A B ) $.
verina53-check-graph-syntax
  $a wff ( VERINA53CheckGraph A B C D ) $.
verina53-check-shifts-syntax
  $a class ( VERINA53CheckShifts A B C ) $.
verina53-minimum-right-shifts-syntax
  $a class ( VERINA53MinimumRightShifts A ) $.
verina53-postcondition-syntax
  $a wff ( VERINA53Post A B ) $.

${
  $d i j A $.

  verina53-nodup-definition $a |- (
    VERINA53Nodup A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) =/= ( A ` j )
          )
    )
  ) $.
$}

${
  $d i j A $.

  verina53-sorted-definition $a |- (
    VERINA53Sorted A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) <_ ( A ` j )
          )
    )
  ) $.
$}

verina53-precondition-definition $a |- (
  VERINA53Pre A
) <-> (
  (
    A e. Word ZZ
    /\
    ( VERINA53Nodup A )
  )
) $.

${
  $d j A B $.

  verina53-right-shift-once-graph-definition $a |- (
    VERINA53RightShiftOnceGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      (
        (
          ( # ` A ) = 0
          /\
          B = (/)
        )
        \/
        (
          0 < ( # ` A )
          /\
          (
            ( B ` 0 ) = ( A ` ( ( # ` A ) - 1 ) )
            /\
            A. j e. ( 0 ..^ ( ( # ` A ) - 1 ) )
              ( B ` ( j + 1 ) ) = ( A ` j )
          )
        )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina53-right-shift-once-definition $a |- (
    VERINA53RightShiftOnce A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA53RightShiftOnceGraph A y )
  ) $.
$}

${
  $d j t A B C $.

  verina53-rotate-graph-definition $a |- (
    VERINA53RotateGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = ( B + 1 )
          /\
          ( t ` 0 ) = A
        )
        /\
        (
          A. j e. ( 0 ..^ B )
            (
              t ` ( j + 1 )
            ) = (
              VERINA53RightShiftOnce ( t ` j )
            )
          /\
          C = ( t ` B )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina53-rotate-definition $a |- (
    VERINA53Rotate A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA53RotateGraph A B y )
  ) $.
$}

${
  $d j q t A B C D $.

  verina53-check-graph-definition $a |- (
    VERINA53CheckGraph A B C D
  ) <-> (
    (
      (
        (
          A e. NN0
          /\
          B e. NN0
        )
        /\
        C e. Word ZZ
      )
      /\
      D e. ZZ
    )
    /\
    E. q e. NN0
      E. t e. Word ( Word ZZ )
        (
          (
            ( # ` t ) = ( q + 1 )
            /\
            ( t ` 0 ) = C
          )
          /\
          (
            A. j e. ( 0 ..^ q )
              (
                (
                  ( B + j ) < A
                  /\
                  -. ( VERINA53Sorted ( t ` j ) )
                )
                /\
                (
                  t ` ( j + 1 )
                ) = (
                  VERINA53RightShiftOnce ( t ` j )
                )
              )
            /\
            (
              (
                A <_ ( B + q )
                /\
                D = ( -u 1 )
              )
              \/
              (
                ( B + q ) < A
                /\
                (
                  ( VERINA53Sorted ( t ` q ) )
                  /\
                  D = ( B + q )
                )
              )
            )
          )
        )
  ) $.
$}

${
  $d y A B C $.

  verina53-check-shifts-definition $a |- (
    VERINA53CheckShifts A B C
  ) = (
    iota_ y e. ZZ
      ( VERINA53CheckGraph A B C y )
  ) $.
$}

verina53-minimum-right-shifts-definition $a |- (
  VERINA53MinimumRightShifts A
) = if (
  ( # ` A ) <_ 1 ,
  0 ,
  if (
    ( VERINA53Sorted A ) ,
    0 ,
    (
      VERINA53CheckShifts
        ( # ` A )
        1
        ( VERINA53RightShiftOnce A )
    )
  )
) $.

${
  $d j k A B $.

  verina53-postcondition-definition $a |- (
    VERINA53Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      (
        ( # ` A ) <_ 1
        /\
        B = 0
      )
      \/
      (
        1 < ( # ` A )
        /\
        (
          (
            (
              B e. NN0
              /\
              B < ( # ` A )
            )
            /\
            (
              ( VERINA53Sorted ( VERINA53Rotate A B ) )
              /\
              A. j e. ( 0 ..^ B )
                -. ( VERINA53Sorted ( VERINA53Rotate A j ) )
            )
          )
          \/
          (
            B = ( -u 1 )
            /\
            A. k e. ( 0 ..^ ( # ` A ) )
              -. ( VERINA53Sorted ( VERINA53Rotate A k ) )
          )
        )
      )
    )
  ) $.
$}

verina-advanced-53-minimum-right-shifts
  $a |- A. w e. Word ZZ
    (
      ( VERINA53Pre w )
      ->
      (
        VERINA53Post
          w
          ( VERINA53MinimumRightShifts w )
      )
    )
  $.
