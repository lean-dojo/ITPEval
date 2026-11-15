$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_69 (verina__metamath__verina_advanced_69), catalog title
  searchInsert: the exact left-to-right search of a strictly increasing
  finite integer list returns the first index whose entry is at least the
  target, or the list length when every entry is smaller, together with its
  bounds and insertion-position correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its natural-number
  length, w ` k is zero-based lookup, and 0 ..^ ( # ` w ) is its complete
  index set.

  VERINA69GetD is Lean List.get! on an integer list, including its integer
  zero default outside the list. VERINA69HelperGraph gives the exact local
  helper computation for arbitrary remaining-list, target, and starting-index
  arguments. Its offset p is the first position whose entry is at least the
  target, or the remaining-list length when there is no such position, and
  the returned index is the starting index plus p. VERINA69Helper selects the
  unique result of this graph.

  VERINA69SearchInsert retains the source's explicit empty-list result zero;
  on a nonempty input it invokes the helper with starting index zero. Thus the
  program result is fixed independently of the postcondition and the graph
  permits no extra outputs.

  VERINA69Pairwise is exactly List.Pairwise with integer <.
  VERINA69Pre retains that strict-increase precondition and the typed source
  arguments. VERINA69Post preserves result <= length, the List.range result
  all-test requiring every earlier defaulted lookup to be below the target,
  and the implication requiring the selected lookup to be at least the target
  when the result is in bounds. The proof-valued precondition argument is
  computationally and propositionally unused and is represented by the
  explicit antecedent of the final correctness assertion. Every earlier $a is
  syntax or a faithful definition required by this rendering, and this root
  statement file has no $p declaration.
$)

$c
  VERINA69GetD
  VERINA69HelperGraph VERINA69Helper
  VERINA69SearchInsert
  VERINA69Pairwise VERINA69Pre VERINA69Post
$.

verina69-get-default-syntax
  $a class ( VERINA69GetD A B ) $.
verina69-helper-graph-syntax
  $a wff ( VERINA69HelperGraph A B C D ) $.
verina69-helper-syntax
  $a class ( VERINA69Helper A B C ) $.
verina69-search-insert-syntax
  $a class ( VERINA69SearchInsert A B ) $.
verina69-pairwise-syntax
  $a wff ( VERINA69Pairwise A ) $.
verina69-precondition-syntax
  $a wff ( VERINA69Pre A B ) $.
verina69-postcondition-syntax
  $a wff ( VERINA69Post A B C ) $.

verina69-get-default-definition $a |- (
  VERINA69GetD A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d j p A B C D $.

  verina69-helper-graph-definition $a |- (
    VERINA69HelperGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
        )
        /\
        C e. NN0
      )
      /\
      D e. NN0
    )
    /\
    E. p e. NN0
      (
        p <_ ( # ` A )
        /\
        (
          (
            A. j e. ( 0 ..^ p )
              ( A ` j ) < B
            /\
            (
              p < ( # ` A )
              ->
              B <_ ( A ` p )
            )
          )
          /\
          D = ( C + p )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina69-helper-definition $a |- (
    VERINA69Helper A B C
  ) = (
    iota_ y e. NN0
      ( VERINA69HelperGraph A B C y )
  ) $.
$}

verina69-search-insert-definition $a |- (
  VERINA69SearchInsert A B
) = if (
  A = (/) ,
  0 ,
  ( VERINA69Helper A B 0 )
) $.

${
  $d i j A $.

  verina69-pairwise-definition $a |- (
    VERINA69Pairwise A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) < ( A ` j )
          )
    )
  ) $.
$}

verina69-precondition-definition $a |- (
  VERINA69Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  ( VERINA69Pairwise A )
) $.

${
  $d i A B C $.

  verina69-postcondition-definition $a |- (
    VERINA69Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. NN0
    )
    /\
    (
      C <_ ( # ` A )
      /\
      (
        A. i e. ( 0 ..^ C )
          ( VERINA69GetD A i ) < B
        /\
        (
          C < ( # ` A )
          ->
          B <_ ( VERINA69GetD A C )
        )
      )
    )
  ) $.
$}

${
  $d t w $.

  verina-advanced-69-search-insert $a |- A. w e. Word ZZ
    A. t e. ZZ
      (
        ( VERINA69Pre w t )
        ->
        (
          VERINA69Post
            w
            t
            ( VERINA69SearchInsert w t )
        )
      )
  $.
$}
