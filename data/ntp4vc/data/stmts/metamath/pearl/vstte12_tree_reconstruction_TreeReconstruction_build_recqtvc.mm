$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc
  (ntp4vc__metamath__pearl/vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc):
  the VSTTE 2012 recursive tree-reconstruction verification condition covers
  failure, leaf recognition, lexicographic descent, and preservation of the
  leaf-depth specification for finite binary trees. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  T is exactly the source inductive carrier of finite binary trees.
  NTP4VCLeaf and NTP4VCNode are disjoint injective tagged constructors;
  closure, exhaustiveness, and structural induction exclude missing finite
  trees, extraneous values, and non-well-founded constructor objects.

  F is the source integer-indexed leaf-depth function into finite integer
  words. Its Leaf and Node equations are the complete recursive definition:
  a leaf contributes its current depth, while a node concatenates the depth
  words of both children at depth d + 1. SetMM Word ZZ is exactly the source
  type of arbitrary finite integer lists, and NTP4VCCons is exact list cons.
  NTP4VCHead is the exported totalized list head with integer default zero.

  NTP4VCFail, NTP4VCMeasure, NTP4VCAfterLeft, NTP4VCRecursive,
  NTP4VCConsCase, and NTP4VCBuildRec only factor the original nested
  verification condition; every helper that uses the tree carrier T or depth
  function F receives it explicitly. Expanding their biconditional definitions
  recovers every source tree, integer, and finite-list quantifier, both
  recursive continuations, both failure continuations, and the complete
  lexicographic variant. The list match is represented by its exact empty and
  cons cases.
  The nested proposition-valued conditionals are represented by the
  equivalent trichotomy h < d, h = d, or d < h over the source integers.
  Let-bound occurrences of d + 1 are substituted definitionally.

  The final $a declaration is Metamath's native unproved statement encoding;
  every preceding $a is syntax or a faithful definition, and this database
  contains no $p proof declaration.
$)

$c
  NTP4VCLeaf NTP4VCNode NTP4VCCons NTP4VCHead
  NTP4VCFail NTP4VCMeasure NTP4VCAfterLeft
  NTP4VCRecursive NTP4VCConsCase NTP4VCBuildRec
$.

ntp4vc-leaf-syntax
  $a class NTP4VCLeaf $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B ) $.
ntp4vc-cons-syntax
  $a class ( NTP4VCCons A B ) $.
ntp4vc-head-syntax
  $a class ( NTP4VCHead A ) $.

ntp4vc-fail-syntax
  $a wff ( NTP4VCFail A B C D ) $.
ntp4vc-measure-syntax
  $a wff ( NTP4VCMeasure A B C D ) $.
ntp4vc-after-left-syntax
  $a wff ( NTP4VCAfterLeft A B C D E F G ) $.
ntp4vc-recursive-syntax
  $a wff ( NTP4VCRecursive A B C D E ) $.
ntp4vc-cons-case-syntax
  $a wff ( NTP4VCConsCase A B C D E F ) $.
ntp4vc-build-rec-syntax
  $a wff ( NTP4VCBuildRec A B C D ) $.

ntp4vc-leaf-definition $a |- (
  NTP4VCLeaf
) = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B
) = <. 1 , <. A , B >. >. $.

ntp4vc-cons-definition $a |- (
  NTP4VCCons A B
) = (
  <" A "> ++ B
) $.

ntp4vc-head-definition $a |- (
  NTP4VCHead A
) = if (
  0 < ( # ` A ) ,
  ( A ` 0 ) ,
  0
) $.

${
  $d h l q r s t x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  ntp4vc-fail-definition $a |- (
    ( NTP4VCFail T F A B )
    <->
    A. x e. T A. q e. Word ZZ
      -.
      (
        (
          F ` <. B , x >.
        )
        ++
        q
      )
      =
      A
  ) $.

  ntp4vc-measure-definition $a |- (
    ( NTP4VCMeasure A B C D )
    <->
    (
      (
        0 <_ ( # ` A )
        /\
        ( # ` B ) < ( # ` A )
      )
      \/
      (
        ( # ` A ) = ( # ` B )
        /\
        (
          0 <_ ( C - D )
          /\
          (
            ( NTP4VCHead B ) - ( D + 1 )
          )
          <
          ( C - D )
        )
      )
    )
  ) $.

  ntp4vc-after-left-definition $a |- (
    ( NTP4VCAfterLeft T F A B C D E )
    <->
    (
      ( NTP4VCMeasure A E C B )
      /\
      (
        A. r e. T A. q e. Word ZZ
          (
            E
            =
            (
              (
                F ` <. ( B + 1 ) , r >.
              )
              ++
              q
            )
            ->
            A
            =
            (
              (
                F `
                <. B , ( NTP4VCNode D r ) >.
              )
              ++
              q
            )
          )
        /\
        (
          ( NTP4VCFail T F E ( B + 1 ) )
          ->
          ( NTP4VCFail T F A B )
        )
      )
    )
  ) $.

  ntp4vc-recursive-definition $a |- (
    ( NTP4VCRecursive T F A B C )
    <->
    (
      (
        0 <_ ( C - B )
        /\
        (
          C - ( B + 1 )
        )
        <
        ( C - B )
      )
      /\
      (
        A. l e. T A. s e. Word ZZ
          (
            A
            =
            (
              (
                F ` <. ( B + 1 ) , l >.
              )
              ++
              s
            )
            ->
            ( NTP4VCAfterLeft T F A B C l s )
          )
        /\
        (
          ( NTP4VCFail T F A ( B + 1 ) )
          ->
          ( NTP4VCFail T F A B )
        )
      )
    )
  ) $.

  ntp4vc-cons-case-definition $a |- (
    ( NTP4VCConsCase T F A B C D )
    <->
    (
      (
        C < B
        /\
        ( NTP4VCFail T F A B )
      )
      \/
      (
        (
          C = B
          /\
          A
          =
          (
            (
              F ` <. B , NTP4VCLeaf >.
            )
            ++
            D
          )
        )
        \/
        (
          B < C
          /\
          ( NTP4VCRecursive T F A B C )
        )
      )
    )
  ) $.

  ntp4vc-build-rec-definition $a |- (
    ( NTP4VCBuildRec T F A B )
    <->
    (
      (
        A = (/)
        /\
        ( NTP4VCFail T F A B )
      )
      \/
      E. h e. ZZ E. t e. Word ZZ
        (
          A = ( NTP4VCCons h t )
          /\
          ( NTP4VCConsCase T F A B h t )
        )
    )
  ) $.

  $( Exact finite inductive binary-tree carrier. $)
  ntp4vc-tree-leaf-closure $e |- NTP4VCLeaf e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. r e. T
    ( NTP4VCNode l r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCLeaf
      \/
      E. l e. T E. r e. T
        t = ( NTP4VCNode l r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCLeaf e. s
        /\
        A. l e. T A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Complete recursive definition of leaf depths over all integer offsets. $)
  ntp4vc-depths-function $e |-
    F e. ( ( Word ZZ ) ^m ( ZZ X. T ) ) $.

  ntp4vc-depths-leaf $e |- A. h e. ZZ
    (
      F ` <. h , NTP4VCLeaf >.
    ) = <" h "> $.

  ntp4vc-depths-node $e |- A. h e. ZZ A. l e. T A. r e. T
    (
      F ` <. h , ( NTP4VCNode l r ) >.
    )
    =
    (
      (
        F ` <. ( h + 1 ) , l >.
      )
      ++
      (
        F ` <. ( h + 1 ) , r >.
      )
    ) $.

  $( Arbitrary source input list and starting depth. $)
  ntp4vc-input-word $e |- A e. Word ZZ $.
  ntp4vc-input-depth $e |- B e. ZZ $.

  ntp4vc-pearl-vstte12-tree-reconstruction-tree-reconstruction-build-rec-vc
    $a |- ( NTP4VCBuildRec T F A B ) $.
$}
