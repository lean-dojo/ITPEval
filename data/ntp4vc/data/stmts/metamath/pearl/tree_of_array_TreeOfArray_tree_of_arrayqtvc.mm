$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/tree_of_array_TreeOfArray_tree_of_arrayqtvc
  (ntp4vc__metamath__pearl/tree_of_array_TreeOfArray_tree_of_arrayqtvc):
  the tree-of-array verification condition states that conversion of an
  arbitrary finite array to a finite binary tree preserves inorder element
  order and gives exact size with powers-of-two height bounds. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source element carrier, and A is an arbitrary
  finite source array, represented exactly by SetMM Word U. T is exactly the
  source inductive carrier of finite U-labelled binary trees:
  NTP4VCEmpty and NTP4VCNode are disjoint injective tagged constructors, and
  closure, exhaustiveness, and structural induction exclude missing finite
  trees and extraneous non-well-founded values.

  S, H, and I are the complete recursive source definitions of tree size,
  height, and inorder traversal. NTP4VCSlice is the exact finite-list
  drop/take interval used by the exported source statement. NTP4VCPow2
  expresses the source natural-exponent power of two; all height exponents
  used by the verification condition are nonnegative under the exact
  recursive tree definitions and the displayed positive-size guards.
  NTP4VCHeightBound is only an abbreviation for the guarded lower and upper
  powers-of-two inequalities.

  The source let-bindings lo = 0, hi = length A, n = hi - lo, and
  h = height result are substituted definitionally. The redundant source
  index preconditions and the universal result scope are retained. Every
  element, finite-array, and finite-tree domain is unchanged. The final $a
  declaration is Metamath's native unproved statement encoding; every
  preceding $a is syntax or a faithful definition, and this database contains
  no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode NTP4VCMax
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice
  NTP4VCPow2 NTP4VCHeightBound
$.

ntp4vc-empty-syntax
  $a class NTP4VCEmpty $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B C ) $.
ntp4vc-max-syntax
  $a class ( NTP4VCMax A B ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax
  $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax
  $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax
  $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax
  $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax
  $a class ( NTP4VCSlice A B C ) $.
ntp4vc-pow2-syntax
  $a class ( NTP4VCPow2 A ) $.
ntp4vc-height-bound-syntax
  $a wff ( NTP4VCHeightBound A B ) $.

ntp4vc-empty-definition $a |- (
  NTP4VCEmpty
) = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

ntp4vc-max-definition $a |- (
  NTP4VCMax A B
) = if (
  A <_ B ,
  B ,
  A
) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-nat-sub-definition $a |- (
  NTP4VCNatSub A B
) = if (
  B <_ A ,
  ( A - B ) ,
  0
) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if (
  A <_ B ,
  A ,
  B
) $.

ntp4vc-slice-start-definition $a |- (
  NTP4VCSliceStart A B
) = (
  NTP4VCMin
    ( NTP4VCToNat B )
    ( # ` A )
) $.

ntp4vc-slice-len-definition $a |- (
  NTP4VCSliceLen A B C
) = (
  NTP4VCMin
    (
      NTP4VCNatSub
        ( NTP4VCToNat C )
        ( NTP4VCToNat B )
    )
    (
      ( # ` A )
      -
      ( NTP4VCSliceStart A B )
    )
) $.

${
  $d k A B C $.
  ntp4vc-slice-definition $a |- (
    NTP4VCSlice A B C
  ) = (
    k e. ( 0 ..^ ( NTP4VCSliceLen A B C ) )
      |-> A ` ( ( NTP4VCSliceStart A B ) + k )
  ) $.
$}

ntp4vc-pow2-definition $a |- (
  NTP4VCPow2 A
) = (
  2 ^ ( NTP4VCToNat A )
) $.

ntp4vc-height-bound-definition $a |- (
  ( NTP4VCHeightBound A B )
  <->
  (
    0 < A
    ->
    (
      ( NTP4VCPow2 ( B - 1 ) ) <_ A
      /\
      A < ( NTP4VCPow2 B )
    )
  )
) $.

${
  $d k l r s t x
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Arbitrary inhabited source carrier and exact finite tree datatype. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.

  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. x e. U A. r e. T
    ( NTP4VCNode l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. x e. U E. r e. T
        t = ( NTP4VCNode l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. x e. U A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l x r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Complete recursive source definitions of size, height, and inorder. $)
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.
  ntp4vc-height-function $e |- H e. ( ZZ ^m T ) $.
  ntp4vc-inorder-function $e |- I e. ( ( Word U ) ^m T ) $.

  ntp4vc-size-empty $e |- (
    S ` NTP4VCEmpty
  ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. x e. U A. r e. T
    (
      S ` ( NTP4VCNode l x r )
    )
    =
    (
      (
        1
        +
        ( S ` l )
      )
      +
      ( S ` r )
    ) $.

  ntp4vc-height-empty $e |- (
    H ` NTP4VCEmpty
  ) = 0 $.

  ntp4vc-height-node $e |- A. l e. T A. x e. U A. r e. T
    (
      H ` ( NTP4VCNode l x r )
    )
    =
    (
      1
      +
      (
        NTP4VCMax
          ( H ` l )
          ( H ` r )
      )
    ) $.

  ntp4vc-inorder-empty $e |- (
    I ` NTP4VCEmpty
  ) = (/) $.

  ntp4vc-inorder-node $e |- A. l e. T A. x e. U A. r e. T
    (
      I ` ( NTP4VCNode l x r )
    )
    =
    (
      ( I ` l )
      ++
      (
        <" x ">
        ++
        ( I ` r )
      )
    ) $.

  $( Arbitrary finite source array. $)
  ntp4vc-array-word $e |- A e. Word U $.

  ntp4vc-pearl-tree-of-array-tree-of-array-vc $a |- (
    (
      0 <_ 0
      /\
      (
        0 <_ ( # ` A )
        /\
        ( # ` A ) <_ ( # ` A )
      )
    )
    /\
    A. t e. T
      (
        (
          (
            S ` t
          ) = (
            ( # ` A )
            -
            0
          )
          /\
          (
            (
              I ` t
            ) = (
              NTP4VCSlice
                A
                0
                ( # ` A )
            )
            /\
            (
              NTP4VCHeightBound
                (
                  ( # ` A )
                  -
                  0
                )
                ( H ` t )
            )
          )
        )
        ->
        (
          (
            I ` t
          ) = (
            NTP4VCSlice
              A
              0
              ( # ` A )
          )
          /\
          (
            NTP4VCHeightBound
              ( S ` t )
              ( H ` t )
          )
        )
      )
  ) $.
$}
