$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/tree_of_list_TreeOfList_tree_of_listqtvc
  (ntp4vc__metamath__pearl/tree_of_list_TreeOfList_tree_of_listqtvc):
  the tree-of-list verification condition states that conversion of an
  arbitrary finite list to a finite binary tree preserves inorder element
  order and the guarded powers-of-two height bound. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source element carrier, and A is an arbitrary
  finite source list, represented exactly by SetMM Word U. T is exactly the
  source inductive carrier of finite U-labelled binary trees:
  NTP4VCEmpty and NTP4VCNode are disjoint injective tagged constructors, and
  closure, exhaustiveness, and structural induction exclude missing finite
  trees and extraneous non-well-founded values.

  S, H, and I are the complete recursive source definitions of tree size,
  height, and inorder traversal. NTP4VCPow2 expresses the exported
  natural-exponent interpretation of Why3 integer power, and
  NTP4VCHeightBound abbreviates the source guarded lower and upper
  powers-of-two inequalities.

  The source let-binding o1 = length A is substituted definitionally.
  The auxiliary result tree and residual list remain universally quantified
  inside their original scope, and the complete auxiliary postcondition is
  retained as the antecedent of the wrapper conclusion. Every element,
  finite-list, finite-tree, and integer domain is unchanged. The final $a
  declaration is Metamath's native unproved statement encoding; every
  preceding $a is syntax or a faithful definition, and this database contains
  no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode NTP4VCMax
  NTP4VCToNat NTP4VCPow2 NTP4VCHeightBound
$.

ntp4vc-empty-syntax
  $a class NTP4VCEmpty $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B C ) $.
ntp4vc-max-syntax
  $a class ( NTP4VCMax A B ) $.
ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
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
  $d l q r s t x
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

  $( Arbitrary finite source list. $)
  ntp4vc-list-word $e |- A e. Word U $.

  ntp4vc-pearl-tree-of-list-tree-of-list-tree-of-list-vc $a |- (
    (
      0 <_ ( # ` A )
      /\
      ( # ` A ) <_ ( # ` A )
    )
    /\
    A. t e. T A. q e. Word U
      (
        (
          (
            (
              I ` t
            )
            ++
            q
          ) = A
          /\
          (
            (
              S ` t
            ) = (
              # ` A
            )
            /\
            (
              NTP4VCHeightBound
                ( # ` A )
                ( H ` t )
            )
          )
        )
        ->
        (
          (
            I ` t
          ) = A
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
