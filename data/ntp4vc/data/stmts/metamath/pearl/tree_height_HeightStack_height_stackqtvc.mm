$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/tree_height_HeightStack_height_stackqtvc
  (ntp4vc__metamath__pearl/tree_height_HeightStack_height_stackqtvc):
  the explicit-stack tree-height verification condition states recursive-call
  termination and preservation of the maximum-height result invariant. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source element carrier. T is exactly the
  source inductive carrier of finite U-labelled binary trees:
  NTP4VCEmpty and NTP4VCNode are disjoint injective tagged constructors, and
  closure, exhaustiveness, and structural induction exclude missing finite
  trees and extraneous non-well-founded values.

  H and S are the source recursive tree height and size functions. G and K
  are the source recursive heights and sizes functions on stacks. SetMM
  Word ( ZZ X. T ) is exactly the source type of arbitrary finite stacks of
  integer/tree pairs. The displayed empty and cons equations are the complete
  recursive definitions. NTP4VCMax is integer maximum, NTP4VCCons is exact
  list cons, and NTP4VCExpand is the source let-bound stack obtained by
  pushing the two children of a node with incremented offsets.

  The final assertion expands the source matches into their exhaustive empty,
  Empty-head, and Node-head cases. In each nonempty case it preserves the
  complete lexicographic variant condition, including the source tail
  comparison, and keeps the result universally quantified inside its original
  scope. Every element, tree, integer, and finite-stack domain is unchanged.
  The final $a declaration is Metamath's native unproved statement encoding;
  every preceding $a is syntax or a faithful definition, and this database
  contains no $p proof declaration.
$)

$c
  NTP4VCEmpty NTP4VCNode NTP4VCMax NTP4VCCons NTP4VCExpand
$.

ntp4vc-empty-syntax
  $a class NTP4VCEmpty $.
ntp4vc-node-syntax
  $a class ( NTP4VCNode A B C ) $.
ntp4vc-max-syntax
  $a class ( NTP4VCMax A B ) $.
ntp4vc-cons-syntax
  $a class ( NTP4VCCons A B ) $.
ntp4vc-expand-syntax
  $a class ( NTP4VCExpand A B C D ) $.

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

ntp4vc-cons-definition $a |- (
  NTP4VCCons A B
) = (
  <" A "> ++ B
) $.

ntp4vc-expand-definition $a |- (
  NTP4VCExpand A B C D
) = (
  NTP4VCCons
    <. ( A + 1 ) , B >.
    (
      NTP4VCCons
        <. ( A + 1 ) , C >.
        D
    )
) $.

${
  $d h l q r s t u v x y z
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

  $( Complete recursive source definitions of tree height and tree size. $)
  ntp4vc-height-function $e |- H e. ( ZZ ^m T ) $.
  ntp4vc-size-function $e |- S e. ( ZZ ^m T ) $.

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

  $(
    Complete recursive source definitions of heights and sizes on finite
    stacks of integer/tree pairs.
  $)
  ntp4vc-stack-heights-function $e |- G e.
    (
      ZZ
      ^m
      ( Word ( ZZ X. T ) )
    ) $.

  ntp4vc-stack-sizes-function $e |- K e.
    (
      ZZ
      ^m
      ( Word ( ZZ X. T ) )
    ) $.

  ntp4vc-stack-heights-empty $e |- (
    G ` (/)
  ) = 0 $.

  ntp4vc-stack-heights-cons $e |- A. h e. ZZ A. t e. T
    A. q e. Word ( ZZ X. T )
      (
        G ` ( NTP4VCCons <. h , t >. q )
      )
      =
      (
        NTP4VCMax
          (
            h
            +
            ( H ` t )
          )
          ( G ` q )
      ) $.

  ntp4vc-stack-sizes-empty $e |- (
    K ` (/)
  ) = 0 $.

  ntp4vc-stack-sizes-cons $e |- A. h e. ZZ A. t e. T
    A. q e. Word ( ZZ X. T )
      (
        K ` ( NTP4VCCons <. h , t >. q )
      )
      =
      (
        ( S ` t )
        +
        ( K ` q )
      ) $.

  $( Source theorem parameters m and s, followed by fact0. $)
  ntp4vc-m-integer $e |- M e. ZZ $.
  ntp4vc-stack-word $e |- A e. Word ( ZZ X. T ) $.
  ntp4vc-fact0 $e |- 0 <_ M $.

  ntp4vc-pearl-tree-height-height-stack-height-stack-vc $a |- (
    (
      A = (/)
      /\
      A. z e. ZZ
        (
          z = M
          ->
          z = (
            NTP4VCMax
              M
              ( G ` A )
          )
        )
    )
    \/
    (
      E. h e. ZZ E. q e. Word ( ZZ X. T )
        (
          A = (
            NTP4VCCons
              <. h , NTP4VCEmpty >.
              q
          )
          /\
          (
            (
              (
                (
                  0 <_ ( K ` A )
                  /\
                  ( K ` q ) < ( K ` A )
                )
                \/
                (
                  ( K ` A ) = ( K ` q )
                  /\
                  q = q
                )
              )
              /\
              0 <_ ( NTP4VCMax M h )
            )
            /\
            A. z e. ZZ
              (
                z = (
                  NTP4VCMax
                    ( NTP4VCMax M h )
                    ( G ` q )
                )
                ->
                z = (
                  NTP4VCMax
                    M
                    ( G ` A )
                )
              )
          )
        )
    )
    \/
    (
      E. h e. ZZ E. l e. T E. x e. U E. r e. T
        E. q e. Word ( ZZ X. T )
          (
            A = (
              NTP4VCCons
                <. h , ( NTP4VCNode l x r ) >.
                q
            )
            /\
            (
              (
                (
                  (
                    0 <_ ( K ` A )
                    /\
                    (
                      K `
                      ( NTP4VCExpand h l r q )
                    )
                    <
                    ( K ` A )
                  )
                  \/
                  (
                    ( K ` A )
                    =
                    (
                      K `
                      ( NTP4VCExpand h l r q )
                    )
                    /\
                    q = ( NTP4VCExpand h l r q )
                  )
                )
                /\
                0 <_ M
              )
              /\
              A. z e. ZZ
                (
                  z = (
                    NTP4VCMax
                      M
                      (
                        G `
                        ( NTP4VCExpand h l r q )
                      )
                  )
                  ->
                  z = (
                    NTP4VCMax
                      M
                      ( G ` A )
                  )
                )
            )
          )
    )
  ) $.
$}
