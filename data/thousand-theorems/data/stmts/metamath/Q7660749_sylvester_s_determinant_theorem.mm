$(
  Statement-only formalization of Thousand Theorems corpus artifact Q7660749
  (thousand-theorems__metamath__Q7660749), "Sylvester's determinant theorem":
  over every commutative ring and arbitrary finite row and column carriers,
  the determinants of I + AB and I + BA are equal for compatible rectangular
  matrices A and B. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For a commutative ring R and finite sets M and N, the function spaces over
  ( Base ` R ) indexed by M X. N and N X. M are the full rectangular matrix
  spaces. The maMul operations form the square products AB and BA, while Mat,
  1r, +g, and maDet provide the corresponding square matrix rings, identity
  matrices, addition, and determinants.

  The following $a is the single unproved corpus statement. This artifact
  adds no $p assertion.
$)

${
  $d A B M N R $.

  thousand-theorems-q7660749-sylvester-determinant-theorem $a |-
    A. R e. CRing
      A. M e. Fin
        A. N e. Fin
          A. A e. ( ( Base ` R ) ^m ( M X. N ) )
            A. B e. ( ( Base ` R ) ^m ( N X. M ) )
              (
                ( ( M maDet R )
                  `
                  (
                    ( 1r ` ( M Mat R ) )
                    ( +g ` ( M Mat R ) )
                    ( A ( R maMul <. M , N , M >. ) B )
                  )
                )
                =
                ( ( N maDet R )
                  `
                  (
                    ( 1r ` ( N Mat R ) )
                    ( +g ` ( N Mat R ) )
                    ( B ( R maMul <. N , M , N >. ) A )
                  )
                )
              )
  $.
$}
