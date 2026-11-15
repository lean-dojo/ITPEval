$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.let_clause_73, catalog title "cong.let_clause_73": under an unrelated
  positive-natural assumption, addition of three natural numbers is unchanged
  when the first two addends are exchanged. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The declaration preserves the
  source's unused natural parameters n and m and its assumption 0 < p.
  Variables x, y, and z represent x134, x135, and x136, respectively. The
  declaration is an unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

${
  $d n m p x y z $.

  logipedia-cong-let-clause-73 $a |-
    A. n e. NN0
      A. m e. NN0
        A. p e. NN0
          (
            0 < p
            ->
            A. x e. NN0
              A. y e. NN0
                A. z e. NN0
                  (
                    x + ( y + z )
                  )
                  =
                  (
                    y + ( x + z )
                  )
          )
  $.
$}
