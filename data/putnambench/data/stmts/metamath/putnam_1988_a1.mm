$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_a1: the region of real-plane points satisfying
  |x| - |y| <= 1 and |y| <= 1 has Lebesgue area six. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The class RR ^m ( 1 ... 2 ) is the full real coordinate plane, and voln
  on the index set 1 ... 2 is two-dimensional Lebesgue measure. The
  restricted class is exactly the source definition of R. Substituting this
  class for R is definitionally equivalent to the source formulation with an
  arbitrary R and the hypothesis equating R to that class.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

putnambench-putnam-1988-a1 $a |- (
  (
    ( voln ` ( 1 ... 2 ) )
    `
    {
      p e. ( RR ^m ( 1 ... 2 ) ) |
      (
        (
          ( abs ` ( p ` 1 ) )
          -
          ( abs ` ( p ` 2 ) )
        )
        <_ 1
        /\
        ( abs ` ( p ` 2 ) ) <_ 1
      )
    }
  )
  =
  6
) $.
