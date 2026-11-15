$(
  Statement-only formalization of Hundred Theorems item 049, the
  Cayley-Hamilton theorem.

  This reproduces the hypotheses and conclusion of set.mm theorem
  cayleyhamilton. A is the N-by-N matrix algebra over the commutative ring R,
  K is the coefficient function of the characteristic polynomial of M, and
  the displayed finite sum is that polynomial evaluated at M.
$)

$[ library/set.mm $]

${
  $d A n $.
  $d B n $.
  $d C n $.
  $d n M $.
  $d n N $.
  $d R n $.
  $d .* n $.
  $d .^ n $.

  hundred-theorems-049-matrix-algebra $e
    |- A = ( N Mat R )
  $.
  hundred-theorems-049-matrix-carrier $e
    |- B = ( Base ` A )
  $.
  hundred-theorems-049-zero-matrix $e
    |- .0. = ( 0g ` A )
  $.
  hundred-theorems-049-polynomial-matrix $e
    |- C = ( N CharPlyMat R )
  $.
  hundred-theorems-049-characteristic-coefficients $e
    |- K = ( coe1 ` ( C ` M ) )
  $.
  hundred-theorems-049-scalar-action $e
    |- .* = ( .s ` A )
  $.
  hundred-theorems-049-matrix-power $e
    |- .^ = ( .g ` ( mulGrp ` A ) )
  $.

  hundred-theorems-049-cayley-hamilton $a
    |- (
         ( N e. Fin /\ R e. CRing /\ M e. B )
         ->
         (
           A gsum
             ( n e. NN0 |-> ( ( K ` n ) .* ( n .^ M ) ) )
         )
         = .0.
       )
  $.
$}
