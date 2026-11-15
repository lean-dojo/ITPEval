;; Statement-only formalization of thousand-theorems corpus artifact Q3527118,
;; "Mahler's theorem": every continuous function from the p-adic integers to a
;; complete nonarchimedean normed p-adic-integer module is the uniform sum of
;; its Mahler series with forward-difference coefficients. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Rational upper cuts represent real-valued norms exactly: NORM-LT(x,q)
;; means ||x|| < q for rational q. The p-adic carrier is characterized as the
;; complete separated completion of the integers for the p-adic norm. Thus its
;; abstract presentation is unique up to the canonical isometric ring
;; isomorphism with Z_p; it is not a finite or rational approximation.
;;
;; APPLY$ function objects retain arbitrary carriers, operations, sequences,
;; and continuous functions. The final HasSum predicate uses the unbounded net
;; of all finite subsets of the natural numbers and uniform convergence on
;; Z_p, exactly matching HasSum in the continuous-map norm.

(defun q3527118-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun q3527118-unary (function value)
  (apply$ function (list value)))

(defun q3527118-binary (function left right)
  (apply$ function (list left right)))

(defun q3527118-positive-rational-p (value)
  (and (rationalp value)
       (< 0 value)))

;; Primality of the p-adic prime.

(defun q3527118-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (q3527118-no-divisor-from-p number (+ divisor 1)))
    t))

(defun q3527118-prime-p (number)
  (and (natp number)
       (< 1 number)
       (q3527118-no-divisor-from-p number 2)))

;; Nonnegative real norms represented by rounded rational upper cuts.

(defun q3527118-norm-lt-p (norm-lt object bound)
  (if (apply$ norm-lt (list object bound)) t nil))

(defun-sk q3527118-norm-finite-p (norm-lt object)
  (exists (bound)
    (and
     (q3527118-positive-rational-p bound)
     (q3527118-norm-lt-p norm-lt object bound))))

(defun-sk q3527118-norm-positive-p (norm-lt object)
  (exists (bound)
    (and
     (q3527118-positive-rational-p bound)
     (not (q3527118-norm-lt-p norm-lt object bound)))))

(defun-sk q3527118-norm-rounded-p (norm-lt object bound)
  (exists (smaller)
    (and
     (q3527118-positive-rational-p smaller)
     (< smaller bound)
     (q3527118-norm-lt-p norm-lt object smaller))))

(defun-sk q3527118-norm-cut-laws-p (carrier zero norm-lt)
  (forall (object bound larger)
    (implies
     (q3527118-member-p carrier object)
     (and
      (implies
       (q3527118-norm-lt-p norm-lt object bound)
       (q3527118-positive-rational-p bound))
      (implies
       (and
        (q3527118-norm-lt-p norm-lt object bound)
        (rationalp larger)
        (< bound larger))
       (q3527118-norm-lt-p norm-lt object larger))
      (implies
       (q3527118-norm-lt-p norm-lt object bound)
       (q3527118-norm-rounded-p norm-lt object bound))
      (q3527118-norm-finite-p norm-lt object)
      (iff
       (equal object zero)
       (not (q3527118-norm-positive-p norm-lt object)))
      (implies
       (equal object zero)
       (iff
        (q3527118-norm-lt-p norm-lt object bound)
        (q3527118-positive-rational-p bound)))))))

(defun-sk q3527118-product-norm-lt-p
    (left-norm-lt right-norm-lt left right bound)
  (exists (left-bound right-bound)
    (and
     (q3527118-positive-rational-p bound)
     (q3527118-positive-rational-p left-bound)
     (q3527118-positive-rational-p right-bound)
     (q3527118-norm-lt-p
      left-norm-lt left left-bound)
     (q3527118-norm-lt-p
      right-norm-lt right right-bound)
     (< (* left-bound right-bound) bound))))

;; The p-adic integer ring.

(defun-sk q3527118-commutative-ring-laws-p
    (carrier add multiply negate zero one)
  (forall (x y z)
    (implies
     (and
      (q3527118-member-p carrier x)
      (q3527118-member-p carrier y)
      (q3527118-member-p carrier z))
     (let* ((xy-add (q3527118-binary add x y))
            (yz-add (q3527118-binary add y z))
            (xy-multiply (q3527118-binary multiply x y))
            (yz-multiply (q3527118-binary multiply y z))
            (negative-x (q3527118-unary negate x)))
       (and
        (q3527118-member-p carrier xy-add)
        (q3527118-member-p carrier xy-multiply)
        (q3527118-member-p carrier negative-x)
        (equal
         (q3527118-binary add xy-add z)
         (q3527118-binary add x yz-add))
        (equal xy-add (q3527118-binary add y x))
        (equal (q3527118-binary add x zero) x)
        (equal
         (q3527118-binary add x negative-x)
         zero)
        (equal
         (q3527118-binary multiply xy-multiply z)
         (q3527118-binary multiply x yz-multiply))
        (equal
         xy-multiply
         (q3527118-binary multiply y x))
        (equal
         (q3527118-binary multiply x one)
         x)
        (equal
         (q3527118-binary multiply x yz-add)
         (q3527118-binary
          add
          (q3527118-binary multiply x y)
          (q3527118-binary multiply x z))))))))

(defun q3527118-ring-nat (add zero one number)
  (declare (xargs :measure (nfix number)))
  (if (zp number)
      zero
    (q3527118-binary
     add
     one
     (q3527118-ring-nat add zero one (1- number)))))

(defun q3527118-ring-int (add negate zero one integer)
  (if (integerp integer)
      (if (< integer 0)
          (q3527118-unary
           negate
           (q3527118-ring-nat
            add zero one (- integer)))
        (q3527118-ring-nat add zero one integer))
    zero))

(defun-sk q3527118-integer-padic-norm-lt-p
    (prime integer bound)
  (exists (exponent)
    (and
     (integerp integer)
     (q3527118-positive-rational-p bound)
     (natp exponent)
     (integerp
      (/ integer (expt prime exponent)))
     (< (/ 1 (expt prime exponent)) bound))))

(defun-sk q3527118-padic-norm-laws-p
    (prime carrier add multiply negate zero one norm-lt)
  (forall (x y bound integer)
    (implies
     (and
      (q3527118-member-p carrier x)
      (q3527118-member-p carrier y))
     (let ((xy-add (q3527118-binary add x y))
           (xy-multiply (q3527118-binary multiply x y))
           (negative-x (q3527118-unary negate x)))
       (and
        (iff
         (q3527118-norm-lt-p
          norm-lt negative-x bound)
         (q3527118-norm-lt-p norm-lt x bound))
        (implies
         (and
          (q3527118-norm-lt-p norm-lt x bound)
          (q3527118-norm-lt-p norm-lt y bound))
         (q3527118-norm-lt-p
          norm-lt xy-add bound))
        (iff
         (q3527118-norm-lt-p
          norm-lt xy-multiply bound)
         (q3527118-product-norm-lt-p
          norm-lt norm-lt x y bound))
        (implies
         (integerp integer)
         (iff
          (q3527118-norm-lt-p
           norm-lt
           (q3527118-ring-int
            add negate zero one integer)
           bound)
          (q3527118-integer-padic-norm-lt-p
           prime integer bound))))))))

(defun q3527118-distance-lt-p
    (add negate norm-lt left right bound)
  (q3527118-norm-lt-p
   norm-lt
   (q3527118-binary
    add left (q3527118-unary negate right))
   bound))

(defun-sk q3527118-sequence-typed-p (carrier sequence)
  (forall (index)
    (implies
     (natp index)
     (q3527118-member-p
      carrier
      (q3527118-unary sequence index)))))

(defun-sk q3527118-cauchy-tail-p
    (add negate norm-lt sequence bound cutoff)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (natp cutoff)
      (<= cutoff left-index)
      (<= cutoff right-index))
     (q3527118-distance-lt-p
      add negate norm-lt
      (q3527118-unary sequence left-index)
      (q3527118-unary sequence right-index)
      bound))))

(defun-sk q3527118-cauchy-cutoff-exists-p
    (add negate norm-lt sequence bound)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q3527118-cauchy-tail-p
      add negate norm-lt sequence bound cutoff))))

(defun-sk q3527118-cauchy-p
    (add negate norm-lt sequence)
  (forall (bound)
    (implies
     (q3527118-positive-rational-p bound)
     (q3527118-cauchy-cutoff-exists-p
      add negate norm-lt sequence bound))))

(defun-sk q3527118-convergence-tail-p
    (add negate norm-lt sequence limit bound cutoff)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp cutoff)
      (<= cutoff index))
     (q3527118-distance-lt-p
      add negate norm-lt
      (q3527118-unary sequence index)
      limit
      bound))))

(defun-sk q3527118-convergence-cutoff-exists-p
    (add negate norm-lt sequence limit bound)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q3527118-convergence-tail-p
      add negate norm-lt
      sequence limit bound cutoff))))

(defun-sk q3527118-sequence-converges-p
    (add negate norm-lt sequence limit)
  (forall (bound)
    (implies
     (q3527118-positive-rational-p bound)
     (q3527118-convergence-cutoff-exists-p
      add negate norm-lt sequence limit bound))))

(defun-sk q3527118-sequence-limit-exists-p
    (carrier add negate norm-lt sequence)
  (exists (limit)
    (and
     (q3527118-member-p carrier limit)
     (q3527118-sequence-converges-p
      add negate norm-lt sequence limit))))

(defun-sk q3527118-complete-space-p
    (carrier add negate norm-lt)
  (forall (sequence)
    (implies
     (and
      (tamep-functionp sequence)
      (q3527118-sequence-typed-p carrier sequence)
      (q3527118-cauchy-p
       add negate norm-lt sequence))
     (q3527118-sequence-limit-exists-p
      carrier add negate norm-lt sequence))))

(defun-sk q3527118-dense-integer-exists-p
    (add negate zero one norm-lt x bound)
  (exists (integer)
    (and
     (integerp integer)
     (q3527118-distance-lt-p
      add negate norm-lt
      x
      (q3527118-ring-int
       add negate zero one integer)
      bound))))

(defun-sk q3527118-integers-dense-p
    (carrier add negate zero one norm-lt)
  (forall (x bound)
    (implies
     (and
      (q3527118-member-p carrier x)
      (q3527118-positive-rational-p bound))
     (q3527118-dense-integer-exists-p
      add negate zero one norm-lt x bound))))

(defun q3527118-padic-integers-p
    (prime carrier add multiply negate zero one norm-lt)
  (and
   (q3527118-prime-p prime)
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp norm-lt)
   (q3527118-member-p carrier zero)
   (q3527118-member-p carrier one)
   (not (equal zero one))
   (q3527118-commutative-ring-laws-p
    carrier add multiply negate zero one)
   (q3527118-norm-cut-laws-p
    carrier zero norm-lt)
   (q3527118-padic-norm-laws-p
    prime carrier add multiply negate zero one norm-lt)
   (q3527118-complete-space-p
    carrier add negate norm-lt)
   (q3527118-integers-dense-p
    carrier add negate zero one norm-lt)))

;; Complete nonarchimedean normed modules over the presented Z_p.

(defun-sk q3527118-module-laws-p
    (scalar-carrier scalar-add scalar-multiply scalar-one
     carrier add negate zero smul)
  (forall (scalar other-scalar x y z)
    (implies
     (and
      (q3527118-member-p scalar-carrier scalar)
      (q3527118-member-p scalar-carrier other-scalar)
      (q3527118-member-p carrier x)
      (q3527118-member-p carrier y)
      (q3527118-member-p carrier z))
     (let* ((xy-add (q3527118-binary add x y))
            (yz-add (q3527118-binary add y z))
            (negative-x (q3527118-unary negate x))
            (scalar-x (q3527118-binary smul scalar x)))
       (and
        (q3527118-member-p carrier xy-add)
        (q3527118-member-p carrier negative-x)
        (q3527118-member-p carrier scalar-x)
        (equal
         (q3527118-binary add xy-add z)
         (q3527118-binary add x yz-add))
        (equal xy-add (q3527118-binary add y x))
        (equal (q3527118-binary add x zero) x)
        (equal
         (q3527118-binary add x negative-x)
         zero)
        (equal
         (q3527118-binary smul scalar-one x)
         x)
        (equal
         (q3527118-binary
          smul
          (q3527118-binary
           scalar-multiply scalar other-scalar)
          x)
         (q3527118-binary
          smul scalar
          (q3527118-binary smul other-scalar x)))
        (equal
         (q3527118-binary
          smul
          (q3527118-binary
           scalar-add scalar other-scalar)
          x)
         (q3527118-binary
          add
          scalar-x
          (q3527118-binary smul other-scalar x)))
        (equal
         (q3527118-binary smul scalar xy-add)
         (q3527118-binary
          add
          scalar-x
          (q3527118-binary smul scalar y))))))))

(defun-sk q3527118-ultrametric-norm-laws-p
    (carrier add negate norm-lt)
  (forall (x y bound)
    (implies
     (and
      (q3527118-member-p carrier x)
      (q3527118-member-p carrier y))
     (and
      (iff
       (q3527118-norm-lt-p
        norm-lt (q3527118-unary negate x) bound)
       (q3527118-norm-lt-p norm-lt x bound))
      (implies
       (and
        (q3527118-norm-lt-p norm-lt x bound)
        (q3527118-norm-lt-p norm-lt y bound))
       (q3527118-norm-lt-p
        norm-lt
        (q3527118-binary add x y)
        bound))))))

(defun-sk q3527118-bounded-smul-p
    (scalar-carrier scalar-norm-lt
     carrier smul norm-lt)
  (forall (scalar x bound)
    (implies
     (and
      (q3527118-member-p scalar-carrier scalar)
      (q3527118-member-p carrier x))
     (implies
      (q3527118-product-norm-lt-p
       scalar-norm-lt norm-lt
       scalar x bound)
      (q3527118-norm-lt-p
       norm-lt
       (q3527118-binary smul scalar x)
       bound)))))

(defun q3527118-banach-module-p
    (scalar-carrier scalar-add scalar-multiply scalar-one
     scalar-norm-lt
     carrier add negate zero smul norm-lt)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp negate)
   (tamep-functionp smul)
   (tamep-functionp norm-lt)
   (q3527118-member-p carrier zero)
   (q3527118-module-laws-p
    scalar-carrier scalar-add scalar-multiply scalar-one
    carrier add negate zero smul)
   (q3527118-norm-cut-laws-p
    carrier zero norm-lt)
   (q3527118-ultrametric-norm-laws-p
    carrier add negate norm-lt)
   (q3527118-bounded-smul-p
    scalar-carrier scalar-norm-lt
    carrier smul norm-lt)
   (q3527118-complete-space-p
    carrier add negate norm-lt)))

;; Continuity in the norm topologies.

(defun-sk q3527118-continuity-ball-p
    (domain-carrier domain-add domain-negate domain-norm-lt
     codomain-add codomain-negate codomain-norm-lt
     function point output-bound input-bound)
  (forall (other-point)
    (implies
     (and
      (q3527118-member-p domain-carrier other-point)
      (q3527118-distance-lt-p
       domain-add domain-negate domain-norm-lt
       other-point point input-bound))
     (q3527118-distance-lt-p
      codomain-add codomain-negate codomain-norm-lt
      (q3527118-unary function other-point)
      (q3527118-unary function point)
      output-bound))))

(defun-sk q3527118-continuity-neighborhood-p
    (domain-carrier domain-add domain-negate domain-norm-lt
     codomain-add codomain-negate codomain-norm-lt
     function point output-bound)
  (exists (input-bound)
    (and
     (q3527118-positive-rational-p input-bound)
     (q3527118-continuity-ball-p
      domain-carrier domain-add domain-negate domain-norm-lt
      codomain-add codomain-negate codomain-norm-lt
      function point output-bound input-bound))))

(defun-sk q3527118-continuous-map-p
    (domain-carrier domain-add domain-negate domain-norm-lt
     codomain-carrier codomain-add codomain-negate codomain-norm-lt
     function)
  (forall (point output-bound)
    (implies
     (and
      (q3527118-member-p domain-carrier point)
      (q3527118-positive-rational-p output-bound))
     (and
      (q3527118-member-p
       codomain-carrier
       (q3527118-unary function point))
      (q3527118-continuity-neighborhood-p
       domain-carrier domain-add domain-negate domain-norm-lt
       codomain-add codomain-negate codomain-norm-lt
       function point output-bound)))))

;; The Mahler basis is the unique continuous extension of n |-> choose(n,k).

(defun q3527118-binomial (number index)
  (declare
   (xargs :measure
          (+ (nfix number) (nfix index))))
  (cond
   ((or (not (natp number))
        (not (natp index)))
    0)
   ((zp index) 1)
   ((zp number) 0)
   ((< number index) 0)
   (t
    (+
     (q3527118-binomial
      (1- number) (1- index))
     (q3527118-binomial
      (1- number) index)))))

(defun-sk q3527118-mahler-typed-p
    (padic-carrier mahler)
  (forall (index x)
    (implies
     (and
      (natp index)
      (q3527118-member-p padic-carrier x))
     (q3527118-member-p
      padic-carrier
      (q3527118-binary mahler index x)))))

(defun-sk q3527118-mahler-natural-values-p
    (padic-add padic-zero padic-one mahler)
  (forall (index number)
    (implies
     (and
      (natp index)
      (natp number))
     (equal
      (q3527118-binary
       mahler
       index
       (q3527118-ring-nat
        padic-add padic-zero padic-one number))
      (q3527118-ring-nat
       padic-add padic-zero padic-one
       (q3527118-binomial number index))))))

(defun-sk q3527118-mahler-continuity-ball-p
    (padic-carrier padic-add padic-negate padic-norm-lt
     mahler index point output-bound input-bound)
  (forall (other-point)
    (implies
     (and
      (q3527118-member-p padic-carrier other-point)
      (q3527118-distance-lt-p
       padic-add padic-negate padic-norm-lt
       other-point point input-bound))
     (q3527118-distance-lt-p
      padic-add padic-negate padic-norm-lt
      (q3527118-binary mahler index other-point)
      (q3527118-binary mahler index point)
      output-bound))))

(defun-sk q3527118-mahler-continuity-neighborhood-p
    (padic-carrier padic-add padic-negate padic-norm-lt
     mahler index point output-bound)
  (exists (input-bound)
    (and
     (q3527118-positive-rational-p input-bound)
     (q3527118-mahler-continuity-ball-p
      padic-carrier padic-add padic-negate padic-norm-lt
      mahler index point output-bound input-bound))))

(defun-sk q3527118-mahler-continuous-p
    (padic-carrier padic-add padic-negate padic-norm-lt mahler)
  (forall (index point output-bound)
    (implies
     (and
      (natp index)
      (q3527118-member-p padic-carrier point)
      (q3527118-positive-rational-p output-bound))
     (q3527118-mahler-continuity-neighborhood-p
      padic-carrier padic-add padic-negate padic-norm-lt
      mahler index point output-bound))))

(defun q3527118-mahler-basis-p
    (padic-carrier padic-add padic-negate
     padic-zero padic-one padic-norm-lt mahler)
  (and
   (tamep-functionp mahler)
   (q3527118-mahler-typed-p
    padic-carrier mahler)
   (q3527118-mahler-natural-values-p
    padic-add padic-zero padic-one mahler)
   (q3527118-mahler-continuous-p
    padic-carrier padic-add padic-negate
    padic-norm-lt mahler)))

;; Iterated forward differences at zero, expressed by the exact finite
;; alternating-binomial formula.

(defun q3527118-forward-coefficient (number index)
  (let ((magnitude (q3527118-binomial number index)))
    (if (equal (mod (- number index) 2) 0)
        magnitude
      (- magnitude))))

(defun q3527118-forward-difference-prefix
    (number count function
     padic-add padic-negate padic-zero padic-one
     module-add module-zero module-smul)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      module-zero
    (let* ((index (1- count))
           (coefficient
            (q3527118-ring-int
             padic-add padic-negate padic-zero padic-one
             (q3527118-forward-coefficient number index)))
           (function-value
            (q3527118-unary
             function
             (q3527118-ring-nat
              padic-add padic-zero padic-one index)))
           (term
            (q3527118-binary
             module-smul coefficient function-value)))
      (q3527118-binary
       module-add
       (q3527118-forward-difference-prefix
        number index function
        padic-add padic-negate padic-zero padic-one
        module-add module-zero module-smul)
       term))))

(defun q3527118-forward-difference
    (number function
     padic-add padic-negate padic-zero padic-one
     module-add module-zero module-smul)
  (q3527118-forward-difference-prefix
   number (+ 1 (nfix number)) function
   padic-add padic-negate padic-zero padic-one
   module-add module-zero module-smul))

(defun q3527118-mahler-term
    (index point function mahler
     padic-add padic-negate padic-zero padic-one
     module-add module-zero module-smul)
  (q3527118-binary
   module-smul
   (q3527118-binary mahler index point)
   (q3527118-forward-difference
    index function
    padic-add padic-negate padic-zero padic-one
    module-add module-zero module-smul)))

;; Finite subsets of N and their Mahler sums.

(defun q3527118-natural-list-p (indices)
  (if (consp indices)
      (and
       (natp (car indices))
       (q3527118-natural-list-p (cdr indices)))
    (equal indices nil)))

(defun q3527118-finite-natural-set-p (indices)
  (and
   (true-listp indices)
   (q3527118-natural-list-p indices)
   (no-duplicatesp-equal indices)))

(defun q3527118-subset-equal-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (q3527118-subset-equal-p (cdr left) right))
    t))

(defun q3527118-mahler-finite-sum
    (indices point function mahler
     padic-add padic-negate padic-zero padic-one
     module-add module-zero module-smul)
  (if (consp indices)
      (q3527118-binary
       module-add
       (q3527118-mahler-term
        (car indices) point function mahler
        padic-add padic-negate padic-zero padic-one
        module-add module-zero module-smul)
       (q3527118-mahler-finite-sum
        (cdr indices) point function mahler
        padic-add padic-negate padic-zero padic-one
        module-add module-zero module-smul))
    module-zero))

(defun-sk q3527118-has-sum-tail-p
    (padic-carrier
     padic-add padic-negate padic-zero padic-one
     module-add module-negate module-zero module-smul module-norm-lt
     function mahler bound base-set)
  (forall (indices point)
    (implies
     (and
      (q3527118-finite-natural-set-p indices)
      (q3527118-subset-equal-p base-set indices)
      (q3527118-member-p padic-carrier point))
     (q3527118-distance-lt-p
      module-add module-negate module-norm-lt
      (q3527118-mahler-finite-sum
       indices point function mahler
       padic-add padic-negate padic-zero padic-one
       module-add module-zero module-smul)
      (q3527118-unary function point)
      bound))))

(defun-sk q3527118-has-sum-base-exists-p
    (padic-carrier
     padic-add padic-negate padic-zero padic-one
     module-add module-negate module-zero module-smul module-norm-lt
     function mahler bound)
  (exists (base-set)
    (and
     (q3527118-finite-natural-set-p base-set)
     (q3527118-has-sum-tail-p
      padic-carrier
      padic-add padic-negate padic-zero padic-one
      module-add module-negate module-zero module-smul module-norm-lt
      function mahler bound base-set))))

(defun-sk q3527118-mahler-has-sum-p
    (padic-carrier
     padic-add padic-negate padic-zero padic-one
     module-add module-negate module-zero module-smul module-norm-lt
     function mahler)
  (forall (bound)
    (implies
     (q3527118-positive-rational-p bound)
     (q3527118-has-sum-base-exists-p
      padic-carrier
      padic-add padic-negate padic-zero padic-one
      module-add module-negate module-zero module-smul module-norm-lt
      function mahler bound))))

(defun thousand-theorems-q3527118-mahler-s-theorem-statement
    (prime
     padic-carrier padic-add padic-multiply padic-negate
     padic-zero padic-one padic-norm-lt
     module-carrier module-add module-negate module-zero
     module-smul module-norm-lt
     mahler function)
  (implies
   (and
    (q3527118-padic-integers-p
     prime
     padic-carrier padic-add padic-multiply padic-negate
     padic-zero padic-one padic-norm-lt)
    (q3527118-banach-module-p
     padic-carrier padic-add padic-multiply padic-one
     padic-norm-lt
     module-carrier module-add module-negate module-zero
     module-smul module-norm-lt)
    (q3527118-mahler-basis-p
     padic-carrier padic-add padic-negate
     padic-zero padic-one padic-norm-lt mahler)
    (tamep-functionp function)
    (q3527118-continuous-map-p
     padic-carrier padic-add padic-negate padic-norm-lt
     module-carrier module-add module-negate module-norm-lt
     function))
   (q3527118-mahler-has-sum-p
    padic-carrier
    padic-add padic-negate padic-zero padic-one
    module-add module-negate module-zero module-smul module-norm-lt
    function mahler)))

(value-triple :itpeval-statement-checked)
:q
