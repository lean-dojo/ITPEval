;; Statement-only formalization of PutnamBench corpus artifact putnam_1965_a3:
;; complex Cesaro averages of an arbitrary unit-circle sequence converge to a
;; given limit iff their square-indexed subsequence converges to that limit.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source sequence occurs only through exp(i*a_k).  Such values are exactly
;; the complex unit circle, since x |-> exp(i*x) is onto that circle.  Thus an
;; arbitrary unit-circle sequence is a bidirectionally equivalent presentation
;; of the source's arbitrary real sequence after applying complex exponential.
;; The real carrier below is a Dedekind-complete ordered field, hence presents
;; the real numbers up to the unique ordered-field isomorphism.

(defun putnam-1965-a3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1965-a3-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-1965-a3-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-1965-a3-positive-p (carrier less zero x)
  (and (putnam-1965-a3-member-p carrier x)
       (apply$ less (list zero x))))

(defun-sk putnam-1965-a3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (putnam-1965-a3-member-p carrier x)
          (putnam-1965-a3-member-p carrier y)
          (putnam-1965-a3-member-p carrier z))
     (and
      (putnam-1965-a3-member-p
       carrier (putnam-1965-a3-binary add x y))
      (putnam-1965-a3-member-p
       carrier (putnam-1965-a3-binary multiply x y))
      (putnam-1965-a3-member-p
       carrier (putnam-1965-a3-unary negate x))
      (putnam-1965-a3-member-p
       carrier (putnam-1965-a3-unary inverse x))
      (equal
       (putnam-1965-a3-binary
        add (putnam-1965-a3-binary add x y) z)
       (putnam-1965-a3-binary
        add x (putnam-1965-a3-binary add y z)))
      (equal (putnam-1965-a3-binary add x y)
             (putnam-1965-a3-binary add y x))
      (equal (putnam-1965-a3-binary add x zero) x)
      (equal
       (putnam-1965-a3-binary
        add x (putnam-1965-a3-unary negate x))
       zero)
      (equal
       (putnam-1965-a3-binary
        multiply (putnam-1965-a3-binary multiply x y) z)
       (putnam-1965-a3-binary
        multiply x (putnam-1965-a3-binary multiply y z)))
      (equal (putnam-1965-a3-binary multiply x y)
             (putnam-1965-a3-binary multiply y x))
      (equal (putnam-1965-a3-binary multiply x one) x)
      (equal (putnam-1965-a3-unary inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1965-a3-binary
         multiply x (putnam-1965-a3-unary inverse x))
        one))
      (equal
       (putnam-1965-a3-binary
        multiply x (putnam-1965-a3-binary add y z))
       (putnam-1965-a3-binary
        add
        (putnam-1965-a3-binary multiply x y)
        (putnam-1965-a3-binary multiply x z)))))))

(defun-sk putnam-1965-a3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (putnam-1965-a3-member-p carrier x)
          (putnam-1965-a3-member-p carrier y)
          (putnam-1965-a3-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or (equal x y)
          (apply$ less (list x y))
          (apply$ less (list y x)))
      (implies
       (and (apply$ less (list x y))
            (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$
        less
        (list (putnam-1965-a3-binary add x z)
              (putnam-1965-a3-binary add y z))))
      (implies
       (and (apply$ less (list zero x))
            (apply$ less (list zero y)))
       (apply$
        less
        (list zero
              (putnam-1965-a3-binary multiply x y))))))))

(defun-sk putnam-1965-a3-set-nonempty-p (carrier set)
  (exists (x)
    (and (putnam-1965-a3-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk putnam-1965-a3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and (putnam-1965-a3-member-p carrier x)
          (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-1965-a3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1965-a3-member-p carrier bound)
     (putnam-1965-a3-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1965-a3-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1965-a3-member-p carrier supremum)
     (putnam-1965-a3-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1965-a3-member-p carrier bound)
       (putnam-1965-a3-upper-bound-p
        carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk putnam-1965-a3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1965-a3-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1965-a3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1965-a3-set-nonempty-p carrier set)
      (putnam-1965-a3-bounded-above-p carrier less set))
     (putnam-1965-a3-has-supremum-p
      carrier less set))))

(defun putnam-1965-a3-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1965-a3-member-p carrier zero)
   (putnam-1965-a3-member-p carrier one)
   (not (equal zero one))
   (putnam-1965-a3-field-laws-p
    carrier add multiply negate inverse zero one)
   (putnam-1965-a3-order-laws-p
    carrier add multiply zero less)
   (apply$ less (list zero one))
   (putnam-1965-a3-dedekind-complete-p carrier less)))

(defun putnam-1965-a3-complex-p (carrier z)
  (and (consp z)
       (putnam-1965-a3-member-p carrier (car z))
       (putnam-1965-a3-member-p carrier (cdr z))))

(defun putnam-1965-a3-complex-zero (zero)
  (cons zero zero))

(defun putnam-1965-a3-complex-add (add z w)
  (cons
   (putnam-1965-a3-binary add (car z) (car w))
   (putnam-1965-a3-binary add (cdr z) (cdr w))))

(defun putnam-1965-a3-complex-negate (negate z)
  (cons
   (putnam-1965-a3-unary negate (car z))
   (putnam-1965-a3-unary negate (cdr z))))

(defun putnam-1965-a3-complex-subtract (add negate z w)
  (putnam-1965-a3-complex-add
   add z (putnam-1965-a3-complex-negate negate w)))

(defun putnam-1965-a3-complex-scale (multiply scalar z)
  (cons
   (putnam-1965-a3-binary multiply scalar (car z))
   (putnam-1965-a3-binary multiply scalar (cdr z))))

(defun putnam-1965-a3-squared-modulus (add multiply z)
  (putnam-1965-a3-binary
   add
   (putnam-1965-a3-binary multiply (car z) (car z))
   (putnam-1965-a3-binary multiply (cdr z) (cdr z))))

(defun putnam-1965-a3-field-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1965-a3-binary
     add one
     (putnam-1965-a3-field-natural
      (- n 1) zero one add))))

(defun putnam-1965-a3-prefix-sum
    (sequence count zero add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-1965-a3-complex-zero zero)
    (putnam-1965-a3-complex-add
     add
     (putnam-1965-a3-prefix-sum
      sequence (- count 1) zero add)
     (apply$ sequence (list count)))))

(defun putnam-1965-a3-average
    (sequence count zero one add multiply inverse)
  (putnam-1965-a3-complex-scale
   multiply
   (putnam-1965-a3-unary
    inverse
    (putnam-1965-a3-field-natural
     count zero one add))
   (putnam-1965-a3-prefix-sum
    sequence count zero add)))

(defun putnam-1965-a3-selected-average
    (sequence n squarep zero one add multiply inverse)
  (putnam-1965-a3-average
   sequence
   (if squarep (* n n) n)
   zero one add multiply inverse))

(defun-sk putnam-1965-a3-unit-sequence-p
    (carrier add multiply one sequence)
  (forall (n)
    (implies
     (natp n)
     (let ((z (apply$ sequence (list n))))
       (and
        (putnam-1965-a3-complex-p carrier z)
        (equal
         (putnam-1965-a3-squared-modulus
          add multiply z)
         one))))))

(defun putnam-1965-a3-close-p
    (add multiply negate less z alpha epsilon)
  (apply$
   less
   (list
    (putnam-1965-a3-squared-modulus
     add
     multiply
     (putnam-1965-a3-complex-subtract
      add negate z alpha))
    (putnam-1965-a3-binary
     multiply epsilon epsilon))))

(defun-sk putnam-1965-a3-convergence-tail-p
    (sequence alpha squarep
     zero one add multiply negate inverse less
     epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (putnam-1965-a3-close-p
      add multiply negate less
      (putnam-1965-a3-selected-average
       sequence n squarep
       zero one add multiply inverse)
      alpha
      epsilon))))

(defun-sk putnam-1965-a3-cutoff-exists-p
    (sequence alpha squarep
     zero one add multiply negate inverse less
     epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1965-a3-convergence-tail-p
      sequence alpha squarep
      zero one add multiply negate inverse less
      epsilon cutoff))))

(defun-sk putnam-1965-a3-converges-p
    (carrier sequence alpha squarep
     zero one add multiply negate inverse less)
  (forall (epsilon)
    (implies
     (putnam-1965-a3-positive-p
      carrier less zero epsilon)
     (putnam-1965-a3-cutoff-exists-p
      sequence alpha squarep
      zero one add multiply negate inverse less
      epsilon))))

(defun putnambench-putnam-1965-a3-statement
    (carrier zero one add multiply negate inverse less
     sequence alpha)
  (implies
   (and
    (putnam-1965-a3-real-field-p
     carrier add multiply negate inverse zero one less)
    (tamep-functionp sequence)
    (putnam-1965-a3-unit-sequence-p
     carrier add multiply one sequence)
    (putnam-1965-a3-complex-p carrier alpha))
   (iff
    (putnam-1965-a3-converges-p
     carrier sequence alpha nil
     zero one add multiply negate inverse less)
    (putnam-1965-a3-converges-p
     carrier sequence alpha t
     zero one add multiply negate inverse less))))

(value-triple :itpeval-statement-checked)
:q
