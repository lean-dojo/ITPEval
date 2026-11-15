;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sieve_Sieve_sieveqtvc: the integer sieve verification condition,
;; preserving no-small-factor invariants while marking composites and finally
;; characterizing the prime indices. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Boolean arrays are represented by proper Boolean lists.  Array observation
;; uses the source integer index directly; outside the finite array it has the
;; fixed Boolean default false.  Every semantically used access is range
;; checked by the verification condition.

(defun sieve-vc-bool-list-p (values)
  (if (consp values)
      (and
       (booleanp (car values))
       (sieve-vc-bool-list-p (cdr values)))
    (equal values nil)))

(defun sieve-vc-nth-bool (values index)
  (if
      (and
       (integerp index)
       (<= 0 index)
       (< index (len values)))
      (nth index values)
    nil))

;; This is finite-array update: an in-range integer position is replaced and
;; an out-of-range position leaves the array unchanged.

(defun sieve-vc-set (values index value)
  (if
      (and
       (integerp index)
       (<= 0 index)
       (< index (len values)))
      (update-nth index value values)
    values))

;; Equality of the total integer-indexed element maps after an update is
;; represented extensionally over every mathematical integer.

(defun-sk sieve-vc-update-law-p
    (updated original index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (sieve-vc-nth-bool updated argument)
      (if (equal argument index)
          value
        (sieve-vc-nth-bool original argument))))))

;; no_factor_lt bnd num says that num is greater than one and has no
;; factorization num = k*l with both factors above one and l below bnd.

(defun-sk sieve-vc-no-factor-below-p (bound number)
  (forall (k l)
    (implies
     (and
      (integerp k)
      (integerp l)
      (< 1 l)
      (< l bound)
      (< 1 k))
     (not (equal number (* k l))))))

(defun sieve-vc-no-factor-lt-p (bound number)
  (and
   (integerp bound)
   (integerp number)
   (< 1 number)
   (sieve-vc-no-factor-below-p bound number)))

;; Nat.Prime is retained directly: a natural number at least two has no
;; natural divisors other than one and itself.

(defun-sk sieve-vc-natural-divides-p (divisor number)
  (exists (quotient)
    (and
     (natp quotient)
     (equal number (* divisor quotient)))))

(defun-sk sieve-vc-only-trivial-divisors-p (number)
  (forall (divisor)
    (implies
     (and
      (natp divisor)
      (sieve-vc-natural-divides-p divisor number))
     (or
      (equal divisor 1)
      (equal divisor number)))))

(defun sieve-vc-prime-p (number)
  (and
   (natp number)
   (<= 2 number)
   (sieve-vc-only-trivial-divisors-p number)))

;; Array.make n true initializes every in-range position.

(defun-sk sieve-vc-initialized-p (values n)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index n))
      (equal
       (sieve-vc-nth-bool values index)
       t)))))

;; The outer-loop invariant at bound is the pointwise equivalence between a
;; marked position and no_factor_lt bound.

(defun-sk sieve-vc-stage-p (values n bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index n))
      (iff
       (equal
        (sieve-vc-nth-bool values index)
        t)
       (sieve-vc-no-factor-lt-p
        bound index))))))

;; The inner-loop invariant additionally excludes products k*i for
;; 1 < k < multiplier-bound.

(defun-sk sieve-vc-not-multiple-below-p
    (number factor multiplier-bound)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (< 1 k)
       (< k multiplier-bound))
      (not
       (equal number (* k factor)))))))

(defun-sk sieve-vc-inner-stage-p
    (values n factor multiplier-bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index n))
      (iff
       (equal
        (sieve-vc-nth-bool values index)
        t)
       (and
        (sieve-vc-no-factor-lt-p factor index)
        (sieve-vc-not-multiple-below-p
         index factor multiplier-bound)))))))

(defun-sk sieve-vc-prime-characterization-p (values n)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index n))
      (iff
       (equal
        (sieve-vc-nth-bool values index)
        t)
       (sieve-vc-prime-p index))))))

;; One universally quantified inner-loop state either marks r*i and advances
;; r, or exits the inner loop and advances the outer bound.

(defun sieve-vc-inner-iteration-conclusion-p
    (values n factor multiplier)
  (let ((product (* multiplier factor)))
    (if (< product n)
        (let ((updated
               (sieve-vc-set values product nil)))
          (and
           (<= 0 product)
           (< product (len values))
           (implies
            (equal (len updated) (len values))
            (implies
             (sieve-vc-update-law-p
              updated values product nil)
             (and
              (<= 0 (- n multiplier))
              (<
               (- n (+ multiplier 1))
               (- n multiplier))
              (< 1 (+ multiplier 1))
              (<= (+ multiplier 1) n)
              (equal
               (+ product factor)
               (* (+ multiplier 1) factor))
              (sieve-vc-inner-stage-p
               updated n factor (+ multiplier 1)))))))
      (and
       (<= 0 (- n factor))
       (< (- n (+ factor 1)) (- n factor))
       (< 1 (+ factor 1))
       (<= (+ factor 1) n)
       (sieve-vc-stage-p
        values n (+ factor 1))))))

(defun-sk sieve-vc-all-inner-iterations-p
    (reference-values n factor)
  (forall (multiplier values)
    (implies
     (and
      (integerp multiplier)
      (sieve-vc-bool-list-p values))
     (implies
      (equal
       (len values)
       (len reference-values))
      (implies
       (and
        (< 1 multiplier)
        (<= multiplier n)
        (sieve-vc-inner-stage-p
         values n factor multiplier))
       (sieve-vc-inner-iteration-conclusion-p
        values n factor multiplier))))))

;; One universally quantified outer-loop state either enters the composite
;; marking loop, advances immediately, or establishes the final postcondition.

(defun sieve-vc-outer-iteration-conclusion-p
    (values n index)
  (if (< index n)
      (and
       (<= 0 index)
       (< index (len values))
       (if
           (equal
            (sieve-vc-nth-bool values index)
            t)
           (and
            (< 1 index)
            (<= index n)
            (sieve-vc-inner-stage-p
             values n index index)
            (sieve-vc-all-inner-iterations-p
             values n index))
         (and
          (<= 0 (- n index))
          (< (- n (+ index 1)) (- n index))
          (< 1 (+ index 1))
          (<= (+ index 1) n)
          (sieve-vc-stage-p
           values n (+ index 1)))))
    (and
     (equal (len values) n)
     (sieve-vc-prime-characterization-p
      values n))))

(defun-sk sieve-vc-all-outer-iterations-p
    (reference-values n)
  (forall (index values)
    (implies
     (and
      (integerp index)
      (sieve-vc-bool-list-p values))
     (implies
      (equal
       (len values)
       (len reference-values))
      (implies
       (and
        (< 1 index)
        (<= index n)
        (sieve-vc-stage-p values n index))
       (sieve-vc-outer-iteration-conclusion-p
        values n index))))))

;; The initial writes at positions zero and one retain the source range,
;; length, and extensional update obligations before establishing the loop.

(defun sieve-vc-after-set-one-p (values n)
  (let ((updated
         (sieve-vc-set values 1 nil)))
    (and
     (<= 0 1)
     (< 1 (len values))
     (implies
      (equal (len updated) (len values))
      (implies
       (sieve-vc-update-law-p
        updated values 1 nil)
       (and
        (< 1 2)
        (<= 2 n)
        (sieve-vc-stage-p updated n 2)
        (sieve-vc-all-outer-iterations-p
         updated n)))))))

(defun sieve-vc-after-set-zero-p (values n)
  (let ((updated
         (sieve-vc-set values 0 nil)))
    (and
     (<= 0 0)
     (< 0 (len values))
     (implies
      (equal (len updated) (len values))
      (implies
       (sieve-vc-update-law-p
        updated values 0 nil)
       (sieve-vc-after-set-one-p
        updated n))))))

(defun-sk sieve-vc-all-initial-arrays-p (n)
  (forall (values)
    (implies
     (sieve-vc-bool-list-p values)
     (implies
      (and
       (sieve-vc-initialized-p values n)
       (equal (len values) n))
      (sieve-vc-after-set-zero-p
       values n)))))

(defun
  ntp4vc-pearl-sieve-sieve-sieveqtvc-statement
  (n)
  (implies
   (and
    (integerp n)
    (< 1 n))
   (and
    (<= 0 n)
    (sieve-vc-all-initial-arrays-p n))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
