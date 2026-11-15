;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_a6:
;; every self-referential sequence of 2s and 3s has its 2s at the positions
;; of a Beatty sequence for some real parameter. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive real carrier. Following the repository's
;; statement-only convention, these conservative symbols present an arbitrary
;; Archimedean Dedekind-complete ordered field, hence the real numbers up to
;; ordered-field isomorphism. Every carrier, field, order, completeness, and
;; Archimedean law used by the statement is explicit below.

(defstub putnam-1993-a6-real-p (real-type value) t)
(defstub putnam-1993-a6-zero (real-type) t)
(defstub putnam-1993-a6-one (real-type) t)
(defstub putnam-1993-a6-add (real-type left right) t)
(defstub putnam-1993-a6-multiply (real-type left right) t)
(defstub putnam-1993-a6-negate (real-type value) t)
(defstub putnam-1993-a6-inverse (real-type value) t)
(defstub putnam-1993-a6-less (real-type left right) t)
(defstub putnam-1993-a6-supremum (real-type set) t)

;; The source sequence remains an arbitrary function on the natural numbers.
(defstub putnam-1993-a6-sequence (index) t)

(defun putnam-1993-a6-leq (real-type left right)
  (not (putnam-1993-a6-less real-type right left)))

(defun putnam-1993-a6-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk putnam-1993-a6-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1993-a6-real-p real-type x)
      (putnam-1993-a6-real-p real-type y)
      (putnam-1993-a6-real-p real-type z))
     (let* ((zero (putnam-1993-a6-zero real-type))
            (one (putnam-1993-a6-one real-type))
            (xy-add (putnam-1993-a6-add real-type x y))
            (yz-add (putnam-1993-a6-add real-type y z))
            (xy-mul (putnam-1993-a6-multiply real-type x y))
            (yz-mul (putnam-1993-a6-multiply real-type y z))
            (neg-x (putnam-1993-a6-negate real-type x))
            (inv-x (putnam-1993-a6-inverse real-type x)))
       (and
        (putnam-1993-a6-real-p real-type xy-add)
        (putnam-1993-a6-real-p real-type xy-mul)
        (putnam-1993-a6-real-p real-type neg-x)
        (putnam-1993-a6-real-p real-type inv-x)
        (equal
         (putnam-1993-a6-add real-type xy-add z)
         (putnam-1993-a6-add real-type x yz-add))
        (equal
         (putnam-1993-a6-add real-type x y)
         (putnam-1993-a6-add real-type y x))
        (equal
         (putnam-1993-a6-add real-type x zero)
         x)
        (equal
         (putnam-1993-a6-add real-type x neg-x)
         zero)
        (equal
         (putnam-1993-a6-multiply real-type xy-mul z)
         (putnam-1993-a6-multiply real-type x yz-mul))
        (equal
         (putnam-1993-a6-multiply real-type x y)
         (putnam-1993-a6-multiply real-type y x))
        (equal
         (putnam-1993-a6-multiply real-type x one)
         x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1993-a6-multiply real-type x inv-x)
          one))
        (equal
         (putnam-1993-a6-multiply real-type x yz-add)
         (putnam-1993-a6-add
          real-type
          (putnam-1993-a6-multiply real-type x y)
          (putnam-1993-a6-multiply real-type x z))))))))

(defun-sk putnam-1993-a6-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1993-a6-real-p real-type x)
      (putnam-1993-a6-real-p real-type y)
      (putnam-1993-a6-real-p real-type z))
     (let ((zero (putnam-1993-a6-zero real-type)))
       (and
        (not (putnam-1993-a6-less real-type x x))
        (or
         (equal x y)
         (putnam-1993-a6-less real-type x y)
         (putnam-1993-a6-less real-type y x))
        (implies
         (and
          (putnam-1993-a6-less real-type x y)
          (putnam-1993-a6-less real-type y z))
         (putnam-1993-a6-less real-type x z))
        (implies
         (putnam-1993-a6-less real-type x y)
         (putnam-1993-a6-less
          real-type
          (putnam-1993-a6-add real-type x z)
          (putnam-1993-a6-add real-type y z)))
        (implies
         (and
          (putnam-1993-a6-less real-type zero x)
          (putnam-1993-a6-less real-type zero y))
         (putnam-1993-a6-less
          real-type
          zero
          (putnam-1993-a6-multiply real-type x y))))))))

(defun-sk putnam-1993-a6-valid-real-set-p (real-type set)
  (forall (value)
    (implies
     (putnam-1993-a6-set-member-p set value)
     (putnam-1993-a6-real-p real-type value))))

(defun-sk putnam-1993-a6-upper-bound-p
    (real-type set upper)
  (forall (value)
    (implies
     (and
      (putnam-1993-a6-real-p real-type value)
      (putnam-1993-a6-set-member-p set value))
     (putnam-1993-a6-leq real-type value upper))))

(defun-sk putnam-1993-a6-set-nonempty-p (real-type set)
  (exists (value)
    (and
     (putnam-1993-a6-real-p real-type value)
     (putnam-1993-a6-set-member-p set value))))

(defun-sk putnam-1993-a6-set-bounded-above-p
    (real-type set)
  (exists (upper)
    (and
     (putnam-1993-a6-real-p real-type upper)
     (putnam-1993-a6-upper-bound-p
      real-type set upper))))

(defun-sk putnam-1993-a6-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-1993-a6-real-p real-type upper)
      (putnam-1993-a6-upper-bound-p
       real-type set upper))
     (putnam-1993-a6-leq
      real-type supremum upper))))

(defun-sk putnam-1993-a6-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1993-a6-valid-real-set-p real-type set)
      (putnam-1993-a6-set-nonempty-p real-type set)
      (putnam-1993-a6-set-bounded-above-p real-type set))
     (let ((supremum
            (putnam-1993-a6-supremum real-type set)))
       (and
        (putnam-1993-a6-real-p real-type supremum)
        (putnam-1993-a6-upper-bound-p
         real-type set supremum)
        (putnam-1993-a6-least-upper-bound-p
         real-type set supremum))))))

(defun putnam-1993-a6-real-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1993-a6-zero real-type)
    (putnam-1993-a6-add
     real-type
     (putnam-1993-a6-one real-type)
     (putnam-1993-a6-real-nat real-type (1- n)))))

(defun-sk putnam-1993-a6-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-1993-a6-less
      real-type
      value
      (putnam-1993-a6-real-nat real-type n)))))

(defun-sk putnam-1993-a6-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-1993-a6-real-p real-type value)
     (putnam-1993-a6-archimedean-bound-exists-p
      real-type value))))

(defun putnam-1993-a6-real-field-p (real-type)
  (let ((zero (putnam-1993-a6-zero real-type))
        (one (putnam-1993-a6-one real-type)))
    (and
     (putnam-1993-a6-real-p real-type zero)
     (putnam-1993-a6-real-p real-type one)
     (not (equal zero one))
     (putnam-1993-a6-field-laws-p real-type)
     (putnam-1993-a6-order-laws-p real-type)
     (putnam-1993-a6-less real-type zero one)
     (putnam-1993-a6-complete-p real-type)
     (putnam-1993-a6-archimedean-p real-type))))

;; Sum of seq(i)+1 over 0 <= i < count, exactly as in the source hypothesis.
(defun putnam-1993-a6-prefix-sum (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((index (1- count)))
      (+
       (putnam-1993-a6-prefix-sum index)
       (+ (putnam-1993-a6-sequence index) 1)))))

(defun-sk putnam-1993-a6-prefix-index-exists-p (index)
  (exists (count)
    (and
     (natp count)
     (equal
      index
      (putnam-1993-a6-prefix-sum count)))))

(defun-sk putnam-1993-a6-values-are-two-or-three-p ()
  (forall (index)
    (implies
     (natp index)
     (or
      (equal (putnam-1993-a6-sequence index) 2)
      (equal (putnam-1993-a6-sequence index) 3)))))

(defun-sk putnam-1993-a6-self-referential-p ()
  (forall (index)
    (implies
     (natp index)
     (iff
      (equal (putnam-1993-a6-sequence index) 2)
      (putnam-1993-a6-prefix-index-exists-p index)))))

;; floor(r*m) = n is represented without approximation by the equivalent
;; ordered-field inequalities n <= r*m < n+1.
(defun-sk putnam-1993-a6-beatty-index-p
    (real-type r index)
  (exists (m)
    (and
     (natp m)
     (let ((product
            (putnam-1993-a6-multiply
             real-type
             r
             (putnam-1993-a6-real-nat real-type m))))
       (and
        (putnam-1993-a6-leq
         real-type
         (putnam-1993-a6-real-nat real-type index)
         product)
        (putnam-1993-a6-less
         real-type
         product
         (putnam-1993-a6-real-nat
          real-type (+ index 1))))))))

(defun-sk putnam-1993-a6-beatty-representation-p
    (real-type r)
  (forall (index)
    (implies
     (natp index)
     (iff
      (equal (putnam-1993-a6-sequence index) 2)
      (putnam-1993-a6-beatty-index-p
       real-type r index)))))

(defun-sk putnam-1993-a6-real-witness-exists-p
    (real-type)
  (exists (r)
    (and
     (putnam-1993-a6-real-p real-type r)
     (putnam-1993-a6-beatty-representation-p
      real-type r))))

(defun putnambench-putnam-1993-a6-statement (real-type)
  (implies
   (and
    (putnam-1993-a6-real-field-p real-type)
    (putnam-1993-a6-values-are-two-or-three-p)
    (putnam-1993-a6-self-referential-p))
   (putnam-1993-a6-real-witness-exists-p
    real-type)))

(value-triple :itpeval-statement-checked)
:q
