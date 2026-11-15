;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_b2:
;; the number of representations of each positive integer as a sum of powers
;; of two, with each power used at most three times, is the floor of the value
;; of some real polynomial at that integer. This file contains no proof and
;; does not choose the polynomial witness.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive carrier for arbitrary real values. These
;; conservative interfaces describe a complete Archimedean ordered field,
;; hence the real field up to ordered-field isomorphism.

(defstub putnam-1983-b2-real-p (real-type value) t)
(defstub putnam-1983-b2-zero (real-type) t)
(defstub putnam-1983-b2-one (real-type) t)
(defstub putnam-1983-b2-add (real-type left right) t)
(defstub putnam-1983-b2-mul (real-type left right) t)
(defstub putnam-1983-b2-neg (real-type value) t)
(defstub putnam-1983-b2-inv (real-type value) t)
(defstub putnam-1983-b2-less (real-type left right) t)
(defstub putnam-1983-b2-integer-embed (real-type value) t)
(defstub putnam-1983-b2-supremum (real-type set) t)

(defun putnam-1983-b2-leq (real-type left right)
  (not (putnam-1983-b2-less real-type right left)))

(defun putnam-1983-b2-real-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk putnam-1983-b2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1983-b2-real-p real-type x)
      (putnam-1983-b2-real-p real-type y)
      (putnam-1983-b2-real-p real-type z))
     (let* ((zero (putnam-1983-b2-zero real-type))
            (one (putnam-1983-b2-one real-type))
            (x-plus-y (putnam-1983-b2-add real-type x y))
            (y-plus-z (putnam-1983-b2-add real-type y z))
            (x-times-y (putnam-1983-b2-mul real-type x y))
            (y-times-z (putnam-1983-b2-mul real-type y z))
            (minus-x (putnam-1983-b2-neg real-type x))
            (inverse-x (putnam-1983-b2-inv real-type x)))
       (and
        (putnam-1983-b2-real-p real-type x-plus-y)
        (putnam-1983-b2-real-p real-type x-times-y)
        (putnam-1983-b2-real-p real-type minus-x)
        (putnam-1983-b2-real-p real-type inverse-x)
        (equal
         (putnam-1983-b2-add real-type x-plus-y z)
         (putnam-1983-b2-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1983-b2-add real-type y x))
        (equal (putnam-1983-b2-add real-type x zero) x)
        (equal (putnam-1983-b2-add real-type x minus-x) zero)
        (equal
         (putnam-1983-b2-mul real-type x-times-y z)
         (putnam-1983-b2-mul real-type x y-times-z))
        (equal x-times-y (putnam-1983-b2-mul real-type y x))
        (equal (putnam-1983-b2-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1983-b2-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1983-b2-mul real-type x y-plus-z)
         (putnam-1983-b2-add
          real-type
          (putnam-1983-b2-mul real-type x y)
          (putnam-1983-b2-mul real-type x z))))))))

(defun-sk putnam-1983-b2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1983-b2-real-p real-type x)
      (putnam-1983-b2-real-p real-type y)
      (putnam-1983-b2-real-p real-type z))
     (let ((zero (putnam-1983-b2-zero real-type)))
       (and
        (not (putnam-1983-b2-less real-type x x))
        (or
         (putnam-1983-b2-less real-type x y)
         (equal x y)
         (putnam-1983-b2-less real-type y x))
        (implies
         (and
          (putnam-1983-b2-less real-type x y)
          (putnam-1983-b2-less real-type y z))
         (putnam-1983-b2-less real-type x z))
        (implies
         (putnam-1983-b2-less real-type x y)
         (putnam-1983-b2-less
          real-type
          (putnam-1983-b2-add real-type x z)
          (putnam-1983-b2-add real-type y z)))
        (implies
         (and
          (putnam-1983-b2-less real-type zero x)
          (putnam-1983-b2-less real-type zero y))
         (putnam-1983-b2-less
          real-type
          zero
          (putnam-1983-b2-mul real-type x y))))))))

(defun-sk putnam-1983-b2-integer-embedding-laws-p (real-type)
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (and
      (putnam-1983-b2-real-p
       real-type
       (putnam-1983-b2-integer-embed real-type m))
      (equal
       (putnam-1983-b2-integer-embed real-type (+ m n))
       (putnam-1983-b2-add
        real-type
        (putnam-1983-b2-integer-embed real-type m)
        (putnam-1983-b2-integer-embed real-type n)))
      (equal
       (putnam-1983-b2-integer-embed real-type (* m n))
       (putnam-1983-b2-mul
        real-type
        (putnam-1983-b2-integer-embed real-type m)
        (putnam-1983-b2-integer-embed real-type n)))
      (iff
       (< m n)
       (putnam-1983-b2-less
        real-type
        (putnam-1983-b2-integer-embed real-type m)
        (putnam-1983-b2-integer-embed real-type n)))))))

(defun-sk putnam-1983-b2-valid-real-set-p (real-type set)
  (forall (value)
    (implies
     (putnam-1983-b2-real-set-member-p set value)
     (putnam-1983-b2-real-p real-type value))))

(defun-sk putnam-1983-b2-upper-bound-p (real-type set upper)
  (forall (value)
    (implies
     (and
      (putnam-1983-b2-real-p real-type value)
      (putnam-1983-b2-real-set-member-p set value))
     (putnam-1983-b2-leq real-type value upper))))

(defun-sk putnam-1983-b2-real-set-nonempty-p (real-type set)
  (exists (value)
    (and
     (putnam-1983-b2-real-p real-type value)
     (putnam-1983-b2-real-set-member-p set value))))

(defun-sk putnam-1983-b2-real-set-bounded-p (real-type set)
  (exists (upper)
    (and
     (putnam-1983-b2-real-p real-type upper)
     (putnam-1983-b2-upper-bound-p real-type set upper))))

(defun-sk putnam-1983-b2-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-1983-b2-real-p real-type upper)
      (putnam-1983-b2-upper-bound-p real-type set upper))
     (putnam-1983-b2-leq real-type supremum upper))))

(defun-sk putnam-1983-b2-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1983-b2-valid-real-set-p real-type set)
      (putnam-1983-b2-real-set-nonempty-p real-type set)
      (putnam-1983-b2-real-set-bounded-p real-type set))
     (let ((supremum
            (putnam-1983-b2-supremum real-type set)))
       (and
        (putnam-1983-b2-real-p real-type supremum)
        (putnam-1983-b2-upper-bound-p
         real-type set supremum)
        (putnam-1983-b2-least-upper-bound-p
         real-type set supremum))))))

(defun-sk putnam-1983-b2-archimedean-witness-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-1983-b2-less
      real-type
      value
      (putnam-1983-b2-integer-embed real-type n)))))

(defun-sk putnam-1983-b2-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-1983-b2-real-p real-type value)
     (putnam-1983-b2-archimedean-witness-p
      real-type value))))

(defun putnam-1983-b2-real-field-p (real-type)
  (let ((zero (putnam-1983-b2-zero real-type))
        (one (putnam-1983-b2-one real-type)))
    (and
     (putnam-1983-b2-real-p real-type zero)
     (putnam-1983-b2-real-p real-type one)
     (not (equal zero one))
     (putnam-1983-b2-field-laws-p real-type)
     (putnam-1983-b2-order-laws-p real-type)
     (putnam-1983-b2-less real-type zero one)
     (equal
      (putnam-1983-b2-integer-embed real-type 0)
      zero)
     (equal
      (putnam-1983-b2-integer-embed real-type 1)
      one)
     (putnam-1983-b2-integer-embedding-laws-p real-type)
     (putnam-1983-b2-completeness-p real-type)
     (putnam-1983-b2-archimedean-p real-type))))

;; A representation is uniquely determined by multiplicities a_k in
;; {0,1,2,3}. For positive n, powers with k >= integer-length(n) cannot occur.
;; The base-4 codes therefore enumerate exactly the source multisets.

(defun putnam-1983-b2-coded-sum (code positions power)
  (declare (xargs :measure (nfix positions)))
  (if (zp positions)
      0
    (+
     (* (mod (nfix code) 4) power)
     (putnam-1983-b2-coded-sum
      (floor (nfix code) 4)
      (- positions 1)
      (* 2 power)))))

(defun putnam-1983-b2-matching-code-count
    (candidate-count positions target)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      0
    (let ((code (- candidate-count 1)))
      (+
       (if (equal
            (putnam-1983-b2-coded-sum code positions 1)
            target)
           1
         0)
       (putnam-1983-b2-matching-code-count
        code positions target)))))

(defun putnam-1983-b2-representation-count (n)
  (if (and (natp n) (< 0 n))
      (let ((positions (integer-length n)))
        (putnam-1983-b2-matching-code-count
         (expt 4 positions)
         positions
         n))
    0))

;; Finite coefficient lists, in ascending degree order, represent exactly the
;; real polynomials. Horner evaluation preserves the source's arbitrary
;; existential polynomial instead of selecting a witness in the statement.

(defun putnam-1983-b2-real-list-p (real-type values)
  (if (consp values)
      (and
       (putnam-1983-b2-real-p real-type (car values))
       (putnam-1983-b2-real-list-p real-type (cdr values)))
    (equal values nil)))

(defun putnam-1983-b2-polynomial-value
    (real-type coefficients x)
  (if (consp coefficients)
      (putnam-1983-b2-add
       real-type
       (car coefficients)
       (putnam-1983-b2-mul
        real-type
        x
        (putnam-1983-b2-polynomial-value
         real-type (cdr coefficients) x)))
    (putnam-1983-b2-zero real-type)))

;; For an integer k, floor(x)=k is exactly k <= x < k+1.

(defun-sk putnam-1983-b2-polynomial-works-p
    (real-type coefficients)
  (forall (n)
    (implies
     (and (natp n) (< 0 n))
     (let* ((x
             (putnam-1983-b2-integer-embed real-type n))
            (count
             (putnam-1983-b2-representation-count n))
            (lower
             (putnam-1983-b2-integer-embed
              real-type count))
            (upper
             (putnam-1983-b2-integer-embed
              real-type (+ count 1)))
            (value
             (putnam-1983-b2-polynomial-value
              real-type coefficients x)))
       (and
        (putnam-1983-b2-leq real-type lower value)
        (putnam-1983-b2-less real-type value upper))))))

(defun-sk putnam-1983-b2-polynomial-exists-p (real-type)
  (exists (coefficients)
    (and
     (putnam-1983-b2-real-list-p real-type coefficients)
     (putnam-1983-b2-polynomial-works-p
      real-type coefficients))))

(defun putnam-1983-b2-solution ()
  t)

(defun putnambench-putnam-1983-b2-statement (real-type)
  (implies
   (putnam-1983-b2-real-field-p real-type)
   (iff
    (putnam-1983-b2-solution)
    (putnam-1983-b2-polynomial-exists-p real-type))))

(value-triple :itpeval-statement-checked)
:q
