;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_a3:
;; a nonzero real sequence satisfying the stated recurrence has integer terms
;; at arbitrarily large indices exactly when its first two terms are the same
;; integer. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive carrier of arbitrary real values. Following
;; the repository's native ACL2 convention, these conservative interfaces
;; describe a complete Archimedean ordered field, hence the real field up to
;; ordered-field isomorphism. The sequence remains an arbitrary function on
;; natural indices; no reciprocal substitution or solved recurrence is built
;; into the statement.

(defstub putnam-1979-a3-real-p (real-type value) t)
(defstub putnam-1979-a3-zero (real-type) t)
(defstub putnam-1979-a3-one (real-type) t)
(defstub putnam-1979-a3-add (real-type left right) t)
(defstub putnam-1979-a3-mul (real-type left right) t)
(defstub putnam-1979-a3-neg (real-type value) t)
(defstub putnam-1979-a3-inv (real-type value) t)
(defstub putnam-1979-a3-less (real-type left right) t)
(defstub putnam-1979-a3-integer-embed (real-type value) t)
(defstub putnam-1979-a3-supremum (real-type set) t)
(defstub putnam-1979-a3-x (real-type index) t)

(defun putnam-1979-a3-leq (real-type left right)
  (not (putnam-1979-a3-less real-type right left)))

(defun putnam-1979-a3-sub (real-type left right)
  (putnam-1979-a3-add
   real-type left (putnam-1979-a3-neg real-type right)))

(defun putnam-1979-a3-div (real-type numerator denominator)
  (putnam-1979-a3-mul
   real-type numerator (putnam-1979-a3-inv real-type denominator)))

(defun putnam-1979-a3-real-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk putnam-1979-a3-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1979-a3-real-p real-type x)
      (putnam-1979-a3-real-p real-type y)
      (putnam-1979-a3-real-p real-type z))
     (let* ((zero (putnam-1979-a3-zero real-type))
            (one (putnam-1979-a3-one real-type))
            (x-plus-y (putnam-1979-a3-add real-type x y))
            (y-plus-z (putnam-1979-a3-add real-type y z))
            (x-times-y (putnam-1979-a3-mul real-type x y))
            (y-times-z (putnam-1979-a3-mul real-type y z))
            (minus-x (putnam-1979-a3-neg real-type x))
            (inverse-x (putnam-1979-a3-inv real-type x)))
       (and
        (putnam-1979-a3-real-p real-type x-plus-y)
        (putnam-1979-a3-real-p real-type x-times-y)
        (putnam-1979-a3-real-p real-type minus-x)
        (putnam-1979-a3-real-p real-type inverse-x)
        (equal
         (putnam-1979-a3-add real-type x-plus-y z)
         (putnam-1979-a3-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1979-a3-add real-type y x))
        (equal (putnam-1979-a3-add real-type x zero) x)
        (equal (putnam-1979-a3-add real-type x minus-x) zero)
        (equal
         (putnam-1979-a3-mul real-type x-times-y z)
         (putnam-1979-a3-mul real-type x y-times-z))
        (equal x-times-y (putnam-1979-a3-mul real-type y x))
        (equal (putnam-1979-a3-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1979-a3-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1979-a3-mul real-type x y-plus-z)
         (putnam-1979-a3-add
          real-type
          (putnam-1979-a3-mul real-type x y)
          (putnam-1979-a3-mul real-type x z))))))))

(defun-sk putnam-1979-a3-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1979-a3-real-p real-type x)
      (putnam-1979-a3-real-p real-type y)
      (putnam-1979-a3-real-p real-type z))
     (let ((zero (putnam-1979-a3-zero real-type)))
       (and
        (not (putnam-1979-a3-less real-type x x))
        (or
         (putnam-1979-a3-less real-type x y)
         (equal x y)
         (putnam-1979-a3-less real-type y x))
        (implies
         (and
          (putnam-1979-a3-less real-type x y)
          (putnam-1979-a3-less real-type y z))
         (putnam-1979-a3-less real-type x z))
        (implies
         (putnam-1979-a3-less real-type x y)
         (putnam-1979-a3-less
          real-type
          (putnam-1979-a3-add real-type x z)
          (putnam-1979-a3-add real-type y z)))
        (implies
         (and
          (putnam-1979-a3-less real-type zero x)
          (putnam-1979-a3-less real-type zero y))
         (putnam-1979-a3-less
          real-type
          zero
          (putnam-1979-a3-mul real-type x y))))))))

(defun-sk putnam-1979-a3-integer-embedding-laws-p
    (real-type)
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (and
      (putnam-1979-a3-real-p
       real-type
       (putnam-1979-a3-integer-embed real-type m))
      (equal
       (putnam-1979-a3-integer-embed real-type (+ m n))
       (putnam-1979-a3-add
        real-type
        (putnam-1979-a3-integer-embed real-type m)
        (putnam-1979-a3-integer-embed real-type n)))
      (equal
       (putnam-1979-a3-integer-embed real-type (* m n))
       (putnam-1979-a3-mul
        real-type
        (putnam-1979-a3-integer-embed real-type m)
        (putnam-1979-a3-integer-embed real-type n)))
      (iff
       (< m n)
       (putnam-1979-a3-less
        real-type
        (putnam-1979-a3-integer-embed real-type m)
        (putnam-1979-a3-integer-embed real-type n)))))))

(defun-sk putnam-1979-a3-valid-real-set-p
    (real-type set)
  (forall (value)
    (implies
     (putnam-1979-a3-real-set-member-p set value)
     (putnam-1979-a3-real-p real-type value))))

(defun-sk putnam-1979-a3-upper-bound-p
    (real-type set upper)
  (forall (value)
    (implies
     (and
      (putnam-1979-a3-real-p real-type value)
      (putnam-1979-a3-real-set-member-p set value))
     (putnam-1979-a3-leq real-type value upper))))

(defun-sk putnam-1979-a3-real-set-nonempty-p
    (real-type set)
  (exists (value)
    (and
     (putnam-1979-a3-real-p real-type value)
     (putnam-1979-a3-real-set-member-p set value))))

(defun-sk putnam-1979-a3-real-set-bounded-p
    (real-type set)
  (exists (upper)
    (and
     (putnam-1979-a3-real-p real-type upper)
     (putnam-1979-a3-upper-bound-p
      real-type set upper))))

(defun-sk putnam-1979-a3-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-1979-a3-real-p real-type upper)
      (putnam-1979-a3-upper-bound-p
       real-type set upper))
     (putnam-1979-a3-leq
      real-type supremum upper))))

(defun-sk putnam-1979-a3-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1979-a3-valid-real-set-p real-type set)
      (putnam-1979-a3-real-set-nonempty-p real-type set)
      (putnam-1979-a3-real-set-bounded-p real-type set))
     (let ((supremum
            (putnam-1979-a3-supremum real-type set)))
       (and
        (putnam-1979-a3-real-p real-type supremum)
        (putnam-1979-a3-upper-bound-p
         real-type set supremum)
        (putnam-1979-a3-least-upper-bound-p
         real-type set supremum))))))

(defun-sk putnam-1979-a3-archimedean-witness-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-1979-a3-less
      real-type
      value
      (putnam-1979-a3-integer-embed real-type n)))))

(defun-sk putnam-1979-a3-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-1979-a3-real-p real-type value)
     (putnam-1979-a3-archimedean-witness-p
      real-type value))))

(defun putnam-1979-a3-real-field-p (real-type)
  (let ((zero (putnam-1979-a3-zero real-type))
        (one (putnam-1979-a3-one real-type)))
    (and
     (putnam-1979-a3-real-p real-type zero)
     (putnam-1979-a3-real-p real-type one)
     (not (equal zero one))
     (putnam-1979-a3-field-laws-p real-type)
     (putnam-1979-a3-order-laws-p real-type)
     (putnam-1979-a3-less real-type zero one)
     (equal
      (putnam-1979-a3-integer-embed real-type 0)
      zero)
     (equal
      (putnam-1979-a3-integer-embed real-type 1)
      one)
     (putnam-1979-a3-integer-embedding-laws-p real-type)
     (putnam-1979-a3-completeness-p real-type)
     (putnam-1979-a3-archimedean-p real-type))))

(defun-sk putnam-1979-a3-sequence-real-valued-p
    (real-type)
  (forall (n)
    (implies
     (natp n)
     (putnam-1979-a3-real-p
      real-type
      (putnam-1979-a3-x real-type n)))))

(defun-sk putnam-1979-a3-sequence-nonzero-p
    (real-type)
  (forall (n)
    (implies
     (natp n)
     (not
      (equal
       (putnam-1979-a3-x real-type n)
       (putnam-1979-a3-zero real-type))))))

(defun-sk putnam-1979-a3-recurrence-p (real-type)
  (forall (n)
    (implies
     (and (natp n) (<= 3 n))
     (let* ((x-n-2
             (putnam-1979-a3-x real-type (- n 2)))
            (x-n-1
             (putnam-1979-a3-x real-type (- n 1)))
            (two
             (putnam-1979-a3-add
              real-type
              (putnam-1979-a3-one real-type)
              (putnam-1979-a3-one real-type))))
       (equal
        (putnam-1979-a3-x real-type n)
        (putnam-1979-a3-div
         real-type
         (putnam-1979-a3-mul real-type x-n-2 x-n-1)
         (putnam-1979-a3-sub
          real-type
          (putnam-1979-a3-mul real-type two x-n-2)
          x-n-1)))))))

(defun-sk putnam-1979-a3-later-integral-term-p
    (real-type m)
  (exists (n integer-value)
    (and
     (natp n)
     (< m n)
     (integerp integer-value)
     (equal
      (putnam-1979-a3-x real-type n)
      (putnam-1979-a3-integer-embed
       real-type integer-value)))))

(defun-sk putnam-1979-a3-infinitely-many-integral-p
    (real-type)
  (forall (m)
    (implies
     (natp m)
     (putnam-1979-a3-later-integral-term-p
      real-type m))))

(defun-sk putnam-1979-a3-solution-p (real-type)
  (exists (integer-value)
    (and
     (integerp integer-value)
     (equal
      (putnam-1979-a3-x real-type 1)
      (putnam-1979-a3-integer-embed
       real-type integer-value))
     (equal
      (putnam-1979-a3-x real-type 2)
      (putnam-1979-a3-integer-embed
       real-type integer-value)))))

(defun putnambench-putnam-1979-a3-statement (real-type)
  (implies
   (and
    (putnam-1979-a3-real-field-p real-type)
    (putnam-1979-a3-sequence-real-valued-p real-type)
    (putnam-1979-a3-sequence-nonzero-p real-type)
    (putnam-1979-a3-recurrence-p real-type))
   (iff
    (putnam-1979-a3-infinitely-many-integral-p real-type)
    (putnam-1979-a3-solution-p real-type))))

(value-triple :itpeval-statement-checked)
:q
