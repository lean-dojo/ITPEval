;; Statement-only formalization of PutnamBench corpus artifact putnam_1963_a4:
;; every positive real sequence has the specified transformed sequence with
;; extended-real limsup at least 1, and no larger universal lower bound works.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has no native arbitrary real numbers.  These conservative
;; interfaces represent a complete Archimedean ordered field, hence the real
;; field up to its unique order-preserving isomorphism, together with arbitrary
;; total sequences on the natural numbers.  The field laws and sequential
;; completeness are explicit hypotheses of the statement; no property of the
;; interfaces is assumed merely from DEFSTUB.

(defstub p63a4-real-p (real-type value) t)
(defstub p63a4-zero (real-type) t)
(defstub p63a4-one (real-type) t)
(defstub p63a4-add (real-type left right) t)
(defstub p63a4-multiply (real-type left right) t)
(defstub p63a4-negate (real-type value) t)
(defstub p63a4-inverse (real-type value) t)
(defstub p63a4-less (real-type left right) t)
(defstub p63a4-sequence-value (real-type sequence index) t)

(defun p63a4-leq (real-type left right)
  (not (p63a4-less real-type right left)))

(defun p63a4-subtract (real-type left right)
  (p63a4-add
   real-type left (p63a4-negate real-type right)))

(defun p63a4-divide (real-type numerator denominator)
  (p63a4-multiply
   real-type numerator (p63a4-inverse real-type denominator)))

(defun p63a4-absolute-value (real-type value)
  (if (p63a4-less real-type value (p63a4-zero real-type))
      (p63a4-negate real-type value)
    value))

(defun p63a4-natural-value (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p63a4-zero real-type)
    (p63a4-add
     real-type
     (p63a4-one real-type)
     (p63a4-natural-value real-type (1- n)))))

(defun-sk p63a4-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p63a4-real-p real-type x)
      (p63a4-real-p real-type y)
      (p63a4-real-p real-type z))
     (let* ((zero (p63a4-zero real-type))
            (one (p63a4-one real-type))
            (x-plus-y (p63a4-add real-type x y))
            (y-plus-z (p63a4-add real-type y z))
            (x-times-y (p63a4-multiply real-type x y))
            (y-times-z (p63a4-multiply real-type y z))
            (minus-x (p63a4-negate real-type x))
            (inverse-x (p63a4-inverse real-type x)))
       (and
        (p63a4-real-p real-type x-plus-y)
        (p63a4-real-p real-type x-times-y)
        (p63a4-real-p real-type minus-x)
        (p63a4-real-p real-type inverse-x)
        (equal
         (p63a4-add real-type x-plus-y z)
         (p63a4-add real-type x y-plus-z))
        (equal x-plus-y (p63a4-add real-type y x))
        (equal (p63a4-add real-type x zero) x)
        (equal (p63a4-add real-type x minus-x) zero)
        (equal
         (p63a4-multiply real-type x-times-y z)
         (p63a4-multiply real-type x y-times-z))
        (equal x-times-y (p63a4-multiply real-type y x))
        (equal (p63a4-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p63a4-multiply real-type x inverse-x)
          one))
        (equal
         (p63a4-multiply real-type x y-plus-z)
         (p63a4-add
          real-type
          (p63a4-multiply real-type x y)
          (p63a4-multiply real-type x z))))))))

(defun-sk p63a4-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p63a4-real-p real-type x)
      (p63a4-real-p real-type y)
      (p63a4-real-p real-type z))
     (let ((zero (p63a4-zero real-type)))
       (and
        (not (p63a4-less real-type x x))
        (or
         (p63a4-less real-type x y)
         (equal x y)
         (p63a4-less real-type y x))
        (implies
         (and
          (p63a4-less real-type x y)
          (p63a4-less real-type y z))
         (p63a4-less real-type x z))
        (implies
         (p63a4-less real-type x y)
         (p63a4-less
          real-type
          (p63a4-add real-type x z)
          (p63a4-add real-type y z)))
        (implies
         (and
          (p63a4-less real-type zero x)
          (p63a4-less real-type zero y))
         (p63a4-less
          real-type
          zero
          (p63a4-multiply real-type x y))))))))

(defun-sk p63a4-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (p63a4-less
      real-type value (p63a4-natural-value real-type n)))))

(defun-sk p63a4-archimedean-p (real-type)
  (forall (value)
    (implies
     (p63a4-real-p real-type value)
     (p63a4-archimedean-bound-exists-p
      real-type value))))

(defun-sk p63a4-sequence-real-valued-p
    (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (p63a4-real-p
      real-type
      (p63a4-sequence-value real-type sequence n)))))

(defun-sk p63a4-cauchy-tail-p
    (real-type sequence epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (p63a4-less
      real-type
      (p63a4-absolute-value
       real-type
       (p63a4-subtract
        real-type
        (p63a4-sequence-value real-type sequence m)
        (p63a4-sequence-value real-type sequence n)))
      epsilon))))

(defun-sk p63a4-cauchy-cutoff-exists-p
    (real-type sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p63a4-cauchy-tail-p
      real-type sequence epsilon cutoff))))

(defun-sk p63a4-cauchy-sequence-p
    (real-type sequence)
  (forall (epsilon)
    (implies
     (and
      (p63a4-real-p real-type epsilon)
      (p63a4-less
       real-type (p63a4-zero real-type) epsilon))
     (p63a4-cauchy-cutoff-exists-p
      real-type sequence epsilon))))

(defun-sk p63a4-convergence-tail-p
    (real-type sequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (p63a4-less
      real-type
      (p63a4-absolute-value
       real-type
       (p63a4-subtract
        real-type
        (p63a4-sequence-value real-type sequence n)
        limit))
      epsilon))))

(defun-sk p63a4-convergence-cutoff-exists-p
    (real-type sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p63a4-convergence-tail-p
      real-type sequence limit epsilon cutoff))))

(defun-sk p63a4-sequence-converges-p
    (real-type sequence limit)
  (forall (epsilon)
    (implies
     (and
      (p63a4-real-p real-type epsilon)
      (p63a4-less
       real-type (p63a4-zero real-type) epsilon))
     (p63a4-convergence-cutoff-exists-p
      real-type sequence limit epsilon))))

(defun-sk p63a4-limit-exists-p
    (real-type sequence)
  (exists (limit)
    (and
     (p63a4-real-p real-type limit)
     (p63a4-sequence-converges-p
      real-type sequence limit))))

(defun-sk p63a4-sequentially-complete-p (real-type)
  (forall (sequence)
    (implies
     (and
      (p63a4-sequence-real-valued-p real-type sequence)
      (p63a4-cauchy-sequence-p real-type sequence))
     (p63a4-limit-exists-p real-type sequence))))

(defun p63a4-real-structure-p (real-type)
  (let ((zero (p63a4-zero real-type))
        (one (p63a4-one real-type)))
    (and
     (p63a4-real-p real-type zero)
     (p63a4-real-p real-type one)
     (not (equal zero one))
     (p63a4-field-laws-p real-type)
     (p63a4-order-laws-p real-type)
     (p63a4-less real-type zero one)
     (p63a4-archimedean-p real-type)
     (p63a4-sequentially-complete-p real-type))))

(defun-sk p63a4-positive-sequence-values-p
    (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (p63a4-less
      real-type
      (p63a4-zero real-type)
      (p63a4-sequence-value real-type sequence n)))))

(defun p63a4-positive-sequence-p (real-type sequence)
  (and
   (p63a4-sequence-real-valued-p real-type sequence)
   (p63a4-positive-sequence-values-p real-type sequence)))

(defun p63a4-transformed-value (real-type sequence n)
  (p63a4-multiply
   real-type
   (p63a4-natural-value real-type n)
   (p63a4-subtract
    real-type
    (p63a4-divide
     real-type
     (p63a4-add
      real-type
      (p63a4-one real-type)
      (p63a4-sequence-value
       real-type sequence (+ n 1)))
     (p63a4-sequence-value real-type sequence n))
    (p63a4-one real-type))))

;; For a real-valued sequence u, this is definitionally equivalent to
;; C <= limsup u in the extended reals:
;;
;;   every b < C is exceeded by u_n at arbitrarily late indices.
;;
;; Thus the same predicate covers both bounded sequences and the +infinity
;; case without replacing limsup by a finite approximation.

(defun-sk p63a4-eventual-exceedance-exists-p
    (real-type sequence lower-bound cutoff)
  (exists (n)
    (and
     (natp n)
     (<= cutoff n)
     (p63a4-less
      real-type
      lower-bound
      (p63a4-transformed-value
       real-type sequence n)))))

(defun-sk p63a4-at-most-extended-limsup-p
    (real-type sequence bound)
  (forall (lower-bound cutoff)
    (implies
     (and
      (p63a4-real-p real-type lower-bound)
      (p63a4-less real-type lower-bound bound)
      (natp cutoff))
     (p63a4-eventual-exceedance-exists-p
      real-type sequence lower-bound cutoff))))

(defun-sk p63a4-universal-lower-bound-p (real-type)
  (forall (sequence)
    (implies
     (p63a4-positive-sequence-p real-type sequence)
     (p63a4-at-most-extended-limsup-p
      real-type sequence (p63a4-one real-type)))))

(defun-sk p63a4-sharp-counterexample-exists-p
    (real-type bound)
  (exists (sequence)
    (and
     (p63a4-positive-sequence-p real-type sequence)
     (not
      (p63a4-at-most-extended-limsup-p
       real-type sequence bound)))))

(defun-sk p63a4-sharpness-p (real-type)
  (forall (bound)
    (implies
     (and
      (p63a4-real-p real-type bound)
      (p63a4-less
       real-type (p63a4-one real-type) bound))
     (p63a4-sharp-counterexample-exists-p
      real-type bound))))

(defun putnambench-putnam-1963-a4-statement (real-type)
  (implies
   (p63a4-real-structure-p real-type)
   (and
    (p63a4-universal-lower-bound-p real-type)
    (p63a4-sharpness-p real-type))))

(value-triple :itpeval-statement-checked)
:q
