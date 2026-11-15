;; Statement-only formalization of PutnamBench artifact putnam_1974_a1:
;; 11 is the largest cardinality of a subset of the integers 1 through 16
;; containing no three distinct pairwise relatively prime elements.
;; This file contains no proof.

(in-package "ACL2")

;; A subset of {1,...,16} is represented by its 16-bit characteristic
;; number. This is a bijection with all source subsets, so the exhaustive
;; searches below preserve both the internal existential witness and the
;; universal maximality assertion.

(defun putnam-1974-a1-selected-p (subset-code element)
  (and
   (natp subset-code)
   (posp element)
   (equal
    (mod
     (floor subset-code
            (expt 2 (- element 1)))
     2)
    1)))

(defun putnam-1974-a1-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond
       ((equal a 0) b)
       ((equal b 0) a)
       ((< a b)
        (putnam-1974-a1-gcd a (- b a)))
       (t
        (putnam-1974-a1-gcd (- a b) b)))
    0))

(defun putnam-1974-a1-triple-condition-p
    (subset-code a b c)
  (or
   (not
    (and
     (putnam-1974-a1-selected-p subset-code a)
     (putnam-1974-a1-selected-p subset-code b)
     (putnam-1974-a1-selected-p subset-code c)
     (not (equal a b))
     (not (equal b c))
     (not (equal a c))))
   (< 1 (putnam-1974-a1-gcd a b))
   (< 1 (putnam-1974-a1-gcd b c))
   (< 1 (putnam-1974-a1-gcd a c))))

(defun putnam-1974-a1-all-c-p
    (subset-code a b c)
  (declare (xargs :measure (nfix c)))
  (if (zp c)
      t
    (and
     (putnam-1974-a1-triple-condition-p
      subset-code a b c)
     (putnam-1974-a1-all-c-p
      subset-code a b (- c 1)))))

(defun putnam-1974-a1-all-b-p
    (subset-code a b)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      t
    (and
     (putnam-1974-a1-all-c-p
      subset-code a b 16)
     (putnam-1974-a1-all-b-p
      subset-code a (- b 1)))))

(defun putnam-1974-a1-conspiratorial-p
    (subset-code a)
  (declare (xargs :measure (nfix a)))
  (if (zp a)
      t
    (and
     (putnam-1974-a1-all-b-p
      subset-code a 16)
     (putnam-1974-a1-conspiratorial-p
      subset-code (- a 1)))))

(defun putnam-1974-a1-cardinality-through
    (subset-code element)
  (declare (xargs :measure (nfix element)))
  (if (zp element)
      0
    (+
     (if
         (putnam-1974-a1-selected-p
          subset-code element)
         1
       0)
     (putnam-1974-a1-cardinality-through
      subset-code (- element 1)))))

(defun putnam-1974-a1-valid-subset-code-p
    (subset-code)
  (and
   (natp subset-code)
   (< subset-code (expt 2 16))
   (putnam-1974-a1-conspiratorial-p
    subset-code 16)))

(defun putnam-1974-a1-size-11-exists-p
    (candidate-count)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      nil
    (let ((subset-code (- candidate-count 1)))
      (or
       (and
        (putnam-1974-a1-valid-subset-code-p
         subset-code)
        (equal
         (putnam-1974-a1-cardinality-through
          subset-code 16)
         11))
       (putnam-1974-a1-size-11-exists-p
        subset-code)))))

(defun putnam-1974-a1-all-sizes-at-most-11-p
    (candidate-count)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      t
    (let ((subset-code (- candidate-count 1)))
      (and
       (or
        (not
         (putnam-1974-a1-valid-subset-code-p
          subset-code))
        (<=
         (putnam-1974-a1-cardinality-through
          subset-code 16)
         11))
       (putnam-1974-a1-all-sizes-at-most-11-p
        subset-code)))))

(defun putnambench-putnam-1974-a1-statement ()
  (let ((subset-count (expt 2 16)))
    (and
     (putnam-1974-a1-size-11-exists-p
      subset-count)
     (putnam-1974-a1-all-sizes-at-most-11-p
      subset-count))))

(value-triple :itpeval-statement-checked)
:q
