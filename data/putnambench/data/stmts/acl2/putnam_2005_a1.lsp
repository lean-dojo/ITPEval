;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_a1:
;; every positive integer is a finite nonempty sum of numbers 2^r * 3^s with
;; natural exponents, with no distinct summand dividing another. This file
;; contains no proof.

(in-package "ACL2")

;; Every summand is positive, so a decomposition of n has length at most n.
;; Also, 2^r * 3^s <= n implies r <= n and s <= n. Thus enumerating nonempty
;; lists of at most n exponent pairs, with both exponents at most n, is
;; bidirectionally equivalent to the source's existential quantification.

(defun putnam-2005-a1-pairs-with-first-through-second (first second)
  (declare (xargs :measure (nfix second)))
  (if (zp second)
      (list (cons (nfix first) 0))
    (cons
     (cons (nfix first) second)
     (putnam-2005-a1-pairs-with-first-through-second
      first
      (- second 1)))))

(defun putnam-2005-a1-pairs-through-first (first bound)
  (declare (xargs :measure (nfix first)))
  (if (zp first)
      (putnam-2005-a1-pairs-with-first-through-second
       0 bound)
    (append
     (putnam-2005-a1-pairs-with-first-through-second
      first bound)
     (putnam-2005-a1-pairs-through-first
      (- first 1)
      bound))))

(defun putnam-2005-a1-prepend-pair-to-each (pair sequences)
  (if (consp sequences)
      (cons
       (cons pair (car sequences))
       (putnam-2005-a1-prepend-pair-to-each
        pair
        (cdr sequences)))
    nil))

(defun putnam-2005-a1-prepend-each-pair (pairs sequences)
  (if (consp pairs)
      (append
       (putnam-2005-a1-prepend-pair-to-each
        (car pairs)
        sequences)
       (putnam-2005-a1-prepend-each-pair
        (cdr pairs)
        sequences))
    nil))

(defun putnam-2005-a1-sequences-exact (length pairs)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      (list nil)
    (putnam-2005-a1-prepend-each-pair
     pairs
     (putnam-2005-a1-sequences-exact
      (- length 1)
      pairs))))

(defun putnam-2005-a1-sequences-through (length pairs)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      nil
    (append
     (putnam-2005-a1-sequences-exact length pairs)
     (putnam-2005-a1-sequences-through
      (- length 1)
      pairs))))

(defun putnam-2005-a1-exponent-pair-p (pair)
  (and (consp pair)
       (natp (car pair))
       (natp (cdr pair))))

(defun putnam-2005-a1-term (pair)
  (* (expt 2 (car pair))
     (expt 3 (cdr pair))))

(defun putnam-2005-a1-divides-p (divisor value)
  (and (posp divisor)
       (integerp value)
       (equal (mod value divisor) 0)))

(defun putnam-2005-a1-compatible-with-sequence-p
    (pair sequence)
  (if (consp sequence)
      (let ((term (putnam-2005-a1-term pair))
            (other (putnam-2005-a1-term (car sequence))))
        (and
         (not (putnam-2005-a1-divides-p term other))
         (not (putnam-2005-a1-divides-p other term))
         (putnam-2005-a1-compatible-with-sequence-p
          pair
          (cdr sequence))))
    (equal sequence nil)))

(defun putnam-2005-a1-pairwise-nondividing-p (sequence)
  (if (consp sequence)
      (and
       (putnam-2005-a1-compatible-with-sequence-p
        (car sequence)
        (cdr sequence))
       (putnam-2005-a1-pairwise-nondividing-p
        (cdr sequence)))
    (equal sequence nil)))

(defun putnam-2005-a1-exponent-pair-list-p (sequence)
  (if (consp sequence)
      (and
       (putnam-2005-a1-exponent-pair-p (car sequence))
       (putnam-2005-a1-exponent-pair-list-p
        (cdr sequence)))
    (equal sequence nil)))

(defun putnam-2005-a1-sum (sequence)
  (if (consp sequence)
      (+ (putnam-2005-a1-term (car sequence))
         (putnam-2005-a1-sum (cdr sequence)))
    0))

(defun putnam-2005-a1-valid-decomposition-p (sequence n)
  (and
   (consp sequence)
   (putnam-2005-a1-exponent-pair-list-p sequence)
   (equal (putnam-2005-a1-sum sequence) n)
   (putnam-2005-a1-pairwise-nondividing-p sequence)))

(defun putnam-2005-a1-some-valid-decomposition-p
    (sequences n)
  (if (consp sequences)
      (or
       (putnam-2005-a1-valid-decomposition-p
        (car sequences)
        n)
       (putnam-2005-a1-some-valid-decomposition-p
        (cdr sequences)
        n))
    nil))

(defun putnam-2005-a1-decomposition-exists-p (n)
  (and
   (posp n)
   (let ((pairs
          (putnam-2005-a1-pairs-through-first n n)))
     (putnam-2005-a1-some-valid-decomposition-p
      (putnam-2005-a1-sequences-through n pairs)
      n))))

(defun putnambench-putnam-2005-a1-statement (n)
  (implies
   (and (integerp n)
        (< 0 n))
   (putnam-2005-a1-decomposition-exists-p n)))

(value-triple :itpeval-statement-checked)
:q
