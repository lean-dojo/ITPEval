;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_a1:
;; positive coprime numerator-denominator sequences satisfying the stated
;; rational recurrence have only finitely many indices where their odd
;; transforms are not coprime. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the two arbitrary sequences from
;; the source theorem. Their natural-valuedness, positivity, recurrence, and
;; coprimality assumptions are all explicit in the statement predicate.

(defstub putnam-2025-a1-m (k) t)
(defstub putnam-2025-a1-n (k) t)

;; On positive integers, checking every possible common divisor from the
;; smaller input down to 2 is equivalent to Nat.Coprime in the Lean source.

(defun putnam-2025-a1-coprime-through-p (a b divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (and (natp divisor) (< 1 divisor))
      (and
       (not
        (and
         (equal (mod a divisor) 0)
         (equal (mod b divisor) 0)))
       (putnam-2025-a1-coprime-through-p
        a b (- divisor 1)))
    t))

(defun putnam-2025-a1-coprime-p (a b)
  (and
   (posp a)
   (posp b)
   (putnam-2025-a1-coprime-through-p
    a b (if (< a b) a b))))

(defun-sk putnam-2025-a1-positive-sequences-p ()
  (forall (k)
    (implies
     (natp k)
     (and
      (posp (putnam-2025-a1-m k))
      (posp (putnam-2025-a1-n k))))))

(defun-sk putnam-2025-a1-reduced-positive-tail-p ()
  (forall (k)
    (implies
     (and (natp k) (< 0 k))
     (putnam-2025-a1-coprime-p
      (putnam-2025-a1-m k)
      (putnam-2025-a1-n k)))))

;; Under positivity, this cross-multiplied equality is equivalent to
;;
;;   m_(k+1) / n_(k+1) = (2*m_k+1) / (2*n_k+1).

(defun-sk putnam-2025-a1-recurrence-p ()
  (forall (k)
    (implies
     (natp k)
     (equal
      (*
       (putnam-2025-a1-m (+ k 1))
       (+ (* 2 (putnam-2025-a1-n k)) 1))
      (*
       (putnam-2025-a1-n (+ k 1))
       (+ (* 2 (putnam-2025-a1-m k)) 1))))))

(defun-sk putnam-2025-a1-eventual-coprime-tail-p (cutoff)
  (forall (k)
    (implies
     (and
      (natp k)
      (< cutoff k))
     (putnam-2025-a1-coprime-p
      (+ (* 2 (putnam-2025-a1-m k)) 1)
      (+ (* 2 (putnam-2025-a1-n k)) 1)))))

;; A subset of the natural numbers is finite exactly when it is bounded.
;; Therefore this existential cutoff is equivalent to finiteness of the
;; exceptional set in the Lean conclusion.

(defun-sk putnam-2025-a1-finite-exceptional-set-p ()
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2025-a1-eventual-coprime-tail-p cutoff))))

(defun putnambench-putnam-2025-a1-statement ()
  (implies
   (and
    (putnam-2025-a1-positive-sequences-p)
    (not
     (equal
      (putnam-2025-a1-m 0)
      (putnam-2025-a1-n 0)))
    (putnam-2025-a1-reduced-positive-tail-p)
    (putnam-2025-a1-recurrence-p))
   (putnam-2025-a1-finite-exceptional-set-p)))

(value-triple :itpeval-statement-checked)
:q
