;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_b4:
;; the gcd of the entries of A^n-I for A=((3,2),(4,3)) tends to positive
;; infinity. This file contains no proof.

(in-package "ACL2")

;; Matrices are row-major four-entry lists.  These operations are exact over
;; the integers and implement the source matrix A and ordinary matrix powers.
(defun putnam-1994-b4-matrix-a ()
  (list 3 2 4 3))

(defun putnam-1994-b4-identity ()
  (list 1 0 0 1))

(defun putnam-1994-b4-matrix-multiply (left right)
  (list
   (+ (* (nth 0 left) (nth 0 right))
      (* (nth 1 left) (nth 2 right)))
   (+ (* (nth 0 left) (nth 1 right))
      (* (nth 1 left) (nth 3 right)))
   (+ (* (nth 2 left) (nth 0 right))
      (* (nth 3 left) (nth 2 right)))
   (+ (* (nth 2 left) (nth 1 right))
      (* (nth 3 left) (nth 3 right)))))

(defun putnam-1994-b4-matrix-power (matrix exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-1994-b4-identity)
    (putnam-1994-b4-matrix-multiply
     (putnam-1994-b4-matrix-power matrix (- exponent 1))
     matrix)))

(defun putnam-1994-b4-minus-identity (matrix)
  (list
   (- (nth 0 matrix) 1)
   (nth 1 matrix)
   (nth 2 matrix)
   (- (nth 3 matrix) 1)))

(defun putnam-1994-b4-gcd (left right)
  (declare (xargs :measure (+ (nfix left) (nfix right))))
  (if (and (natp left) (natp right))
      (cond
       ((equal left 0) right)
       ((equal right 0) left)
       ((< left right)
        (putnam-1994-b4-gcd left (- right left)))
       (t
        (putnam-1994-b4-gcd (- left right) right)))
    0))

(defun putnam-1994-b4-matrix-gcd (matrix)
  (putnam-1994-b4-gcd
   (putnam-1994-b4-gcd
    (putnam-1994-b4-gcd
     (abs (nth 0 matrix))
     (abs (nth 1 matrix)))
    (abs (nth 2 matrix)))
   (abs (nth 3 matrix))))

(defun putnam-1994-b4-d (n)
  (putnam-1994-b4-matrix-gcd
   (putnam-1994-b4-minus-identity
    (putnam-1994-b4-matrix-power
     (putnam-1994-b4-matrix-a)
     n))))

(defun-sk putnam-1994-b4-tail-p (k cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (<= k (putnam-1994-b4-d n)))))

(defun-sk putnam-1994-b4-cutoff-exists-p (k)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1994-b4-tail-p k cutoff))))

(defun putnambench-putnam-1994-b4-statement (k)
  (implies
   (natp k)
   (putnam-1994-b4-cutoff-exists-p k)))

(value-triple :itpeval-statement-checked)
:q
