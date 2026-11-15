;; Statement-only formalization of PutnamBench corpus artifact putnam_1968_b5:
;; for prime p, the number of 2 by 2 matrices over ZMod p with trace one and
;; determinant zero is p^2 + p. This file contains no proof.

(in-package "ACL2")

;; Every element of ZMod p has a unique representative in {0,...,p-1}.
;; Consequently, matrices over ZMod p are in bijection with the quadruples
;; enumerated below. ACL2's mod by the positive prime p expresses exactly the
;; two source equalities in ZMod p, so the nested count is the source ncard.

(defun putnam-1968-b5-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1968-b5-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1968-b5-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1968-b5-no-divisor-through-p
    p (- p 1))))

(defun putnam-1968-b5-matrix-p (p a b c d)
  (and
   (natp p)
   (< 0 p)
   (natp a)
   (< a p)
   (natp b)
   (< b p)
   (natp c)
   (< c p)
   (natp d)
   (< d p)
   (equal (mod (+ a d) p) 1)
   (equal (mod (- (* a d) (* b c)) p) 0)))

(defun putnam-1968-b5-count-d (p a b c d-count)
  (declare (xargs :measure (nfix d-count)))
  (if (zp d-count)
      0
    (let ((d (- d-count 1)))
      (+
       (if (putnam-1968-b5-matrix-p p a b c d)
           1
         0)
       (putnam-1968-b5-count-d p a b c d)))))

(defun putnam-1968-b5-count-c (p a b c-count)
  (declare (xargs :measure (nfix c-count)))
  (if (zp c-count)
      0
    (let ((c (- c-count 1)))
      (+
       (putnam-1968-b5-count-d p a b c p)
       (putnam-1968-b5-count-c p a b c)))))

(defun putnam-1968-b5-count-b (p a b-count)
  (declare (xargs :measure (nfix b-count)))
  (if (zp b-count)
      0
    (let ((b (- b-count 1)))
      (+
       (putnam-1968-b5-count-c p a b p)
       (putnam-1968-b5-count-b p a b)))))

(defun putnam-1968-b5-count-a (p a-count)
  (declare (xargs :measure (nfix a-count)))
  (if (zp a-count)
      0
    (let ((a (- a-count 1)))
      (+
       (putnam-1968-b5-count-b p a p)
       (putnam-1968-b5-count-a p a)))))

(defun putnam-1968-b5-matrix-count (p)
  (if (natp p)
      (putnam-1968-b5-count-a p p)
    0))

(defun putnambench-putnam-1968-b5-statement (p)
  (implies
   (and
    (natp p)
    (putnam-1968-b5-prime-p p))
   (equal
    (putnam-1968-b5-matrix-count p)
    (+ (* p p) p))))

(value-triple :itpeval-statement-checked)
:q
