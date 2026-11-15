;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_b1:
;; positive integer multiples of square roots have a difference strictly
;; between epsilon and twice epsilon for every positive real epsilon. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative generic symbol is an arbitrary rational Cauchy name for
;; EPSILON. Regularity and positivity remain explicit in the statement, so
;; the symbol supplies no mathematical assumption by itself.
(defstub putnam-2011-b1-epsilon-approx (precision) t)

;; A regular rational Cauchy name denotes an exact element of the real
;; completion. Thus EPSILON is an arbitrary positive real, not a rational.
(defun putnam-2011-b1-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun-sk putnam-2011-b1-regular-real-name-p ()
  (forall (precision eta)
    (implies
     (and
      (putnam-2011-b1-positive-rational-p precision)
      (putnam-2011-b1-positive-rational-p eta))
     (let ((left (putnam-2011-b1-epsilon-approx precision))
           (right (putnam-2011-b1-epsilon-approx eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ precision eta)))))))

;; For a regular name, these predicates are exactly strict comparison with a
;; rational. The positive MARGIN makes the comparison strict, and rational
;; density makes the existential characterizations bidirectional.
(defun-sk putnam-2011-b1-real-less-than-rational-p (q)
  (exists (precision margin)
    (and
     (rationalp q)
     (putnam-2011-b1-positive-rational-p precision)
     (putnam-2011-b1-positive-rational-p margin)
     (let ((sample
            (putnam-2011-b1-epsilon-approx precision)))
       (and
        (rationalp sample)
        (< (+ sample precision margin) q))))))

(defun-sk putnam-2011-b1-rational-less-than-real-p (q)
  (exists (precision margin)
    (and
     (rationalp q)
     (putnam-2011-b1-positive-rational-p precision)
     (putnam-2011-b1-positive-rational-p margin)
     (let ((sample
            (putnam-2011-b1-epsilon-approx precision)))
       (and
        (rationalp sample)
        (< (+ q precision margin) sample))))))

(defun putnam-2011-b1-positive-real-p ()
  (and
   (putnam-2011-b1-regular-real-name-p)
   (putnam-2011-b1-rational-less-than-real-p 0)))

;; For positive A and B, |sqrt(A)-sqrt(B)| < Q is equivalent to
;; A+B-Q^2 < 2*sqrt(A*B). Squaring after the sign split is exact.
(defun putnam-2011-b1-root-distance-less-p (a b q)
  (and
   (posp a)
   (posp b)
   (rationalp q)
   (< 0 q)
   (let ((side (- (+ a b) (* q q))))
     (or
      (< side 0)
      (< (* side side)
         (* 4 a b))))))

;; This is the analogous exact characterization of
;; Q < |sqrt(A)-sqrt(B)|.
(defun putnam-2011-b1-root-distance-greater-p (a b q)
  (and
   (posp a)
   (posp b)
   (rationalp q)
   (< 0 q)
   (let ((side (- (+ a b) (* q q))))
     (and
      (< 0 side)
      (< (* 4 a b)
         (* side side))))))

;; LOWER and UPPER are dense rational separators:
;;
;;   epsilon < LOWER < |h*sqrt(m)-k*sqrt(n)|
;;     < UPPER < 2*epsilon.
;;
;; Their existence is equivalent to the source's two strict real
;; inequalities. The positive integer witnesses M and N remain internal.
(defun-sk putnam-2011-b1-witness-exists-p (h k)
  (exists (m n lower upper)
    (and
     (posp m)
     (posp n)
     (putnam-2011-b1-real-less-than-rational-p
      lower)
     (let ((left (* h h m))
           (right (* k k n)))
       (and
        (putnam-2011-b1-root-distance-greater-p
         left right lower)
        (putnam-2011-b1-root-distance-less-p
         left right upper)))
     (putnam-2011-b1-rational-less-than-real-p
      (/ upper 2)))))

(defun putnambench-putnam-2011-b1-statement (h k)
  (implies
   (and
    (posp h)
    (posp k)
    (putnam-2011-b1-positive-real-p))
   (putnam-2011-b1-witness-exists-p h k)))

(value-triple :itpeval-statement-checked)
:q
