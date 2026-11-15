;; Statement-only formalization of PutnamBench artifact putnam_1965_b3:
;; exactly three positive integer right triangles, with the shorter leg first,
;; have area equal to twice their perimeter. This file contains no proof.

(in-package "ACL2")

;; This is the source predicate on integer triples. ACL2 division is exact on
;; rationals, matching the rational area equation in the Lean and Rocq sources;
;; the Isabelle integer division agrees because a*b is even for every integer
;; Pythagorean triple.
(defun putnam-1965-b3-solution-p (a b c)
  (and (integerp a)
       (integerp b)
       (integerp c)
       (< 0 a)
       (<= a b)
       (< 0 c)
       (equal (+ (* a a) (* b b))
              (* c c))
       (equal (/ (* a b) 2)
              (* 2 (+ a b c)))))

;; Exact cardinality is expressed without a proof-derived search bound:
;; three distinct triples are solutions, and every solution is one of them.

(defun putnam-1965-b3-same-triple-p
    (a b c x y z)
  (and (equal a x)
       (equal b y)
       (equal c z)))

(defun-sk putnam-1965-b3-all-solutions-listed-p
    (a1 b1 c1 a2 b2 c2 a3 b3 c3)
  (forall (a b c)
    (implies
     (putnam-1965-b3-solution-p a b c)
     (or
      (putnam-1965-b3-same-triple-p a b c a1 b1 c1)
      (putnam-1965-b3-same-triple-p a b c a2 b2 c2)
      (putnam-1965-b3-same-triple-p a b c a3 b3 c3)))))

(defun putnam-1965-b3-exactly-three-witness-p
    (a1 b1 c1 a2 b2 c2 a3 b3 c3)
  (and
   (putnam-1965-b3-solution-p a1 b1 c1)
   (putnam-1965-b3-solution-p a2 b2 c2)
   (putnam-1965-b3-solution-p a3 b3 c3)
   (not (putnam-1965-b3-same-triple-p a1 b1 c1 a2 b2 c2))
   (not (putnam-1965-b3-same-triple-p a1 b1 c1 a3 b3 c3))
   (not (putnam-1965-b3-same-triple-p a2 b2 c2 a3 b3 c3))
   (putnam-1965-b3-all-solutions-listed-p
    a1 b1 c1 a2 b2 c2 a3 b3 c3)))

(defun-sk putnambench-putnam-1965-b3-statement ()
  (exists (a1 b1 c1 a2 b2 c2 a3 b3 c3)
    (putnam-1965-b3-exactly-three-witness-p
     a1 b1 c1 a2 b2 c2 a3 b3 c3)))

(value-triple :itpeval-statement-checked)
:q
