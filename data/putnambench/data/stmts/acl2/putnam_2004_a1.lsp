;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_a1:
;; a finite prefix of free-throw attempts whose success rate rises from below
;; 80 percent to above 80 percent has an intermediate prefix with success rate
;; exactly 80 percent. This file contains no proof.

(in-package "ACL2")

;; For fixed a < b, the source proposition reads an attempt sequence only at
;; indices below b. ATTEMPTS therefore records exactly that length-b binary
;; prefix. Restricting any infinite Boolean (or Fin 2) sequence gives such a
;; list, and every such list extends to an infinite sequence by appending
;; zeros, so this is a bidirectional finite-prefix encoding rather than a
;; restriction to finite sequences.
;;
;; The hypothesis hS uniquely defines S at every positive index used here.
;; If C(N) is the number of successes in the first N attempts, comparison of
;; S(N) = C(N)/N with 0.8 = 4/5 is exactly comparison of 5*C(N) with 4*N.
;; Thus the integer formulas below definitionally eliminate both S and the
;; real-valued divisions without changing any inequality or equality.

(defun putnam-2004-a1-binary-prefix-p (attempts)
  (if (consp attempts)
      (and (or (equal (car attempts) 0)
               (equal (car attempts) 1))
           (putnam-2004-a1-binary-prefix-p (cdr attempts)))
    (equal attempts nil)))

(defun putnam-2004-a1-success-count (attempts terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (if (equal (nth (- (nfix terms) 1) attempts) 1)
           1
         0)
       (putnam-2004-a1-success-count
        attempts (- (nfix terms) 1)))))

(defun putnam-2004-a1-rate-below-four-fifths-p
    (attempts terms)
  (< (* 5 (putnam-2004-a1-success-count attempts terms))
     (* 4 terms)))

(defun putnam-2004-a1-rate-above-four-fifths-p
    (attempts terms)
  (< (* 4 terms)
     (* 5 (putnam-2004-a1-success-count attempts terms))))

(defun putnam-2004-a1-rate-equals-four-fifths-p
    (attempts terms)
  (equal
   (* 5 (putnam-2004-a1-success-count attempts terms))
   (* 4 terms)))

;; Search every c with a < c < b. The existential witness stays internal to
;; the statement predicate.
(defun putnam-2004-a1-intermediate-through-p
    (attempts a candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (and (natp a)
           (natp candidate)
           (< a candidate))
      (or
       (putnam-2004-a1-rate-equals-four-fifths-p
        attempts candidate)
       (putnam-2004-a1-intermediate-through-p
        attempts a (- candidate 1)))
    nil))

(defun putnam-2004-a1-intermediate-exists-p
    (attempts a b)
  (and (natp a)
       (natp b)
       (< a b)
       (putnam-2004-a1-intermediate-through-p
        attempts a (- b 1))))

;; The root predicate is universally closed over ATTEMPTS, A, and B by the
;; ACL2 statement-corpus convention. Since the annotated solution is True,
;; this implication is exactly the source's universally quantified
;; proposition iff its solution.
(defun putnambench-putnam-2004-a1-statement
    (attempts a b)
  (implies
   (and
    (natp a)
    (natp b)
    (<= 1 a)
    (< a b)
    (putnam-2004-a1-binary-prefix-p attempts)
    (equal (len attempts) b)
    (putnam-2004-a1-rate-below-four-fifths-p attempts a)
    (putnam-2004-a1-rate-above-four-fifths-p attempts b))
   (putnam-2004-a1-intermediate-exists-p attempts a b)))

(value-triple :itpeval-statement-checked)
:q
