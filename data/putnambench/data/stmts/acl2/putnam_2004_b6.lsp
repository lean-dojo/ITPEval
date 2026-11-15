;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_b6:
;; a positive-integer set whose increasing positive-difference enumeration has
;; unbounded successive gaps has counting-function density tending to zero.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative generic symbols represent the arbitrary characteristic
;; predicate of A and the arbitrary sequence b. DEFSTUB imposes no
;; executability or finiteness restriction. Every domain condition and every
;; source quantifier is stated explicitly below with DEFUN-SK.
(defstub putnam-2004-b6-a-member (n) t)
(defstub putnam-2004-b6-b (i) t)

(defun putnam-2004-b6-member-p (n)
  (if (putnam-2004-b6-a-member n) t nil))

(defun putnam-2004-b6-nat-subtract (left right)
  (if (< left right)
      0
    (- left right)))

(defun-sk putnam-2004-b6-set-nonempty-p ()
  (exists (a)
    (and
     (natp a)
     (putnam-2004-b6-member-p a))))

(defun-sk putnam-2004-b6-positive-set-p ()
  (forall (a)
    (implies
     (and
      (natp a)
      (putnam-2004-b6-member-p a))
     (< 0 a))))

(defun-sk putnam-2004-b6-increasing-natural-sequence-p ()
  (forall (i)
    (implies
     (natp i)
     (and
      (natp (putnam-2004-b6-b i))
      (natp (putnam-2004-b6-b (+ i 1)))
      (< (putnam-2004-b6-b i)
         (putnam-2004-b6-b (+ i 1)))))))

(defun-sk putnam-2004-b6-in-sequence-range-p (value)
  (exists (i)
    (and
     (natp i)
     (equal (putnam-2004-b6-b i) value))))

(defun-sk putnam-2004-b6-positive-difference-p (value)
  (exists (a a-prime)
    (and
     (natp value)
     (< 0 value)
     (natp a)
     (natp a-prime)
     (putnam-2004-b6-member-p a)
     (putnam-2004-b6-member-p a-prime)
     (equal
      value
      (putnam-2004-b6-nat-subtract a a-prime)))))

(defun-sk putnam-2004-b6-exact-difference-range-p ()
  (forall (value)
    (implies
     (natp value)
     (iff
      (putnam-2004-b6-in-sequence-range-p value)
      (putnam-2004-b6-positive-difference-p value)))))

(defun-sk putnam-2004-b6-gap-at-least-exists-p (bound)
  (exists (i)
    (and
     (natp i)
     (<=
      bound
      (putnam-2004-b6-nat-subtract
       (putnam-2004-b6-b (+ i 1))
       (putnam-2004-b6-b i))))))

(defun-sk putnam-2004-b6-unbounded-gaps-p ()
  (forall (bound)
    (implies
     (natp bound)
     (putnam-2004-b6-gap-at-least-exists-p bound))))

;; This is exactly the cardinality of {a in A | a <= n}.
(defun putnam-2004-b6-count-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (if (putnam-2004-b6-member-p 0)
          1
        0)
    (+ (if (putnam-2004-b6-member-p n)
           1
         0)
       (putnam-2004-b6-count-through (- n 1)))))

(defun-sk putnam-2004-b6-limit-from-cutoff-p
    (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (<
      (* (putnam-2004-b6-count-through n)
         (/ n))
      epsilon))))

(defun-sk putnam-2004-b6-limit-at-tolerance-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (putnam-2004-b6-limit-from-cutoff-p
      epsilon cutoff))))

(defun-sk putnam-2004-b6-density-tends-to-zero-p ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2004-b6-limit-at-tolerance-p epsilon))))

;; B and N are eliminated by their source definitions. For real x >= 1 and
;; n=floor(x), the count is constant on [n,n+1), and
;; count(n)/x <= count(n)/n; natural arguments are cofinal in the reals.
;; Thus the source real limit is equivalent to the natural-argument limit
;; above. Positive rational tolerances are cofinal among positive real ones.
(defun putnambench-putnam-2004-b6-statement ()
  (implies
   (and
    (putnam-2004-b6-set-nonempty-p)
    (putnam-2004-b6-positive-set-p)
    (putnam-2004-b6-increasing-natural-sequence-p)
    (putnam-2004-b6-exact-difference-range-p))
   (implies
    (putnam-2004-b6-unbounded-gaps-p)
    (putnam-2004-b6-density-tends-to-zero-p))))

(value-triple :itpeval-statement-checked)
:q
