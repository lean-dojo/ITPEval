;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binomial_Top_computeqtvc: the binomial-coefficient computation
;; verification condition for its iterative recurrence. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary
;; integer-valued division and binomial-coefficient functions. Their complete
;; typing and assumed laws are explicit in the statement predicate below.

(defstub ntp4vc-binomial-infix-sl (x y) t)
(defstub ntp4vc-binomial-comb (n k) t)

;; Euclidean integer division: the remainder is nonnegative and smaller than
;; the absolute value of the nonzero divisor.

(defun ntp4vc-binomial-ediv (x y)
  (if (and
       (integerp x)
       (integerp y)
       (not (equal y 0)))
      (if (< y 0)
          (- (floor x (- y)))
        (floor x y))
    0))

(defun-sk ntp4vc-binomial-infix-sl-type-p ()
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y))
     (integerp
      (ntp4vc-binomial-infix-sl x y)))))

(defun-sk ntp4vc-binomial-infix-sl-def-p ()
  (forall (y x)
    (implies
     (and
      (integerp y)
      (integerp x)
      (not (equal y 0)))
     (equal
      (ntp4vc-binomial-infix-sl x y)
      (ntp4vc-binomial-ediv x y)))))

(defun-sk ntp4vc-binomial-comb-type-p ()
  (forall (n k)
    (implies
     (and
      (integerp n)
      (integerp k))
     (integerp
      (ntp4vc-binomial-comb n k)))))

(defun-sk ntp4vc-binomial-comb-def-p ()
  (forall (k n)
    (implies
     (and
      (integerp k)
      (integerp n)
      (<= 0 k)
      (<= k n))
     (equal
      (ntp4vc-binomial-comb n k)
      (if (or
           (equal k 0)
           (equal k n))
          1
        (+
         (ntp4vc-binomial-comb (- n 1) k)
         (ntp4vc-binomial-comb
          (- n 1)
          (- k 1))))))))

(defun-sk ntp4vc-binomial-comb-spec-p ()
  (forall (k n)
    (implies
     (and
      (integerp k)
      (integerp n)
      (<= 0 k)
      (<= k n))
     (<= 1
         (ntp4vc-binomial-comb n k)))))

(defun ntp4vc-binomial-background-p ()
  (and
   (ntp4vc-binomial-infix-sl-type-p)
   (ntp4vc-binomial-infix-sl-def-p)
   (ntp4vc-binomial-comb-type-p)
   (ntp4vc-binomial-comb-def-p)
   (ntp4vc-binomial-comb-spec-p)))

(defun ntp4vc-binomial-int-min (x y)
  (if (<= x y) x y))

;; Preserve the source loop-preservation condition as a universal statement
;; over every mathematical integer i.

(defun-sk ntp4vc-binomial-loop-preservation-p
    (n k1 r)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (and
        (<= 1 i)
        (<= i k1))
       (and
        (<= 1 i)
        (<= i (+ k1 1)))
       (equal
        r
        (ntp4vc-binomial-comb
         n
         (- i 1))))
      (and
       (not (equal i 0))
       (and
        (<= 1 (+ i 1))
        (<= (+ i 1) (+ k1 1)))
       (equal
        (ntp4vc-binomial-infix-sl
         (* r (+ (- n i) 1))
         i)
        (ntp4vc-binomial-comb
         n
         (- (+ i 1) 1))))))))

;; Preserve the source universal quantifier over r, including the loop exit
;; implication attached to each such integer.

(defun-sk ntp4vc-binomial-all-r-p
    (k n k1)
  (forall (r)
    (implies
     (integerp r)
     (and
      (ntp4vc-binomial-loop-preservation-p
       n k1 r)
      (implies
       (and
        (and
         (<= 1 (+ k1 1))
         (<= (+ k1 1) (+ k1 1)))
        (equal
         r
         (ntp4vc-binomial-comb
          n
          (- (+ k1 1) 1))))
       (equal
        r
        (ntp4vc-binomial-comb n k)))))))

(defun ntp4vc-pearl-binomial-top-computeqtvc-statement
    (k n)
  (implies
   (ntp4vc-binomial-background-p)
   (implies
    (and
     (integerp k)
     (integerp n)
     (<= 0 k)
     (<= k n))
    (let ((k1
           (ntp4vc-binomial-int-min
            k
            (- n k))))
      (and
       (implies
        (<= 1 (+ k1 1))
        (and
         (and
          (and
           (<= 1 1)
           (<= 1 (+ k1 1)))
          (equal
           1
           (ntp4vc-binomial-comb
            n
            (- 1 1))))
         (ntp4vc-binomial-all-r-p
          k n k1)))
       (implies
        (< (+ k1 1) 1)
        (equal
         1
         (ntp4vc-binomial-comb n k))))))))

(value-triple :itpeval-statement-checked)
:q
