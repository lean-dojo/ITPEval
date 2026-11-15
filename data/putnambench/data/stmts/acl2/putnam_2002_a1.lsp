;; Statement-only formalization of PutnamBench corpus artifact putnam_2002_a1:
;; the numerator polynomial in the nth derivative of 1/(x^k-1), evaluated at
;; x=1, is (-k)^n*n! for every positive integer k. This file contains no proof.

(in-package "ACL2")

;; ACL2 has no first-class function quantifiers. This unconstrained function
;; symbol is the standard ACL2 representation of the source's arbitrary
;; polynomial family P.

(defstub putnam-2002-a1-p (n) t)

;; Polynomials use canonical nonempty integer coefficient lists in ascending
;; degree order. Writing D=X^k-1, the source derivative identity is equivalent
;; to the explicit hypotheses
;;
;;   P_0 = 1,
;;   P_(n+1) = P_n' D - (n+1) P_n D'.
;;
;; Differentiating P_n/D^(n+1) gives the forward implication. Conversely, the
;; recurrence reconstructs every iterated derivative identity. Equality away
;; from the finitely many roots of D is polynomial equality, so every source
;; real-polynomial family is uniquely this integer-coefficient family. Using
;; integer coefficient lists therefore does not narrow the admissible P.

(defun putnam-2002-a1-integer-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (integerp (car values))
     (putnam-2002-a1-integer-list-p (cdr values)))))

(defun putnam-2002-a1-polynomial-p (polynomial)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-2002-a1-integer-list-p polynomial)
   (or
    (equal (len polynomial) 1)
    (not (equal (car (last polynomial)) 0)))))

(defun putnam-2002-a1-trim-zero-tail (polynomial)
  (if (endp polynomial)
      nil
    (let ((rest
           (putnam-2002-a1-trim-zero-tail
            (cdr polynomial))))
      (if (and (endp rest)
               (equal (car polynomial) 0))
          nil
        (cons (car polynomial) rest)))))

(defun putnam-2002-a1-canonicalize (polynomial)
  (let ((trimmed
         (putnam-2002-a1-trim-zero-tail polynomial)))
    (if (endp trimmed)
        (list 0)
      trimmed)))

(defun putnam-2002-a1-poly-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons
     (+ (car left) (car right))
     (putnam-2002-a1-poly-add
      (cdr left) (cdr right))))))

(defun putnam-2002-a1-poly-negate (polynomial)
  (if (endp polynomial)
      nil
    (cons
     (- (car polynomial))
     (putnam-2002-a1-poly-negate
      (cdr polynomial)))))

(defun putnam-2002-a1-poly-subtract (left right)
  (putnam-2002-a1-poly-add
   left
   (putnam-2002-a1-poly-negate right)))

(defun putnam-2002-a1-poly-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons
     (* scalar (car polynomial))
     (putnam-2002-a1-poly-scale
      scalar (cdr polynomial)))))

(defun putnam-2002-a1-poly-multiply (left right)
  (if (endp left)
      nil
    (putnam-2002-a1-poly-add
     (putnam-2002-a1-poly-scale (car left) right)
     (cons
      0
      (putnam-2002-a1-poly-multiply
       (cdr left) right)))))

(defun putnam-2002-a1-poly-derivative-aux
    (polynomial degree)
  (if (endp polynomial)
      nil
    (cons
     (* degree (car polynomial))
     (putnam-2002-a1-poly-derivative-aux
      (cdr polynomial) (+ degree 1)))))

(defun putnam-2002-a1-poly-derivative (polynomial)
  (if (endp polynomial)
      (list 0)
    (putnam-2002-a1-canonicalize
     (putnam-2002-a1-poly-derivative-aux
      (cdr polynomial) 1))))

(defun putnam-2002-a1-poly-eval (polynomial x)
  (if (endp polynomial)
      0
    (+ (car polynomial)
       (* x
          (putnam-2002-a1-poly-eval
           (cdr polynomial) x)))))

(defun putnam-2002-a1-monomial (degree coefficient)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (list coefficient)
    (cons
     0
     (putnam-2002-a1-monomial
      (- degree 1) coefficient))))

(defun putnam-2002-a1-x-power-minus-one (k)
  (putnam-2002-a1-canonicalize
   (putnam-2002-a1-poly-add
    (putnam-2002-a1-monomial k 1)
    (list -1))))

(defun putnam-2002-a1-next-numerator
    (k n polynomial)
  (let* ((denominator
          (putnam-2002-a1-x-power-minus-one k))
         (denominator-derivative
          (putnam-2002-a1-poly-derivative denominator))
         (left
          (putnam-2002-a1-poly-multiply
           (putnam-2002-a1-poly-derivative polynomial)
           denominator))
         (right
          (putnam-2002-a1-poly-scale
           (+ n 1)
           (putnam-2002-a1-poly-multiply
            polynomial denominator-derivative))))
    (putnam-2002-a1-canonicalize
     (putnam-2002-a1-poly-subtract left right))))

(defun putnam-2002-a1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2002-a1-factorial (- n 1)))))

(defun putnam-2002-a1-solution (k n)
  (* (expt (- k) n)
     (putnam-2002-a1-factorial n)))

(defun-sk putnam-2002-a1-recurrence-p (k)
  (forall
   (index)
   (implies
    (natp index)
    (and
     (putnam-2002-a1-polynomial-p
      (putnam-2002-a1-p index))
     (equal
      (putnam-2002-a1-p (+ index 1))
      (putnam-2002-a1-next-numerator
       k index (putnam-2002-a1-p index)))))))

(defun putnam-2002-a1-valid-family-p (k)
  (and
   (equal (putnam-2002-a1-p 0) (list 1))
   (putnam-2002-a1-recurrence-p k)))

(defun putnambench-putnam-2002-a1-statement (k n)
  (implies
   (and
    (natp k)
    (< 0 k)
    (natp n)
    (putnam-2002-a1-valid-family-p k))
   (equal
    (putnam-2002-a1-poly-eval
     (putnam-2002-a1-p n)
     1)
    (putnam-2002-a1-solution k n))))

(value-triple :itpeval-statement-checked)
:q
