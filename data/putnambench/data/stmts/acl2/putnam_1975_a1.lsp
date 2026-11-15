;; Statement-only formalization of PutnamBench corpus artifact putnam_1975_a1:
;; the equivalence between representing an integer as a sum of two triangular
;; numbers and representing four times that integer plus one as two squares,
;; with the specified forward witnesses. This file contains no proof.

(in-package "ACL2")

(defun putnam-1975-a1-triangular (z)
  (/ (+ (* z z) z) 2))

(defun putnam-1975-a1-nab-p (n a b)
  (and (integerp n)
       (integerp a)
       (integerp b)
       (equal n
              (+ (putnam-1975-a1-triangular a)
                 (putnam-1975-a1-triangular b)))))

(defun putnam-1975-a1-nxy-p (n x y)
  (and (integerp n)
       (integerp x)
       (integerp y)
       (equal (+ (* 4 n) 1)
              (+ (* x x) (* y y)))))

(defun putnam-1975-a1-solution-x (a b)
  (+ a b 1))

(defun putnam-1975-a1-solution-y (a b)
  (- a b))

;; If x^2+y^2=4*n+1, then n is nonnegative and both absolute values are at
;; most 4*n+1. Thus this search is equivalent to the unbounded existential
;; quantifier over integer x and y.
(defun putnam-1975-a1-nxy-y-through-index-p
    (n x bound y-index)
  (declare (xargs :measure (nfix y-index)))
  (if (and (integerp n)
           (integerp x)
           (natp bound)
           (natp y-index))
      (or (putnam-1975-a1-nxy-p
           n x (- y-index bound))
          (and (not (zp y-index))
               (putnam-1975-a1-nxy-y-through-index-p
                n x bound (- y-index 1))))
    nil))

(defun putnam-1975-a1-nxy-x-through-index-p
    (n bound x-index)
  (declare (xargs :measure (nfix x-index)))
  (if (and (integerp n)
           (natp bound)
           (natp x-index))
      (or (putnam-1975-a1-nxy-y-through-index-p
           n (- x-index bound) bound (* 2 bound))
          (and (not (zp x-index))
               (putnam-1975-a1-nxy-x-through-index-p
                n bound (- x-index 1))))
    nil))

(defun putnam-1975-a1-nxy-exists-p (n)
  (if (and (integerp n)
           (<= 0 n))
      (let ((bound (+ (* 4 n) 1)))
        (putnam-1975-a1-nxy-x-through-index-p
         n bound (* 2 bound)))
    nil))

;; Every integer triangular number z*(z+1)/2 is nonnegative. If two such
;; numbers sum to n, then n is nonnegative; using T(z)=T(-z-1), each witness
;; has absolute value at most n+1. Hence this search is equivalent to the
;; unbounded existential quantifier over integer a and b.
(defun putnam-1975-a1-nab-b-through-index-p
    (n a bound b-index)
  (declare (xargs :measure (nfix b-index)))
  (if (and (integerp n)
           (integerp a)
           (natp bound)
           (natp b-index))
      (or (putnam-1975-a1-nab-p
           n a (- b-index bound))
          (and (not (zp b-index))
               (putnam-1975-a1-nab-b-through-index-p
                n a bound (- b-index 1))))
    nil))

(defun putnam-1975-a1-nab-a-through-index-p
    (n bound a-index)
  (declare (xargs :measure (nfix a-index)))
  (if (and (integerp n)
           (natp bound)
           (natp a-index))
      (or (putnam-1975-a1-nab-b-through-index-p
           n (- a-index bound) bound (* 2 bound))
          (and (not (zp a-index))
               (putnam-1975-a1-nab-a-through-index-p
                n bound (- a-index 1))))
    nil))

(defun putnam-1975-a1-nab-exists-p (n)
  (if (and (integerp n)
           (<= 0 n))
      (let ((bound (+ n 1)))
        (putnam-1975-a1-nab-a-through-index-p
         n bound (* 2 bound)))
    nil))

;; Rocq states the fixed-witness forward clause as an equivalence, whereas
;; Lean and Isabelle state its forward implication. Expanding x=a+b+1 and
;; y=a-b makes the reverse implication the same integer identity, so Boolean
;; equality below is equivalent to the implication under these definitions.
(defun putnambench-putnam-1975-a1-statement (n a b)
  (implies
   (and (integerp n)
        (integerp a)
        (integerp b))
   (and
    (equal
     (putnam-1975-a1-nab-p n a b)
     (putnam-1975-a1-nxy-p
      n
      (putnam-1975-a1-solution-x a b)
      (putnam-1975-a1-solution-y a b)))
    (implies
     (putnam-1975-a1-nxy-exists-p n)
     (putnam-1975-a1-nab-exists-p n)))))

(value-triple :itpeval-statement-checked)
:q
