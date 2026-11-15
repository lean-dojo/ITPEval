;; Statement-only formalization of miniF2F artifact mathd_algebra_400: a
;; rational-linear equation in one real variable implies x = 50. The source
;; real is encoded exactly for this formula by a two-dimensional rational
;; coordinate vector with 1 as the first basis vector: 1 and x span a
;; Q-vector space of dimension at most two, while Q^2 embeds Q-linearly into
;; R with the same distinguished unit. Thus the hypothesis and conclusion are
;; preserved and reflected. This file contains no proof.

(in-package "ACL2")

;; A dotted pair (r . s) is a two-dimensional rational coordinate vector.
(defun mathd-algebra-400-realp (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun mathd-algebra-400-real-constant (q)
  (cons q 0))

(defun mathd-algebra-400-real-add (x y)
  (cons (+ (car x) (car y))
        (+ (cdr x) (cdr y))))

(defun mathd-algebra-400-real-scale (q x)
  (cons (* q (car x))
        (* q (cdr x))))

(defun mathd-algebra-400-statement (x)
  (implies
   (and
    (mathd-algebra-400-realp x)
    (equal
     (mathd-algebra-400-real-add
      (mathd-algebra-400-real-constant 5)
      (mathd-algebra-400-real-constant
       (* (/ 500 100) 10)))
     (mathd-algebra-400-real-scale
      (/ 110 100)
      x)))
   (equal x
          (mathd-algebra-400-real-constant 50))))

(value-triple :itpeval-statement-checked)
:q
