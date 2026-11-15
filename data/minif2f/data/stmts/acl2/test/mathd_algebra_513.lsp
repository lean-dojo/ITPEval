;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_513:
;; two linear equations in real variables a and b imply a = 1 and b = 1.
;; This file contains no proof.
;;
;; The source reals are encoded exactly for this rational-linear formula by
;; three-dimensional rational coordinate vectors with 1 as the first basis
;; vector. Any two reals together with 1 span a Q-vector space of dimension at
;; most three, while Q^3 embeds Q-linearly into R with the same distinguished
;; unit. Therefore the hypotheses and conclusion are preserved and reflected.

(in-package "ACL2")

(defun mathd-algebra-513-rational-listp (xs)
  (if (consp xs)
      (and (rationalp (car xs))
           (mathd-algebra-513-rational-listp (cdr xs)))
    (equal xs nil)))

(defun mathd-algebra-513-realp (x)
  (and (equal (len x) 3)
       (mathd-algebra-513-rational-listp x)))

(defun mathd-algebra-513-real-constant (q)
  (list q 0 0))

(defun mathd-algebra-513-real-add (x y)
  (if (consp x)
      (cons (+ (car x) (car y))
            (mathd-algebra-513-real-add (cdr x) (cdr y)))
    nil))

(defun mathd-algebra-513-real-scale (q x)
  (if (consp x)
      (cons (* q (car x))
            (mathd-algebra-513-real-scale q (cdr x)))
    nil))

(defun mathd-algebra-513-statement (a b)
  (implies
   (and
    (mathd-algebra-513-realp a)
    (mathd-algebra-513-realp b)
    (equal
     (mathd-algebra-513-real-add
      (mathd-algebra-513-real-scale 3 a)
      (mathd-algebra-513-real-scale 2 b))
     (mathd-algebra-513-real-constant 5))
    (equal
     (mathd-algebra-513-real-add a b)
     (mathd-algebra-513-real-constant 2)))
   (and
    (equal a (mathd-algebra-513-real-constant 1))
    (equal b (mathd-algebra-513-real-constant 1)))))

(value-triple :itpeval-statement-checked)
:q
