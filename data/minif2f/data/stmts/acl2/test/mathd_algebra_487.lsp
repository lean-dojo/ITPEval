;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_487:
;; two distinct real solutions a and c of x + x^2 = 1, with b = a^2 and
;; d = c^2, determine points whose Euclidean distance is sqrt(10). This file
;; contains no proof.
;;
;; The quadratic hypotheses force every satisfying real tuple into Q(sqrt(5)),
;; represented exactly below by rational pairs. The squared-distance conclusion
;; is equivalent in both directions to the source equality of principal square
;; roots because its radicand and 10 are nonnegative.

(in-package "ACL2")

;; A dotted pair (r . s) represents the real number r + s*sqrt(5).
(defun mathd-algebra-487-q5p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun mathd-algebra-487-q5 (r s)
  (cons r s))

(defun mathd-algebra-487-rational (q)
  (mathd-algebra-487-q5 q 0))

(defun mathd-algebra-487-add (x y)
  (mathd-algebra-487-q5
   (+ (car x) (car y))
   (+ (cdr x) (cdr y))))

(defun mathd-algebra-487-neg (x)
  (mathd-algebra-487-q5
   (- (car x))
   (- (cdr x))))

(defun mathd-algebra-487-sub (x y)
  (mathd-algebra-487-add
   x
   (mathd-algebra-487-neg y)))

(defun mathd-algebra-487-mul (x y)
  (mathd-algebra-487-q5
   (+ (* (car x) (car y))
      (* 5 (* (cdr x) (cdr y))))
   (+ (* (car x) (cdr y))
      (* (cdr x) (car y)))))

(defun mathd-algebra-487-statement (a b c d)
  (implies
   (and
    (mathd-algebra-487-q5p a)
    (mathd-algebra-487-q5p b)
    (mathd-algebra-487-q5p c)
    (mathd-algebra-487-q5p d)
    (equal b
           (mathd-algebra-487-mul a a))
    (equal
     (mathd-algebra-487-add a b)
     (mathd-algebra-487-rational 1))
    (equal d
           (mathd-algebra-487-mul c c))
    (equal
     (mathd-algebra-487-add c d)
     (mathd-algebra-487-rational 1))
    (not (equal a c)))
   (equal
    (mathd-algebra-487-add
     (mathd-algebra-487-mul
      (mathd-algebra-487-sub a c)
      (mathd-algebra-487-sub a c))
     (mathd-algebra-487-mul
      (mathd-algebra-487-sub b d)
      (mathd-algebra-487-sub b d)))
    (mathd-algebra-487-rational 10))))

(value-triple :itpeval-statement-checked)
:q
