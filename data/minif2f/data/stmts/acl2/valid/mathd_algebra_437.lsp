;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_437:
;; real cube roots x and y of -45 and -101, with an integer n strictly
;; between x and y, force n = -4. This file contains no proof.

(in-package "ACL2")

;; Each cubic equation has a unique real solution. A rational triple
;; (a b c) represents a + b*alpha + c*alpha^2 in Q(alpha), where alpha^3 is
;; the indicated radicand. Thus the two representations contain the unique
;; source-real values forced by the hypotheses and embed exactly in the reals.
;; Under x^3 = -45 and y^3 = -101, strict monotonicity of the real cube map
;; makes x < n and n < y equivalent respectively to -45 < n^3 and
;; n^3 < -101.

(defun mathd-algebra-437-cubicp (x)
  (and (true-listp x)
       (equal (len x) 3)
       (rationalp (car x))
       (rationalp (cadr x))
       (rationalp (caddr x))))

(defun mathd-algebra-437-constant (q)
  (list q 0 0))

(defun mathd-algebra-437-multiply (x y radicand)
  (list
   (+ (* (car x) (car y))
      (* radicand
         (+ (* (cadr x) (caddr y))
            (* (caddr x) (cadr y)))))
   (+ (* (car x) (cadr y))
      (* (cadr x) (car y))
      (* radicand (caddr x) (caddr y)))
   (+ (* (car x) (caddr y))
      (* (cadr x) (cadr y))
      (* (caddr x) (car y)))))

(defun mathd-algebra-437-cube (x radicand)
  (mathd-algebra-437-multiply
   (mathd-algebra-437-multiply x x radicand)
   x
   radicand))

(defun mathd-algebra-437-statement (x y n)
  (implies
   (and
    (mathd-algebra-437-cubicp x)
    (mathd-algebra-437-cubicp y)
    (integerp n)
    (equal
     (mathd-algebra-437-cube x -45)
     (mathd-algebra-437-constant -45))
    (equal
     (mathd-algebra-437-cube y -101)
     (mathd-algebra-437-constant -101))
    (< -45 (expt n 3))
    (< (expt n 3) -101))
   (equal n -4)))

(value-triple :itpeval-statement-checked)
:q
