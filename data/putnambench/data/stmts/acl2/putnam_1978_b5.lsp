;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_b5:
;; the quartic 4*x^4 - 4*x^2 + 1 maps [-1,1] into [0,1] and has the largest
;; possible leading coefficient among real quartics with that property. This
;; file contains no proof.

(in-package "ACL2")

;; Standard ACL2 has exact rational arithmetic but no primitive real sort.
;; For a rational-coefficient polynomial, requiring the interval inequalities
;; at every rational x in [-1,1] is equivalent, by continuity and density, to
;; requiring them at every real x in that interval.
;;
;; Restricting the universally quantified coefficient tuple to rationals is
;; also bidirectionally equivalent here. A rational counterexample is a real
;; counterexample. Conversely, from a real counterexample with leading
;; coefficient greater than 4, first replace p by
;;
;;   delta + (1 - 2*delta)*p
;;
;; for sufficiently small positive delta. This retains a leading coefficient
;; greater than 4 and gives a strict margin inside [0,1]. A sufficiently close
;; rational approximation to all five coefficients then preserves the margin,
;; the degree, and the strict leading-coefficient violation uniformly on
;; [-1,1]. Thus a real counterexample exists exactly when a rational one does.
;;
;; FN-EQUAL against the constant-true lambda retains the internal universal
;; quantifier over interval points; no finite sampling is used.

(defun putnam-1978-b5-quoted (object)
  (list 'quote object))

(defun putnam-1978-b5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1978-b5-and-terms (cdr terms))
            (putnam-1978-b5-quoted nil))
    (putnam-1978-b5-quoted t)))

(defun putnam-1978-b5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-1978-b5-quoted t)))

(defun putnam-1978-b5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1978-b5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1978-b5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-1978-b5-quoted nil)
        (putnam-1978-b5-quoted t)))

(defun putnam-1978-b5-polynomial-value-term
    (a0 a1 a2 a3 a4 x)
  (putnam-1978-b5-add-term
   (putnam-1978-b5-quoted a0)
   (putnam-1978-b5-multiply-term
    x
    (putnam-1978-b5-add-term
     (putnam-1978-b5-quoted a1)
     (putnam-1978-b5-multiply-term
      x
      (putnam-1978-b5-add-term
       (putnam-1978-b5-quoted a2)
       (putnam-1978-b5-multiply-term
        x
        (putnam-1978-b5-add-term
         (putnam-1978-b5-quoted a3)
         (putnam-1978-b5-multiply-term
          x
          (putnam-1978-b5-quoted a4))))))))))

(defun putnam-1978-b5-interval-function
    (a0 a1 a2 a3 a4)
  (let ((value
         (putnam-1978-b5-polynomial-value-term
          a0 a1 a2 a3 a4 'x)))
    (list
     'lambda
     '(x)
     (putnam-1978-b5-implies-term
      (putnam-1978-b5-and-terms
       (list
        (list 'rationalp 'x)
        (putnam-1978-b5-less-equal-term
         (putnam-1978-b5-quoted -1) 'x)
        (putnam-1978-b5-less-equal-term
         'x (putnam-1978-b5-quoted 1))))
      (putnam-1978-b5-and-terms
       (list
        (putnam-1978-b5-less-equal-term
         (putnam-1978-b5-quoted 0) value)
        (putnam-1978-b5-less-equal-term
         value (putnam-1978-b5-quoted 1))))))))

(defun putnam-1978-b5-true-function ()
  (list 'lambda '(x) (putnam-1978-b5-quoted t)))

(defun putnam-1978-b5-admissible-p
    (a0 a1 a2 a3 a4)
  (let ((interval-function
         (putnam-1978-b5-interval-function
          a0 a1 a2 a3 a4)))
    (and
     (tamep-functionp interval-function)
     (fn-equal
      interval-function
      (putnam-1978-b5-true-function)))))

(defun putnambench-putnam-1978-b5-statement
    (a0 a1 a2 a3 a4)
  (and
   (not (equal 4 0))
   (putnam-1978-b5-admissible-p 1 0 -4 0 4)
   (implies
    (and
     (rationalp a0)
     (rationalp a1)
     (rationalp a2)
     (rationalp a3)
     (rationalp a4)
     (not (equal a4 0))
     (putnam-1978-b5-admissible-p a0 a1 a2 a3 a4))
    (<= a4 4))))

(value-triple :itpeval-statement-checked)
:q
