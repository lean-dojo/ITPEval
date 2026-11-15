;; Statement-only formalization of miniF2F corpus artifact amc12a_2021_p19:
;; the real solution set in [0, pi] of
;; sin((pi/2) cos(x)) = cos((pi/2) sin(x)) has cardinality two, encoded by
;; an exact bijective reduction to a Sturm root count. This file contains no
;; proof.

(in-package "ACL2")

;; On [0,pi], both (pi/2)*cos(x) and (pi/2)*(1-sin(x)) lie in the interval
;; where sine is injective. Thus the source equation is equivalent to
;; sin(x)+cos(x)=1. The map c=cos(x) is a bijection from [0,pi] to [-1,1],
;; with sin(x)=sqrt(1-c^2). Since 1-c is nonnegative there, squaring
;; sqrt(1-c^2)=1-c is reversible and gives c*(c-1)=0.

(defun amc12a-2021-p19-polynomial-value (c)
  (- (* c c) c))

(defun amc12a-2021-p19-polynomial-derivative-value (c)
  (- (* 2 c) 1))

;; For P(c)=c^2-c, the exact Sturm chain is P, P', 1/4.
(defun amc12a-2021-p19-sturm-values-at (c)
  (list
   (amc12a-2021-p19-polynomial-value c)
   (amc12a-2021-p19-polynomial-derivative-value c)
   (/ 1 4)))

(defun amc12a-2021-p19-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun amc12a-2021-p19-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (amc12a-2021-p19-sign (car values))))
        (cond
         ((equal current-sign 0)
          (amc12a-2021-p19-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (amc12a-2021-p19-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (amc12a-2021-p19-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun amc12a-2021-p19-sign-variations (values)
  (amc12a-2021-p19-sign-variations-aux values 0))

;; Omitting zero entries gives the Sturm endpoint convention that counts
;; roots in (-1,1]. Since P(-1) is nonzero, this is exactly the number of
;; roots in the source interval [-1,1].
(defun amc12a-2021-p19-solution-count ()
  (-
   (amc12a-2021-p19-sign-variations
    (amc12a-2021-p19-sturm-values-at -1))
   (amc12a-2021-p19-sign-variations
    (amc12a-2021-p19-sturm-values-at 1))))

(defun amc12a-2021-p19-statement ()
  (equal (amc12a-2021-p19-solution-count) 2))

(value-triple :itpeval-statement-checked)
:q
