;; Statement-only formalization of miniF2F corpus artifact amc12b_2021_p13:
;; the real solution set in (0, 2*pi] of
;; 1 - 3*sin(x) + 5*cos(3*x) = 0 has cardinality six, encoded by an exact
;; bijective reduction to a Sturm root count. This file contains no proof.

(in-package "ACL2")

;; The map x |-> (cos(x), sin(x)) is a bijection from (0,2*pi] to the unit
;; circle. Put c = cos(x) and s = sin(x). The triple-angle identity turns the
;; source equation into
;;
;;   3*s = 20*c^3 - 15*c + 1.
;;
;; Substitution in s^2+c^2=1 is reversible because this equation determines s
;; uniquely. After division by 2, the resulting polynomial is
;;
;;   P(c) = 200*c^6 - 300*c^4 + 20*c^3 + 117*c^2 - 15*c - 4.
;;
;; Conversely, every real root c of P gives s=(20*c^3-15*c+1)/3 on the unit
;; circle, hence exactly one source-interval solution x. The circle equation
;; also forces every root into [-1,1].

(defun amc12b-2021-p13-triple-angle-numerator (c)
  (+ (* 20 c c c)
     (* -15 c)
     1))

(defun amc12b-2021-p13-polynomial-value (c)
  (let ((a
         (amc12b-2021-p13-triple-angle-numerator c)))
    (/ (+ (* a a)
          (* 9 c c)
          -9)
       2)))

;; These polynomials form the exact Sturm chain of P up to positive constant
;; rescaling of individual entries, which does not change sign variations.
(defun amc12b-2021-p13-sturm-p1 (c)
  (+ (* 400 c c c c c)
     (* -400 c c c)
     (* 20 c c)
     (* 78 c)
     -5))

(defun amc12b-2021-p13-sturm-p2 (c)
  (+ (* 200 c c c c)
     (* -20 c c c)
     (* -156 c c)
     (* 25 c)
     8))

(defun amc12b-2021-p13-sturm-p3 (c)
  (+ (* 140 c c c)
     (* -2 c c)
     (* -95 c)
     11))

(defun amc12b-2021-p13-sturm-p4 (c)
  (+ (* 1006 c c)
     (* 115 c)
     -458))

(defun amc12b-2021-p13-sturm-p5 (c)
  (+ (* 10053 c)
     -965))

(defun amc12b-2021-p13-sturm-values-at (c)
  (list
   (amc12b-2021-p13-polynomial-value c)
   (amc12b-2021-p13-sturm-p1 c)
   (amc12b-2021-p13-sturm-p2 c)
   (amc12b-2021-p13-sturm-p3 c)
   (amc12b-2021-p13-sturm-p4 c)
   (amc12b-2021-p13-sturm-p5 c)
   1))

(defun amc12b-2021-p13-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun amc12b-2021-p13-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (amc12b-2021-p13-sign (car values))))
        (cond
         ((equal current-sign 0)
          (amc12b-2021-p13-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (amc12b-2021-p13-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (amc12b-2021-p13-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun amc12b-2021-p13-sign-variations (values)
  (amc12b-2021-p13-sign-variations-aux values 0))

;; P(-1)=8 and P(1)=18, so the endpoint variation difference counts all roots
;; in [-1,1] without replacing any real root by a rational approximation.
(defun amc12b-2021-p13-solution-count ()
  (-
   (amc12b-2021-p13-sign-variations
    (amc12b-2021-p13-sturm-values-at -1))
   (amc12b-2021-p13-sign-variations
    (amc12b-2021-p13-sturm-values-at 1))))

(defun amc12b-2021-p13-statement ()
  (equal (amc12b-2021-p13-solution-count) 6))

(value-triple :itpeval-statement-checked)
:q
