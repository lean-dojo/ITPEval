;; Statement-only formalization of miniF2F artifact aime_1994_p3: an
;; integer-valued function satisfying f(x) + f(x - 1) = x^2 for every
;; integer x and f(19) = 94 has f(94) congruent to 561 modulo 1000. ACL2
;; represents the needed finite restriction f(19), ..., f(94) as an integer
;; list. This file contains no proof.

(in-package "ACL2")

(defun aime-1994-p3-integer-listp (values)
  (if (consp values)
      (and (integerp (car values))
           (aime-1994-p3-integer-listp (cdr values)))
    (equal values nil)))

(defun aime-1994-p3-recurrence-p (values x)
  (if (and (consp values)
           (consp (cdr values)))
      (and (equal (+ (car (cdr values))
                     (car values))
                  (* x x))
           (aime-1994-p3-recurrence-p (cdr values) (+ x 1)))
    t))

(defun aime-1994-p3-last-value (values)
  (if (and (consp values)
           (consp (cdr values)))
      (aime-1994-p3-last-value (cdr values))
    (if (consp values)
        (car values)
      0)))

(defun aime-1994-p3-statement (f-values)
  (implies
   (and (aime-1994-p3-integer-listp f-values)
        (equal (len f-values) 76)
        (equal (car f-values) 94)
        (aime-1994-p3-recurrence-p f-values 20))
   (equal (mod (aime-1994-p3-last-value f-values) 1000)
          561)))

(value-triple :itpeval-statement-checked)
:q
