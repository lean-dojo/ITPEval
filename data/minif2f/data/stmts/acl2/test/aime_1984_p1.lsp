;; Statement-only formalization of miniF2F artifact aime_1984_p1: a rational
;; sequence satisfying u(n + 1) = u(n) + 1 whose terms u(1) through u(98)
;; sum to 137 has even-indexed sum u(2) + u(4) + ... + u(98) = 93. This file
;; contains no proof.

(in-package "ACL2")

(defun aime-1984-p1-rational-listp (xs)
  (if (consp xs)
      (and (rationalp (car xs))
           (aime-1984-p1-rational-listp (cdr xs)))
    (equal xs nil)))

(defun aime-1984-p1-recurrence-p (xs)
  (if (and (consp xs)
           (consp (cdr xs)))
      (and (equal (car (cdr xs))
                  (+ (car xs) 1))
           (aime-1984-p1-recurrence-p (cdr xs)))
    t))

(defun aime-1984-p1-sum (xs)
  (if (consp xs)
      (+ (car xs)
         (aime-1984-p1-sum (cdr xs)))
    0))

(defun aime-1984-p1-even-index-sum (tail)
  (if (and (consp tail)
           (consp (cdr tail)))
      (+ (car (cdr tail))
         (aime-1984-p1-even-index-sum
          (cdr (cdr tail))))
    0))

(defun aime-1984-p1-statement (u)
  (implies
   (and (aime-1984-p1-rational-listp u)
        (equal (len u) 99)
        (aime-1984-p1-recurrence-p u)
        (equal (aime-1984-p1-sum (cdr u)) 137))
   (equal (aime-1984-p1-even-index-sum (cdr u))
          93)))

(value-triple :itpeval-statement-checked)
:q
