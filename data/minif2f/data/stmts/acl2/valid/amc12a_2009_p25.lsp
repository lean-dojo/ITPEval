;; Statement-only formalization of miniF2F corpus artifact amc12a_2009_p25:
;; a real sequence beginning with 1 and 1/sqrt(3), and satisfying
;; a(n+2) = (a(n)+a(n+1))/(1-a(n)*a(n+1)) for every n >= 1, has
;; |a(2009)| = 0. This file contains no proof.
;;
;; The initial values and recurrence uniquely determine every positive-index
;; term and force it to lie in Q(sqrt(3)). A pair (r . s) represents the real
;; number r+s*sqrt(3), so the recursive sequence below is bidirectionally
;; equivalent to every source sequence on all relevant indices and is not a
;; finite-table restriction. Division is totalized at zero as in the source
;; real fields. Finally, |x|=0 is equivalent to x=0.

(in-package "ACL2")

(defun amc12a-2009-p25-q3p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun amc12a-2009-p25-q3 (r s)
  (cons r s))

(defun amc12a-2009-p25-zero ()
  (amc12a-2009-p25-q3 0 0))

(defun amc12a-2009-p25-one ()
  (amc12a-2009-p25-q3 1 0))

(defun amc12a-2009-p25-inverse-sqrt3 ()
  (amc12a-2009-p25-q3 0 1/3))

(defun amc12a-2009-p25-add (x y)
  (amc12a-2009-p25-q3
   (+ (car x) (car y))
   (+ (cdr x) (cdr y))))

(defun amc12a-2009-p25-negate (x)
  (amc12a-2009-p25-q3
   (- (car x))
   (- (cdr x))))

(defun amc12a-2009-p25-subtract (x y)
  (amc12a-2009-p25-add
   x
   (amc12a-2009-p25-negate y)))

(defun amc12a-2009-p25-multiply (x y)
  (amc12a-2009-p25-q3
   (+ (* (car x) (car y))
      (* 3 (cdr x) (cdr y)))
   (+ (* (car x) (cdr y))
      (* (cdr x) (car y)))))

(defun amc12a-2009-p25-inverse (x)
  (let ((norm (- (* (car x) (car x))
                 (* 3 (cdr x) (cdr x)))))
    (if (equal norm 0)
        (amc12a-2009-p25-zero)
      (amc12a-2009-p25-q3
       (/ (car x) norm)
       (/ (- (cdr x)) norm)))))

(defun amc12a-2009-p25-divide (x y)
  (amc12a-2009-p25-multiply
   x
   (amc12a-2009-p25-inverse y)))

(defun amc12a-2009-p25-next (earlier later)
  (amc12a-2009-p25-divide
   (amc12a-2009-p25-add earlier later)
   (amc12a-2009-p25-subtract
    (amc12a-2009-p25-one)
    (amc12a-2009-p25-multiply earlier later))))

(defun amc12a-2009-p25-sequence-aux (steps earlier later)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      later
    (amc12a-2009-p25-sequence-aux
     (- steps 1)
     later
     (amc12a-2009-p25-next earlier later))))

(defun amc12a-2009-p25-sequence (a1 a2 n)
  (cond ((not (natp n)) (amc12a-2009-p25-zero))
        ((equal n 0) (amc12a-2009-p25-zero))
        ((equal n 1) a1)
        (t (amc12a-2009-p25-sequence-aux
            (- n 2) a1 a2))))

(defun amc12a-2009-p25-statement (a1 a2)
  (implies
   (and (amc12a-2009-p25-q3p a1)
        (amc12a-2009-p25-q3p a2)
        (equal a1 (amc12a-2009-p25-one))
        (equal a2 (amc12a-2009-p25-inverse-sqrt3)))
   (equal (amc12a-2009-p25-sequence a1 a2 2009)
          (amc12a-2009-p25-zero))))

(value-triple :itpeval-statement-checked)
:q
