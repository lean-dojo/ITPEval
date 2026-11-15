;; Statement-only formalization of miniF2F corpus artifact amc12a_2019_p21:
;; for z = (1+i)/sqrt(2), the product of the sums from k=1 through 12 of
;; z^(k^2) and 1/z^(k^2) equals 36. This file contains no proof.
;;
;; A rational pair represents an element of Q(sqrt(2)), and a pair of those
;; elements represents a complex number in Q(sqrt(2),i). The hypothesis fixes
;; z to (sqrt(2)/2)(1+i), so every satisfying source instance is represented
;; exactly, and conversely the displayed encoding is that source complex
;; value. The recursive sums preserve the complete source index range.

(in-package "ACL2")

;; The dotted pair (r . s) represents r + s*sqrt(2).
(defun amc12a-2019-p21-q2p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun amc12a-2019-p21-q2 (r s)
  (cons r s))

(defun amc12a-2019-p21-q2-rational (q)
  (amc12a-2019-p21-q2 q 0))

(defun amc12a-2019-p21-q2-add (x y)
  (amc12a-2019-p21-q2
   (+ (car x) (car y))
   (+ (cdr x) (cdr y))))

(defun amc12a-2019-p21-q2-neg (x)
  (amc12a-2019-p21-q2
   (- (car x))
   (- (cdr x))))

(defun amc12a-2019-p21-q2-sub (x y)
  (amc12a-2019-p21-q2-add
   x
   (amc12a-2019-p21-q2-neg y)))

(defun amc12a-2019-p21-q2-mul (x y)
  (amc12a-2019-p21-q2
   (+ (* (car x) (car y))
      (* 2 (cdr x) (cdr y)))
   (+ (* (car x) (cdr y))
      (* (cdr x) (car y)))))

(defun amc12a-2019-p21-q2-inverse (x)
  (let ((norm (- (* (car x) (car x))
                 (* 2 (cdr x) (cdr x)))))
    (if (equal norm 0)
        (amc12a-2019-p21-q2-rational 0)
      (amc12a-2019-p21-q2
       (/ (car x) norm)
       (/ (- (cdr x)) norm)))))

;; The pair (real-part . imaginary-part) represents a complex value over
;; Q(sqrt(2)).
(defun amc12a-2019-p21-complexp (z)
  (and (consp z)
       (amc12a-2019-p21-q2p (car z))
       (amc12a-2019-p21-q2p (cdr z))))

(defun amc12a-2019-p21-complex (real-part imaginary-part)
  (cons real-part imaginary-part))

(defun amc12a-2019-p21-complex-rational (q)
  (amc12a-2019-p21-complex
   (amc12a-2019-p21-q2-rational q)
   (amc12a-2019-p21-q2-rational 0)))

(defun amc12a-2019-p21-complex-add (x y)
  (amc12a-2019-p21-complex
   (amc12a-2019-p21-q2-add (car x) (car y))
   (amc12a-2019-p21-q2-add (cdr x) (cdr y))))

(defun amc12a-2019-p21-complex-mul (x y)
  (amc12a-2019-p21-complex
   (amc12a-2019-p21-q2-sub
    (amc12a-2019-p21-q2-mul (car x) (car y))
    (amc12a-2019-p21-q2-mul (cdr x) (cdr y)))
   (amc12a-2019-p21-q2-add
    (amc12a-2019-p21-q2-mul (car x) (cdr y))
    (amc12a-2019-p21-q2-mul (cdr x) (car y)))))

(defun amc12a-2019-p21-complex-norm-squared (x)
  (amc12a-2019-p21-q2-add
   (amc12a-2019-p21-q2-mul (car x) (car x))
   (amc12a-2019-p21-q2-mul (cdr x) (cdr x))))

(defun amc12a-2019-p21-complex-inverse (x)
  (let ((inverse-norm
         (amc12a-2019-p21-q2-inverse
          (amc12a-2019-p21-complex-norm-squared x))))
    (amc12a-2019-p21-complex
     (amc12a-2019-p21-q2-mul (car x) inverse-norm)
     (amc12a-2019-p21-q2-neg
      (amc12a-2019-p21-q2-mul (cdr x) inverse-norm)))))

(defun amc12a-2019-p21-complex-power (z n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (amc12a-2019-p21-complex-rational 1)
    (amc12a-2019-p21-complex-mul
     z
     (amc12a-2019-p21-complex-power z (- n 1)))))

(defun amc12a-2019-p21-power-sum (z k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (amc12a-2019-p21-complex-rational 0)
    (amc12a-2019-p21-complex-add
     (amc12a-2019-p21-power-sum z (- k 1))
     (amc12a-2019-p21-complex-power z (* k k)))))

(defun amc12a-2019-p21-inverse-power-sum (z k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (amc12a-2019-p21-complex-rational 0)
    (amc12a-2019-p21-complex-add
     (amc12a-2019-p21-inverse-power-sum z (- k 1))
     (amc12a-2019-p21-complex-inverse
      (amc12a-2019-p21-complex-power z (* k k))))))

(defun amc12a-2019-p21-target-z ()
  (let ((inverse-sqrt-two
         (amc12a-2019-p21-q2 0 1/2)))
    (amc12a-2019-p21-complex
     inverse-sqrt-two
     inverse-sqrt-two)))

(defun amc12a-2019-p21-statement (z)
  (implies
   (and (amc12a-2019-p21-complexp z)
        (equal z (amc12a-2019-p21-target-z)))
   (equal
    (amc12a-2019-p21-complex-mul
     (amc12a-2019-p21-power-sum z 12)
     (amc12a-2019-p21-inverse-power-sum z 12))
    (amc12a-2019-p21-complex-rational 36))))

(value-triple :itpeval-statement-checked)
:q
