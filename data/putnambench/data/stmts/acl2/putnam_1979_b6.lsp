;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_b6:
;; the real part of the principal square root of a finite sum of complex
;; squares is bounded by the sum of the absolute real parts. This file
;; contains no proof.

(in-package "ACL2")

;; A length-n list is definitionally equivalent to a function on Fin n, with
;; each complex number represented by its real and imaginary coordinates.
;; Standard ACL2 evaluates these coordinates as exact rationals. This
;; presentation is bidirectionally equivalent to validity over arbitrary
;; complex numbers: rational families are complex families, while failure of
;; either non-strict inequality in the square-root-free conclusion below is a
;; strict, continuously varying condition, so every real-coordinate
;; counterexample has a nearby rational-coordinate counterexample.
;;
;; Write the sum of the squares as A+iB and put
;;
;;   X = sum_i |Re(z_i)|,       D = 2*X^2-A.
;;
;; For the principal complex square root,
;;
;;   |Re(sqrt(A+iB))|^2 = (sqrt(A^2+B^2)+A)/2.
;;
;; Since X is nonnegative, the source inequality is therefore equivalent in
;; both directions to D >= 0 and A^2+B^2 <= D^2. The predicate below uses
;; exactly these radical-free conditions.

(defun putnam-1979-b6-complex-rational-p (z)
  (and (true-listp z)
       (equal (len z) 2)
       (rationalp (nth 0 z))
       (rationalp (nth 1 z))))

(defun putnam-1979-b6-complex-rational-list-p (values)
  (if (consp values)
      (and (putnam-1979-b6-complex-rational-p (car values))
           (putnam-1979-b6-complex-rational-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1979-b6-sum-square-real-parts (values)
  (if (consp values)
      (let ((x (nth 0 (car values)))
            (y (nth 1 (car values))))
        (+ (- (* x x) (* y y))
           (putnam-1979-b6-sum-square-real-parts (cdr values))))
    0))

(defun putnam-1979-b6-sum-square-imaginary-parts (values)
  (if (consp values)
      (let ((x (nth 0 (car values)))
            (y (nth 1 (car values))))
        (+ (* 2 x y)
           (putnam-1979-b6-sum-square-imaginary-parts (cdr values))))
    0))

(defun putnam-1979-b6-sum-absolute-real-parts (values)
  (if (consp values)
      (+ (abs (nth 0 (car values)))
         (putnam-1979-b6-sum-absolute-real-parts (cdr values)))
    0))

(defun putnambench-putnam-1979-b6-statement (n values)
  (implies
   (and (natp n)
        (true-listp values)
        (equal (len values) n)
        (putnam-1979-b6-complex-rational-list-p values))
   (let* ((a (putnam-1979-b6-sum-square-real-parts values))
          (b (putnam-1979-b6-sum-square-imaginary-parts values))
          (x (putnam-1979-b6-sum-absolute-real-parts values))
          (d (- (* 2 x x) a)))
     (and (<= 0 d)
          (<= (+ (* a a) (* b b))
              (* d d))))))

(value-triple :itpeval-statement-checked)
:q
