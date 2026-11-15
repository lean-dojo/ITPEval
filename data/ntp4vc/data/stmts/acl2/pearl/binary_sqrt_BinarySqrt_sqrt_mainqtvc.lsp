;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binary_sqrt_BinarySqrt_sqrt_mainqtvc: the binary-square-root entry
;; verification condition repeats nonnegativity of r and positivity of eps,
;; together with 1 <= 1 and the real identity eps = 1 * eps.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars range over an arbitrary real closed ordered field. Real closed
;; fields have the same first-order ordered-field theory as the mathematical
;; reals, so this preserves the real domain without restricting values to
;; ACL2 rationals.

(defstub bsqrt-real-op (ctx x) t)
(defstub bsqrt-add-op (ctx x y) t)
(defstub bsqrt-mul-op (ctx x y) t)
(defstub bsqrt-neg-op (ctx x) t)
(defstub bsqrt-inv-op (ctx x) t)
(defstub bsqrt-lt-op (ctx x y) t)

(defun bsqrt-real-p (ctx x)
  (if (bsqrt-real-op ctx x) t nil))

(defun bsqrt-add (ctx x y)
  (bsqrt-add-op ctx x y))

(defun bsqrt-mul (ctx x y)
  (bsqrt-mul-op ctx x y))

(defun bsqrt-neg (ctx x)
  (bsqrt-neg-op ctx x))

(defun bsqrt-inv (ctx x)
  (bsqrt-inv-op ctx x))

(defun bsqrt-lt (ctx x y)
  (if (bsqrt-lt-op ctx x y) t nil))

(defun bsqrt-le (ctx x y)
  (not (bsqrt-lt ctx y x)))

(defun-sk bsqrt-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (bsqrt-real-p ctx x)
      (bsqrt-real-p ctx y)
      (bsqrt-real-p ctx z))
     (and
      (bsqrt-real-p ctx (bsqrt-add ctx x y))
      (bsqrt-real-p ctx (bsqrt-mul ctx x y))
      (bsqrt-real-p ctx (bsqrt-neg ctx x))
      (bsqrt-real-p ctx (bsqrt-inv ctx x))
      (equal
       (bsqrt-add ctx (bsqrt-add ctx x y) z)
       (bsqrt-add ctx x (bsqrt-add ctx y z)))
      (equal (bsqrt-add ctx x y) (bsqrt-add ctx y x))
      (equal (bsqrt-add ctx x zero) x)
      (equal (bsqrt-add ctx x (bsqrt-neg ctx x)) zero)
      (equal
       (bsqrt-mul ctx (bsqrt-mul ctx x y) z)
       (bsqrt-mul ctx x (bsqrt-mul ctx y z)))
      (equal (bsqrt-mul ctx x y) (bsqrt-mul ctx y x))
      (equal (bsqrt-mul ctx x one) x)
      (equal (bsqrt-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal (bsqrt-mul ctx x (bsqrt-inv ctx x)) one))
      (equal
       (bsqrt-mul ctx x (bsqrt-add ctx y z))
       (bsqrt-add
        ctx
        (bsqrt-mul ctx x y)
        (bsqrt-mul ctx x z)))))))

(defun-sk bsqrt-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (bsqrt-real-p ctx x)
      (bsqrt-real-p ctx y)
      (bsqrt-real-p ctx z))
     (and
      (not (bsqrt-lt ctx x x))
      (or
       (equal x y)
       (bsqrt-lt ctx x y)
       (bsqrt-lt ctx y x))
      (implies
       (and
        (bsqrt-lt ctx x y)
        (bsqrt-lt ctx y z))
       (bsqrt-lt ctx x z))
      (implies
       (bsqrt-lt ctx x y)
       (bsqrt-lt
        ctx
        (bsqrt-add ctx x z)
        (bsqrt-add ctx y z)))
      (implies
       (and
        (bsqrt-lt ctx zero x)
        (bsqrt-lt ctx zero y))
       (bsqrt-lt ctx zero (bsqrt-mul ctx x y)))))))

(defun-sk bsqrt-positive-square-root-exists-p
    (ctx zero x)
  (exists (root)
    (and
     (bsqrt-real-p ctx root)
     (bsqrt-le ctx zero root)
     (equal (bsqrt-mul ctx root root) x))))

(defun-sk bsqrt-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (bsqrt-real-p ctx x)
      (bsqrt-lt ctx zero x))
     (bsqrt-positive-square-root-exists-p
      ctx zero x))))

(defun bsqrt-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (bsqrt-real-p ctx (car coefficients))
       (bsqrt-real-coefficient-list-p
        ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun bsqrt-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
      (bsqrt-add
       ctx
       (car coefficients)
       (bsqrt-mul
        ctx
        x
        (bsqrt-poly-eval
         ctx zero (cdr coefficients) x)))
    zero))

(defun-sk bsqrt-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (bsqrt-real-p ctx root)
     (equal
      (bsqrt-poly-eval ctx zero coefficients root)
      zero))))

(defun-sk bsqrt-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (bsqrt-real-coefficient-list-p ctx coefficients)
      (not (equal (car (last coefficients)) zero)))
     (bsqrt-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun bsqrt-real-context-p (ctx zero one)
  (and
   (bsqrt-real-p ctx zero)
   (bsqrt-real-p ctx one)
   (not (equal zero one))
   (bsqrt-lt ctx zero one)
   (bsqrt-field-laws-p ctx zero one)
   (bsqrt-order-laws-p ctx zero)
   (bsqrt-positive-square-root-laws-p ctx zero)
   (bsqrt-odd-root-laws-p ctx zero)))

(defun ntp4vc-pearl-binary-sqrt-binarysqrt-sqrt-mainqtvc-statement
    (ctx zero one r eps)
  (implies
   (and
    (bsqrt-real-context-p ctx zero one)
    (bsqrt-real-p ctx r)
    (bsqrt-real-p ctx eps)
    (bsqrt-le ctx zero r)
    (bsqrt-lt ctx zero eps))
   (and
    (bsqrt-le ctx zero r)
    (bsqrt-lt ctx zero eps)
    (<= 1 1)
    (equal eps (bsqrt-mul ctx one eps)))))

(value-triple :itpeval-statement-checked)
:q
