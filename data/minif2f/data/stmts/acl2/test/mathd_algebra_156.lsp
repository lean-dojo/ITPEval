;; Statement-only formalization of miniF2F artifact mathd_algebra_156:
;; if f(t)=t^4 and g(t)=5*t^2-6 for every real t, and x and y are
;; intersections with x^2<y^2, then y^2-x^2=1. This file contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, order, and functions below preserve the source objects
;; directly. Every structural and pointwise law is an explicit premise;
;; DEFSTUB introduces no law, and no premise encodes the conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd156-real-p (value) t)
(defstub mathd156-zero () t)
(defstub mathd156-one () t)
(defstub mathd156-add (left right) t)
(defstub mathd156-mul (left right) t)
(defstub mathd156-neg (value) t)
(defstub mathd156-inv (value) t)
(defstub mathd156-lt (left right) t)
(defstub mathd156-f (value) t)
(defstub mathd156-g (value) t)

(defun mathd156-sub (left right)
  (mathd156-add left (mathd156-neg right)))

(defun mathd156-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd156-zero)
    (mathd156-add
     (mathd156-one)
     (mathd156-natural (1- n)))))

(defun mathd156-pow (value exponent)
  (declare (xargs :guard (natp exponent)))
  (if (zp exponent)
      (mathd156-one)
    (mathd156-mul
     value
     (mathd156-pow value (1- exponent)))))

(defun-sk mathd156-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (mathd156-real-p x)
          (mathd156-real-p y))
     (and
      (mathd156-real-p (mathd156-add x y))
      (mathd156-real-p (mathd156-mul x y))))
    (implies
     (mathd156-real-p x)
     (and
      (mathd156-real-p (mathd156-neg x))
      (mathd156-real-p (mathd156-inv x))))
    (implies
     (and
      (mathd156-real-p x)
      (mathd156-real-p y)
      (mathd156-real-p z))
     (equal
      (mathd156-add (mathd156-add x y) z)
      (mathd156-add x (mathd156-add y z))))
    (implies
     (and (mathd156-real-p x)
          (mathd156-real-p y))
     (equal (mathd156-add x y)
            (mathd156-add y x)))
    (implies
     (mathd156-real-p x)
     (and
      (equal (mathd156-add x (mathd156-zero)) x)
      (equal
       (mathd156-add x (mathd156-neg x))
       (mathd156-zero))))
    (implies
     (and
      (mathd156-real-p x)
      (mathd156-real-p y)
      (mathd156-real-p z))
     (equal
      (mathd156-mul (mathd156-mul x y) z)
      (mathd156-mul x (mathd156-mul y z))))
    (implies
     (and (mathd156-real-p x)
          (mathd156-real-p y))
     (equal (mathd156-mul x y)
            (mathd156-mul y x)))
    (implies
     (mathd156-real-p x)
     (equal (mathd156-mul x (mathd156-one)) x))
    (implies
     (and
      (mathd156-real-p x)
      (not (equal x (mathd156-zero))))
     (equal
      (mathd156-mul x (mathd156-inv x))
      (mathd156-one)))
    (equal (mathd156-inv (mathd156-zero))
           (mathd156-zero))
    (implies
     (and
      (mathd156-real-p x)
      (mathd156-real-p y)
      (mathd156-real-p z))
     (equal
      (mathd156-mul x (mathd156-add y z))
      (mathd156-add
       (mathd156-mul x y)
       (mathd156-mul x z)))))))

(defun-sk mathd156-order-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (mathd156-real-p x)
     (not (mathd156-lt x x)))
    (implies
     (and (mathd156-real-p x)
          (mathd156-real-p y))
     (or (mathd156-lt x y)
         (equal x y)
         (mathd156-lt y x)))
    (implies
     (and
      (mathd156-real-p x)
      (mathd156-real-p y)
      (mathd156-real-p z)
      (mathd156-lt x y)
      (mathd156-lt y z))
     (mathd156-lt x z))
    (implies
     (and
      (mathd156-real-p x)
      (mathd156-real-p y)
      (mathd156-real-p z))
     (iff
      (mathd156-lt x y)
      (mathd156-lt
       (mathd156-add x z)
       (mathd156-add y z))))
    (implies
     (and
      (mathd156-real-p x)
      (mathd156-real-p y)
      (mathd156-lt (mathd156-zero) x)
      (mathd156-lt (mathd156-zero) y))
     (mathd156-lt
      (mathd156-zero)
      (mathd156-mul x y))))))

(defun-sk mathd156-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd156-lt x (mathd156-natural n)))))

(defun-sk mathd156-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd156-real-p x)
    (mathd156-natural-bound-exists-p x))))

(defun mathd156-real-field-p ()
  (and
   (mathd156-real-p (mathd156-zero))
   (mathd156-real-p (mathd156-one))
   (not (equal (mathd156-zero) (mathd156-one)))
   (mathd156-lt (mathd156-zero) (mathd156-one))
   (mathd156-field-laws-p)
   (mathd156-order-laws-p)
   (mathd156-archimedean-p)))

(defun-sk mathd156-function-laws-p ()
  (forall
   (value)
   (implies
    (mathd156-real-p value)
    (and
     (mathd156-real-p (mathd156-f value))
     (mathd156-real-p (mathd156-g value))
     (equal
      (mathd156-f value)
      (mathd156-pow value 4))
     (equal
      (mathd156-g value)
      (mathd156-sub
       (mathd156-mul
        (mathd156-natural 5)
        (mathd156-pow value 2))
       (mathd156-natural 6)))))))

(defun-sk mathd-algebra-156-statement-p ()
  (forall
   (x y)
   (implies
    (and
     (mathd156-real-field-p)
     (mathd156-function-laws-p)
     (mathd156-real-p x)
     (mathd156-real-p y)
     (equal (mathd156-f x) (mathd156-g x))
     (equal (mathd156-f y) (mathd156-g y))
     (mathd156-lt
      (mathd156-pow x 2)
      (mathd156-pow y 2)))
    (equal
     (mathd156-sub
      (mathd156-pow y 2)
      (mathd156-pow x 2))
     (mathd156-one)))))

(value-triple :itpeval-statement-checked)
:q
