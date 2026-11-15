;; Statement-only formalization of miniF2F artifact mathd_algebra_28:
;; if f(x)=2*x^2+5*x+c for every real x and f is nonpositive somewhere,
;; then c is at most 25/8. This file contains no proof.
;;
;; ACL2 has no native complete real field. The arbitrary carrier,
;; operations, rational embedding, order, and function below preserve the
;; source objects directly. Every law is an explicit statement premise;
;; DEFSTUB introduces no law, and no premise encodes the conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd28-real-p (value) t)
(defstub mathd28-zero () t)
(defstub mathd28-one () t)
(defstub mathd28-add (left right) t)
(defstub mathd28-mul (left right) t)
(defstub mathd28-neg (value) t)
(defstub mathd28-inv (value) t)
(defstub mathd28-lt (left right) t)
(defstub mathd28-of-rational (value) t)
(defstub mathd28-f (value) t)

(defun mathd28-sub (left right)
  (mathd28-add left (mathd28-neg right)))

(defun mathd28-le (left right)
  (or (mathd28-lt left right)
      (equal left right)))

(defun mathd28-pow2 (value)
  (mathd28-mul value value))

(defun mathd28-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd28-zero)
    (mathd28-add
     (mathd28-one)
     (mathd28-natural (1- n)))))

(defun-sk mathd28-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (mathd28-real-p x)
          (mathd28-real-p y))
     (and
      (mathd28-real-p (mathd28-add x y))
      (mathd28-real-p (mathd28-mul x y))))
    (implies
     (mathd28-real-p x)
     (and
      (mathd28-real-p (mathd28-neg x))
      (mathd28-real-p (mathd28-inv x))))
    (implies
     (and
      (mathd28-real-p x)
      (mathd28-real-p y)
      (mathd28-real-p z))
     (equal
      (mathd28-add (mathd28-add x y) z)
      (mathd28-add x (mathd28-add y z))))
    (implies
     (and (mathd28-real-p x)
          (mathd28-real-p y))
     (equal (mathd28-add x y)
            (mathd28-add y x)))
    (implies
     (mathd28-real-p x)
     (and
      (equal (mathd28-add x (mathd28-zero)) x)
      (equal
       (mathd28-add x (mathd28-neg x))
       (mathd28-zero))))
    (implies
     (and
      (mathd28-real-p x)
      (mathd28-real-p y)
      (mathd28-real-p z))
     (equal
      (mathd28-mul (mathd28-mul x y) z)
      (mathd28-mul x (mathd28-mul y z))))
    (implies
     (and (mathd28-real-p x)
          (mathd28-real-p y))
     (equal (mathd28-mul x y)
            (mathd28-mul y x)))
    (implies
     (mathd28-real-p x)
     (equal (mathd28-mul x (mathd28-one)) x))
    (implies
     (and
      (mathd28-real-p x)
      (not (equal x (mathd28-zero))))
     (equal
      (mathd28-mul x (mathd28-inv x))
      (mathd28-one)))
    (equal (mathd28-inv (mathd28-zero))
           (mathd28-zero))
    (implies
     (and
      (mathd28-real-p x)
      (mathd28-real-p y)
      (mathd28-real-p z))
     (equal
      (mathd28-mul x (mathd28-add y z))
      (mathd28-add
       (mathd28-mul x y)
       (mathd28-mul x z)))))))

(defun-sk mathd28-order-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (mathd28-real-p x)
     (not (mathd28-lt x x)))
    (implies
     (and (mathd28-real-p x)
          (mathd28-real-p y))
     (or (mathd28-lt x y)
         (equal x y)
         (mathd28-lt y x)))
    (implies
     (and
      (mathd28-real-p x)
      (mathd28-real-p y)
      (mathd28-real-p z)
      (mathd28-lt x y)
      (mathd28-lt y z))
     (mathd28-lt x z))
    (implies
     (and
      (mathd28-real-p x)
      (mathd28-real-p y)
      (mathd28-real-p z))
     (iff
      (mathd28-lt x y)
      (mathd28-lt
       (mathd28-add x z)
       (mathd28-add y z))))
    (implies
     (and
      (mathd28-real-p x)
      (mathd28-real-p y)
      (mathd28-lt (mathd28-zero) x)
      (mathd28-lt (mathd28-zero) y))
     (mathd28-lt
      (mathd28-zero)
      (mathd28-mul x y))))))

(defun-sk mathd28-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (mathd28-real-p (mathd28-of-rational p))
     (equal (mathd28-of-rational 0)
            (mathd28-zero))
     (equal (mathd28-of-rational 1)
            (mathd28-one))
     (equal
      (mathd28-of-rational (+ p q))
      (mathd28-add
       (mathd28-of-rational p)
       (mathd28-of-rational q)))
     (equal
      (mathd28-of-rational (* p q))
      (mathd28-mul
       (mathd28-of-rational p)
       (mathd28-of-rational q)))
     (iff
      (equal p q)
      (equal
       (mathd28-of-rational p)
       (mathd28-of-rational q)))
     (iff
      (< p q)
      (mathd28-lt
       (mathd28-of-rational p)
       (mathd28-of-rational q)))))))

(defun-sk mathd28-natural-bound-exists-p (x)
  (exists
   (n)
   (and
    (natp n)
    (mathd28-lt x (mathd28-natural n)))))

(defun-sk mathd28-archimedean-p ()
  (forall
   (x)
   (implies
    (mathd28-real-p x)
    (mathd28-natural-bound-exists-p x))))

(defun mathd28-real-field-p ()
  (and
   (mathd28-real-p (mathd28-zero))
   (mathd28-real-p (mathd28-one))
   (not (equal (mathd28-zero) (mathd28-one)))
   (mathd28-lt (mathd28-zero) (mathd28-one))
   (mathd28-field-laws-p)
   (mathd28-order-laws-p)
   (mathd28-rational-laws-p)
   (mathd28-archimedean-p)))

(defun-sk mathd28-function-law-p (c)
  (forall
   (x)
   (implies
    (mathd28-real-p x)
    (equal
     (mathd28-f x)
     (mathd28-add
      (mathd28-add
       (mathd28-mul
        (mathd28-of-rational 2)
        (mathd28-pow2 x))
       (mathd28-mul
        (mathd28-of-rational 5)
        x))
      c)))))

(defun-sk mathd28-nonpositive-witness-p ()
  (exists
   (x)
   (and
    (mathd28-real-p x)
    (mathd28-le (mathd28-f x)
                (mathd28-zero)))))

(defun-sk mathd-algebra-28-statement-p ()
  (forall
   (c)
   (implies
    (and
     (mathd28-real-field-p)
     (mathd28-real-p c)
     (mathd28-function-law-p c)
     (mathd28-nonpositive-witness-p))
    (mathd28-le
     c
     (mathd28-of-rational 25/8)))))

(value-triple :itpeval-statement-checked)
:q
