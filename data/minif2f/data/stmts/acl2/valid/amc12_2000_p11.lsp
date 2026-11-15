;; Statement-only formalization of miniF2F artifact amc12_2000_p11:
;; for all nonzero real a and b satisfying a*b = a-b, the expression
;; a/b + b/a - a*b is equal to 2. This file contains no proof.
;;
;; ACL2 has no native real field. The arbitrary characteristic-zero field
;; carrier below preserves the source variables and operations directly and
;; includes the real field as an instance. Every law is an explicit premise;
;; DEFSTUB introduces no law, and no premise encodes the conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub amc2000p11-real-p (value) t)
(defstub amc2000p11-zero () t)
(defstub amc2000p11-one () t)
(defstub amc2000p11-add (left right) t)
(defstub amc2000p11-mul (left right) t)
(defstub amc2000p11-neg (value) t)
(defstub amc2000p11-inv (value) t)
(defstub amc2000p11-of-rational (value) t)

(defun amc2000p11-sub (left right)
  (amc2000p11-add left (amc2000p11-neg right)))

(defun amc2000p11-div (left right)
  (amc2000p11-mul left (amc2000p11-inv right)))

(defun-sk amc2000p11-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (amc2000p11-real-p x)
          (amc2000p11-real-p y))
     (and
      (amc2000p11-real-p (amc2000p11-add x y))
      (amc2000p11-real-p (amc2000p11-mul x y))))
    (implies
     (amc2000p11-real-p x)
     (and
      (amc2000p11-real-p (amc2000p11-neg x))
      (amc2000p11-real-p (amc2000p11-inv x))))
    (implies
     (and
      (amc2000p11-real-p x)
      (amc2000p11-real-p y)
      (amc2000p11-real-p z))
     (equal
      (amc2000p11-add (amc2000p11-add x y) z)
      (amc2000p11-add x (amc2000p11-add y z))))
    (implies
     (and (amc2000p11-real-p x)
          (amc2000p11-real-p y))
     (equal (amc2000p11-add x y)
            (amc2000p11-add y x)))
    (implies
     (amc2000p11-real-p x)
     (and
      (equal (amc2000p11-add x (amc2000p11-zero)) x)
      (equal
       (amc2000p11-add x (amc2000p11-neg x))
       (amc2000p11-zero))))
    (implies
     (and
      (amc2000p11-real-p x)
      (amc2000p11-real-p y)
      (amc2000p11-real-p z))
     (equal
      (amc2000p11-mul (amc2000p11-mul x y) z)
      (amc2000p11-mul x (amc2000p11-mul y z))))
    (implies
     (and (amc2000p11-real-p x)
          (amc2000p11-real-p y))
     (equal (amc2000p11-mul x y)
            (amc2000p11-mul y x)))
    (implies
     (amc2000p11-real-p x)
     (equal (amc2000p11-mul x (amc2000p11-one)) x))
    (implies
     (and
      (amc2000p11-real-p x)
      (not (equal x (amc2000p11-zero))))
     (equal
      (amc2000p11-mul x (amc2000p11-inv x))
      (amc2000p11-one)))
    (equal (amc2000p11-inv (amc2000p11-zero))
           (amc2000p11-zero))
    (implies
     (and
      (amc2000p11-real-p x)
      (amc2000p11-real-p y)
      (amc2000p11-real-p z))
     (equal
      (amc2000p11-mul x (amc2000p11-add y z))
      (amc2000p11-add
       (amc2000p11-mul x y)
       (amc2000p11-mul x z)))))))

(defun-sk amc2000p11-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (amc2000p11-real-p (amc2000p11-of-rational p))
     (equal (amc2000p11-of-rational 0)
            (amc2000p11-zero))
     (equal (amc2000p11-of-rational 1)
            (amc2000p11-one))
     (equal
      (amc2000p11-of-rational (+ p q))
      (amc2000p11-add
       (amc2000p11-of-rational p)
       (amc2000p11-of-rational q)))
     (equal
      (amc2000p11-of-rational (* p q))
      (amc2000p11-mul
       (amc2000p11-of-rational p)
       (amc2000p11-of-rational q)))
     (iff
      (equal p q)
      (equal
       (amc2000p11-of-rational p)
       (amc2000p11-of-rational q)))))))

(defun amc2000p11-real-field-p ()
  (and
   (amc2000p11-real-p (amc2000p11-zero))
   (amc2000p11-real-p (amc2000p11-one))
   (not (equal (amc2000p11-zero)
               (amc2000p11-one)))
   (amc2000p11-field-laws-p)
   (amc2000p11-rational-laws-p)))

(defun-sk amc12-2000-p11-statement-p ()
  (forall
   (a b)
   (implies
    (and
     (amc2000p11-real-field-p)
     (amc2000p11-real-p a)
     (amc2000p11-real-p b)
     (not (equal a (amc2000p11-zero)))
     (not (equal b (amc2000p11-zero)))
     (equal
      (amc2000p11-mul a b)
      (amc2000p11-sub a b)))
    (equal
     (amc2000p11-sub
      (amc2000p11-add
       (amc2000p11-div a b)
       (amc2000p11-div b a))
      (amc2000p11-mul a b))
     (amc2000p11-of-rational 2)))))

(value-triple :itpeval-statement-checked)
:q
